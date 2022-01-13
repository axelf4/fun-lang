/// Lexical analysis.
use logos::Logos;
use std::fmt;
use std::ops::Range;

#[derive(Logos, Clone, Copy, PartialEq, Debug)]
pub enum Token<'input> {
    #[regex("-?[0-9]+", |lex| lex.slice().parse(), priority = 100)]
    Number(i32),
    #[regex(r#"[[:^space:]--[\\.()@"]]+"#)]
    Ident(&'input str),

    #[token(r"\")]
    BackSlash,
    #[token("->")]
    Arrow,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("=")]
    Equals,
    #[token(":")]
    Colon,

    #[token("case")]
    Case,
    #[token("of")]
    Of,
    #[token("let")]
    Let,
    #[token("in")]
    In,

    LayoutStart,
    LayoutSep,
    LayoutEnd,

    #[error]
    #[regex(r"[ \n\f]+", logos::skip)]
    #[regex(r"--.*", logos::skip)]
    Error,
}

impl<'input> fmt::Display for Token<'input> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        use Token::*;
        match self {
            Number(n) => n.fmt(fmt),
            Ident(s) => s.fmt(fmt),
            BackSlash => write!(fmt, "\\"),
            Arrow => write!(fmt, "->"),
            LParen => write!(fmt, "("),
            RParen => write!(fmt, ")"),
            Equals => write!(fmt, "="),
            Colon => write!(fmt, ":"),
            Case => write!(fmt, "case"),
            Of => write!(fmt, "of"),
            Let => write!(fmt, "let"),
            In => write!(fmt, "in"),
            LayoutStart => write!(fmt, "{{"),
            LayoutSep => write!(fmt, ","),
            LayoutEnd => write!(fmt, "}}"),
            Error => write!(fmt, "error"),
        }
    }
}

#[derive(PartialEq, Eq, Debug)]
pub struct Error;

impl<'input> fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "error")
    }
}

pub type Spanned<Tok, Loc, Error> = Result<(Loc, Tok, Loc), Error>;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Delimiter {
    Paren,
    LetIn,
    CaseOf,
}

#[derive(PartialEq, Eq, Debug)]
enum State {
    LayoutStart(usize),
    Layout(usize),
    Delimiter(Delimiter),
}

impl State {
    /// Returns whether this stack entry was implicitly added.
    ///
    /// Implicit entries should be collapsed when explicit layout
    /// tokens are encountered in lookahead.
    fn is_implicit(&self) -> bool {
        match self {
            State::LayoutStart(_) | State::Layout(_) => true,
            State::Delimiter(_) => false,
        }
    }
}

pub struct Lexer<'input> {
    input: &'input str,
    iter: logos::SpannedIter<'input, Token<'input>>,
    /// The start byte index of the previous token.
    cursor: usize,
    /// The column index of the previous token.
    column: usize,
    line_start: usize,
    next: Vec<(usize, Token<'input>, usize)>,

    stack: Vec<State>,
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str) -> Self {
        Self {
            input,
            iter: Token::lexer(input).spanned(),
            cursor: 0,
            column: 0,
            line_start: 0,
            stack: Vec::new(),
            next: Vec::new(),
        }
    }

    fn collapse(&mut self, mut f: impl FnMut(&State) -> bool) {
        let pos = self.cursor;
        while let Some(state) = self.stack.last() {
            if !f(state) {
                break;
            }
            match state {
                // Empty layout
                State::LayoutStart(_) => {
                    self.next
                        .extend([(pos, Token::LayoutEnd, pos), (pos, Token::LayoutStart, pos)]);
                }

                State::Layout(_) => self.next.push((pos, Token::LayoutEnd, pos)),
                State::Delimiter(_) => {}
            }
            self.stack.pop();
        }
    }
}

impl<'input> Iterator for Lexer<'input> {
    type Item = Spanned<Token<'input>, usize, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(item) = self.next.pop() {
            return Some(Ok(item));
        }

        let (token, Range { start, end }) = if let Some(item) = self.iter.next() {
            item
        } else {
            // Pop all remaining stack entries
            self.cursor = self.input.len();
            self.collapse(|_| true);
            return self.next.pop().map(Ok);
        };
        if let Token::Error = token {
            return Some(Err(Error));
        }
        self.next.push((start, token, end));

        let mut newline = false;
        self.column =
            self.input[self.cursor..start]
                .chars()
                .fold(self.column, |acc, ch| match ch {
                    '\n' => {
                        newline = true;
                        0
                    }
                    _ => acc + 1,
                });
        self.cursor = start;
        if newline {
            self.line_start = self.column;
        }

        let column = self.column;
        let is_offside = |state: &State| match state {
            State::Layout(layout_col) if newline && column < *layout_col => true,
            _ => false,
        };
        /*
        let until_delim = |delim| {
            let mut saw_delim = false;
            move |state: &State| {
                let result = !saw_delim;
                saw_delim = state == &State::Delimiter(delim);
                result
            }
        };
        */

        let mut should_insert_default = false;
        match token {
            Token::LParen => {
                self.stack.push(State::Delimiter(Delimiter::Paren));
                self.collapse(is_offside);
                should_insert_default = true;
            }
            Token::RParen => {
                // self.collapse(until_delim(Delimiter::Paren));
                self.collapse(State::is_implicit);
                if self.stack.last() == Some(&State::Delimiter(Delimiter::Paren)) {
                    self.stack.pop();
                }
            }

            Token::Case => {
                self.collapse(is_offside);
                self.stack.push(State::Delimiter(Delimiter::CaseOf));
            }
            Token::Of => {
                self.collapse(State::is_implicit);
                if self.stack.last() == Some(&State::Delimiter(Delimiter::CaseOf)) {
                    self.stack.pop();
                }
                self.stack.push(State::LayoutStart(self.line_start));
            }

            Token::Let => {
                self.collapse(is_offside);
                self.stack.push(State::Delimiter(Delimiter::LetIn));
                self.stack.push(State::LayoutStart(self.line_start));
            }
            Token::In => {
                // Collapse up to and including "let" start marker
                self.collapse(State::is_implicit);
                if self.stack.last() == Some(&State::Delimiter(Delimiter::LetIn)) {
                    self.stack.pop();
                }
            }

            _ => {
                should_insert_default = true;
            }
        }

        if should_insert_default {
            match self.stack.last() {
                Some(State::LayoutStart(min_col)) if self.column > *min_col => {
                    self.stack.pop();
                    self.stack.push(State::Layout(self.column));
                    self.next.push((start, Token::LayoutStart, start));
                }

                Some(State::Layout(layout_col)) if newline && self.column == *layout_col => {
                    self.next.push((start, Token::LayoutSep, start));
                }

                Some(State::Layout(_)) => {}
                Some(State::Delimiter(_)) => {}
                _ => {}
            }
        }

        Some(Ok(self.next.pop().expect("The next token got popped?")))
    }
}

mod tests {
    use super::*;
    use Token::*;

    #[test]
    fn test_lex_number() {
        assert_eq!(
            Lexer::new("-42").collect::<Result<_, _>>(),
            Ok(vec![(0, Number(-42), 3)])
        );
    }

    #[test]
    fn test_lex_case_layout_good() {
        let expected = Ok(vec![
            (0, Case, 4),
            (5, Number(0), 6),
            (7, Of, 9),
            (11, LayoutStart, 11),
            (11, Ident("x"), 12),
            (13, Arrow, 15),
            (16, Ident("x"), 17),
            (17, LayoutEnd, 17),
        ]);
        assert_eq!(
            Lexer::new("case 0 of\n x -> x").collect::<Result<_, _>>(),
            expected
        );
        assert_eq!(
            Lexer::new("case 0 of  x -> x").collect::<Result<_, _>>(),
            expected
        );
    }

    #[test]
    fn test_lex_layout_paren_parse_rule() {
        assert_eq!(
            Lexer::new("(case 0 of) x -> x").collect::<Result<_, _>>(),
            Ok(vec![
                (0, LParen, 1),
                (1, Case, 5),
                (6, Number(0), 7),
                (8, Of, 10),
                (10, LayoutStart, 10),
                (10, LayoutEnd, 10),
                (10, RParen, 11),
                (12, Ident("x"), 13),
                (14, Arrow, 16),
                (17, Ident("x"), 18),
            ])
        );
    }

    #[test]
    fn test_lex_nested_let_in() {
        assert_eq!(
            Lexer::new(
                "let
  x = let y = 0
          z = y
      in z in x"
            )
            .collect::<Result<_, _>>(),
            Ok(vec![
                (0, Let, 3),
                (6, LayoutStart, 6),
                (6, Ident("x"), 7),
                (8, Equals, 9),
                (10, Let, 13),
                (14, LayoutStart, 14),
                (14, Ident("y"), 15),
                (16, Equals, 17),
                (18, Number(0), 19),
                (30, LayoutSep, 30),
                (30, Ident("z"), 31),
                (32, Equals, 33),
                (34, Ident("y"), 35),
                (42, LayoutEnd, 42),
                (42, In, 44),
                (45, Ident("z"), 46),
                (47, LayoutEnd, 47),
                (47, In, 49),
                (50, Ident("x"), 51)
            ])
        );
    }
}
