use salsa::DebugWithDb;

#[derive(Default)]
#[salsa::db(crate::Jar)]
pub(crate) struct Database {
    storage: salsa::Storage<Self>,
}

impl salsa::Database for Database {
    fn salsa_event(&self, event: salsa::Event) {
        if let salsa::EventKind::WillExecute { .. } = event.kind {
            println!("salsa_event: {:?}", event.debug(self));
        }
    }
}
