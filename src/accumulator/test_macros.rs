#[macro_export]
macro_rules! get_json_field {
    ($idx: literal, $json: ident) => {
        $json[$idx].as_array().expect("Test data is missing")
    };
}
#[macro_export]
macro_rules! get_u64_array_from_obj {
    ($value: ident) => {{
        let mut new_vec = vec![];
        for i in $value {
            new_vec.push(i.as_u64().unwrap());
        }
        new_vec
    }};
}

#[macro_export]
macro_rules! get_str_array_from_obj {
    ($value: ident) => {{
        let mut new_vec = vec![];
        for i in $value {
            new_vec.push(i.as_str().unwrap());
        }
        new_vec
    }};
}

#[macro_export]
macro_rules! get_hash_array_from_obj {
    ($value: ident) => {{
        let mut new_vec = vec![];
        for i in $value {
            new_vec.push(bitcoin_hashes::sha256::Hash::from_str(i.as_str().unwrap()).unwrap());
        }
        new_vec
    }};
}
