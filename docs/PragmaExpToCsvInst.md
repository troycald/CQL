Emits an instance as a set of CSV files, one file per entity and one column per attribute and foreign key.  
The file for en will be a CSV file with a header; the fields of the header will be an ID column name (specified using options), as well as any attributes and foreign keys whose domain is en .   CQL values that are not constants will be exported as nulls.  
See id_column_name, and start_ids_at and csv_emit_ids