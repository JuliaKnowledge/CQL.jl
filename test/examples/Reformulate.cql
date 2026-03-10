
schema S = literal : sql {
entities
	CUST SUPPCATALOG WEBORDER
attributes
	CUST_ID : CUST -> Integer
	CNATION : CUST -> Text
	SUPP_ID : WEBORDER -> Smallint
	ORDERKEY : WEBORDER -> Varchar
	CUST_ID : WEBORDER -> Integer
	SUPP_ID : SUPPCATALOG -> Smallint
	SADDR : SUPPCATALOG -> Other
	SNATION : SUPPCATALOG -> String
}

instance I = literal : S {
	generators
		CUST_3:CUST	CUST_2:CUST	CUST_1:CUST	
		WEBORDER_2:WEBORDER	WEBORDER_1:WEBORDER	
		SUPPCATALOG_4:SUPPCATALOG	SUPPCATALOG_3:SUPPCATALOG	
		SUPPCATALOG_2:SUPPCATALOG	SUPPCATALOG_1:SUPPCATALOG
	equations	
		CUST_3.CUST_ID = 3	
		CUST_3.CNATION = jpy	
		CUST_2.CUST_ID = 2	
		CUST_2.CNATION = uk	
		CUST_1.CUST_ID = 1	
		CUST_1.CNATION = usa	
		WEBORDER_2.SUPP_ID = 52	
		WEBORDER_2.ORDERKEY = order2	
		WEBORDER_2.CUST_ID = 1	
		WEBORDER_1.SUPP_ID = 51	
		WEBORDER_1.ORDERKEY = order1	
		WEBORDER_1.CUST_ID = 1	
		SUPPCATALOG_4.SUPP_ID = 54	
		SUPPCATALOG_4.SADDR = s4addr	
		SUPPCATALOG_4.SNATION = mexico	
		SUPPCATALOG_3.SUPP_ID = 53	
		SUPPCATALOG_3.SADDR = s3addr	
		SUPPCATALOG_3.SNATION = cn	
		SUPPCATALOG_2.SUPP_ID = 52	
		SUPPCATALOG_2.SADDR = s2addr	
		SUPPCATALOG_2.SNATION = india	
		SUPPCATALOG_1.SUPP_ID = 51	
		SUPPCATALOG_1.SADDR = s1addr	
		SUPPCATALOG_1.SNATION = usa	
}
 

schema T = literal : sql {
	entities
		mastercust mastersupp supp2cust
	attributes
		cnation : mastercust -> Text
		cust_id : mastercust -> Integer
		cust_id : supp2cust -> Integer
		orderkey : supp2cust -> Varchar
		supp_id : supp2cust -> Smallint
		saddr : mastersupp -> Other
		snation : mastersupp -> String
		supp_id : mastersupp -> Smallint
}

instance J = literal : T {
	generators
		x:mastercust	y:mastersupp	z:mastersupp	w:supp2cust	v:supp2cust
	equations	
		x.cnation = usa	
		x.cust_id = 1	
		y.saddr = s2addr	
		y.snation = india	
		y.supp_id = 52	
		z.saddr = s1addr	
		z.snation = usa	
		z.supp_id = 51	
		w.cust_id = 1	
		w.orderkey = order2	
		w.supp_id = 52	
		v.cust_id = 1	
		v.orderkey = order1	
		v.supp_id = 51
}

schema ST = literal : sql {	imports S T }

instance IJ = literal : ST {
	imports I J
}

constraints C = all IJ T

query Qold = simple : ST {
	from s:SUPPCATALOG w:WEBORDER 
	where w.SUPP_ID=s.SUPP_ID 
	attributes SNATION->s.SNATION
		CUST_ID->w.CUST_ID
		SADDR->s.SADDR
		SUPP_ID->w.SUPP_ID
}

query Qnew = reformulate C (chase C Qold) T 0 
instance QoldResult = eval Qold IJ
instance QnewResult = eval Qnew IJ
