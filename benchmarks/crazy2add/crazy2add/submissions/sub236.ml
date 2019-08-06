type crazy2 = NIL
			| ZERO of crazy2
			| ONE of crazy2
			| MONE of crazy2
let rec crazy2add: crazy2 * crazy2 -> crazy2 =
	fun (input1, input2) ->
	match (input1, input2) with
	| (NIL, NIL) -> NIL
	| (NIL, input2) -> input2
	| (input1, NIL) -> input1
	| (ZERO a, ZERO b) -> ZERO (crazy2add(a,b))
	| (ZERO a, ONE b) -> ONE (crazy2add(a,b))
	| (ZERO a, MONE b) -> MONE (crazy2add(a,b))
	| (ONE a, ZERO b) -> ONE(crazy2add(a,b))
	| (ONE a, ONE b) -> ZERO (crazy2add(ONE NIL, crazy2add(a,b)) )
	| (ONE a, MONE b) -> ZERO(crazy2add(a,b))
	| (MONE a, ZERO b) -> MONE(crazy2add(a,b))
	| (MONE a, ONE b) -> ZERO(crazy2add(a,b))
	| (MONE a, MONE b) -> ZERO(crazy2add(MONE NIL, crazy2add(a,b)) )
