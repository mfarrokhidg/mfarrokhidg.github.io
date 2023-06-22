##################################################
# The function returns whether the number n is a 
# Cayley number.
#
# The output is a list [true/false/fail, MRxxxxxxx].
# The first element is true, false, or fail 
# if n is a Cayley number, a non-Cayley number, 
# or a number that is not yet determined to be 
# Cayley or non-Cayley. In case the first element 
# is true or false the second element is the 
# Mathematical Review of a paper in which the 
# number n is proved (or cited properly) to be 
# Cyaley or non-Cayley.
##################################################
IsCayleyNumber := function(n)
local IsSquareFreeCayleyNumber, issquarefreecayleynumber, primepower, x;

	##################################################
	# The function checks whether the square-free 
	# number n is Cayley number by known results 
	# without checking divisors.
	##################################################
	IsSquareFreeCayleyNumber := function(n)
	local factors, p, q, r, e, qe, qep, qen, re, k, ke, kk, binomials;

	factors := Factors(n);

	#jt:1967
	if Number(factors) = 1 then
		return [true, "MR0211908"];
	elif Number(factors) = 2 then
		p := factors[1];
		q := factors[2];
		
		#ba-rfp:1982
		if (q - 1) mod (p ^ 2) = 0 then
			return [false, "MR0658968"];
		
		#cep-myx:1993, bdm-cep:1996
		elif (q = 2 * p - 1 and q > 3) or (q = (p ^ 2 +1) / 2) then
			return [false, "MR1244933, MR1397877"];
		
		#dm-rs:1992, bdm-cep:1996
		elif IsPrimePowerInt(q - 1) and (((q - 2) mod p = 0) or (p = (q - 1) / 2 - 1)) then
			return [false, "MR1174460, MR1397877"];
		
		#dm-rs:1992, bdm-cep:1996
		elif IsPrimePowerInt(q + 1) and p = (q + 1) / 2 + 1 then
			return [false, "MR1174460, MR1397877"];
		
		#dm-rs:1992, bdm-cep:1996
		elif p = 7 and q = 11 then
			return [false, "MR1174460, MR1244933, MR1397877"];

		#bdm-cep:1996 
		else
			return [true, "MR1397877"];
		fi;
	elif Number(factors) = 3 then
		p := factors[1];
		q := factors[2];
		r := factors[3];

		if IsOddInt(n) then
			e := PValuation((n - 1) / 2, 2);

			if IsPrimePowerInt(q + 1) then
				qe := PValuation(q + 1, 2);
			else
				qe := 0;
			fi;

			if IsPrimePowerInt(qe - 1) then
				qep := PValuation(q - 1, 2);
			else
				qep := 0;
			fi;

			if IsPrimePowerInt(qe + 1) then
				qen := PValuation(q + 1, 2);
			else
				qen := 0;
			fi;

			if IsPrimePowerInt(r + 1) then
				re := PValuation(r + 1, 2);
			else
				re := 0;
			fi;

			k := (p + q - 2) / (q - p);
			if IsPrimeInt(k) and IsPrimePowerInt(r * (k - 1) + 1) and r mod k = 1 then
				ke := PValuation(r * (k - 1) + 1, k);
			else
				ke := 0;
			fi;

			if 3 * p - 3 = RootInt(3 * p - 3) ^ 2 then
				kk := (RootInt(3 * p - 3) + 1) / 2;
			else
				kk := 0;
			fi;
		fi;

		#mai-cep:2001
		if ((q - 1) mod p ^ 2 = 0) or ((r - 1) mod p ^ 2 = 0) or ((r - 1) mod q ^ 2 = 0) then
			return [false, "MR1809423"];

		#mai-cep:2001
		elif true in List(Filtered(factors, IsOddInt), s -> (2 * s - 1) in factors or (s ^ 2 + 1) / 2 in factors) then
			return [false, "MR1809423"];

		#mai-cep:2001
		elif true in List([q, r], s -> IsPrimePowerInt(s - 1) and ((s - 1) / 2 - 1 in factors or Number(Intersection(DivisorsInt(q - 2), factors)) > 0)) then
			return [false, "MR1809423"];

		#mai-cep:2001
		elif true in List(factors, s -> IsPrimePowerInt(s + 1) and ((s + 1) / 2 + 1) in factors) then
			return [false, "MR1809423"];

		#mai-cep:2001
		elif IsSubsetSet(factors, [7, 11]) then
			return [false, "MR1809423"];

		#mai-cep:2001
		elif IsOddInt(n) and e > 0 and e = 2^ PValuation(e, 2) and n = (2 ^ e + 1) * (4 ^ e + 1) then
			return [false, "MR1809423"];

		#mai-cep:2001
		elif IsOddInt(n) and p * q in [2 * r + 1, 2 * r - 1] then
			return [false, "MR1809423"];

		#mai-cep:2001
		elif  p * q = (r + 1) / 2 then
			return [false, "MR1809423"];

		#mai-cep:2001
		elif IsOddInt(n) and (p * q = (r ^ 2 + 1) / 2 or p * r = (q ^ 2 + 1) / 2) then
			return [false, "MR1809423"];

		#mai-cep:2001
		elif IsOddInt(n) and (p * q in List([1, 2, 5], x -> (r ^ 2 - 1) / (24 * x)) or p * r in List([1, 2, 5], x -> (q ^ 2 - 1) / (24 * x))) then
			return [false, "MR1809423"];

		#mai-cep:2001
		elif IsOddInt(n) and ((IsPrimePowerInt(p * q - 1) and p * q - 2 mod r = 0) or (IsPrimePowerInt(p * r - 1) and p * r - 2 mod q = 0) or (IsPrimePowerInt(q * r - 1) and q * r - 2 mod p = 0)) then
			return [false, "MR1809423"];

		#mai-cep:2001
		elif PValuation(q - 1, p) = 1 and PValuation(r - 1, q) = 1 then
			return [false, "MR1809423"];

		#mai-cep:2001
		elif IsOddInt(n) and q = (3 * p + 1) / 2 and r = 3 * p + 2 then
			return [false, "MR1809423"];

		#mai-cep:2001
		elif IsOddInt(n) and q = 6 * p - 1 and r = 6 * p + 1 then
			return [false, "MR1809423"];

		#mai-cep:2001
		elif IsOddInt(n) and q = (r - 1) / 2 and (r + 1) mod p = 0 then
			return [false, "MR1809423"];

		#mai-cep:2001
		elif IsOddInt(n) and p = (r - 1) / 2 and q = (p + 1) / 2 then
			return [false, "MR1809423"];

		#mai-cep:2001
		elif IsOddInt(n) and IsPrimeInt(ke) and IsPrimeInt((ke + 1) / 2) and p = (k ^ ((ke + 1) / 2) + 1) / (k + 1) and q = (k ^ ((ke + 1) / 2) -1) / (k - 1) and r = (k ^ ke - 1) / (k - 1) then
			return [false, "MR1809423"];

		#mai-cep:2001
		elif IsOddInt(n) and IsPrimeInt(ke) and IsPrimeInt((ke - 1) / 2) and p = (k ^ ((ke - 1) / 2) + 1) / (k + 1) and q = (k ^ ((ke - 1) / 2) -1) / (k - 1) and r = (k ^ ke - 1) / (k - 1) then
			return [false, "MR1809423"];

		#mai-cep:2001
		elif IsOddInt(n) and IsPrimeInt(kk) and p = (kk ^ 3 + 1) / (kk + 1) and q = (kk ^ 5 - 1) / (kk - 1) and p = (kk ^ 7 - 1) / (kk - 1) then
			return [false, "MR1809423"];

		#mai-cep:2001
		elif IsOddInt(n) and IsPrimeInt(re) and p = 3 and q = (2 ^ re + 1) / 3 then
			return [false, "MR1809423"];

		#mai-cep:2001
		elif IsOddInt(n) and IsPrimeInt(qe) and qep > 0 and p = (2 ^ qe + 1) / 3 and r = 4 ^ (qe - 1) + 1 then
			return [false, "MR1809423"];

		#mai-cep:2001
		elif IsOddInt(n) and IsPrimeInt(qe) and qen > 0 and p = (2 ^ qe + 1) / 3 and r = 4 ^ (qe + 1) + 1 then
			return [false, "MR1809423"];

		#mai-cep:2001
		elif p = 5 and q = 11 and r = 19 then
			return [false, "MR1809423"];

		#mai-cep:2001
		elif p = 7 and q = 73 and r = 257 then
			return [false, "MR1809423"];

		#mai-cep:2001
		elif p = 2 and q = 7 and r = 19 then
			return [false, "MR1809423"];

		#mai-cep:2001
		else
			return [true, "MR1809423"];
		fi;

	#rf-jg-mw:1971
	elif IsEvenInt(n) and true in List(factors, x -> x mod 4 = 1) then
		return [false, "MR0289365"];

	#mfdg-eg-hrm-frm
	elif Filtered(RootsOfPolynomial(x * (x + 1) - n), p -> not IsPrimeInt(p + 1)) <> [] then
		return [false, "MR???????"];

	#cdg:1980
	elif n in Flat(List([3..LogInt(n, 2)], x -> List([(2 * x + 1)..(LogInt(n * Factorial(x), x) + x)], y -> Binomial(y, x)))) then
		return [false, "MR0592856"];

	#cdg:1980
	elif Filtered(RootsOfPolynomial(x * (x - 1) / 2 - n), p -> IsPosInt(p) and not (IsPrimePowerInt(p) and p mod 4 = 3)) <> [] then
		return [false, "MR0592856"];

	#mew:1990
	elif Filtered(RootsOfPolynomial(x * (2 * x - 1) - n), IsPosInt) <> [] then
		return [false, "MR1096997"];

	#mew:1990
	elif Filtered(RootsOfPolynomial(x * (2 * x - 1) * (16 * x ^ 2 - 1) - n), IsPosInt) <> [] then
		return [false, "MR1096997"];

	#mew:1990
	elif Filtered(RootsOfPolynomial(x * (2 * x - 1) * (16 * x ^ 2 - 1) - n), p -> IsPosInt(p) and IsPrimeInt(p) and p mod 16 in [1, 15]) <> [] then
		return [false, "MR0342427, MR1096997"];

	#td-ps:2017
	elif GcdInt(n, Phi(n)) = 1 and Unique(List([2..Length(factors)], k -> Product(factors{[1..(k - 1)]}) ^ 4 < factors[k])) = [true] and List(Combinations(factors), subset -> subset <> [] and Unique(List([2..(LogInt(n) + 1)], d -> Filtered(RootsOfPolynomial((x ^ d - 1) / (x - 1) - Product(subset)), q -> IsPosInt(q) and IsPrimePowerInt(q)) = [])) = [true]) then
		return [true, "MR3575206?"];

	#jt:2010 
	elif Filtered(RootsOfPolynomial(3 * x * (x ^ 2 - 1) / 4 - n), q -> q > 4 and IsPosInt(q) and IsOddInt(q) and IsPrimePowerInt(q)) <> [] then
		return [false, "MR2558983?"];

	else
		if n = 1 then
			return [true, ""];
		else
			return [fail, ""];
		fi;
	fi;
	end;

x := Indeterminate(Rationals, "x");

primepower := First(Collected(Factors(n)), x -> x[2] > 1);

if primepower <> fail then
	if n = 12 then
		return [true, ""];

	#dm:1985
	elif n in [primepower[1] ^ 2, primepower[1] ^ 3] then
		return [true, "MR0821510"];

	#dm:1985, bdm-cep:1994
	else
		return [false, "MR0821510, MR1250993"];
	fi;
else
	issquarefreecayleynumber := IsSquareFreeCayleyNumber(n);

	if issquarefreecayleynumber[1] in [true, false] then
		return issquarefreecayleynumber;
	else
		issquarefreecayleynumber := List(DivisorsInt(n), IsSquareFreeCayleyNumber);
		if false in List(issquarefreecayleynumber, x -> x[1]) then
			return First(issquarefreecayleynumber, x -> x[1] = false);
		else
			return [fail, ""];
		fi;
	fi;
fi;
end;
