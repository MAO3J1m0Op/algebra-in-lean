-- ## Modular arithmetic interlude

-- ### GCD and LCM

#check Nat.gcd
-- The command `#print` is useful to see what is going on beneath the hood
#print Nat.gcd

-- From the output of `#check Nat.gcd`, we can see that the _greatest common
-- denominator_ function takes in two natural numbers and outputs the largest
-- natural number that will divide both inputs. Particularly, the gcd of any
-- number and 0 is the number itself.

#eval gcd 1 2
#eval gcd 100 45
#eval gcd 73 0

-- Similarly, we define the _least common multiple_. It is a function which takes in two natural numbers and outputs the minimal natural number that is divisible by both inputs. The lcm of any number and 9 is 0, since 0 divided by any number is 0.

#check Nat.lcm
#print Nat.lcm

#eval lcm 1 2
#eval lcm 100 45
#eval lcm 73 0

-- Note that the definition for lcm uses the gcd.

-- Efficiently computing the gcd is a seemingly mundane, boring problem, but
-- its implications quite literally form the backbone of the internet as we
-- know it today.

-- The "naive" way to do it is through _prime factorization_; break up each of
-- the numbers into their constituent, atomic parts, and then find the largest
-- part they have in common. But this brute-force algorithm scales very poorly
-- for large numbers. If you find an efficient way to do this, you will also be
-- compromising some of the most important crytography schemes to ever be
-- realized, for example RSA cryptography.

-- Thankfully, there is a quicker way to find the gcd (and therefore lcm) via
-- the Euclidean Algorithm.

-- To introduce the Euclidean Algorithm, first we have to cover modular
-- arithmetic. Basic number theory might seem completely separate from abstract
-- algebra at first, but it shows up increasingly in areas like ring theory, so
-- bear with us.

-- ### Congruence modulo some integer `m`

-- Given two integers `a` and `b`, with `b` non-zero, there exist unique
-- integers `q` and `r` such that:

-- a = bq + r, where 0 ≤ r < |b|.

-- In other words, we can write an integer a as a multiple of some other
-- integer `b`, plus a positive remainder `r` with `r` strictly less than `b`.
-- (What would happen if `r` were equal to or greater than `b`?)

-- Another useful and small piece of notation is the vertical bar `∣`, not to
-- be confused with the "pipe" operator `|` on your keyboard. You can write it
-- as `\mid`.

-- Given two integers `a` and `b`, `a ∣ b` simply means that `a` divides `b`,
-- or `a` is a factor of `b`. `a ∤ b` means the inverse; `a` does not divide
-- `b`.

#eval Nat.mod 4 5

def congr_mod (m : ℕ) (a b : ℤ) : Prop := (↑m : ℤ) ∣ (a - b)
notation:50  a " ≡ " b "(mod " m ")" => congr_mod m a b

#check 5 ≡ 2 (mod 2) -- false; 5 (mod 2) = 1 and 2 (mod 2) = 0
#check 9 ≡ 27 (mod 3) -- true; 9 (mod 6) = 3 and 27 (mod 6) = 3


