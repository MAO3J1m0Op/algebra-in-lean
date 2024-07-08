-- ## Modular arithmetic interlude

-- ### GCD and LCM

namespace Nat

/-

From the output of `#check Nat.gcd`, we can see that the _greatest common
denominator_ function takes in two natural numbers and outputs the largest
natural number that will divide both inputs. Particularly, the gcd of any
number and 0 is the number itself.

-/
#check Nat.gcd

-- The command `#print` is useful to see what is going on beneath the hood

#print Nat.gcd

#eval gcd 1 2
#eval gcd 100 45
#eval gcd 73 0

/-

Similarly, we define the _least common multiple_. It is a function which
takes in two natural numbers and outputs the minimal natural number that is
divisible by both inputs. The lcm of any number and 9 is 0, since 0 divided
by any number is 0.

-/
#check lcm
#print lcm

#eval lcm 1 2
#eval lcm 100 45
#eval lcm 73 0

variable (n : Nat)

#check (gcd_zero_right n : gcd n 0 = n)
#check (gcd_zero_left n : gcd 0 n = n)
#check (lcm_zero_right n : lcm n 0 = 0)
#check (lcm_zero_left n : lcm 0 n = 0)

/-

Note that the definition for lcm uses the gcd.

Efficiently computing the gcd is a seemingly mundane, boring problem, but
its implications quite literally form the backbone of the internet as we
know it today.

The "naive" way to do it is through _prime factorization_; break up each of
the numbers into their constituent, atomic parts, and then find the largest
part they have in common. But this brute-force algorithm scales very poorly
for large numbers, a performance bottleneck that cryptographic schemes like
RSA depend on.

Thankfully, there is a quicker way to find the gcd (and therefore lcm) via
the Euclidean Algorithm.

To introduce the Euclidean Algorithm, first we have to cover modular
arithmetic. Basic number theory might seem completely separate from abstract
algebra at first, but it shows up increasingly in areas like ring theory, so
bear with us.

### Congruence modulo some integer `m`

Given two integers `a` and `b`, with `b` non-zero, there exist unique
integers `q` and `r` such that:

a = bq + r, where 0 ≤ r < |b|.

In other words, we can write an integer a as a multiple of some other
integer `b`, plus a positive remainder `r` with `r` strictly less than `b`.
(What would happen if `r` were equal to or greater than `b`?)

When we talk about some integer `n` modulo `q`, we are simply disregarding
the first term in the sum, `bq`, and only considering the remainder `r`.

A common real-world example is the analog clock. The clock runs modulo 12;
once we get to the 12th hour, we "roll over" and start at 1 again. Thus, 13
modulo 12 is 1. Another way to look at it is that 13 divided by 12 is 1 with
remainder 1.

Another useful and small piece of notation is the vertical bar `∣`, not to
be confused with the "pipe" operator `|` on your keyboard. You can write it
as `\mid`.

Given two integers `a` and `b`, `a ∣ b` simply means that `a` divides `b`,
or `a` is a factor of `b`. `a ∤ b` means the inverse; `a` does not divide
`b`.

-/
#eval Nat.mod 4 5

-- `%` represents the mod operation.
#eval 4 % 5

/- `↑` coerces the `(m : Nat)` into an `Int`, which is what we need to look at
divisibility -/
def congr_mod (m : Nat) (a b : Int) : Prop := (↑m : Int) ∣ (a - b)
notation:50  a " ≡ " b "(mod " m ")" => congr_mod m a b

#check 5 ≡ 2 (mod 2) -- false; 5 (mod 2) = 1 and 2 (mod 2) = 0
#check 9 ≡ 27 (mod 3) -- true; 9 (mod 6) = 3 and 27 (mod 6) = 3

-- Here are some identities regarding mod:

#check (∀ a b m : Nat, (a + b).mod m = ((a.mod m) + (b.mod m)).mod m)

#check (∀ a b m : Nat, (a * b).mod m = ((a.mod m) * (b.mod m)).mod m)

/-

Perhaps you would expect a + b (mod m) to equal (a mod m) + (b mod m).
Similarly, a * b (mod m) does not simply equal (a mod m) * (b mod m). Why do
we need the extra (mod m) at the end? We leave this as a (hopefully)
thought-provoking exercise to the reader.

### The Euclidean Algorithm

As mentioned before, the Euclidean Algorithm offers a quicker way (than the
brute-force method) for finding the gcd, relying on a recursive definition
of the gcd function.

Simply, gcd(a, b) equals gcd(b, a mod b). The termination step (or in more
computer science-y terms, the "base case") of the Euclidean algorithm is
gcd(n, 0) = 0; in other words, when b = 0.

Here's our homemade, and of course, recursive version of the gcd function.

-/
def gcd' (a b : Nat) : Nat :=
  match b with
    | 0 => a
    | n + 1 => gcd (n + 1) (a % (n + 1))
