import AlgebraInLean.Chapter02.Sheet01

-- TODO: remove?

/-
Disclaimer: This sheet covers basic concepts of modular arithmetic at a high-level, introducing
already-existing mechanisms in Lean, and does not require you to write any proofs. At the end is an
interesting quirk of recursive functions in Lean, which we recommend you to check out.
-/

open Nat

/-
From the output of `#check Nat.gcd` ("greatest common divisor"), we can see that this function takes
in two natural numbers and outputs another natural number. This output should be the largest number
that divides both inputs. Particularly, the gcd of any number and 0 is the number itself.
-/
#check Nat.gcd

#eval Nat.gcd 1 2
#eval Nat.gcd 100 45
#eval Nat.gcd 73 0

/-
Similarly, we define the "least common multiple". It is a function which takes in two natural
numbers and outputs the smallest natural number that is divisible by both inputs. The `lcm` of any
number and 0 is 0, since 0 divided by any number is 0.
-/
#check Nat.lcm

/- The `#print` command is sometimes useful to peek under the hood -/
#print Nat.lcm

#eval Nat.lcm 1 2
#eval Nat.lcm 100 45
#eval Nat.lcm 73 0


/- We can verify those claims from before by checking the following theorems -/
#check Nat.gcd_zero_right
#check Nat.gcd_zero_left
#check Nat.lcm_zero_right
#check Nat.lcm_zero_left

/-
Note that the definition for `lcm` uses `gcd`.

Efficiently computing the `gcd` is a seemingly boring problem, but its implications quite literally
form the backbone of the internet as we know it today.

The "naive" way to compute the `gcd` is through prime factorization: break up each of the numbers
into their constituent, atomic parts, and then find the largest part they have in common. But this
brute-force algorithm scales very poorly for large numbers, a performance bottleneck that
cryptographic schemes like RSA depend on.

Thankfully, there is a quicker way to find the `gcd` (and therefore the `lcm`) via the Euclidean
Algorithm.

To introduce the Euclidean Algorithm, first we have to cover modular arithmetic. Basic number theory
might seem completely separate from abstract algebra at first, but it shows up increasingly in areas
like ring theory, so bear with us.
-/

/-
Given two integers `a` and `b`, with `b` non-zero, there exist unique integers `q` and `r` such
that: a = bq + r, where 0 ≤ r < |b|. In other words, we can write an integer `a` as a multiple of
some other integer `b`, plus a positive remainder `r` with `r` strictly less than `b`. (What would
happen if `r` were equal to or greater than `b`?)

When we talk about some integer `n` modulo `q`, we are simply disregarding the first term in the
sum, `bq`, and only considering the remainder `r`.

A common real-world example is the analog clock. The clock runs modulo 12; once we get to the 12th
hour, we "roll over" and start at 1 again. Thus, 13 modulo 12 is 1. Another way to look at it is
that 13 divided by 12 is 1 with remainder 1.

Two useful pieces of notation here are `%` and `∣` (`\mid` in VSCode, not to be confused with `|` on
your keyboard). Given two integers `a` and `b`, `a % b` is the remainder `r` above, and `a ∣ b` is a
proposition on whether `a` divides `b` (i.e., whether r = 0). `a ∤ b` is the negation of that.
-/

#eval Nat.mod 13 5
#eval 13 % 5

/-
Sometimes we will want to compare two numbers after taking a modulus. This notion of comparison is
called "congruence modulo n", where `n` is some integer.
-/

/- Here are some identities regarding mod: -/

#check (∀ a b m : Nat, (a + b).mod m = ((a.mod m) + (b.mod m)).mod m)

#check (∀ a b m : Nat, (a * b).mod m = ((a.mod m) * (b.mod m)).mod m)

/-

Perhaps you would expect `a + b (mod m)` to equal `(a mod m) + (b mod m)`. Similarly, `a * b (mod
m)` does not simply equal `(a mod m) * (b mod m)`. Why do we need the extra `(mod m)` at the end?
Try computing an example where the extra `(mod m)` is not included. We leave this as a (hopefully)
thought-provoking exercise to the reader.

### The Euclidean Algorithm

As mentioned before, the Euclidean Algorithm offers a quicker way (than the brute-force method) for
finding the `gcd`, relying on a recursive definition of the `gcd` function.

Simply, `gcd(a, b)` equals `gcd(b, a mod b)`. This is our recursive case. The termination step (or
in more computer science-y terms, the "base case") of the Euclidean algorithm is `gcd(n, 0) = 0`; in
other words, `when b = 0`.

Here's our homemade, and of course, recursive version of the `gcd` function. Note how it reflects the
inductive definition of the natural numbers, which you have seen hinted at in the NNG (all natural
numbers are either 0, or a successor to a natural number).

-/

def Custom.gcd (a b : Nat) : Nat :=
  match b with
    | 0 => a
    | n + 1 => have : a % (n + 1) < n + 1 := by
    { have h₁ : n + 1 > 0 := succ_pos n
      have h₂ : a % (n + 1) < n + 1 := mod_lt a h₁
      exact h₂
    }
      gcd (n + 1) (a % (n + 1))
  termination_by b

/-

What is that bracketed proof nestled in the recursive case? It turns out that Lean is awfully (and
rightfully) picky about the structure of its recursive arguments. If it isn't immediately obvious
that the recursive case will _always result in an output smaller in some way_, Lean will panic and
throw an error: `unable to prove termination`. As far as Lean is concerned, recursion has its
dangers and a recursive function is guilty of stack overflow until proven innocent.

Once we provide a proof that `a % (n + 1)` is always lesser than `n + 1`, and stick in a
`termination_by b` at the end, Lean will stop complaining.

-/
