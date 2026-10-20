/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Erdos940.Powerful

/-!
# Sums of r-powerful numbers

`Representable r n` means that `n` is a sum of at most `r` `r`-powerful
natural numbers. Erdős Problem 940 asks whether infinitely many numbers are
not representable, and whether the representable numbers have natural
density zero.

See also the [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/1a339399f9d49d5f086e78851a372d38ded8c427/FormalConjectures/ErdosProblems/940.lean).
-/

@[expose] public section

namespace Erdos940

/-- `n` is the sum of at most `r` `r`-powerful natural numbers. -/
def Representable (r : ℕ) (n : ℕ) : Prop :=
  ∃ S : Multiset ℕ,
    S.card ≤ r ∧ (∀ s ∈ S, Nat.Full r s) ∧ n = S.sum

/-- Infinitely many natural numbers are not representable. -/
def CoinfiniteFor (r : ℕ) : Prop :=
  ({n : ℕ | Representable r n}ᶜ).Infinite

end Erdos940
