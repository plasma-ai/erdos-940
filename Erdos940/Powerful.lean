/-
Copyright 2025 The Formal Conjectures Authors.

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

public import Mathlib.Data.Nat.PrimeFin

/-!
# Powerful natural numbers

This is the definition of `Nat.Full` from the Formal Conjectures support
library (`FormalConjecturesForMathlib/Data/Nat/Full.lean`), copied verbatim.
-/

@[expose] public section

namespace Nat

/--
A natural number $n$ is said to be $k$-full (or $k$-powerful) if for every prime factor $p$ of $n$,
the $k$-th power $p^k$ also divides $n$.
-/
def Full (k : ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p^k ∣ n

end Nat
