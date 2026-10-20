# Erdős Problem 940

This Lean 4 project proves partial results on [Erdős Problem 940](https://www.erdosproblems.com/940), as cataloged by Thomas F. Bloom. Call a natural number `r`-powerful if `p^r` divides it for every prime `p` dividing it. Erdős asked, for `r ≥ 3`, whether infinitely many integers are not the sum of at most `r` `r`-powerful numbers, and whether the integers that are such sums have density zero. We prove that for `r = 3` and `r = 4` the integers that are not such sums have positive lower density, and so there are infinitely many of them.

To our knowledge, the case `r = 4` is new. The case `r = 3` is due to Beyer de Ryke in [*A density deficit for sums of three cube-full numbers*](https://arxiv.org/abs/2609.35772), and this project formalizes it. Whether the representable integers have density zero remains open for every `r ≥ 3`, and so does the infinitude question for every `r ≥ 5`.

## Literature and scope

Erdős posed the question in *Problems and results on number theoretic properties of consecutive integers and related questions* (Proceedings of the Fifth Manitoba Conference on Numerical Mathematics, 1976, p. 33). For `r = 2` the representable integers have density zero; Baker and Brüdern gave the first proof in *On sums of two squarefull numbers* (Math. Proc. Cambridge Philos. Soc., 1994), and Heath-Brown showed in *Ternary quadratic forms and sums of three square-full numbers* (1988) that every large integer is a sum of three square-full numbers. Beyer de Ryke proved the `r = 3` case of the infinitude question, with positive lower density, and notes that the argument does not extend to `r ≥ 4`.

The "to our knowledge" novelty claim reflects a targeted search on October 12, 2026 of arXiv, the web, Bloom's problem entry with its discussion thread and proof claims, the 2025 Oberwolfach problem session (OWR 2025/51), and the works citing Baker and Brüdern and Beyer de Ryke. That search found no result on the infinitude or density questions for any `r ≥ 4`.

Both proofs choose a residue class `a (mod M)` on which the representable integers have small upper relative density, which gives positive lower density for the complement. Values with fewer than `r` positive summands are negligible, so it suffices to count sums of exactly `r` positive `r`-powerful numbers. Each such number factors uniquely as an `r`-th power times a canonical `(r + 1)`-full part, and a convergent weighted sum over the canonical parts reduces the count to finitely many fixed parts with a small tail.

**Cubic case.** `Erdos940/Cubic/` follows Beyer de Ryke. For a fixed triple of canonical parts, the sums of three weighted cubes in the class `a (mod M)` are counted by local densities modulo primes `q ≡ 1 (mod 3)` at which every part is a cube. The Chebotarev density theorem supplies enough such primes for the product of local densities to become arbitrarily small.

**Quartic case.** `Erdos940/Quartic/` carries out the same plan for fourth powers, with `a ≡ 8 (mod 16)`. Quartic Gauss sums express the local densities through a character of the coefficients. Hilbert reciprocity eliminates the coefficient tuples for which that character is principal. For the remaining tuples, Chebotarev density in multiquadratic fields selects primes at which the local factors save. A coefficient-uniform bound for partial Euler products, compared with Hecke L-functions of `ℚ(i)`, makes the saving uniform over the canonical parts.

## Publication layout

`Challenge.lean` states the results using only Mathlib imports. Its four `sorry` proofs are deliberate: this file contains the statements to audit. For `r = 3` and `r = 4` it states positive lower density of the nonrepresentable integers, as a count below `N`, and their infinitude, in the form of formal-conjectures' `erdos_940.variants.large_integers`. The definition of `Nat.Full` is copied verbatim from [`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures/blob/1a339399f9d49d5f086e78851a372d38ded8c427/FormalConjecturesForMathlib/Data/Nat/Full.lean). `Solution.lean` imports the proof development and supplies the four theorems. `comparator.json` selects their names and the allowed axioms for [Comparator](https://github.com/leanprover/comparator).

The proof development lives under `Erdos940/`. `Erdos940/Statement.lean` defines representability, `Erdos940/Density.lean` and `Erdos940/Progression.lean` hold the counting shared by both cases, and `Erdos940/FinalAssembly.lean` restates the two cases in the form of `Challenge.lean`.

Two vendored libraries supply the algebraic number theory, each under its own directory with its upstream license and a provenance README:

- `vendor/ClassFieldTheory/` holds the import closure, under its upstream module names, of the modules the quartic case uses from [n-yamaguchi-0729/ClassFieldTheory](https://github.com/n-yamaguchi-0729/ClassFieldTheory). Its README lists the changes made to port it to this toolchain.
- `vendor/AINTLIB/` holds the Chebotarev density theorem from [CBirkbeck/AINTLIB](https://github.com/CBirkbeck/AINTLIB), unchanged.

`Challenge.lean`, the files shared by both cases, `Erdos940/Cubic/`, and the AINTLIB modules use the module system. The class field theory library does not, and a module cannot import an ordinary file, so `Erdos940/Quartic/`, `Erdos940/FinalAssembly.lean`, and `Solution.lean` are ordinary files.

`formalization.yaml` records the mathematical sources, authorship, AI use, source fidelity, and review status for a registry submission.

The Lean and Mathlib versions are fixed by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The full build includes `Challenge` and therefore reports its intentional `sorry` warnings. The proofs in `Solution` can also be built directly with `lake build Solution`, and the cubic case alone with `lake build Erdos940.Cubic.Assembly`.
