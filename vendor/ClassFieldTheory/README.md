# ClassFieldTheory source provenance

The 1,025 Lean modules in this directory are taken from
[n-yamaguchi-0729/ClassFieldTheory](https://github.com/n-yamaguchi-0729/ClassFieldTheory)
at commit `7713795234690681b4406ae198b07aa95e82716a` (2026-09-26), by Naganori
Yamaguchi, assisted by OpenAI Codex as recorded upstream. They are distributed
under the Apache License 2.0, whose full text is in [LICENSE](LICENSE).

They are the import closure of the class field theory modules used by
`Erdos940/Quartic/`, not the whole upstream library. The upstream `Lean4/`
subdirectories `ClassFieldTheory/`, `ValuedFieldTheory/`, `GaloisCohomology/`,
and `ProCGroups/` are placed here with their upstream module names, so no
import was rewritten.

The quartic proofs were first written against upstream commit
`a9139b1969763cfcdb5580767b06f47eec31b1c0` (2026-09-22, Lean `v4.34.0`).
Commit `7713795` is upstream's port of the same tree to Lean `v4.35.0-rc2`.
This project pins Lean and Mathlib `v4.35.0-rc4`, and 30 of the modules were
changed to build there. The changes follow Mathlib renames and keep the
meaning of every statement:

- `Rep.norm` is now an endomorphism, so `A.norm.hom` and
  `A.norm.toModuleCatHom` became `A.norm.asHom.hom` and
  `A.norm.asHom.toModuleCatHom`.
- Mathlib split the old injective-power notion of torsion-freeness into
  `HasUniqueDiv` and `HasUniqueRoots`. Hypotheses and instances that used
  `IsAddTorsionFree` or `IsMulTorsionFree` in that sense now use these names,
  including `HasUniqueDiv ZHat` and the two instances renamed to
  `rationalCyclotomicZHatFieldGal_hasUniqueRoots` and
  `numberFieldCyclotomicZHatCompositumGal_hasUniqueRoots`;
  `smul_right_inj` became `nsmul_right_inj` in one proof.
- `IntermediateField.adjoin_induction` names its predicate `motive`, not `p`.
- `NumberField.LiesOver.completionMap` and `continuous_completionMap` take the
  two places explicitly.
- `HeightOneSpectrum.valuation_liesOver` is stated with `Ideal.ramificationIdx`;
  two proofs rewrite with `Ideal.ramificationIdx'_eq_ramificationIdx` first.
- One theorem in `KummerTheory/Concrete/SimpleExtensionLocalBehavior.lean`
  raises `maxHeartbeats` to 400000.
