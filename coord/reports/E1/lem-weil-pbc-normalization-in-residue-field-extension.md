## Worker report

The module states the normalization result for a quasi-separated scheme `X`, a point `x`, and a finite field extension `K` of `X.residueField x`. It defines the composite `h` as `Spec.map (algebraMap (X.residueField x) K) ≫ X.fromSpecResidueField x`, renders quasi-compactness and quasi-separatedness as `QuasiCompact h ∧ QuasiSeparated h`, and states the existence of `Y`, an integral morphism `ν`, and `g` with `h = g ≫ ν`. The scheme `Y` is rendered by `IsIntegral Y`; normality is `∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)`. The generic-point clause is rendered by `∃ η : Y, IsGenericPoint η Set.univ ∧ g (IsLocalRing.closedPoint K) = η`, and the induced residue-field map is required to be an isomorphism by `IsIso (g.residueFieldMap (IsLocalRing.closedPoint K))`.

The hypotheses are rendered as `(X : Scheme.{u}) [QuasiSeparatedSpace X]`, `(x : X)`, `(K : Type u) [Field K]`, `[Algebra (X.residueField x) K]`, and `[Module.Finite (X.residueField x) K]`; the last two express a finite field extension of the residue field. The dependency declarations used are `AlgebraicGeometry.Scheme.residueField` and `AlgebraicGeometry.Scheme.fromSpecResidueField` from Mathlib, `AlgebraicGeometry.Spec`/`Spec.map` from Mathlib, `AlgebraicGeometry.IsIntegralHom` and `AlgebraicGeometry.IsIntegral` from Mathlib, and `AlgebraicGeometry.Scheme.Hom.residueFieldMap` from Mathlib. The relative normalization declarations and integrally-closed-stalk theorem are available in `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization` for later proofs, but the stage-2 statement only uses their resulting predicates.

Edge cases checked: `K` is any field with finite module dimension over the residue field, including the trivial extension; `Spec K` is represented by `Spec (.of K)` and its unique point by `IsLocalRing.closedPoint K`; genericity is stated without requiring an unavailable typeclass instance by using `IsGenericPoint η Set.univ`; the factorization order is the categorical order `g ≫ ν`.

Searches made: `msearch.py leanfinder "normalization of a scheme in a finite extension of a residue field is a normal integral scheme with integral morphism"` returned the relative-normalization declarations but no theorem with this full statement; `msearch.py loogle "AlgebraicGeometry.Scheme.Hom.normalization, AlgebraicGeometry.IsIntegral"` returned only integrality of relative normalization; `msearch.py grep "IsNormal|isNormal|IsIntegrallyClosed|functionField" Mathlib/AlgebraicGeometry/Normalization.lean` found no complete normal-scheme predicate, while the source repository contains `AlgebraicGeometry.Scheme.Hom.isIntegrallyClosed_stalk_normalization` and `exists_iso_toNormalization_normalizationIn`; `rg` over `lean/Sheaf` found no existing declaration for this node. Thus no existing declaration exactly states the node.

No `STATEMENT-DISPUTED` or node fault.

## Earlier second reading (a previous round; superseded)

Independent reading of the node and module found that every hypothesis and conclusion clause is represented: the finite extension is `[Algebra ...] [Module.Finite ...]`, `h` is the stated composite, factorization uses the categorical order `g ≫ ν`, normality is expressed by integrally closed stalks, and genericity plus the residue-field isomorphism are explicit. No mismatch was found.

## Second reading by E1

I reread the node statement, its Stacks source (Morphisms 035H, 035I, 035L and the
Etale Cohomology 09Z6 proof), and the Lean declaration item by item. The objects and
hypotheses render as follows: `X : Scheme.{u}` with `[QuasiSeparatedSpace X]`, a point
`x : X`, a field `K : Type u` with `[Algebra (X.residueField x) K]` and
`[Module.Finite (X.residueField x) K]`; `h` is the composite
`Spec.map (CommRingCat.ofHom (algebraMap ...)) ≫ X.fromSpecResidueField x`.
The first conclusion is `QuasiCompact h ∧ QuasiSeparated h`. The existential introduces
`Y : Scheme.{u}`, `ν : Y ⟶ X`, and `g : Spec (.of K) ⟶ Y`, with
`IsIntegralHom ν` and `h = g ≫ ν`; this is the categorical rendering of
`h = ν ∘ g`. The integral-scheme clause is `IsIntegral Y`. The normality clause is
`∀ y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y)`.
The generic-point clause is `∃ η, IsGenericPoint η Set.univ ∧
 g (IsLocalRing.closedPoint K) = η`, followed by
`IsIso (g.residueFieldMap (IsLocalRing.closedPoint K))`, the residue-field
isomorphism to `K`.

The worker version omitted `IsDomain` from the stalk clause. `IsIntegrallyClosed` is a
separate property in Mathlib and does not itself assert that the ring is a domain, so
that version was weaker than the node's “integrally closed domains”. I added the explicit
`IsDomain` conjunct and kept all other text unchanged. The module compiles cleanly with
`scompile.py`; its statement docstring now records the source and the six proof steps.

Edge cases are covered: the finite extension may be trivial; `Spec K` has its unique
`closedPoint`; `IsIntegral Y` and the explicit stalk-domain condition cover the integral
normal scheme; no nonempty-index, characteristic, or Noetherian hypothesis is introduced;
and the universe `Type u` matches `Scheme.{u}` and the residue field. The source's empty
open preimages do not alter the statement.

Searches (`msearch.py` LeanFinder/Loogle/grep and `rg` in Mathlib, WeilConjectures, and
`lean/Sheaf`) found only relative-normalization and stalk-normality ingredients, with no
existing declaration of this full theorem. The node remains a new statement module; its
Lean record now points to `Sheaf.Paper.WeilPbcNormalizationInResidueFieldExtension` and
its declaration verbatim. No dependency module or node required repair.
