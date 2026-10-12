/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.Algebra.Homology.DerivedInternalHom
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import Sheaf.Algebra.Homology.HomComplex

/-! # Internal Hom from a strictly perfect complex

Source: Stacks Project, Cohomology of Sheaves, Lemma 20.46.9, Tag 08DM
(blueprint: lem-pc-rhom-strict-perfect-hom).

The affine scheme is presented as an affine open `U` of a scheme `X`; its module
category is the recorded localized-site carrier of `Scheme.IsStrictlyPerfect`.
The comparison is computed with any functorial K-injective replacement, as in
`derivedInternalHom_comparison`. No boundedness is imposed on the second complex.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- On an affine open, the ordinary Hom complex from a strictly perfect complex represents
its derived internal Hom. For every functorial K-injective replacement `η : 𝟭 ⟶ I`, the
canonical map `𝓗om^•(P, M) ⟶ 𝓗om^•(P, I(M))` becomes an isomorphism in the derived
category. Since `Q (𝓗om^•(P, I(M)))` computes derived internal Hom
(`derivedInternalHom_comparison`), this map is the ordinary-to-derived comparison.

Source: Stacks Project, Cohomology of Sheaves, Lemma 20.46.9, Tag 08DM
(blueprint: lem-pc-rhom-strict-perfect-hom).

Proof:
1. Replace `M` by a functorial K-injective resolution `η.app M : M ⟶ I.obj M`.
   By `def-pur-derived-internal-hom`, the Hom complex from `P` into this resolution
   represents derived internal Hom.
2. Each term of `P` is a direct summand of a finite free module. Its internal Hom
   functor is therefore a direct summand of an exact finite-free internal Hom functor
   (`lem-sc-finite-free-internal-hom-exact`), hence exact. It preserves the
   quasi-isomorphism to the resolution in each fixed degree of `P`.
3. The bounded stupid-truncation filtration of `P` has finitely many graded pieces
   `P^k[-k]`. Applying the Hom-complex functor gives termwise split short exact
   sequences, since only finitely many factors are nonzero. Induction, the long exact
   cohomology sequence (Stacks Tag 0117), and the five lemma show that the induced
   Hom-complex map is a quasi-isomorphism.
4. Localization inverts that map. Compose with the computation isomorphism of
   `def-pur-derived-internal-hom` to obtain the representation and the canonical
   comparison isomorphism. Functoriality makes this independent of the replacement. -/
theorem isIso_homComplex_resolution_of_isStrictlyPerfect
    (X : Scheme.{u}) (U : X.Opens) [IsAffine U.toScheme]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose ((Opens.grothendieckTopology X).over U)
        (forget₂ CommRingCat RingCat)).obj (X.sheaf.over U)))]
    (P M : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (_hP : IsStrictlyPerfect X U P) :
    Nonempty (DerivedCategory.Q.obj (homComplex (R := X.sheaf.over U) P M) ≅
      (derivedInternalHom ((Opens.grothendieckTopology X).over U) (X.sheaf.over U)).obj
        (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj M)) ∧
    ∀ (I : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ ⥤
        CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
      (η : 𝟭 (CochainComplex
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ) ⟶ I),
      (∀ N : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
        QuasiIso (η.app N) ∧ (I.obj N).IsKInjective) →
        IsIso (DerivedCategory.Q.map
          (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map (η.app M))) := by
  sorry

end AlgebraicGeometry.Scheme
