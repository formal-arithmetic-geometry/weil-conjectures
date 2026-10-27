/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleClopenMonoidalNormalization

/-! # Braided lift of clopen restriction with its model square

Source: Stacks Project, Tags 06YS, 0G7D, 06YU and 0FPT.
(blueprint: lem-pur-clopen-braided-model-normalization).
-/

@[expose] public noncomputable section

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open WeilConjectures

attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory

namespace AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent

/-- The summand-normalized total comparison descends to a braided structure on the
specified exact derived restriction, satisfying the K-flat computation square and
canonical degree-zero unit equation.

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 0G7D, 06YU and 0FPT.
(blueprint: lem-pur-clopen-braided-model-normalization).

Proof: Coproduct preservation and exactness give preservation of the countable sums
forming total complexes. The ordinary braided functor therefore induces a braided
functor on signed cochain complexes. Its inverse tensorator agrees with b: precompose
with each total summand, use the displayed summand equation, and apply the direct-sum
universal property. Flat-term K-flat resolutions give the left derivability structure
for the categorical K-flat subcategory. The independent-coefficient K-flat predicate
implies categorical K-flatness, and the converse follows by tensoring the
quasi-isomorphism from zero to an acyclic complex. Thus hk preserves these models.
The native localization is lax braided, with invertible unit and tensorators when one
input is K-flat. Apply normalizedBraidedLocalization to the canonical factorization
factors, obtaining a braided structure whose factorization is monoidal. In its tensor
equation cancel the native tensorators on a K-flat pair. Their inverses are exactly the
native computation isomorphisms, giving ModelNormalization for braidedComparison.
In the unit equation cancel the two native unit maps. The induced cochain unit is the
single-complex restriction of the ordinary ring unit; the resulting composite is
unitComparison. This proves the claimed unit equation. The argument uses neither a
nonzero coefficient ring nor a nonempty scheme. -/
theorem clopen_braided_model_normalization
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (clopenTensorRestriction.{t, u} j R).Braided)
    (b : coefficientTotalTensor.{u, t + 1, t} (topology X) R ⋙
        clopenTensorComplexRestriction.{t, u} j R ≅
      ((clopenTensorComplexRestriction.{t, u} j R).prod
        (clopenTensorComplexRestriction.{t, u} j R)) ⋙
          coefficientTotalTensor.{u, t + 1, t} (topology Y)
            ((clopenTensorRings.{t, u} j).obj R))
    (hsum : ∀ (P Q : CochainComplex (clopenTensorModules.{t, u} R) ℤ)
      (p q n : ℤ) (hpq : p + q = n),
      (clopenTensorRestriction.{t, u} j R).map
          (clopenTotalTensorSummand.{t, u} R P Q p q n hpq) ≫
          (b.hom.app (P, Q)).f n =
        (clopenTensorComparison.{t, u} j R h (P.X p) (Q.X q)).hom ≫
          clopenTotalTensorSummand.{t, u} ((clopenTensorRings.{t, u} j).obj R)
            ((clopenTensorComplexRestriction.{t, u} j R).obj P)
            ((clopenTensorComplexRestriction.{t, u} j R).obj Q) p q n hpq)
    (hk : ∀ P : CochainComplex (clopenTensorModules.{t, u} R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) P →
      CochainComplex.IsKFlatIndependentCoefficients (J := topology Y)
        (R := (clopenTensorRings.{t, u} j).obj R)
        ((clopenTensorComplexRestriction.{t, u} j R).obj P))
    (hcolim : ∀ (K : Type (max u (t + 1))),
      PreservesColimitsOfShape (Discrete K) (clopenTensorRestriction.{t, u} j R)) :
    ∃ d : (derivedRestriction.{t, u} j R).Braided,
      ModelNormalization.{t, u} j R b (braidedComparison.{t, u} j R d) ∧
      braidedUnit.{t, u} j R d = unitComparison.{t, u} j R h := by sorry

end AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent
