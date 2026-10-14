/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.SecondLocalizationMap
/-! # Raw cohomological counit square for second localization
Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-second-localization-raw-counit-square). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace RingTensorCohomology

variable (R A B Bp D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Bp] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra B Bp] [Algebra R Bp]
  [tRB : IsScalarTower R B Bp]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[R] Bp) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Bp)]

include tRB in
/-- Flat coefficient extension commutes with the raw derived counits on homology.
Source: Stacks Project, Tag 06Y6, lemma-derived-base-change; Tag 0DJ8.
(blueprint: lem-pc-second-localization-raw-counit-square).

Proof: install K.universal and apply leftDerived_fac to the lift defining
secondLocalizationDerivedMap. Its composite with K.counit is L.counit extended
along B to Bp, followed by the scalar-extension associator. Evaluate this
identity at the homotopy class of the restriction of Q to R and apply homology.
Naturality of flatDerivedHomologyIso moves homology of the extended L.counit
to extension of homology of L.counit. At an ordinary complex the defining
localization factorization of that isomorphism is precisely mapHomologyIso
for exact scalar extension, composed with the homotopy/derived homology
factorization isomorphisms. Transpose along extension/restriction of scalars.
The unit on complexes is termwise x mapped to 1 tensor x. Naturality of exact
restriction homology identifies this transpose with homology of the termwise
unit followed by the scalar-extension associator. That map sends b tensor x
to image(b) tensor x; tensor induction and hχ identify it with χ. Cancelling
the exact-restriction homology isomorphism gives the displayed identity.
This is only the raw counit calculation: it uses neither ordinaryIso,
cohomologyIso nor comparison of either model. Zero complexes and zero rings
are covered by tensor induction and the same categorical identities. -/
theorem secondLocalization_raw_counit_square
    (hflat : (algebraMap B Bp).Flat) (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D) :
    let T := ((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
      (.up ℤ)).obj Q
    let P := ((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex
      (.up ℤ)).obj T
    let Pp := ((ModuleCat.extendScalars (algebraMap R Bp)).mapHomologicalComplex
      (.up ℤ)).obj T
    let U := ModuleCat.restrictScalars (algebraMap B Bp)
    let qR := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
    let qB := HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ)
    let qBp := HomotopyCategory.quotient (ModuleCat.{u} Bp) (.up ℤ)
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
    let Hp := DerivedCategory.homologyFunctor (ModuleCat.{u} Bp) i
    let X := DerivedCategory.Qh.obj (qR.obj T)
    let c := H.map (L.counit.app (qR.obj T)) ≫
      (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i).hom.app (qB.obj P) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).hom.app P
    let cp := Hp.map (K.counit.app (qR.obj T)) ≫
      (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} Bp) i).hom.app (qBp.obj Pp) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} Bp) (.up ℤ) i).hom.app Pp
    letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
    let d := (flatDerivedHomologyIso B Bp hflat i).inv.app (L.derived.obj X) ≫
      Hp.map ((secondLocalizationDerivedMap R A B Bp D hflat Q L K).app X)
    ∀ (χ : P ⟶ (U.mapHomologicalComplex (.up ℤ)).obj Pp)
      (_hχ : ∀ (j : ℤ) (b : B) (x : Q.X j),
        χ.f j (b ⊗ₜ[R,algebraMap R B] (show T.X j from x)) =
          algebraMap B Bp b ⊗ₜ[R,algebraMap R Bp] (show T.X j from x)),
      c ≫ HomologicalComplex.homologyMap χ i =
        (ModuleCat.extendRestrictScalarsAdj (algebraMap B Bp)).homEquiv _ _ (d ≫ cp) ≫
          ((Pp.sc i).mapHomologyIso U).inv := by
  sorry

end RingTensorCohomology
