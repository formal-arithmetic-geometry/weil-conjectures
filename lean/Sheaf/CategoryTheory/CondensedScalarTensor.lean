/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.CategoryTheory.CondensedDerivedCup

/-! # Balanced derived scalar tensor and regular coefficient arrow

Source: main-20261015 direct-images proof (sk-thm-sf-ctf-stability-direct-images.proof.md),
paragraph (3), agent-formulated formal restriction and cup-product infrastructure;
exact reference wanted
(blueprint: def-sfb-condensed-scalar-tensor).

## Main definitions

* `scalarOrdinaryLax`, `scalarComplexTensor`, `scalarLax`: the balanced lax comparison of
  scalar restriction on modules, on total complexes, and on derived categories (K-flat
  R'-representatives; no flatness of the ring map).
* `regularScalar`, `baseRingArrow`, `coefficientArrow`, `coefficientCupMap`: the ring map as
  a module, derived and equivariant arrow, and the coefficient map C_R(J) → s C_R'(J).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.CondensedBar
namespace CategoryTheory.CondensedDerivedRestriction
variable {A A' : CondensedBar.Ring.{u}}

/-- The existing ordinary scalar restriction, with its module-category action explicit.
Source: paragraph (3) (blueprint: def-sfb-condensed-scalar-tensor). -/
abbrev scalarModules (a : A ⟶ A') : Modules A' ⥤ Modules A :=
  Mod.comap a.hom.hom

/-- Normalization of ordinary scalar restriction on balanced pure tensors and on 1.
Source: paragraph (3) (blueprint: def-sfb-condensed-scalar-tensor). -/
def ScalarTensorModel (a : A ⟶ A')
    (m : (scalarModules a).LaxMonoidal) : Prop :=
  (@Functor.LaxMonoidal.ε _ _ _ _ _ _ (scalarModules a) m).hom = a.hom.hom ∧
  ∀ (M N : Modules A') (S : Profinite.{u}) (x : sections A' M S)
      (y : sections A' N S),
    ((@Functor.LaxMonoidal.μ _ _ _ _ _ _ (scalarModules a) m M N).hom.hom.app (op S))
        (tensorSection (A := A) ((scalarModules a).obj M)
          ((scalarModules a).obj N) S x y) = tensorSection (A := A') M N S x y

/-- The balanced tensor universal property determines scalar restriction's lax structure.
Source: paragraph (3) (blueprint: def-sfb-condensed-scalar-tensor).
Proof: the R'-balanced universal pairing is R-balanced after restriction and hence factors
uniquely through the R-tensor. Its value on pure tensors is the displayed value. The
unit is the ring map. The unit, associativity and naturality equations follow on pure
tensors from the corresponding equations over R'. Pure tensors generate locally, so
these equations also prove uniqueness, including the coherence proof fields. -/
theorem scalarTensorExist (a : A ⟶ A') :
    ∃! m : (scalarModules a).LaxMonoidal, ScalarTensorModel a m := by
  sorry

/-- The normalized balanced scalar tensor structure, with no flatness hypothesis.
Source: paragraph (3) (blueprint: def-sfb-condensed-scalar-tensor). -/
instance scalarOrdinaryLax (a : A ⟶ A') : (scalarModules a).LaxMonoidal :=
  Classical.choose (scalarTensorExist a)

/-- Scalar restriction preserves all small sums on the unchanged underlying sheaves.
Source: paragraph (3) (blueprint: def-sfb-condensed-scalar-tensor).
Proof: the scalar action descends uniquely to every sheafified colimit; its universal
property is exactly the same internal-module colimit universal property. -/
@[instance] theorem scalarSmallColimits (a : A ⟶ A') :
    PreservesColimitsOfSize.{0, 0} (scalarModules a) := by
  sorry

/-- The scalar comparison for total tensor is fixed on each degree summand.
Source: paragraph (3) (blueprint: def-sfb-condensed-scalar-tensor).
Proof: factor each summand by the ordinary balanced scalar tensor map. The differential
commutes with this map by naturality and the signed Leibniz rule. The total tensor sum
universal property gives the unique chain map. -/
theorem scalarComplexTensorExist (a : A ⟶ A') (P Q : CochainComplex (Modules A') ℤ) :
    ∃! m : ((scalarModules a).mapHomologicalComplex (.up ℤ)).obj P ⊗
        ((scalarModules a).mapHomologicalComplex (.up ℤ)).obj Q ⟶
      ((scalarModules a).mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q),
      ∀ (p q n : ℤ) (h : p + q = n),
        HomologicalComplex.ιTensorObj
          (((scalarModules a).mapHomologicalComplex (.up ℤ)).obj P)
          (((scalarModules a).mapHomologicalComplex (.up ℤ)).obj Q) p q n h ≫ m.f n =
        Functor.LaxMonoidal.μ (scalarModules a) (P.X p) (Q.X q) ≫
          (scalarModules a).map (HomologicalComplex.ιTensorObj P Q p q n h) := by
  sorry

/-- The unique summand-normalized scalar tensor map of complexes.
Source: paragraph (3) (blueprint: def-sfb-condensed-scalar-tensor). -/
def scalarComplexTensor (a : A ⟶ A') (P Q : CochainComplex (Modules A') ℤ) :
    ((scalarModules a).mapHomologicalComplex (.up ℤ)).obj P ⊗
      ((scalarModules a).mapHomologicalComplex (.up ℤ)).obj Q ⟶
    ((scalarModules a).mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) :=
  Classical.choose (scalarComplexTensorExist a P Q)

/-- The computation equation fixing the derived scalar tensorator, including its unit.
Source: paragraph (3) (blueprint: def-sfb-condensed-scalar-tensor). -/
def DerivedScalarTensorModel (a : A ⟶ A') (m : (scalarBase a).LaxMonoidal) : Prop :=
  (∀ P Q : CochainComplex (Modules A') ℤ,
    @Functor.LaxMonoidal.μ _ _ _ _ _ _ (scalarBase a) m
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
      (scalarBase a).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) =
    ((scalarModules a).mapDerivedCategoryFactors.hom.app P ⊗ₘ
      (scalarModules a).mapDerivedCategoryFactors.hom.app Q) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        (((scalarModules a).mapHomologicalComplex (.up ℤ)).obj P)
        (((scalarModules a).mapHomologicalComplex (.up ℤ)).obj Q) ≫
      DerivedCategory.Q.map (scalarComplexTensor a P Q) ≫
      (scalarModules a).mapDerivedCategoryFactors.inv.app (P ⊗ Q)) ∧
  @Functor.LaxMonoidal.ε _ _ _ _ _ _ (scalarBase a) m ≫
      (scalarBase a).map (Functor.LaxMonoidal.ε DerivedCategory.Q) =
    Functor.LaxMonoidal.ε DerivedCategory.Q ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.single _ (.up ℤ) 0).map
          (Functor.LaxMonoidal.ε (scalarModules a)) ≫
          ((HomologicalComplex.singleMapHomologicalComplex (scalarModules a)
            (.up ℤ) 0).app (𝟙_ (Modules A'))).inv) ≫
      (scalarModules a).mapDerivedCategoryFactors.inv.app
        (𝟙_ (CochainComplex (Modules A') ℤ))

/-- The canonical derived scalar lax structure is fixed by the balanced tensor model.
Source: paragraph (3) (blueprint: def-sfb-condensed-scalar-tensor).
Proof: on K-flat R'-complexes the target localization tensor comparison is invertible.
The displayed equation then defines the comparison from the derived R-tensor through
its canonical map to the ordinary R-tensor of the restricted complexes. K-flat
localization gives independence and naturality. The ordinary coherence equations
descend, giving a lax structure and the unit equation. Every derived R'-object has a
K-flat representative, which proves uniqueness. No restricted object is assumed flat. -/
theorem derivedScalarTensorExist (a : A ⟶ A') :
    ∃! m : (scalarBase a).LaxMonoidal, DerivedScalarTensorModel a m := by
  sorry

/-- Canonical lax scalar restriction on the ordinary derived tensor products.
Source: paragraph (3) (blueprint: def-sfb-condensed-scalar-tensor). -/
instance scalarLax (a : A ⟶ A') : (scalarBase a).LaxMonoidal :=
  Classical.choose (derivedScalarTensorExist a)

/-- The ring morphism is the unique linear map of the regular module with that underlying
condensed additive map.
Source: paragraph (3) (blueprint: def-sfb-condensed-scalar-tensor).
Proof: multiplicativity of the ring morphism is precisely linearity after scalar
restriction. Equality of internal-module morphisms is equality of their underlying maps. -/
theorem regularScalarExist (a : A ⟶ A') :
    ∃! f : Mod.regular A.X ⟶ (scalarModules a).obj (Mod.regular A'.X),
      f.hom = a.hom.hom := by
  sorry

/-- The scalar unit on the actual regular modules.
Source: paragraph (3) (blueprint: def-sfb-condensed-scalar-tensor). -/
def regularScalar (a : A ⟶ A') :
    Mod.regular A.X ⟶ (scalarModules a).obj (Mod.regular A'.X) :=
  Classical.choose (regularScalarExist a)

/-- The regular-ring scalar map in degree zero, using exact scalar restriction.
Source: paragraph (3) (blueprint: def-sfb-condensed-scalar-tensor). -/
def baseRingArrow (a : A ⟶ A') :
    (DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X) ⟶
      (scalarBase a).obj
        ((DerivedCategory.singleFunctor (Modules A') 0).obj (Mod.regular A'.X)) :=
  (DerivedCategory.singleFunctor (Modules A) 0).map (regularScalar a) ≫
    ((scalarModules a).mapDerivedCategorySingleFunctor 0).inv.app (Mod.regular A'.X)

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The regular scalar map between trivial actions is equivariant, with the scalar
restriction comparison fixed by its underlying sheaf identity.
Source: paragraph (3) (blueprint: def-sfb-condensed-scalar-tensor).
Proof: trivial actions fix every section, and scalar restriction has the same action
under its underlying comparison. Hence the displayed map commutes with every section. -/
theorem regularScalarEquivariant (a : A ⟶ A') :
    Profinite.CondensedAction.Equivariant (regularTrivial A G)
      ((scalarAction (G := G) a).functor.obj (regularTrivial A' G))
      (regularScalar a ≫ (scalarAction a).underlying.inv.app (regularTrivial A' G)) := by
  sorry

/-- The ring map regarded as an equivariant map between the trivial coefficients.
Source: paragraph (3) (blueprint: def-sfb-condensed-scalar-tensor). -/
def regularScalarAction (a : A ⟶ A') : regularTrivial A G ⟶
    (scalarAction (G := G) a).functor.obj (regularTrivial A' G) :=
  ⟨regularScalar a ≫ (scalarAction a).underlying.inv.app (regularTrivial A' G),
    regularScalarEquivariant (G := G) a⟩

/-- The specified scalar coefficient morphism in the ordinary derived action category.
Source: paragraph (3) (blueprint: def-sfb-condensed-scalar-tensor). -/
def coefficientArrow (a : A ⟶ A') : coefficient A G ⟶
    (scalarDerived a G).obj (coefficient A' G) :=
  (DerivedCategory.singleFunctor (Equivariant A G) 0).map (regularScalarAction (G := G) a) ≫
    ((scalarAction a).functor.mapDerivedCategorySingleFunctor 0).inv.app (regularTrivial A' G)

/-- The coefficient map for the original ring morphism, retaining its actual arrow.
Source: paragraph (3) (blueprint: def-sfb-condensed-scalar-tensor). -/
def coefficientCupMap (a : A ⟶ A') : cohomology A G ⟶
    (scalarBase a).obj (cohomology A' G) :=
  coefficientMap a (coefficientArrow (G := G) a)

end CategoryTheory.CondensedDerivedRestriction
