/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Mathlib.Algebra.Homology.Localization

/-!
# The derived category of a monoidal closed Grothendieck abelian category is monoidal closed

Let `C` be a Grothendieck abelian category which is monoidal closed, and whose monoidal
structure is compatible with the additive structure in the way that is needed in order to
tensor cochain complexes (`MonoidalPreadditive C` and the `GradedObject` hypotheses below,
which are exactly the ones under which `DerivedCategory C` is monoidal, see
`WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal`). This file shows that,
when moreover K-flat complexes form a left derivability structure for the quasi-isomorphisms
(which holds as soon as `C` has functorial flat resolutions, see
`WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat`), the derived category `D(C)`
is again monoidal closed, the monoidal structure being the derived tensor product `- ⊗^L -`.

Since `MonoidalClosed` only asks for a right adjoint of `X ⊗^L -` for every object `X` of
`D(C)`, no binary `RHom` bifunctor has to be constructed by hand: the bifunctoriality of the
internal hom is produced by the closed structure itself. The proof of the instance below is
therefore organized in the following four steps.

1. **Closedness at the homotopy level** (done in
   `WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom`). For cochain complexes
   `P`, `Y` in `C`, the internal hom complex `CochainComplex.internalHomObj P Y` has
   `(iHom P Y)ⁿ = ∏_{p + n = q} iHom (P.X p) (Y.X q)`, with differential
   `(-1)ᵖ • (f ≫ d_Y - d_P ≫ f)` on the factor indexed by `(p, q)` (the products exist since
   `C` is Grothendieck abelian). The tensor-hom bijection `(P ⊗ X ⟶ Y) ≃ (X ⟶ iHom P Y)` is
   plain currying on morphisms of complexes, and currying with the sign `(-1) ^ (p * n)` on
   cochains of degree `n` commutes with `δ`, so it is compatible with homotopies. This gives
   `HomotopyCategory.tensorHomAdjunction P : tensorLeft P ⊣ H_P` on
   `K(C) := HomotopyCategory C (ComplexShape.up ℤ)`, with `H_P = HomotopyCategory.internalHom P`.
2. **Fixing one variable of the binary derived tensor.** Deduce from the fact that the derived
   tensor product is the binary left derived functor of the tensor product on `K(C)` (the
   `IsLeftDerivedFunctor₂` instance in
   `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal`) that `Qh.obj P ⊗^L -`
   is the (unary) left derived functor of `P ⊗ -`: the comparison map
   `Qh.obj P ⊗^L Qh.obj Z ⟶ Qh.obj (P ⊗ Z)` is an isomorphism for K-flat `Z`
   (`DerivedCategory.tensorLeftQhObjCounit`).
3. **Deriving the adjunction.** Right derive `H_P` using K-injective resolutions, which exist
   since `C` is Grothendieck abelian
   (`CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`), and apply
   `CategoryTheory.Adjunction.derived` to `P ⊗ - ⊣ H_P` to obtain `Qh.obj P ⊗^L - ⊣ R H_P`
   (`DerivedCategory.tensorHomAdjunctionQhObj`). The absoluteness hypotheses of
   `Adjunction.derived` are checked on K-flat, respectively K-injective, complexes. Only the
   individual right derived functors are needed here, not their functoriality in `P`.
4. **Transport to an arbitrary object.** Every `X : DerivedCategory C` is isomorphic to
   `Qh.obj P` for some `P` (essential surjectivity of the localization functor), and
   closedness transfers along an isomorphism of objects, since an isomorphism `Qh.obj P ≅ X`
   induces a natural isomorphism `Qh.obj P ⊗^L - ≅ X ⊗^L -`, along which the adjunction of
   step 3 can be transported (`CategoryTheory.Adjunction.ofNatIsoLeft`).

Once the instance is available, its internal hom is *the* derived internal hom; identifying it
with the concrete hom-complex-of-a-K-injective-replacement model is further work, which is what
an `RHom` API would be about.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
  [(HomotopyCategory.quasiIso C
    (ComplexShape.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure]
  (P : HomotopyCategory C (ComplexShape.up ℤ))

/-- The comparison `Qh.obj P ⊗^L Qh.obj Z ⟶ Qh.obj (P ⊗ Z)`, natural in `Z`, exhibiting
`Qh.obj P ⊗^L -` as the left derived functor of `P ⊗ -`. -/
noncomputable def tensorLeftQhObjCounit :
    Qh ⋙ tensorLeft (Qh.obj P) ⟶ tensorLeft P ⋙ Qh :=
  Functor.bifunctorCounit₁ (Functor.LaxMonoidal.μNatTrans Qh) P

omit [IsGrothendieckAbelian.{w} C] in
lemma isIso_tensorLeftQhObjCounit_app (Z : HomotopyCategory C (ComplexShape.up ℤ))
    (hZ : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).kFlat Z) :
    IsIso ((tensorLeftQhObjCounit P).app Z) :=
  have := instIsLeftDerivedFunctor₂HomotopyCategoryIntUpCurriedTensorμNatTransQhQuasiIso C
  ((HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).id_prod_kFlat_derives_curriedTensor
    Qh).isIso_of_isLeftDerivabilityStructure (Functor.LaxMonoidal.μNatTrans Qh) P ⟨Z, hZ⟩

instance : (tensorLeft (Qh.obj P)).IsLeftDerivedFunctor (tensorLeftQhObjCounit P)
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  (HomotopyCategory.quasiIso C
    (ComplexShape.up ℤ)).localizerMorphismKFlat.isLeftDerivedFunctor_of_isLeftDerivabilityStructure
      _ (fun Z ↦ isIso_tensorLeftQhObjCounit_app P Z.1 Z.2)

/-- The right derived functor of the internal hom `iHom P -` of the homotopy category,
computed on K-injective complexes. It is the internal hom out of `Qh.obj P` in `D(C)`. -/
noncomputable def internalHomQhObj : DerivedCategory C ⥤ DerivedCategory C :=
  (HomotopyCategory.internalHom P ⋙ Qh).totalRightDerived Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

/-- The natural transformation exhibiting `internalHomQhObj P` as the right derived functor
of `iHom P -`. -/
noncomputable def internalHomQhObjUnit :
    HomotopyCategory.internalHom P ⋙ Qh ⟶ Qh ⋙ internalHomQhObj P :=
  (HomotopyCategory.internalHom P ⋙ Qh).totalRightDerivedUnit Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

instance : (internalHomQhObj P).IsRightDerivedFunctor (internalHomQhObjUnit P)
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  dsimp only [internalHomQhObj, internalHomQhObjUnit]
  infer_instance

instance : (tensorLeft (Qh.obj P) ⋙ internalHomQhObj P).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (tensorLeftQhObjCounit P) (internalHomQhObj P))
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  (HomotopyCategory.quasiIso C
    (ComplexShape.up ℤ)).localizerMorphismKFlat.isLeftDerivedFunctor_of_isLeftDerivabilityStructure
      _ (fun Z ↦ by
        have := isIso_tensorLeftQhObjCounit_app P Z.1 Z.2
        have : IsIso ((internalHomQhObj P).map ((tensorLeftQhObjCounit P).app Z.1)) :=
          inferInstance
        exact IsIso.comp_isIso' inferInstance this)

instance : (internalHomQhObj P ⋙ tensorLeft (Qh.obj P)).IsRightDerivedFunctor
      (Functor.whiskerRight (internalHomQhObjUnit P) (tensorLeft (Qh.obj P)) ≫
        (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  (HomotopyCategory.KInjectives.localizerMorphism
    C).isRightDerivedFunctor_of_isRightDerivabilityStructure
      _ (fun I ↦ by
        have := (HomotopyCategory.KInjectives.localizerMorphism_derives
          (HomotopyCategory.internalHom P ⋙ Qh)).isIso_of_isRightDerivedFunctor
            (internalHomQhObjUnit P) I
        exact IsIso.comp_isIso' (Functor.map_isIso (tensorLeft (Qh.obj P)) _) inferInstance)

/-- The derived tensor-hom adjunction `Qh.obj P ⊗^L - ⊣ R iHom P -`, obtained by deriving
the tensor-hom adjunction `P ⊗ - ⊣ iHom P -` of the homotopy category. -/
noncomputable def tensorHomAdjunctionQhObj :
    tensorLeft (Qh.obj P) ⊣ internalHomQhObj P :=
  (HomotopyCategory.tensorHomAdjunction P).derived
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (tensorLeftQhObjCounit P) (internalHomQhObjUnit P)

variable (C) in
/-- The derived category of a monoidal closed Grothendieck abelian category is monoidal
closed for the derived tensor product: for every `X : DerivedCategory C`, the functor
`X ⊗^L -` admits a right adjoint. Writing `X ≅ Qh.obj P`, this right adjoint is the right
derived functor of `iHom P -`. -/
noncomputable instance monoidalClosed : MonoidalClosed (DerivedCategory C) where
  closed X :=
    { rightAdj := internalHomQhObj (Qh.objPreimage X)
      adj := (tensorHomAdjunctionQhObj (Qh.objPreimage X)).ofNatIsoLeft
        ((tensoringLeft _).mapIso (Qh.objObjPreimageIso X)) }

end DerivedCategory
