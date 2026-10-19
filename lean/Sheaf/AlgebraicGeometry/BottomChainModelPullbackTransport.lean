/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.LocalizedPullbackPerfectCounit
import Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Transport of a bottom chain model through derived pullback

Source: Stacks Project, Tags 06YD, 06YJ and 08DW.
(blueprint: lem-sc-bottom-chain-model-pullback-transport).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem compose_squares {C : Type*} [Category C]
    {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : C}
    (x₁ : X₁ ⟶ Y₁) (x₂ : X₂ ⟶ Y₂) (x₃ : X₃ ⟶ Y₃) (x₄ : X₄ ⟶ Y₄)
    (a₁ : X₁ ⟶ X₂) (a₂ : Y₁ ⟶ Y₂)
    (b₁ : X₂ ⟶ X₃) (b₂ : Y₂ ⟶ Y₃)
    (c₁ : X₃ ⟶ X₄) (c₂ : Y₃ ⟶ Y₄)
    (ha : x₁ ≫ a₂ = a₁ ≫ x₂) (hb : x₂ ≫ b₂ = b₁ ≫ x₃)
    (hc : x₃ ≫ c₂ = c₁ ≫ x₄) :
    x₁ ≫ (a₂ ≫ b₂ ≫ c₂) = (a₁ ≫ b₁ ≫ c₁) ≫ x₄ := by
  calc
    _ = (x₁ ≫ a₂) ≫ b₂ ≫ c₂ := by simp only [Category.assoc]
    _ = (a₁ ≫ x₂) ≫ b₂ ≫ c₂ := by rw [ha]
    _ = a₁ ≫ (x₂ ≫ b₂) ≫ c₂ := by simp only [Category.assoc]
    _ = a₁ ≫ (b₁ ≫ x₃) ≫ c₂ := by rw [hb]
    _ = a₁ ≫ b₁ ≫ (x₃ ≫ c₂) := by simp only [Category.assoc]
    _ = a₁ ≫ b₁ ≫ (c₁ ≫ x₄) := by rw [hc]
    _ = _ := by simp only [Category.assoc]

/-- Pulling back a local strictly perfect chain representative gives a local
cohomology square with the pulled-back chain map. Zero bottom differentials
and an invertible bottom component persist. This asserts the square for the
specified arrow, rather than an unrelated isomorphism between its endpoints.

Source: Stacks Project, Tags 06YD and 06YJ (termwise flat pullback),
08DW (restriction compatibility); Tag 0BDL, canonical pullback clause.
(blueprint: lem-sc-bottom-chain-model-pullback-transport).

Proof: Let V be the inverse image of U. The point hypothesis gives y in V.
Use the equivalence of module sheaves on the localized open site with modules
on U.toScheme to transport A, B and alpha there. Strictly perfect terms are
retracts of finite free modules, hence flat, and the complexes are bounded
above. The flat-complex derived-pullback counit therefore computes their
pullbacks termwise along V.toScheme -> U.toScheme. Use this one natural counit
for both complexes: its naturality transports the given square for f to the
termwise pulled-back alpha. Ordinary tensor pullback preserves zero objects,
zero differentials and isomorphisms. Thus the resulting P and Q have zero
term in degree -1 and zero differential 0 -> 1, and beta.f 0 is invertible.
Transport P and Q back to the localized site over V. Exact open restriction
commutes with homology, and derived pullback commutes with open restriction.
Apply homology to the naturality square and compose with these comparison
isomorphisms and the homology factorization of the localization Q. This gives
eP, eQ and the displayed equality for the restriction of H0(Lk*f).
The constructions preserve zero objects also on the empty open and in rank zero. -/
theorem bottom_chain_model_pullback_transport
    [∀ T : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (S : Scheme.{u})
    [∀ U : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (X Z : schemeDerivedCategory S) (f : X ⟶ Z) (U : S.Opens)
    (A B : CochainComplex
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ)
    (hA : IsStrictlyPerfect S U A) (hB : IsStrictlyPerfect S U B)
    (hAzero : ∀ i : ℤ, i ≠ 0 → IsZero (A.X i))
    (hBnegative : ∀ i : ℤ, i < 0 → IsZero (B.X i))
    (hBzero : B.d 0 1 = 0) (α : A ⟶ B) (hα : IsIso (α.f 0))
    (eA : (SheafOfModules.overFunctor.{u}
        (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj X ≅
          DerivedCategory.Q.obj A)
    (eB : (SheafOfModules.overFunctor.{u}
        (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj Z ≅
          DerivedCategory.Q.obj B)
    (hsquare : (SheafOfModules.overFunctor.{u}
        (moduleRings S.toRingedSpace) U).mapDerivedCategory.map f ≫ eB.hom =
          eA.hom ≫ DerivedCategory.Q.map α)
    {Y : Scheme.{u}} (k : Y ⟶ S) (y : Y) (hy : k.base y ∈ U) :
    ∃ V : Y.Opens, y ∈ V ∧
      ∃ P Q : CochainComplex
          (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V)) ℤ,
        IsZero (P.X (-1)) ∧ IsZero (Q.X (-1)) ∧
        P.d 0 1 = 0 ∧ Q.d 0 1 = 0 ∧
        ∃ β : P ⟶ Q, IsIso (β.f 0) ∧
          ∃ (eP : ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((derivedPullback k).obj X)).over V ≅ P.homology 0)
            (eQ : ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((derivedPullback k).obj Z)).over V ≅ Q.homology 0),
            (((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map
                ((derivedPullback k).map f)).over V) ≫ eQ.hom =
                  eP.hom ≫ HomologicalComplex.homologyMap β 0 := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  set_option synthInstance.maxSize 2048 in
  let V := k ⁻¹ᵁ U
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
  let R := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V
  let D := SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U
  let A' : SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    (Scheme.Modules.overEquiv U).functor
  let C : SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V) ⥤
      SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) :=
    (Scheme.Modules.overEquiv V).functor
  have : A'.Additive := Functor.additive_of_preserves_binary_products _
  have : C.Additive := Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteLimits (R ⋙ C) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (R ⋙ C) := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits (D ⋙ A') := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (D ⋙ A') := comp_preservesFiniteColimits _ _
  let F := Modules.localizedPullback k U
  let FC := F.mapHomologicalComplex (.up ℤ)
  let P := FC.obj A
  let Q := FC.obj B
  let β := FC.map α
  let L := derivedPullback (k.resLE U V le_rfl)
  obtain ⟨η, hη⟩ := localizedPullback_perfectCounit k U
  have : IsIso (η.app A) := hη A hA
  have : IsIso (η.app B) := hη B hB
  obtain ⟨θ⟩ := derivedPullback_openRestriction_iso_universes k V U le_rfl
  let τ : derivedPullback k ⋙ R.mapDerivedCategory ⋙ C.mapDerivedCategory ≅
      D.mapDerivedCategory ⋙ A'.mapDerivedCategory ⋙ L :=
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso R C).symm ≪≫
      θ ≪≫ Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso D A') L ≪≫
        Functor.associator _ _ _
  let a : C.mapDerivedCategory.obj
      (R.mapDerivedCategory.obj ((derivedPullback k).obj X)) ≅
        C.mapDerivedCategory.obj (DerivedCategory.Q.obj P) :=
    τ.app X ≪≫ (A'.mapDerivedCategory ⋙ L).mapIso eA ≪≫ asIso (η.app A)
  let b : C.mapDerivedCategory.obj
      (R.mapDerivedCategory.obj ((derivedPullback k).obj Z)) ≅
        C.mapDerivedCategory.obj (DerivedCategory.Q.obj Q) :=
    τ.app Z ≪≫ (A'.mapDerivedCategory ⋙ L).mapIso eB ≪≫ asIso (η.app B)
  have hs := congrArg (fun t ↦ (A'.mapDerivedCategory ⋙ L).map t) hsquare
  simp only [Functor.map_comp] at hs
  have hab : C.mapDerivedCategory.map
      (R.mapDerivedCategory.map ((derivedPullback k).map f)) ≫ b.hom =
        a.hom ≫ C.mapDerivedCategory.map (DerivedCategory.Q.map β) := by
    have ht : C.mapDerivedCategory.map
        (R.mapDerivedCategory.map ((derivedPullback k).map f)) ≫ (τ.app Z).hom =
      (τ.app X).hom ≫ (A'.mapDerivedCategory ⋙ L).map (D.mapDerivedCategory.map f) :=
      τ.hom.naturality f
    have he : (A'.mapDerivedCategory ⋙ L).map (DerivedCategory.Q.map α) ≫ η.app B =
        η.app A ≫ C.mapDerivedCategory.map (DerivedCategory.Q.map β) :=
      η.naturality α
    exact compose_squares _ _ _ _ _ _ _ _ _ _ ht hs he
  let a' := C.mapDerivedCategory.preimageIso a
  let b' := C.mapDerivedCategory.preimageIso b
  have hab' : R.mapDerivedCategory.map ((derivedPullback k).map f) ≫ b'.hom =
      a'.hom ≫ DerivedCategory.Q.map β := by
    apply C.mapDerivedCategory.map_injective
    simpa only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage,
      a', b'] using hab
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V)) 0
  let hR := R.mapDerivedCategoryHomologyFunctorIso 0
  let hQ := DerivedCategory.homologyFunctorFactors
    (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V)) 0
  let eP := hR.app ((derivedPullback k).obj X) ≪≫ H.mapIso a' ≪≫ hQ.app P
  let eQ := hR.app ((derivedPullback k).obj Z) ≪≫ H.mapIso b' ≪≫ hQ.app Q
  refine ⟨V, hy, P, Q, F.map_isZero (hAzero (-1) (by decide)),
    F.map_isZero (hBnegative (-1) (by decide)), ?_, ?_, β, ?_, eP, eQ, ?_⟩
  · change F.map (A.d 0 1) = 0
    erw [(hAzero 1 (by decide)).eq_of_tgt (A.d 0 1) 0, F.map_zero]
  · change F.map (B.d 0 1) = 0
    erw [hBzero, F.map_zero]
  · let := hα
    change IsIso (F.map (α.f 0))
    infer_instance
  · have hh := congrArg H.map hab'
    simp only [Functor.map_comp] at hh
    have hr : (((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map
          ((derivedPullback k).map f)).over V) ≫
        (hR.app ((derivedPullback k).obj Z)).hom =
      (hR.app ((derivedPullback k).obj X)).hom ≫
        H.map (R.mapDerivedCategory.map ((derivedPullback k).map f)) :=
      hR.hom.naturality ((derivedPullback k).map f)
    have hq : H.map (DerivedCategory.Q.map β) ≫ (hQ.app Q).hom =
        (hQ.app P).hom ≫ HomologicalComplex.homologyMap β 0 :=
      hQ.hom.naturality β
    exact compose_squares _ _ _ _ _ _ _ _ _ _ hr hh hq

end AlgebraicGeometry.Scheme
