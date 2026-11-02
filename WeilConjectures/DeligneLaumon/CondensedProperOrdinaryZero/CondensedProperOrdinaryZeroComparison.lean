/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedProperNative.CondensedProperNativeExchangeComparison
public import WeilConjectures.SmoothPurity.CondensedWeilModules

/-! # Degree-zero augmentation for ordinary native Weil exchange

Source: identity-compactification specialization of normalized cohomology transport.
(blueprint: lem-a1-condensed-proper-ordinary-zero-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedProperOrdinaryZero
namespace NativeArrow

private theorem map_exchange_naturality {C B : Type*} [Category C] [Category B]
    (R : C ⥤ B) (H : C ⥤ C) (Q U : B ⥤ B)
    (α : U ⋙ 𝟭 B ≅ Q ⋙ U) (e : R ⋙ Q ⟶ H ⋙ R)
    {M N : C} (φ : H.obj M ⟶ M) (ψ : H.obj N ⟶ N) (f : M ⟶ N)
    (hf : H.map f ≫ ψ = φ ≫ f) :
    U.map (R.map f) ≫ (α.hom.app (R.obj N) ≫ U.map (e.app N ≫ R.map ψ)) =
      (α.hom.app (R.obj M) ≫ U.map (e.app M ≫ R.map φ)) ≫ U.map (R.map f) := by
  have hα := α.hom.naturality (R.map f)
  simp only [Functor.comp_map, Functor.id_map] at hα
  have he := e.naturality f
  simp only [Functor.comp_map] at he
  rw [← Category.assoc, hα]
  simp only [Category.assoc, ← U.map_comp]
  congr 1
  rw [← Category.assoc, he]
  simp only [Category.assoc, ← R.map_comp]
  rw [hf]
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {P Y : Scheme.{u}}
  (a : Y ⟶ P) (g : Y ⟶ Y) (h : P ⟶ P) (w : g ≫ a = a ≫ h)
  (τ : CondensedRing.upperStar Λ h ≅ 𝟭 _)
attribute [local irreducible] CondensedRing.upperStar CondensedRing.lowerStar
/-- Native module arrow with variable point trivialization.
Source: the ordinary point-comparison/exchange/structure-map formula.
(blueprint: lem-a1-condensed-proper-ordinary-zero-comparison). -/
def operator
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (φ : (CondensedRing.upperStar Λ g).obj M ⟶ M) :=
  (CondensedRing.pointComparison Λ τ h
    (show (𝟙 P) ≫ h = h ≫ 𝟙 P by simp)).hom.app
      ((CondensedRing.lowerStar Λ a).obj M) ≫
    (CondensedRing.upperStar Λ (𝟙 P)).map
      ((CondensedRing.lowerStarBaseChange Λ (CommSq.mk w)).app M ≫
        (CondensedRing.lowerStar Λ a).map φ)
/-- Naturality of the native arrow. -/
private theorem naturality
    {M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
    (φ : (CondensedRing.upperStar Λ g).obj M ⟶ M)
    (ψ : (CondensedRing.upperStar Λ g).obj N ⟶ N) (f : M ⟶ N)
    (hf : (CondensedRing.upperStar Λ g).map f ≫ ψ = φ ≫ f) :
    (CondensedRing.upperStar Λ (𝟙 P)).map ((CondensedRing.lowerStar Λ a).map f) ≫
        operator Λ a g h w τ N ψ =
      operator Λ a g h w τ M φ ≫
        (CondensedRing.upperStar Λ (𝟙 P)).map ((CondensedRing.lowerStar Λ a).map f) := by
  exact map_exchange_naturality (CondensedRing.lowerStar Λ a) (CondensedRing.upperStar Λ g)
    (CondensedRing.upperStar Λ h) (CondensedRing.upperStar Λ (𝟙 P))
    (CondensedRing.pointComparison Λ τ h (show (𝟙 P) ≫ h = h ≫ 𝟙 P by simp))
    (CondensedRing.lowerStarBaseChange Λ (CommSq.mk w)) φ ψ f hf
/-- The source stalk exchange with native generic point data.
(blueprint: lem-a1-condensed-proper-ordinary-zero-comparison). -/
private theorem stalk_compatibility
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (φ : (CondensedRing.upperStar Λ g).obj M ⟶ M)
    (z z' : P ⟶ Y) (hz : z ≫ a = 𝟙 P) (hz' : z' ≫ a = 𝟙 P)
    (hs : z ≫ g = h ≫ z') :
    operator Λ a g h w τ M φ ≫ CondensedRing.stalkLowerStarProj Λ hz M =
      CondensedRing.stalkLowerStarProj Λ hz' M ≫
        ((CondensedRing.pointComparison Λ τ g hs).hom.app M ≫
          (CondensedRing.upperStar Λ z).map φ) := by
  exact CondensedRing.pointComparison_lowerStarBaseChange_stalkLowerStarProj
    Λ (CommSq.mk w) τ (by simp) hz hz' hs M φ

end NativeArrow

variable (l : ℕ) [Fact l.Prime] (k : Type u) [Field k] [IsAlgClosed k]
  {Y : Scheme.{u}} (a : Y ⟶ Spec (.of k))
  (g : Y ⟶ Y) [IsIso g] (h : Spec (.of k) ⟶ Spec (.of k)) [IsIso h]
  (w : g ≫ a = a ≫ h)

/-- The ordinary augmentation with inverse identity pullback inserted.
Source: H0 of the right derived functor on a single object is its canonical augmentation.
(blueprint: lem-a1-condensed-proper-ordinary-zero-comparison). -/
def comparison :
    DerivedCategory.singleFunctor (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) Y)) 0 ⋙
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) a).rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor
          (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
            (condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (.of k)))) 0 ≅
      CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) a ⋙
        CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (𝟙 (Spec (.of k))) :=
  Functor.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) a) ≪≫
    (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _
      (CondensedRing.upperStarId (Profinite.padicAlgClRingObj l) (Spec (.of k))).symm

section OrdinaryConstruction
set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Endofunctor.IsoAlgebra

/-- The ordinary native Weil operator, with its coefficient and point variables fixed once.
Source: the unit--square--counit operator in steps 5--6 of the parent node.
(blueprint: lem-a1-condensed-proper-ordinary-zero-comparison). -/
def ordinary (M : condensedWeilModules (Profinite.padicAlgClRingObj l) g) :
    End ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (𝟙 (Spec (.of k)))).obj
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) a).obj M.carrier)) :=
  NativeArrow.operator (Profinite.padicAlgClRingObj l) a g h w
    (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l) h)
    M.carrier M.obj.str

end OrdinaryConstruction

/-- The degree-zero Weil isomorphism with the canonical exact-pullback comparison.
Source: exact pullback in step 1 of the parent node
(blueprint: lem-a1-condensed-proper-ordinary-zero-comparison). -/
def weilStructure (M : condensedWeilModules (Profinite.padicAlgClRingObj l) g) :=
  (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj l)
    g).app ((DerivedCategory.singleFunctor _ 0).obj M.carrier) ≪≫
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g).mapDerivedCategorySingleFunctor
      0).app M.carrier ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso M.str

/-- The ordinary derived Weil operator is its underived mate under zero augmentation.

Source: latest blueprint lem-a1-finite-boundary-weights.proof.md, opening evaluation
sentence, ordinary degree-zero augmentation calculation; the derived-base-change
augmentation unit law and exact module pullback.
(blueprint: lem-a1-condensed-proper-ordinary-zero-comparison).

Proof: expand the ordinary derived operator as inverse point insertion, the right
adjunction mate of the canonical pullback square, and right derived image of θ.
Both side pullbacks are exact, so their left derived comparisons carry single
objects to the singles of their underived pullbacks. Under the canonical
right-derived augmentation, the mate unit becomes the underived adjunction unit
and its counit becomes the underived counit. This can be checked on the injective
resolution comparison: its degree-zero augmentation is the original sheaf map,
and the two unit identities identify the same square. Thus the derived square
mate becomes lowerStarBaseChange. Naturality of the exact-pullback single
comparison makes the last derived arrow the ordinary Weil structure map. Finally,
the identity-pullback compositor unit law converts inverse point insertion to the
pointComparison at the identity point. Composing these identities proves the
formula. This calculation needs no properness, compact comparison or normalized
compactification data; zero modules satisfy the same identities.
-/
theorem ordinary_comp_comparison
    (M : condensedWeilModules (Profinite.padicAlgClRingObj l) g) :
    (DerivedCategory.homologyFunctor
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (.of k)))) 0).map
          (CondensedProperNative.ordinary l k a g h w
            ((DerivedCategory.singleFunctor (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
              (condensedRingObj (Profinite.padicAlgClRingObj l) Y)) 0).obj M.carrier)
            (weilStructure l g M)) ≫ (comparison l k a).hom.app M.carrier =
      (comparison l k a).hom.app M.carrier ≫ ordinary l k a g h w M := by
  sorry

-- The established Weil-algebra alias is reduced only for these proof calculations.
set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Endofunctor.IsoAlgebra
attribute [local irreducible] CondensedRing.upperStar CondensedRing.lowerStar

omit [IsIso g] [IsIso h] in
/-- Naturality of the ordinary Weil operator for every Weil morphism.
Source: naturality of point comparison, base change, and the Weil morphism equation.
(blueprint: lem-a1-condensed-proper-ordinary-zero-comparison). -/
theorem ordinary_naturality
    (M N : condensedWeilModules (Profinite.padicAlgClRingObj l) g) (f : M ⟶ N) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (𝟙 (Spec (.of k)))).map
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) a).map f.hom.f) ≫
        ordinary l k a g h w N =
      ordinary l k a g h w M ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (𝟙 (Spec (.of k)))).map
          ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) a).map f.hom.f) := by
  exact NativeArrow.naturality (Profinite.padicAlgClRingObj l) a g h w
    (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l) h)
    M.obj.str N.obj.str f.hom.f f.hom.h


omit [IsIso g] [IsIso h] in
/-- Ordinary Frobenius followed by a germ is the next germ followed by one-step transport.
Source: pointComparison_lowerStarBaseChange_stalkLowerStarProj.
(blueprint: lem-a1-condensed-proper-ordinary-zero-comparison). -/
theorem ordinary_stalk_compatibility
    (M : condensedWeilModules (Profinite.padicAlgClRingObj l) g)
    (z z' : Spec (.of k) ⟶ Y) (hz : z ≫ a = 𝟙 _) (hz' : z' ≫ a = 𝟙 _)
    (hs : z ≫ g = h ≫ z') :
    ordinary l k a g h w M ≫
        CondensedRing.stalkLowerStarProj (Profinite.padicAlgClRingObj l) hz M.carrier =
      CondensedRing.stalkLowerStarProj (Profinite.padicAlgClRingObj l) hz' M.carrier ≫
        ((CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
          (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l) h)
          g hs).hom.app M.carrier ≫
            (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map M.obj.str) := by
  exact NativeArrow.stalk_compatibility (Profinite.padicAlgClRingObj l) a g h w
    (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l) h)
    M.carrier M.obj.str z z' hz hz' hs

end WeilConjectures.CondensedProperOrdinaryZero
