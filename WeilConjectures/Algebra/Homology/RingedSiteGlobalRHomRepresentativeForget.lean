/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedSiteGlobalRHomModel
public import WeilConjectures.Algebra.Homology.RingedSiteGlobalRHomCohomologyNaturality
import all WeilConjectures.Algebra.Homology.HomComplexGlobalHomotopyOfUniverses
import all WeilConjectures.Algebra.Homology.RingedSiteGlobalRHomSectionUnit

/-! The global Hom representative after forgetting its coefficient action. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v r a w z

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RingedSiteGlobalRHom

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max c v r})
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w} (Modules.{c, v, max c v r} R)]
  (A : Type a) [CommRing A] (φ : A →+* Scalars.{c, v, max c v r} R)
  [HasDerivedCategory.{z} (ModuleCat.{max c v r} A)]

attribute [local irreducible] homComplexFunctor derivedInternalHomOfUniverses
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit

/-- Ordinary Hom complexes as a functor in the target.
Source: Stacks Project, Tag 08JA.
(blueprint: lem-sfb-global-rhom-representative-forget-comparison). -/
def ordinaryHomFunctor
    (L : CochainComplex (Modules.{c, v, max c v r} R) ℤ) :
    CochainComplex (Modules.{c, v, max c v r} R) ℤ ⥤
      CochainComplex AddCommGrpCat.{max c v r} ℤ where
  obj I := CochainComplex.HomComplex L I
  map f := externalHomMap (𝟙 L) f
  map_id I := by
    ext n x
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q h
    change ((externalHomMap (𝟙 L) (𝟙 I)).f n x).v p q h = x.v p q h
    simp only [externalHomMap_v, HomologicalComplex.id_f, Category.id_comp, Category.comp_id]
  map_comp f g := by
    ext n x
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q h
    simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply]
    change ((externalHomMap (𝟙 L) (f ≫ g)).f n x).v p q h =
      ((externalHomMap (𝟙 L) g).f n ((externalHomMap (𝟙 L) f).f n x)).v p q h
    simp only [externalHomMap_v, HomologicalComplex.id_f, HomologicalComplex.comp_f,
      Category.id_comp, Category.assoc]

omit [HasDerivedCategory.{w} (Modules.{c, v, max c v r} R)] in
private theorem externalMap_eq
    {L L' I I' : CochainComplex (Modules.{c, v, max c v r} R) ℤ}
    (f : L' ⟶ L) (g : I ⟶ I') : externalMap f g = externalHomMap f g := by
  rfl

attribute [local irreducible] externalMap externalHomMap globalComplexIso forgetSectionsIso

private theorem uncurry_map_id_comp
    {B D E F : Type*} [Category* B] [Category* D] [Category* E] [Category* F]
    (H : B ⥤ D ⥤ E) (G : E ⥤ F) (X : B) {Y Y' : D} (f : Y ⟶ Y') :
    (Functor.uncurry.obj H ⋙ G).map (X := (X, Y)) (Y := (X, Y')) (𝟙 X, f) =
      G.map ((H.obj X).map f) := by
  simp only [Functor.comp_map, Functor.uncurry_obj_map, Functor.map_id,
    NatTrans.id_app, Category.id_comp]

omit [HasDerivedCategory.{w} (Modules.{c, v, max c v r} R)] in
private theorem ordinaryHom_naturality
    (L : CochainComplex (Modules.{c, v, max c v r} R) ℤ)
    {I I' : CochainComplex (Modules.{c, v, max c v r} R) ℤ} (f : I ⟶ I') :
    ((preadditiveCoyoneda.obj (op (SheafOfModules.unit
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))).mapHomologicalComplex
      (.up ℤ)).map (((homComplexFunctor (R := R)).obj (op L)).map f) ≫
      (globalComplexIso.{c, v, r} R (op L, I')).hom =
    (globalComplexIso.{c, v, r} R (op L, I)).hom ≫ externalHomMap (𝟙 L) f := by
  have hn := globalComplexIso_naturality.{c, v, r} R (𝟙 L) f
  dsimp only [globalBifunctor] at hn
  rw [show (𝟙 L).op = 𝟙 (op L) from rfl, uncurry_map_id_comp] at hn
  exact hn.trans (congrArg
    (fun k ↦ (globalComplexIso.{c, v, r} R (op L, I)).hom ≫ k)
    (externalMap_eq.{c, v, r} R (𝟙 L) f))

omit [HasDerivedCategory.{w} (Modules.{c, v, max c v r} R)]
  [HasDerivedCategory.{z} (ModuleCat.{max c v r} A)] in
/-- Forgetting the coefficient action identifies the section representative with ordinary Hom.
Source: Stacks Project, Tags 0B6E and 08JA.
(blueprint: lem-sfb-global-rhom-representative-forget-comparison).

Proof: forgetting the restricted scalar module turns sections into the additive
Yoneda functor of the unit sheaf. Apply this comparison degreewise, then use the
product-projection isomorphism with ordinary Hom cochains. Its naturality under
postcomposition supplies naturality of the isomorphism of complexes. -/
theorem representative_forget_comparison
    (L : CochainComplex (Modules.{c, v, max c v r} R) ℤ) :
    Nonempty (representative.{c, v, r, a} R A φ L ⋙
      (forget₂ (ModuleCat.{max c v r} A) AddCommGrpCat.{max c v r}).mapHomologicalComplex
        (.up ℤ) ≅ ordinaryHomFunctor.{c, v, r} R L) := by
  refine ⟨?_⟩
  refine Functor.associator ((homComplexFunctor (R := R)).obj (op L))
    ((sections.{c, v, max c v r} R A φ).mapHomologicalComplex (.up ℤ))
    ((forget₂ (ModuleCat.{max c v r} A) AddCommGrpCat.{max c v r}).mapHomologicalComplex
      (.up ℤ)) ≪≫
    Functor.isoWhiskerLeft ((homComplexFunctor (R := R)).obj (op L))
      (forgetSectionsIso.{c, v, r, a} R A φ) ≪≫ ?_
  exact NatIso.ofComponents (fun I ↦ globalComplexIso.{c, v, r} R (op L, I))
    (fun f ↦ ordinaryHom_naturality.{c, v, r} R L f)

end CategoryTheory.RingedSiteGlobalRHom
