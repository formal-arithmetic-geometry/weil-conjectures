/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import Sheaf.CategoryTheory.SheafTensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import Sheaf.AlgebraicGeometry.WeaklyEtaleStability
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# The specified finite presentation on a base-changed pro-étale cover

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-def-sfb-dc-restricted-functors/lem-sfb-dc-upper-star-preserves.proof.md`,
from "Choose a pro-étale cover" to the end
(blueprint: lem-sfb-local-finite-presentation-inverse-image).

The witness records the canonical comparison and coordinate maps, and the
cokernel arrow equation ties the resulting presentation to the given one.
-/

@[expose] public section

set_option autoImplicit false

universe u v w₁ w₂ w₃ w₄ z₁ z₂ z₃ z₄

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The local witnesses in the specified-cover inverse-image assertion. This record
only packages its ring, module, basis and presentation isomorphisms. It uses abstract
ambient categories to keep their elaboration independent of the sheaf constructions.
The comparison e is supplied in the theorem by the existing `upperStarCompIso` of the
pullback square.

Source: blueprint main-20261015, proof of `lem-sfb-dc-upper-star-preserves`,
from "Choose a pro-étale cover" through the final sentence
(blueprint: lem-sfb-local-finite-presentation-inverse-image).
-/
structure FinitePresentationTransportWitness
    {C : Type w₁} [Category.{z₁} C] [MonoidalCategory C]
    {B : Type w₂} [Category.{z₂} B] [MonoidalCategory B]
    {D : Type w₃} [Category.{z₃} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D] [∀ A : D, PreservesFiniteColimits (tensorLeft A)]
    {E : Type w₄} [Category.{z₄} E] [MonoidalCategory E] [Abelian E]
    [MonoidalPreadditive E] [∀ A : E, PreservesFiniteColimits (tensorLeft A)]
    (F : C ⥤ B) (G : B ⥤ E) (J : C ⥤ D) (H : D ⥤ E)
    [F.LaxMonoidal] [G.LaxMonoidal] [J.LaxMonoidal] [H.LaxMonoidal]
    (e : F ⋙ G ≅ J ⋙ H) (R : C) [MonObj R] (M : Mod C R) (m n : ℕ)
    (d : Mod.finiteFree (J.obj R) m ⟶ Mod.finiteFree (J.obj R) n)
    (p : (J.mapMod R).obj M ≅ cokernel d) where
  /-- The ring isomorphism supplied by the specified composition comparison. -/
  ringIso : Mon.mk (G.obj (F.obj R)) ≅ Mon.mk (H.obj (J.obj R))
  /-- The ring map is the component of the specified comparison. -/
  ringIso_hom : ringIso.hom.hom = e.hom.app R
  /-- The comparison of actual module objects, with restriction along beta. -/
  moduleIso : (G.mapMod (F.obj R)).obj ((F.mapMod R).obj M) ≅
    (Mod.comap ringIso.hom.hom).obj ((H.mapMod (J.obj R)).obj ((J.mapMod R).obj M))
  /-- Its underlying sheaf map is the component of the same comparison. -/
  moduleIso_hom : moduleIso.hom.hom = e.hom.app M.X
  /-- The finite-free identification for every rank, including zero. -/
  freeIso : ∀ k : ℕ,
    (Mod.comap ringIso.hom.hom).obj
      ((H.mapMod (J.obj R)).obj (Mod.finiteFree (J.obj R) k)) ≅
    Mod.finiteFree (G.obj (F.obj R)) k
  /-- Its coordinates determine the canonical identification uniquely. -/
  freeIso_projection : ∀ (k : ℕ) (j : Fin k),
    (freeIso k).hom.hom ≫
      (biproduct.π (fun _ : Fin k ↦ Mod.regular (G.obj (F.obj R))) j).hom =
    H.map ((biproduct.π (fun _ : Fin k ↦ Mod.regular (J.obj R)) j).hom) ≫ ringIso.inv.hom
  /-- The presentation with the actual conjugated transported differential. -/
  presentationIso : (G.mapMod (F.obj R)).obj ((F.mapMod R).obj M) ≅
    cokernel ((freeIso m).inv ≫
      (Mod.comap ringIso.hom.hom).map ((H.mapMod (J.obj R)).map d) ≫ (freeIso n).hom)
  /-- The chosen presentation induces this cokernel arrow, fixing its normalization. -/
  presentationIso_π : (freeIso n).inv ≫
      (Mod.comap ringIso.hom.hom).map
        ((H.mapMod (J.obj R)).map (cokernel.π d ≫ p.inv)) ≫
      moduleIso.inv ≫ presentationIso.hom =
    cokernel.π ((freeIso m).inv ≫
      (Mod.comap ringIso.hom.hom).map ((H.mapMod (J.obj R)).map d) ≫ (freeIso n).hom)

private theorem upperStarComp_monoidal
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} a b).inv := by
  have h₁ : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (upperStarLowerStarAdjunction Ab.{u + 1} (a ≫ b))
      Functor.Monoidal.toOplaxMonoidal _ :=
    isMonoidal_upperStarLowerStarAdjunction _ _
  have h₂ : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      ((upperStarLowerStarAdjunction Ab.{u + 1} b).comp
        (upperStarLowerStarAdjunction Ab.{u + 1} a))
      Functor.Monoidal.toOplaxMonoidal _ :=
    Adjunction.isMonoidal_comp _ _
  exact isMonoidal_conjugateEquiv_symm _ _ (lowerStarComp Ab.{u + 1} a b).inv

private theorem upperStarSquare_monoidal
    {X Y Z T : Scheme.{u}} {a : X ⟶ Y} {b : Y ⟶ T}
    {c : X ⟶ Z} {d : Z ⟶ T} (h : a ≫ b = c ≫ d) :
    NatTrans.IsMonoidal (upperStarCompIso Ab.{u + 1} h).hom := by
  have := upperStarComp_monoidal a b
  have hc : NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} c d).hom := by
    have : NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} c d).symm.hom :=
      upperStarComp_monoidal c d
    exact inferInstanceAs
      (NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} c d).symm.inv)
  have he : NatTrans.IsMonoidal (upperStarCongr Ab.{u + 1} h).hom := by
    generalize a ≫ b = g, c ≫ d = g' at h ⊢
    subst g'
    exact inferInstanceAs (NatTrans.IsMonoidal (𝟙 _))
  dsimp [upperStarCompIso]
  infer_instance

private theorem transportWitness
    {C : Type w₁} [Category.{z₁} C] [MonoidalCategory C]
    {B : Type w₂} [Category.{z₂} B] [MonoidalCategory B]
    {D : Type w₃} [Category.{z₃} D] [MonoidalCategory D] [Abelian D]
    [MonoidalPreadditive D] [∀ A : D, PreservesFiniteColimits (tensorLeft A)]
    {E : Type w₄} [Category.{z₄} E] [MonoidalCategory E] [Abelian E]
    [MonoidalPreadditive E] [∀ A : E, PreservesFiniteColimits (tensorLeft A)]
    (F : C ⥤ B) (G : B ⥤ E) (J : C ⥤ D) (H : D ⥤ E)
    [F.LaxMonoidal] [G.LaxMonoidal] [J.LaxMonoidal] [H.LaxMonoidal]
    [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ J ⋙ H) [NatTrans.IsMonoidal e.hom]
    (R : C) [MonObj R] (M : Mod C R) (m n : ℕ)
    (d : Mod.finiteFree (J.obj R) m ⟶ Mod.finiteFree (J.obj R) n)
    (p : (J.mapMod R).obj M ≅ cokernel d) :
    Nonempty (FinitePresentationTransportWitness F G J H e R M m n d p) := by
  classical
  have he : @IsMonHom E _ _ (G.obj (F.obj R)) (H.obj (J.obj R))
      (G.monObjObj (F.obj R)) (H.monObjObj (J.obj R)) (e.hom.app R) :=
    IsMonHom.of_eq (h₁ := (F ⋙ G).monObjObj R)
      (h₂ := (J ⋙ H).monObjObj R) (e.hom.app R)
      (Functor.monObjObj_comp F G R) (Functor.monObjObj_comp J H R)
  let b : Mon.mk (G.obj (F.obj R)) ≅ Mon.mk (H.obj (J.obj R)) :=
    @Mon.mkIso' E _ _ _ _ (G.monObjObj (F.obj R)) (H.monObjObj (J.obj R))
      (e.app R) he
  let T := H.mapMod (J.obj R) ⋙ Mod.comap b.hom.hom
  have hT : PreservesFiniteColimits T := by
    have : PreservesFiniteColimits (T ⋙ Mod.forget (G.obj (F.obj R))) :=
      inferInstanceAs (PreservesFiniteColimits (H.mapMod (J.obj R) ⋙
        Mod.forget (H.obj (J.obj R))))
    have : ReflectsFiniteColimits
        (Mod.forget (G.obj (F.obj R)) : Mod E (G.obj (F.obj R)) ⥤ E) :=
      { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
    exact preservesFiniteColimits_of_reflects_of_preserves T
      (Mod.forget (G.obj (F.obj R)))
  have : T.Additive := rightExactFunctor_le_additiveFunctor _ _ T hT
  let q : (G.mapMod (F.obj R)).obj ((F.mapMod R).obj M) ≅
      (Mod.comap b.hom.hom).obj ((H.mapMod (J.obj R)).obj ((J.mapMod R).obj M)) :=
    Mod.isoMk (e.app M.X) (by
      have ht := NatTrans.IsMonoidal.tensor (τ := e.hom) R M.X
      simp only [Functor.LaxMonoidal.comp_μ] at ht
      change (Functor.LaxMonoidal.μ G _ _ ≫
        G.map (Functor.LaxMonoidal.μ F _ _ ≫ F.map (Mod.act M.X))) ≫ e.hom.app M.X =
        _ ◁ e.hom.app M.X ≫ e.hom.app R ▷ _ ≫
          Functor.LaxMonoidal.μ H _ _ ≫
            H.map (Functor.LaxMonoidal.μ J _ _ ≫ J.map (Mod.act M.X))
      simp only [Functor.map_comp, Category.assoc]
      have hn := e.hom.naturality (Mod.act (A := R) M.X)
      change G.map (F.map (Mod.act M.X)) ≫ e.hom.app M.X =
        e.hom.app (R ⊗ M.X) ≫ H.map (J.map (Mod.act M.X)) at hn
      rw [hn, ← Category.assoc, ← Category.assoc, ht]
      simp only [tensorHom_def', Category.assoc])
  let r : T.obj (Mod.regular (J.obj R)) ≅ Mod.regular (G.obj (F.obj R)) :=
    Mod.isoMk ((Mon.forget E).mapIso b.symm) (by
      change (b.hom.hom ▷ _ ≫ MonObj.mul) ≫ b.inv.hom =
        _ ◁ b.inv.hom ≫ MonObj.mul
      rw [Category.assoc, IsMonHom.mul_hom, tensorHom_def]
      simp only [← Category.assoc, ← comp_whiskerRight]
      have hb : b.hom.hom ≫ b.inv.hom = 𝟙 _ :=
        congrArg Mon.Hom.hom b.hom_inv_id
      rw [hb]
      simp)
  let a (k : ℕ) : T.obj (Mod.finiteFree (J.obj R) k) ≅
      Mod.finiteFree (G.obj (F.obj R)) k :=
    T.mapBiproduct (fun _ : Fin k ↦ Mod.regular (J.obj R)) ≪≫
      biproduct.mapIso (fun _ ↦ r)
  let d' := (a m).inv ≫ T.map d ≫ (a n).hom
  let c : T.obj (cokernel d) ≅ cokernel d' :=
    PreservesCokernel.iso T d ≪≫
      cokernel.mapIso _ d' (a m) (a n) (by simp [d'])
  refine ⟨{
    ringIso := b
    ringIso_hom := rfl
    moduleIso := q
    moduleIso_hom := rfl
    freeIso := a
    freeIso_projection := ?_
    presentationIso := q ≪≫ T.mapIso p ≪≫ c
    presentationIso_π := ?_ }⟩
  · intro k j
    have h : (a k).hom ≫ biproduct.π _ j =
        T.map (biproduct.π (fun _ : Fin k ↦ Mod.regular (J.obj R)) j) ≫ r.hom := by
      dsimp [a]
      simp
    change ((a k).hom ≫ biproduct.π _ j).hom = _
    rw [h]
    rfl
  · change (a n).inv ≫ T.map (cokernel.π d ≫ p.inv) ≫
      q.inv ≫ (q ≪≫ T.mapIso p ≪≫ c).hom = _
    simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
      Iso.inv_hom_id_assoc, ← T.map_comp_assoc, p.inv_hom_id, T.map_id,
      Category.id_comp]
    dsimp [c]
    rw [PreservesCokernel.π_iso_hom_assoc]
    simp [d']
    rfl

/-- Pullback transports the chosen covering and all its specified finite presentations,
with unchanged ranks; in particular it preserves local finite presentation.

Source: blueprint main-20261015, proof of `lem-sfb-dc-upper-star-preserves`,
from "Choose a pro-étale cover" through the final sentence
(blueprint: lem-sfb-local-finite-presentation-inverse-image).

Proof:
1. Pro-etale inverse image preserves finite colimits as a left adjoint. Finite
   colimits of internal modules are computed by their forgetful functors.
2. The base-change operation on covers gives precisely the requested family.
3. The specified inverse-image compositors are monoidal, being conjugates of the
   monoidal pushforward compositors under the given monoidal adjunctions. Compose
   with the equality comparison of the pullback square and evaluate at R.
4. Naturality at the module action and the tensor equation for this same comparison
   prove linearity on the actual iterated actions. Use Mod.isoMk for the inverse.
5. Transport followed by restriction along the ring comparison preserves finite
   colimits, as checked through the forgetful functor, hence is additive.
6. The inverse ring comparison identifies the transported regular module with the
   regular module. Apply mapBiproduct and this isomorphism in every coordinate.
   The biproduct projection equations give the stated coordinate normalization.
7. Compose the image of p with the preserved-cokernel isomorphism and the cokernel
   isomorphism induced by the square of finite-free comparisons. Cancel the images
   of p inverse and p and apply the two cokernel-arrow equations to get the required
   normalization of presentationIso.
8. Restrict the base-changed cover to its existing small-index subcover to satisfy
   the index universe of IsLocallyFinitelyPresented. Every presentation restricts
   definitionally; the explicit witnesses still retain the entire original family.
The empty cover, zero ranks, and the zero ring are included in the same construction.
-/
theorem localFinitePresentation_inverseImage
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) R)
    (𝒰 : Scheme.Cover.{v} Scheme.proetalePrecoverage Y) (m n : 𝒰.I₀ → ℕ)
    (d : ∀ i, Mod.finiteFree ((upperStar Ab.{u + 1} (𝒰.f i)).obj R) (m i) ⟶
      Mod.finiteFree ((upperStar Ab.{u + 1} (𝒰.f i)).obj R) (n i))
    (p : ∀ i, ((upperStar Ab.{u + 1} (𝒰.f i)).mapMod R).obj M ≅ cokernel (d i)) :
    (𝒰.toPreZeroHypercover.pullback₁ f).presieve₀ ∈ Scheme.proetalePrecoverage X ∧
    (∀ i : 𝒰.I₀, Nonempty (FinitePresentationTransportWitness
      (upperStar Ab.{u + 1} f) (upperStar Ab.{u + 1} (pullback.fst f (𝒰.f i)))
      (upperStar Ab.{u + 1} (𝒰.f i)) (upperStar Ab.{u + 1} (pullback.snd f (𝒰.f i)))
      (upperStarCompIso Ab.{u + 1} (pullback.condition (f := f) (g := 𝒰.f i)))
      R M (m i) (n i) (d i) (p i))) ∧
    IsLocallyFinitelyPresented ((upperStar Ab.{u + 1} f).obj R)
      (((upperStar Ab.{u + 1} f).mapMod R).obj M) := by
  classical
  have hw (i : 𝒰.I₀) : Nonempty (FinitePresentationTransportWitness
      (upperStar Ab.{u + 1} f) (upperStar Ab.{u + 1} (pullback.fst f (𝒰.f i)))
      (upperStar Ab.{u + 1} (𝒰.f i)) (upperStar Ab.{u + 1} (pullback.snd f (𝒰.f i)))
      (upperStarCompIso Ab.{u + 1} (pullback.condition (f := f) (g := 𝒰.f i)))
      R M (m i) (n i) (d i) (p i)) := by
    have := upperStarSquare_monoidal (pullback.condition (f := f) (g := 𝒰.f i))
    exact transportWitness _ _ _ _ _ R M (m i) (n i) (d i) (p i)
  refine ⟨(𝒰.pullback₁ f).mem₀, hw, ?_⟩
  let V := 𝒰.pullback₁ f
  have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
    inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
  refine ⟨V.restrictIndexOfSmall.{u}, ?_⟩
  intro j
  let i := Precoverage.ZeroHypercover.Small.restrictFun V j
  obtain ⟨w⟩ := hw i
  exact ⟨n i, m i, _, ⟨w.presentationIso⟩⟩

end AlgebraicGeometry.ProEtale
