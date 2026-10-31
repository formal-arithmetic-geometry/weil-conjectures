/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeCoverDescentDatum
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Limits
import WeilConjectures.AlgebraicGeometry.FppfFamilyCoproductDescentEncoding
import WeilConjectures.AlgebraicGeometry.FppfAffineRefinementPullbackModel
import WeilConjectures.AlgebraicGeometry.FppfSheafRepresentabilityDescentData
import WeilConjectures.CategoryTheory.SetSheafCoverDescent
import WeilConjectures.AlgebraicGeometry.FpqcRefinementReflectsEffectivity
import WeilConjectures.AlgebraicGeometry.FpqcEffectivityOpenLocal

/-!
# Reduction of effective fppf descent to affine singleton covers

Source: Stacks Project, Descent, Tag 02W3, `lemma-descending-types-morphisms`,
specialized to fppf coverings (blueprint: lem-trf-fppf-family-affine-effectivity-reduction).
-/

@[expose] public section

set_option autoImplicit false

universe u v w v' w'

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

-- Keep restriction independent of the large concrete sheaf pseudofunctor.
private def restrictData
    {C : Type w} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', w'}}
    {I J : Type (u + 1)} {T : C} {U : I → C} {f : ∀ i, U i ⟶ T}
    (D : F.DescentData f) (j : J → I) : F.DescentData (fun t ↦ f (j t)) where
  obj t := D.obj (j t)
  hom {_} q {_ _} a b ha hb := D.hom q a b ha hb
  pullHom_hom {_ _} g q q' hq {_ _} a b ha hb ga gb hga hgb :=
    D.pullHom_hom g q q' hq a b ha hb ga gb hga hgb
  hom_self {_} q {_} a ha := D.hom_self q a ha
  hom_comp {_} q {_ _ _} a b c ha hb hc := D.hom_comp q a b c ha hb hc

private def restrictIso
    {C : Type w} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', w'}}
    {I J : Type (u + 1)} {T : C} {U : I → C} {f : ∀ i, U i ⟶ T}
    {D E : F.DescentData f}
    (e : D ≅ E) (j : J → I) : restrictData D j ≅ restrictData E j where
  hom := {
    hom := fun t ↦ e.hom.hom (j t)
    comm := fun {_} q {_ _} a b ha hb ↦ e.hom.comm q a b ha hb }
  inv := {
    hom := fun t ↦ e.inv.hom (j t)
    comm := fun {_} q {_ _} a b ha hb ↦ e.inv.comm q a b ha hb }
  hom_inv_id := Pseudofunctor.DescentData.hom_ext (fun t ↦
    congrArg (fun k ↦ k.hom (j t)) e.hom_inv_id)
  inv_hom_id := Pseudofunctor.DescentData.hom_ext (fun t ↦
    congrArg (fun k ↦ k.hom (j t)) e.inv_hom_id)

private theorem restrictData_ofObj
    {C : Type w} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', w'})
    {I J : Type (u + 1)} {T : C} {U : I → C} (f : ∀ i, U i ⟶ T)
    (M : F.obj (.mk (op T))) (j : J → I) :
    restrictData ((F.toDescentData f).obj M) j =
      (F.toDescentData (fun t ↦ f (j t))).obj M := rfl

/-- The coproduct argument for families whose two coproducts exist in `Scheme.{u}`.
Source: Stacks Project, Descent, Tags 023X and 02W3. -/
private theorem isEffective_of_hasCoproducts
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] [P.IsStableUnderBaseChange]
    (hfinite : ∀ (n : ℕ) (Y B : Fin n → Scheme.{u}) (h : ∀ j, Y j ⟶ B j),
      (∀ j, P (h j)) → P (CategoryTheory.Limits.Sigma.map h))
    (haffine : ∀ (A B : Scheme.{u}) [IsAffine A] [IsAffine B] (p : A ⟶ B),
      Flat p → Surjective p → LocallyOfFinitePresentation p → QuasiCompact p →
        QuasiSeparated p → ∀ (V : Over A) (D : Over.DescentDatum p V),
          P V.hom → D.IsEffective)
    {I : Type (u + 1)} (T : Scheme.{u}) (U : I → Scheme.{u}) (f : ∀ i, U i ⟶ T)
    (hcov : Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T)
    (D : SchemeCoverDescentDatum f) (hP : ∀ i, P (D.localScheme i).hom)
    [HasCoproduct U] [HasCoproduct (fun i ↦ (D.localScheme i).left)] :
    D.IsEffective := by
  -- Encode the family without requiring P on its infinite coproduct.
  obtain ⟨_, _, _, _, _, _, _, E, _, htrans, hfpqc, _, heff⟩ :=
    fppf_family_coproduct_descent_encoding T U f hcov D
  apply heff.mpr
  apply fpqc_isEffective_of_affine_open_restrictions (Sigma.desc f) hfpqc E
  intro B
  obtain ⟨EB, hEB, m, idx, W, _, _, _, p, _, hpaff, hpflat, hpsurj, hplfp,
      hpqc, hpqs, hpcov, h, hh, _, F, hF, e, he⟩ :=
    exists_fppf_affine_refinement_pullback_model f hcov D
      (Sigma.ι U) (Sigma.ι (fun i ↦ (D.localScheme i).left))
      (coproductIsCoproduct U) (coproductIsCoproduct _)
      (Sigma.desc f) D.coproductScheme.hom
      (fun i ↦ Sigma.ι_desc f i) (fun i ↦ Sigma.ι_map (fun i ↦ (D.localScheme i).hom) i) E
      (by
        intro H pH i k r s hr hs x y ht hy
        have hy' : y = D.coproductPoint i r x := by
          apply Over.OverMorphism.ext
          exact hy
        subst y
        exact htrans H pH i k r s hr hs x)
      B.1 B.2 (pullback.fst _ _) (pullback.snd _ _)
      (IsPullback.of_hasPullback _ _) (pullback.fst _ _) (pullback.snd _ _)
      (IsPullback.of_hasPullback _ _)
  -- The finite affine model has P componentwise, then on its coproduct.
  have hPB : P (pullback.snd
      (pullback.snd D.coproductScheme.hom (pullback.fst (Sigma.desc f) B.1.ι)) h) := by
    rw [← he]
    apply (P.cancel_left_of_respectsIso e.hom _).mpr
    have hs := hfinite m
      (fun j ↦ pullback (D.localScheme (idx j)).hom
        ((W j).ι ≫ pullback.fst (f (idx j)) B.1.ι))
      (fun j ↦ (W j).toScheme)
      (fun j ↦ pullback.snd (D.localScheme (idx j)).hom
        ((W j).ι ≫ pullback.fst (f (idx j)) B.1.ι))
      (fun j ↦ P.pullback_snd _ _ (hP (idx j)))
    exact hs
  have : IsAffine B.1.toScheme := B.2
  have : IsAffine (∐ fun j ↦ (W j).toScheme) := hpaff
  have hFeff := haffine _ _ p hpflat hpsurj hplfp hpqc hpqs _ F hPB
  have hBcov : Presieve.singleton (pullback.snd (Sigma.desc f) B.1.ι) ∈
      Scheme.fpqcPrecoverage B.1.toScheme := by
    rw [← Presieve.ofArrows_pUnit.{0}] at hfpqc ⊢
    exact Precoverage.mem_coverings_of_isPullback
      (fun _ : PUnit ↦ Sigma.desc f) hfpqc B.1.ι
      (fun _ ↦ pullback.snd _ _) (fun _ ↦ pullback.fst _ _)
      (fun _ ↦ (IsPullback.of_hasPullback _ _).flip)
  refine ⟨EB, ?_, ?_⟩
  · exact fpqc_refinement_reflects_effectivity _ p h hBcov hpcov hh
      (pullback.fst _ _) (pullback.condition (f := _) (g := h)) EB F
      (IsPullback.of_hasPullback _ _) hF hFeff
  · intro H a b hab x
    symm
    apply hEB H a b hab x _ _ rfl

/-- Effective descent for a base-change-stable morphism property reduces to affine singleton
covers. Source: Stacks Project, Descent, Tag 02W3, invoked in Tag 02W8
(blueprint: lem-trf-fppf-family-affine-effectivity-reduction).

Proof: Choose one covering member above each point of the base, giving a small
covering subfamily. Restrict the datum and property to it. Encode this small family
by a singleton datum on the coproduct. On each affine base open, the finite affine
refinement pullback model identifies the refined map with the finite coproduct of
base changes of the original maps. Base-change stability, finite-coproduct stability
(including zero components) and isomorphism invariance give P for this map. The affine
singleton hypothesis gives effectivity, fpqc refinement reflects it, and affine-open
locality gives effectivity of the small family. Finally identify the global sheaves
attached to the original and small data: their restrictions to the small subcover
are isomorphic with all transitions, so full faithfulness of sheaf descent gives an
isomorphism globally. Representability of the small datum's sheaf, hence effectivity,
transfers to the original datum. No property of the infinite coproduct map or of the
final descended map is asserted. -/
theorem fppf_family_isEffective_of_affine_singletons
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] [P.IsStableUnderBaseChange]
    (hfinite : ∀ (n : ℕ) (Y B : Fin n → Scheme.{u}) (h : ∀ j, Y j ⟶ B j),
      (∀ j, P (h j)) → P (CategoryTheory.Limits.Sigma.map h))
    (haffine : ∀ (A B : Scheme.{u}) [IsAffine A] [IsAffine B] (p : A ⟶ B),
      Flat p → Surjective p → LocallyOfFinitePresentation p → QuasiCompact p →
        QuasiSeparated p → ∀ (V : Over A) (D : Over.DescentDatum p V),
          P V.hom → D.IsEffective)
    {I : Type (u + 1)} (T : Scheme.{u}) (U : I → Scheme.{u}) (f : ∀ i, U i ⟶ T)
    (hcov : Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T)
    (D : SchemeCoverDescentDatum f) (hP : ∀ i, P (D.localScheme i).hom) :
    D.IsEffective := by
  classical
  obtain ⟨hcover, hmaps⟩ := (Scheme.ofArrows_mem_precoverage_iff
    (P := @Flat ⊓ @LocallyOfFinitePresentation)).mp hcov
  -- One chosen member per point keeps both coproducts in the scheme universe.
  choose idx pt hpt using hcover
  let J := ULift.{u + 1} T
  let j : J → I := fun t ↦ idx t.down
  let U' : J → Scheme.{u} := fun t ↦ U (j t)
  let f' : ∀ t, U' t ⟶ T := fun t ↦ f (j t)
  have hcov' : Presieve.ofArrows U' f' ∈ Scheme.fppfPrecoverage T := by
    apply (Scheme.ofArrows_mem_precoverage_iff
      (P := @Flat ⊓ @LocallyOfFinitePresentation)).mpr
    exact ⟨fun t ↦ ⟨⟨t⟩, pt t, hpt t⟩, fun t ↦ hmaps (j t)⟩
  let D' : SchemeCoverDescentDatum f' := {
    data := restrictData D.data j
    localScheme := fun t ↦ D.localScheme (j t)
    representation := fun t ↦ D.representation (j t) }
  have hD' : D'.IsEffective :=
    isEffective_of_hasCoproducts P hfinite haffine T U' f' hcov' D'
      (fun t ↦ hP (j t))
  -- The two global sheaves agree on the small subcover, with their transitions.
  obtain ⟨e, ⟨ei⟩, _, ee⟩ := fppfSheafRepresentabilityDescentData T U f hcov
  obtain ⟨e', ⟨ei'⟩, _, ee'⟩ := fppfSheafRepresentabilityDescentData T U' f' hcov'
  let H : Sheaf (Scheme.fppfTopology.over T) (Type (u + 1)) := (e.functor.obj D).obj
  let H' : Sheaf (Scheme.fppfTopology.over T) (Type (u + 1)) := (e'.functor.obj D').obj
  let R := (Scheme.fppfTopology.pseudofunctorOver (Type (u + 1))).toDescentData f'
  let ed := ei.app D
  let di := restrictIso
    (F := Scheme.fppfTopology.pseudofunctorOver (Type (u + 1)))
    (D := ((e.functor ⋙ (IsLocallyRepresentableFppfSheaf f).ι ⋙
      (Scheme.fppfTopology.pseudofunctorOver (Type (u + 1))).toDescentData f).obj D))
    (E := (schemeCoverDescentForget f).obj D) ed j
  have di' : @Iso
      ((Scheme.fppfTopology.pseudofunctorOver (Type (u + 1))).DescentData f')
      Pseudofunctor.DescentData.instCategory (R.obj H) D'.data := by
    have d := di
    dsimp only [Functor.comp_obj, ObjectProperty.ι_obj, schemeCoverDescentForget,
      inducedFunctor_obj] at d
    rw [restrictData_ofObj] at d
    exact d
  have dj : @Iso
      ((Scheme.fppfTopology.pseudofunctorOver (Type (u + 1))).DescentData f')
      Pseudofunctor.DescentData.instCategory (R.obj H') D'.data := by
    have d := ei'.app D'
    dsimp only [Functor.comp_obj, ObjectProperty.ι_obj, schemeCoverDescentForget,
      inducedFunctor_obj] at d
    exact d
  have ff : R.FullyFaithful := (setSheafCoverDescent Scheme.fppfTopology T U' f'
    (Precoverage.generate_mem_toGrothendieck hcov')).2.some
  let hi : H' ≅ H := ff.preimageIso (X := H') (Y := H) (dj ≪≫ di'.symm)
  have : H'.obj.IsRepresentable := (ee' D').mpr hD'
  have : H.obj.IsRepresentable :=
    isRepresentable_of_natIso H'.obj
      ((sheafToPresheaf (Scheme.fppfTopology.over T) (Type (u + 1))).mapIso hi)
  exact (ee D).mp inferInstance

end AlgebraicGeometry
