/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.CartesianCoefficientTwistsSupplement
import all WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransportSupplement

/-! # Normalized ordinary coefficient and module comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The section-ring inverse-image identification fixed by the published coefficient adjunct.

Source: blueprint det-prop-scalar-six-pullback.proof.md, (1), module and coefficient
identifications; Stacks, Modules on Sites, Tags 03D6 and 03D7.
(blueprint: lem-sfb-scalar-six-geometry).

Proof: apply the section-ring construction to the commutative internal ring object
`condensedRingObj`. The monoidal coefficient adjunct `condensedPushforwardHom` induces
a morphism of section-ring sheaves: its map on a section is the given additive map,
and monoidality gives preservation of one and multiplication. Transpose this morphism
under the ring-sheaf inverse-image adjunction. Its underlying inverse-image comparison
is the published `condensedPullbackHom`, which is invertible by `isIso_condensedPullbackHom`.
The forgetful functor from ring sheaves reflects isomorphisms, so the transposed ring
map is an isomorphism. Its adjunct has the required section formula by the adjunction
triangle identities. Finally the section formula determines the adjunct, adjunction
transposition determines the hom, and an isomorphism is determined by its hom. -/
private theorem scalarSixCoefficientIso_existsUnique (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (scalarSixSectionRing Λ Y) ≅ scalarSixSectionRing Λ X,
      ∀ (V : Y.ProEtᵒᵖ) (r : (scalarSixSectionRing Λ Y).obj.obj V),
        ((proEtaleRingDirectImageMap f (scalarSixSectionRing Λ Y)
          (scalarSixSectionRing Λ X) c).hom.app V).hom r =
            ((condensedPushforwardHom Λ.X f).hom.app V).hom r := by
  obtain ⟨c, hc, hu⟩ := spCoefficientIso_existsUnique f Λ.X
  refine ⟨c, ?_, ?_⟩
  · intro V r
    simpa only [Adjunction.homEquiv_unit, proEtaleRingDirectImageMap,
      scalarSixSectionRing, ModuleRingedComparison.ring, CommRingCat.Hom.hom,
      AddCommGrpCat.Hom.hom] using hc V r
  · intro d hd
    apply hu d
    intro V r
    simpa only [Adjunction.homEquiv_unit, proEtaleRingDirectImageMap,
      scalarSixSectionRing, ModuleRingedComparison.ring, CommRingCat.Hom.hom,
      AddCommGrpCat.Hom.hom] using hd V r



private theorem scalarSixComparison_existsUnique
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (E : A ≌ C) (H : B ≌ D) {L : A ⥤ B} {R : B ⥤ A}
    {L' : C ⥤ D} {R' : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R')
    (r : R ⋙ E.functor ≅ H.functor ⋙ R') :
    ∃! c : L ⋙ H.functor ≅ E.functor ⋙ L',
      (mateEquiv a b (.mk _ _ _ _ c.inv)).natTrans = r.hom := by
  let β : TwoSquare R H.functor E.functor R' := .mk _ _ _ _ r.hom
  let α := (mateEquiv a b).symm β
  have hγ : IsIso (mateEquiv H.toAdjunction E.toAdjunction β).natTrans := by
    simp only [mateEquiv_apply]
    infer_instance
  have hα : IsIso α.natTrans := by
    have h := iterated_mateEquiv_conjugateEquiv a b E.toAdjunction H.toAdjunction α
    have : IsIso (conjugateEquiv (a.comp H.toAdjunction)
        (E.toAdjunction.comp b) α.natTrans) := by
      rw [← h]
      simpa only [α, Equiv.apply_symm_apply] using hγ
    exact conjugateEquiv_of_iso (a.comp H.toAdjunction)
      (E.toAdjunction.comp b) α.natTrans
  refine ⟨(asIso α.natTrans).symm, ?_, ?_⟩
  · exact congrArg TwoSquare.natTrans ((mateEquiv a b).apply_symm_apply β)
  · intro c hc
    apply Iso.ext_inv
    change c.inv = α.natTrans
    have h : mateEquiv a b (.mk _ _ _ _ c.inv) = β := by
      ext M
      exact congr_app hc M
    exact congrArg TwoSquare.natTrans ((mateEquiv a b).eq_symm_apply.mpr h)

private theorem scalarSixPush_existsUnique (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (scalarSixSectionRing Λ Y) ≅ scalarSixSectionRing Λ X)
    (hc : ∀ (V : Y.ProEtᵒᵖ) (r : (scalarSixSectionRing Λ Y).obj.obj V),
      ((proEtaleRingDirectImageMap f (scalarSixSectionRing Λ Y)
        (scalarSixSectionRing Λ X) c).hom.app V).hom r =
          ((condensedPushforwardHom Λ.X f).hom.app V).hom r) :
    ∃! e : lowerStar Λ.X f ⋙ (ModuleRingedComparison.equivalence Λ.X Y).functor ≅
        (ModuleRingedComparison.equivalence Λ.X X).functor ⋙
          proEtaleRingModuleDirectImage f (scalarSixSectionRing Λ Y)
            (scalarSixSectionRing Λ X) c,
      ∀ (M : ModuleRingedComparison.internalModules Λ.X X) (V : Y.ProEtᵒᵖ)
        (m : ((lowerStar Λ.X f).obj M).X.obj.obj V),
        ((e.hom.app M).val.app V) m = m := by
  classical
  let L := lowerStar Λ.X f ⋙ (ModuleRingedComparison.equivalence Λ.X Y).functor
  let R := (ModuleRingedComparison.equivalence Λ.X X).functor ⋙
    proEtaleRingModuleDirectImage f (scalarSixSectionRing Λ Y)
      (scalarSixSectionRing Λ X) c
  have h (M : ModuleRingedComparison.internalModules Λ.X X) (V : Y.ProEtᵒᵖ)
      (r : (scalarSixSectionRing Λ Y).obj.obj V) (m : (R.obj M).val.obj V) :
      ((ModuleCat.smul ((L.obj M).val.obj V) r).hom) m =
        ((ModuleCat.smul ((R.obj M).val.obj V) r).hom) m := by
    change ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ.X Y)
      (((InternalModuleOperations.siteMap f).sheafPushforwardContinuous Ab.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj M.X)).app V ≫
      (condensedPushforwardHom Λ.X f ▷ _ ≫ Functor.LaxMonoidal.μ
        ((InternalModuleOperations.siteMap f).sheafPushforwardContinuous Ab.{u + 1}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X))
        (condensedRingObj Λ.X X) M.X ≫
          ((InternalModuleOperations.siteMap f).sheafPushforwardContinuous Ab.{u + 1}
            (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).map
              (Mod.act M.X)).hom.app V).hom (r ⊗ₜ[ℤ] m) = _
    rw [InternalModuleOperations.section_action]
    change ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X) M.X).app ((InternalModuleOperations.siteMap f).op.obj V) ≫
      (Mod.act M.X).hom.app ((InternalModuleOperations.siteMap f).op.obj V)).hom
        (((condensedPushforwardHom Λ.X f).hom.app V).hom r ⊗ₜ[ℤ] m) =
      ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ.X X) M.X).app ((InternalModuleOperations.siteMap f).op.obj V) ≫
        (Mod.act M.X).hom.app ((InternalModuleOperations.siteMap f).op.obj V)).hom
          (((proEtaleRingDirectImageMap f (scalarSixSectionRing Λ Y)
            (scalarSixSectionRing Λ X) c).hom.app V).hom r ⊗ₜ[ℤ] m)
    rw [hc V r]
  let q (M) : L.obj M ⟶ R.obj M :=
    ⟨PresheafOfModules.homMk (M₁ := (L.obj M).val) (M₂ := (R.obj M).val)
      (𝟙 _) (fun V r m ↦ h M V r m)⟩
  let p (M) : R.obj M ⟶ L.obj M :=
    ⟨PresheafOfModules.homMk (M₁ := (R.obj M).val) (M₂ := (L.obj M).val)
      (𝟙 _) (fun V r m ↦ (h M V r m).symm)⟩
  let e : L ≅ R := NatIso.ofComponents
    (fun M ↦ { hom := q M, inv := p M,
               hom_inv_id := by ext V m; rfl,
               inv_hom_id := by ext V m; rfl })
    (fun α ↦ by ext V m; rfl)
  refine ⟨e, ?_, ?_⟩
  · intro M V m
    rfl
  · intro d hd
    apply Iso.ext
    ext M V m
    exact hd M V m

/-- The ordinary internal/sectionwise comparison with the coefficient and mate normalizations.

Source: blueprint det-prop-scalar-six-pullback.proof.md, (1), module and coefficient
identifications; Stacks Tags 03D6, 03D7 and 0B65.
(blueprint: lem-sfb-scalar-six-geometry).

Proof: choose the uniquely section-normalized ring isomorphism. Its adjunct is the
section-ring map of the operations-transport theorem, since both have the same value
on every section. The direct-image functors are therefore equal to the transported
ones; take the unique identity-on-sections comparison. Conjugate the pullback
adjunctions by the fixed module equivalences. Uniqueness of left adjoints gives the
pullback comparison, and its defining unit equation gives the required mate equation. -/
theorem scalarSixGeometry_exists : Nonempty ScalarSixGeometry.{u} := by
  classical
  let c (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
    (scalarSixCoefficientIso_existsUnique Λ f).exists.choose
  have hc (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
    (scalarSixCoefficientIso_existsUnique Λ f).exists.choose_spec
  let p (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
    (scalarSixPush_existsUnique Λ f (c Λ f) (hc Λ f)).exists.choose
  have hp (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
    (scalarSixPush_existsUnique Λ f (c Λ f) (hc Λ f)).exists.choose_spec
  have hq (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
    scalarSixComparison_existsUnique
      (ModuleRingedComparison.equivalence Λ.X Y)
      (ModuleRingedComparison.equivalence Λ.X X)
      (upperStarLowerStarAdjunction Λ.X f)
      (proEtaleRingModuleAdjunction f (scalarSixSectionRing Λ Y)
        (scalarSixSectionRing Λ X) (c Λ f)) (p Λ f)
  exact ⟨{
    coefficient := c
    coefficientNormalization := hc
    push := p
    pushNormalization := hp
    pull := fun Λ _ _ f ↦ (hq Λ f).exists.choose
    pullNormalization := fun Λ _ _ f ↦ (hq Λ f).exists.choose_spec }⟩

end AlgebraicGeometry.ProEtale.CondensedRing
