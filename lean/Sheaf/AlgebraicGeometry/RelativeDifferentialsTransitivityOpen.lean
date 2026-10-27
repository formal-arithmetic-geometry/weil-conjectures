/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D5
-/
module

public import Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

/-! # RelativeDifferentialsTransitivityOpen

Source: Stacks Project, Morphisms, Tags 01UX, 01UV, 01UT and 01US. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Hom

private theorem differentialsCongr_hom_apply_d {X S : Scheme.{u}}
    (f f' : X ⟶ S) (hf : f = f') (T : X.Opens) (a : Γ(X, T)) :
    (relativeDifferentialsCongr f hf).hom.val.app (op T)
      (f.relativeDifferentialsDerivation.d a) = f'.relativeDifferentialsDerivation.d a := by
  subst f'
  rfl

/-- The canonical differential arrows commute with every source open restriction.
Source: Stacks Project, Morphisms, Tags 01US, 01UV and 01UX.

Proof: write j=O.ι. Compose the tensor pullback adjunction for h with the
restriction adjunction for j. The pushforward-composition isomorphism identifies
the right adjoint with that of tensor pullback for j≫h. Uniqueness of left adjoints
gives e, and its unit identity evaluated on db proves the section normalization.
The universal derivation for j≫h is also relative to j≫(h≫g); its universal property
constructs qO with da↦da. For the second square apply the restriction adjunction
and differential universal-property Hom equivalences. Their naturality reduces
both sides on da to d(j-sharp a), using q(da)=da and qO(da)=da.
For the first square apply the composite tensor/restriction adjunction and the
universal property for g. The left-adjoint comparison identity converts the route
through e into the tensor adjunction for j≫h. Both sides on db are then
 d(j-sharp(h-sharp b)), by the canonical first-arrow formulas and the derivation
restriction formula. Equality induction shows that the associativity congruence
preserves these differentials. Injectivity of the Hom equivalences proves both
squares. This works for empty opens and needs no exactness or finiteness assumption.
(blueprint: lem-a1-differential-transitivity-open). -/
theorem relativeDifferentials_transitivity_open
    {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S)
    (q : (h ≫ g).relativeDifferentials ⟶ h.relativeDifferentials)
    (hq : ∀ (O : X.Opens) (a : Γ(X, O)),
      q.app O ((h ≫ g).relativeDifferentialsDerivation.d (X := op O) a) =
        h.relativeDifferentialsDerivation.d (X := op O) a) :
      (∀ O : X.Opens,
        ∃ (e : ((Modules.tensorPullback h).obj g.relativeDifferentials).restrict O.ι ≅
              (Modules.tensorPullback (O.ι ≫ h)).obj g.relativeDifferentials)
          (qO : (O.ι ≫ (h ≫ g)).relativeDifferentials ⟶ (O.ι ≫ h).relativeDifferentials),
          (∀ (V : Y.Opens) (b : Γ(Y, V)),
            e.hom.app (O.ι ⁻¹ᵁ (h ⁻¹ᵁ V))
              (((Modules.tensorPullback h).obj g.relativeDifferentials).presheaf.map
                (homOfLE (O.ι.image_preimage_le (h ⁻¹ᵁ V))).op
                  (g.relativeDifferentialsPullbackGenerator h V b)) =
              g.relativeDifferentialsPullbackGenerator (O.ι ≫ h) V b) ∧
          (Modules.restrictFunctor O.ι).map (g.relativeDifferentialsPullbackMap h) ≫
              ((h ≫ g).relativeDifferentialsRestrictIso O.ι).hom =
            e.hom ≫ g.relativeDifferentialsPullbackMap (O.ι ≫ h) ≫
              (relativeDifferentialsCongr _ (Category.assoc O.ι h g)).hom ∧
          (Modules.restrictFunctor O.ι).map q ≫
              (h.relativeDifferentialsRestrictIso O.ι).hom =
            ((h ≫ g).relativeDifferentialsRestrictIso O.ι).hom ≫ qO ∧
          (∀ (T : O.toScheme.Opens) (a : Γ(O.toScheme, T)),
            qO.app T ((O.ι ≫ (h ≫ g)).relativeDifferentialsDerivation.d (X := op T) a) =
              (O.ι ≫ h).relativeDifferentialsDerivation.d (X := op T) a)) := by
  intro O
  let j := O.ι
  let M := g.relativeDifferentials
  obtain ⟨adjh, hadjh⟩ := Modules.exists_tensorPullbackAdjunction h
  obtain ⟨adjt, hadjt⟩ := Modules.exists_tensorPullbackAdjunction (j ≫ h)
  let adjr := Modules.restrictAdjunction j
  let adj₁ := adjh.comp adjr
  let adj₂ := adjt.ofNatIsoRight (Modules.pushforwardComp j h).symm
  let k := adj₁.leftAdjointUniq adj₂
  let e := k.app M
  have he : ∀ (V : Y.Opens) (b : Γ(Y, V)),
      e.hom.app (j ⁻¹ᵁ (h ⁻¹ᵁ V))
        (((Modules.tensorPullback h).obj M).presheaf.map
          (homOfLE (j.image_preimage_le (h ⁻¹ᵁ V))).op
            (g.relativeDifferentialsPullbackGenerator h V b)) =
        g.relativeDifferentialsPullbackGenerator (j ≫ h) V b := by
    intro V b
    have hu := adj₁.unit_leftAdjointUniq_hom_app adj₂ M
    have hv := congrArg (fun f ↦ f.app V (g.relativeDifferentialsDerivation.d b)) hu
    simp only [adj₁, adj₂, Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit,
      NatTrans.comp_app, Modules.Hom.comp_app, Modules.pushforward_map_app,
      Functor.comp_map, ConcreteCategory.comp_apply] at hv
    change e.hom.app (j ⁻¹ᵁ (h ⁻¹ᵁ V))
      (((Modules.tensorPullback h).obj M).presheaf.map
        (homOfLE (j.image_preimage_le (h ⁻¹ᵁ V))).op
        ((adjh.unit.app M).val.app (op V) (g.relativeDifferentialsDerivation.d b))) =
      (adjt.unit.app M).val.app (op V) (g.relativeDifferentialsDerivation.d b) at hv
    have hηh : (adjh.unit.app M).val.app (op V)
        (g.relativeDifferentialsDerivation.d b) =
          g.relativeDifferentialsPullbackGenerator h V b := by
      rw [hadjh]
      rfl
    have hηt : (adjt.unit.app M).val.app (op V)
        (g.relativeDifferentialsDerivation.d b) =
          g.relativeDifferentialsPullbackGenerator (j ≫ h) V b := by
      rw [hadjt]
      rfl
    rw [hηh, hηt] at hv
    exact hv
  let D : (j ≫ h).relativeDifferentials.val.Derivation'
      (j ≫ (h ≫ g)).pullbackPresheafToPresheaf :=
    (j ≫ (h ≫ g)).derivationMk
      (j ≫ h).relativeDifferentialsDerivation.d
      (fun {U} a b ↦ (j ≫ h).relativeDifferentialsDerivation.d_mul a b)
      (fun {U V} i x ↦ (j ≫ h).relativeDifferentialsDerivation.d_map i x)
      (by
        intro V a
        change (j ≫ h).relativeDifferentialsDerivation.d
          ((j ≫ h).app (g ⁻¹ᵁ V) (g.app V a)) = 0
        exact (j ≫ h).relativeDifferentialsDerivation.d_app_app (g ⁻¹ᵁ V) (g.app V a))
  let qO := ((j ≫ (h ≫ g)).relativeDifferentialsHomEquiv _).symm D
  have hqO : ∀ (T : O.toScheme.Opens) (a : Γ(O.toScheme, T)),
      qO.app T ((j ≫ (h ≫ g)).relativeDifferentialsDerivation.d (X := op T) a) =
        (j ≫ h).relativeDifferentialsDerivation.d (X := op T) a := by
    intro T a
    exact (j ≫ (h ≫ g)).relativeDifferentialsHomEquiv_symm_app_d D a
  have hsecond : (Modules.restrictFunctor j).map q ≫
      (h.relativeDifferentialsRestrictIso j).hom =
        ((h ≫ g).relativeDifferentialsRestrictIso j).hom ≫ qO := by
    apply (adjr.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    simp only [adjr, relativeDifferentialsRestrictIso, restrictToRelativeDifferentials,
      Equiv.apply_symm_apply]
    apply ((h ≫ g).relativeDifferentialsHomEquiv _).injective
    ext V a
    change (((h.relativeDifferentialsHomEquiv _).symm
      (h.pushforwardDerivation j)).val.app V)
        (q.val.app V ((h ≫ g).relativeDifferentialsDerivation.d a)) =
      qO.val.app (op (j ⁻¹ᵁ V.unop))
        ((((h ≫ g).relativeDifferentialsHomEquiv _).symm
          ((h ≫ g).pushforwardDerivation j)).val.app V
            ((h ≫ g).relativeDifferentialsDerivation.d a))
    have hq' : q.val.app V ((h ≫ g).relativeDifferentialsDerivation.d a) =
        h.relativeDifferentialsDerivation.d a := hq V.unop a
    rw [hq', h.pushforwardDerivation_desc_app_d,
      (h ≫ g).pushforwardDerivation_desc_app_d]
    exact (hqO (j ⁻¹ᵁ V.unop) (j.app V.unop a)).symm
  refine ⟨e, qO, he, ?_, hsecond, hqO⟩
  let c := relativeDifferentialsCongr ((j ≫ h) ≫ g) (Category.assoc j h g)
  let df := ((h ≫ g).relativeDifferentialsHomEquiv _).symm
    ((h ≫ g).pushforwardDerivation j)
  have hk (N : O.toScheme.Modules)
      (v : (Modules.tensorPullback (j ≫ h)).obj M ⟶ N) :
      (adj₁.homEquiv M N) (e.hom ≫ v) = (adj₂.homEquiv M N) v := by
    change (adj₁.homEquiv M N) (k.hom.app M ≫ v) = _
    rw [Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]
  apply (adj₁.homEquiv M _).injective
  rw [hk]
  change (adjh.homEquiv M _) ((adjr.homEquiv _ _)
    ((Modules.restrictFunctor j).map (g.relativeDifferentialsPullbackMap h) ≫
      ((h ≫ g).relativeDifferentialsRestrictIso j).hom)) =
    (adj₂.homEquiv M _) (g.relativeDifferentialsPullbackMap (j ≫ h) ≫ c.hom)
  rw [Adjunction.homEquiv_naturality_left]
  simp only [adjr, relativeDifferentialsRestrictIso, restrictToRelativeDifferentials,
    Equiv.apply_symm_apply]
  change (adjh.homEquiv M _) (g.relativeDifferentialsPullbackMap h ≫ df) =
    (adjt.ofNatIsoRight (Modules.pushforwardComp j h).symm).homEquiv M _
      (g.relativeDifferentialsPullbackMap (j ≫ h) ≫ c.hom)
  rw [Adjunction.homEquiv_ofNatIsoRight_apply]
  apply (g.relativeDifferentialsHomEquiv _).injective
  ext V b
  rw [relativeDifferentialsHomEquiv_apply, relativeDifferentialsHomEquiv_apply]
  simp only [PresheafOfModules.Derivation.postcomp_d_apply]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change df.val.app (op (h ⁻¹ᵁ V.unop))
      ((g.relativeDifferentialsPullbackMap h).val.app (op (h ⁻¹ᵁ V.unop))
        ((adjh.unit.app M).val.app V (g.relativeDifferentialsDerivation.d b))) =
    c.hom.val.app (op (j ⁻¹ᵁ (h ⁻¹ᵁ V.unop)))
      ((g.relativeDifferentialsPullbackMap (j ≫ h)).val.app
        (op ((j ≫ h) ⁻¹ᵁ V.unop))
          ((adjt.unit.app M).val.app V (g.relativeDifferentialsDerivation.d b)))
  have hηh : (adjh.unit.app M).val.app V (g.relativeDifferentialsDerivation.d b) =
      g.relativeDifferentialsPullbackGenerator h V.unop b := by
    rw [hadjh]
    rfl
  have hηt : (adjt.unit.app M).val.app V (g.relativeDifferentialsDerivation.d b) =
      g.relativeDifferentialsPullbackGenerator (j ≫ h) V.unop b := by
    rw [hadjt]
    rfl
  rw [hηh, hηt]
  have hdh : (g.relativeDifferentialsPullbackMap h).val.app (op (h ⁻¹ᵁ V.unop))
      (g.relativeDifferentialsPullbackGenerator h V.unop b) =
        (h ≫ g).relativeDifferentialsDerivation.d (h.app V.unop b) :=
    (Classical.choose_spec (existsUnique_relativeDifferentialsPullbackMap g h)).1 V.unop b
  have hdt : (g.relativeDifferentialsPullbackMap (j ≫ h)).val.app
      (op ((j ≫ h) ⁻¹ᵁ V.unop))
        (g.relativeDifferentialsPullbackGenerator (j ≫ h) V.unop b) =
          ((j ≫ h) ≫ g).relativeDifferentialsDerivation.d ((j ≫ h).app V.unop b) :=
    (Classical.choose_spec (existsUnique_relativeDifferentialsPullbackMap g (j ≫ h))).1
      V.unop b
  rw [hdh, hdt]
  exact ((h ≫ g).pushforwardDerivation_desc_app_d j
    (h ⁻¹ᵁ V.unop) (h.app V.unop b)).trans
      (differentialsCongr_hom_apply_d _ _ (Category.assoc j h g)
        ((j ≫ h) ⁻¹ᵁ V.unop) ((j ≫ h).app V.unop b)).symm

end AlgebraicGeometry.Scheme.Hom
