/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryInertia
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation

/-!
# Lisse Weil sheaves with trivial inertia at a boundary point

Let `j : U₀ ⟶ C₀` be a nonempty open of a smooth geometrically connected curve over a finite
field, `U₀` geometrically connected, and `z ∈ C₀ ∖ U₀` a boundary point with inertia group
`I_z ⊆ W(U₀)` (`AlgebraicGeometry.WeilGroup.boundaryInertia`). A lisse representation of `W(U₀)`
which is trivial on `I_z` is trivial on the whole kernel of `π₁(U₀) → π₁(U₀ ∪ {z})`, intersected
with the Weil group (`AlgebraicGeometry.WeilGroup.apply_eq_self_of_mem_weilLocalKernel`): its
kernel on the geometric part is closed and normal, so its image in `π₁(U₀)` is a closed normal
subgroup (by the density of the Weil group) containing the inertia group, hence the closed normal
subgroup it generates, which is the local kernel
(`AlgebraicGeometry.WeilGroup.localKernel_le_topologicalClosure_normalClosure`).
-/

@[expose] public section

universe u

open CategoryTheory PreGaloisCategory

namespace AlgebraicGeometry.WeilGroup

open Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  [GeometricallyConnected p] [ConnectedSpace C] [Smooth p] {pU : U ⟶ Spec (.of K)} [IsCurve pU]
  [GeometricallyConnected pU] [ConnectedSpace U] (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U]
  [IsIntegral C] [SmoothOfRelativeDimension 1 p] (hj : j ≫ p = pU)
  (sU : Spec (.of (AlgebraicClosure K)) ⟶ U)
  (GU : Type u) [Group GU] [TopologicalSpace GU] [IsTopologicalGroup GU] [CompactSpace GU]
  [∀ P, MulAction GU ((fiber sU).obj P)] [IsFundamentalGroup (fiber sU) GU]
  {sC : Spec (.of (AlgebraicClosure K)) ⟶ C} (τ : fiber (sU ≫ j) ≅ fiber sC)
  (GC : Type u) [Group GC] [TopologicalSpace GC] [IsTopologicalGroup GC] [CompactSpace GC]
  [∀ P, MulAction GC ((fiber sC).obj P)] [IsFundamentalGroup (fiber sC) GC]
  (l : ℕ) [Fact l.Prime] {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
  [FiniteDimensional (PadicAlgCl l) V]

include hj τ GC in
/-- **A lisse representation trivial on inertia is trivial on the local kernel.** Let `ρ` be a
lisse representation of `W(U₀)` on which the inertia group `I_z` at a boundary point `z` acts
trivially. Then every element of `W(U₀)` of degree zero acting trivially on the covers of `U₀`
which extend over `z` (`AlgebraicGeometry.WeilGroup.weilLocalKernel`) acts trivially through `ρ`.

The elements of the geometric part acting trivially form a closed normal subgroup `N` of
`W(U₀)`, since `ρ` is continuous on the geometric part. Its image in `π₁(U₀)` is compact, hence
closed, and normal since the Weil group is dense; it contains the inertia group, hence the local
kernel (`AlgebraicGeometry.WeilGroup.localKernel_le_topologicalClosure_normalClosure`).
(blueprint: `cor-wf-unramified-boundary-purity`) -/
theorem apply_eq_self_of_mem_weilLocalKernel
    {ρ : Representation (PadicAlgCl l) (weilGroup pU sU GU) V}
    (hρ : (ofFundamentalGroup pU sU GU).IsLisse l ρ) (z : ↥((Set.range j.base)ᶜ))
    (hI : ∀ g ∈ boundaryInertia (p := p) (pU := pU) j sU GU z, ∀ v, ρ g v = v)
    {w : weilGroup pU sU GU} (hw : w ∈ weilLocalKernel (p := p) (pU := pU) j sU GU z.1)
    (v : V) : ρ w v = v := by
  have hcU : ∀ P, ContinuousSMul GU ((fiber sU).obj P) := fun P ↦
    IsFundamentalGroup.continuous_smul P
  have : T2Space GU := (toAutHomeo (fiber sU) GU).isEmbedding.t2Space
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace pU
  have : QuasiSeparatedSpace U := quasiSeparatedSpace_of_quasiSeparated pU
  let φ : weilGroup pU sU GU →* GU := (MonoidHom.fst _ _).comp (weilGroup pU sU GU).subtype
  -- the elements of the geometric part acting trivially
  let N : Subgroup (weilGroup pU sU GU) := ρ.asGroupHom.ker ⊓ (weilGroupDeg pU sU GU).ker
  have hNmem (g : weilGroup pU sU GU) :
      g ∈ N ↔ (∀ v, ρ g v = v) ∧ g ∈ (weilGroupDeg pU sU GU).ker := by
    refine and_congr_left' ⟨fun h v ↦ ?_, fun h ↦ MonoidHom.mem_ker.2 (Units.ext ?_)⟩
    · have h' := congrArg (fun u : (Module.End (PadicAlgCl l) V)ˣ ↦ u.1 v)
        (MonoidHom.mem_ker.1 h)
      simpa [Representation.asGroupHom_apply] using h'
    · rw [Representation.asGroupHom_apply]
      exact LinearMap.ext h
  -- `N` is the image of a closed subset of the compact geometric part
  have hK : CompactSpace (weilGroupDeg pU sU GU).ker :=
    isCompact_iff_compactSpace.mp (isCompact_ker_weilGroupDeg pU sU GU)
  let b := Module.finBasis (PadicAlgCl l) V
  let T : Set (weilGroupDeg pU sU GU).ker := {g | ∀ i i', LinearMap.toMatrix b b (ρ g) i i' =
    LinearMap.toMatrix b b 1 i i'}
  have hT : IsClosed T := by
    simp only [T, Set.ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_iInter fun i' ↦
      isClosed_eq (hρ.continuous_toMatrix b i i') continuous_const
  have hNT : (N : Set (weilGroup pU sU GU)) = Subtype.val '' T := by
    ext g
    refine ⟨fun hg ↦ ⟨⟨g, ((hNmem g).1 hg).2⟩, fun i i' ↦ ?_, rfl⟩, ?_⟩
    · have h1 : ρ g = 1 := LinearMap.ext fun v ↦
        (((hNmem g).1 hg).1 v).trans (Module.End.one_apply v).symm
      change LinearMap.toMatrix b b (ρ g) i i' = _
      rw [h1]
    · rintro ⟨g, hg, rfl⟩
      refine (hNmem g).2 ⟨fun v ↦ ?_, g.2⟩
      have h : ρ g = 1 := (LinearMap.toMatrix b b).injective (Matrix.ext hg)
      rw [h, Module.End.one_apply]
  -- its image `H` in `π₁(U₀)` is closed
  let H : Subgroup GU := N.map φ
  have hHc : IsClosed (H : Set GU) := by
    rw [Subgroup.coe_map, hNT, Set.image_image]
    exact (hT.isCompact.image ((continuous_fst.comp continuous_subtype_val).comp
      continuous_subtype_val)).isClosed
  -- it is normal, being normalised by the dense Weil group
  have hHn : H.Normal := by
    let S : Subgroup GU :=
      { carrier := {g | ∀ h ∈ H, g * h * g⁻¹ ∈ H ∧ g⁻¹ * h * g ∈ H}
        mul_mem' := fun {a b} ha hb h hh ↦
          ⟨by simpa [mul_assoc] using (ha _ (hb h hh).1).1,
            by simpa [mul_assoc] using (hb _ (ha h hh).2).2⟩
        one_mem' := fun h hh ↦ by simpa using hh
        inv_mem' := fun {a} ha h hh ↦ by simpa using (ha h hh).symm }
    have hSc : IsClosed (S : Set GU) := by
      have : (S : Set GU) =
          ⋂ h ∈ (H : Set GU), ({g | g * h * g⁻¹ ∈ H} ∩ {g | g⁻¹ * h * g ∈ H}) := by
        ext g
        simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_ofPred_eq]
        exact Iff.rfl
      rw [this]
      exact isClosed_biInter fun h _ ↦
        (hHc.preimage (by fun_prop)).inter (hHc.preimage (by fun_prop))
    have hN : N.Normal := inferInstance
    have hSW : ∀ w ∈ weilGroup pU sU GU, w.1 ∈ S := by
      intro w hw h hh
      obtain ⟨v, hv, rfl⟩ := hh
      exact ⟨⟨_, hN.conj_mem v hv ⟨w, hw⟩, rfl⟩, ⟨_, hN.conj_mem v hv ⟨w, hw⟩⁻¹, by simp [φ]⟩⟩
    have hS := eq_top_of_forall_mem_weilGroup pU GU S hSc hSW
    exact ⟨fun h hh g ↦ ((hS ▸ Subgroup.mem_top g : g ∈ S) h hh).1⟩
  -- it contains the inertia group, hence the local kernel
  have : Finite (C.residueField z.1) := boundary_subset_finitePoints (p := p) j z.2
  have hIH : (inertiaGroup sU GU (boundaryChart (p := p) j z)
      (boundaryChart (p := p) j z).point : Set GU) ⊆ H := by
    intro k hk
    have hkL := inertiaGroup_le_localKernel (p := p) sU GU _ _ hk
    have hkW : (k, (1 : Multiplicative ℤ)) ∈ weilGroup pU sU GU := by
      rw [mem_weilGroup_fundamentalGroupMap_iff j hj sU τ GU GC,
        MonoidHom.mem_ker.1 (localKernel_le_ker_restrictionMap j τ GU GC z.1 hkL)]
      exact (weilGroup p sC GC).one_mem
    refine ⟨⟨_, hkW⟩, (hNmem _).2 ⟨hI _ ⟨hk, rfl⟩, rfl⟩, rfl⟩
  have hle : localKernel (p := p) j sU GU z.1 ≤ H :=
    (localKernel_le_topologicalClosure_normalClosure (p := p) sU GU
      (boundaryChart (p := p) j z) z.2 _).trans
      (Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal hIH) hHc)
  obtain ⟨hg, hdeg⟩ := hw
  obtain ⟨w', hw'N, hw'⟩ := hle hg
  obtain rfl : w' = w := Subtype.ext (Prod.ext hw' (((hNmem w').1 hw'N).2.trans hdeg.symm))
  exact ((hNmem w').1 hw'N).1 v

omit [Finite K] [IsCurve p] [GeometricallyConnected p] [ConnectedSpace C] [Smooth p]
  [IsOpenImmersion j] [Nonempty U] [IsIntegral C] [SmoothOfRelativeDimension 1 p] in
/-- An automorphism `σ` of a fibre functor acting trivially on the geometric fibres of all base
changes along `f` acts trivially on the geometric fibre of every object isomorphic to one. -/
lemma _root_.AlgebraicGeometry.Scheme.FiniteEtale.app_apply_eq_of_pullbackPathIso_eq_refl
    {X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (f : X ⟶ Y)
    {y : Spec (.of Ω) ⟶ X} {σ : Aut (fiber y)} (hσ : pullbackPathIso f σ = Iso.refl _)
    {Q : X.FiniteEtale} {P : Y.FiniteEtale} (i : Q ≅ (pullback f).obj P) (a : (fiber y).obj Q) :
    σ.hom.app Q a = a := by
  have h₁ : σ.hom.app ((pullback f).obj P) = 𝟙 _ := by
    have h := congrArg (fun τ : fiber (y ≫ f) ≅ fiber (y ≫ f) ↦ τ.hom.app P) hσ
    simp only [pullbackPathIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.refl_hom, NatTrans.id_app] at h
    rw [← cancel_epi ((pullbackFiberIso f y).inv.app P),
      ← cancel_mono ((pullbackFiberIso f y).hom.app P), Category.assoc, h]
    simp
  have h₂ : σ.hom.app Q = 𝟙 _ := by
    have h := σ.hom.naturality i.hom
    rw [h₁, Category.comp_id] at h
    rw [← cancel_mono ((fiber y).map i.hom), ← h, Category.id_comp]
  rw [h₂]
  rfl

omit [Nonempty U] in
/-- **Loops of `Ū` trivial on `V̄` push down into the kernel of `π₁(U₀) → π₁(V₀)`.** For a
morphism `k : U₀ ⟶ V₀` over `𝔽_q` and base point data `B` of the Weil group of `U₀`, a loop `σ`
of the geometric curve `Ū` at `B.t` acting trivially on the base changes of finite étale covers of
`V̄` maps to an element of `π₁(U₀, s_U)` acting trivially on the base changes of the finite étale
covers of `V₀`: these are base changes of covers of `V̄`, since `Ū ⟶ U₀ ⟶ V₀` is `Ū ⟶ V̄ ⟶ V₀`. -/
theorem BasePointData.geomAut_mem_fixingSubgroup
    (B : BasePointData (ofFundamentalGroup pU sU GU)) {V : Scheme.{u}} (k : U ⟶ V)
    {q : V ⟶ Spec (.of K)} (hk : k ≫ q = pU) {σ : Aut (fiber B.t)}
    (hσ : pullbackPathIso (Scheme.Hom.geometricFiberMap k hk) σ = Iso.refl _) :
    B.geomAut σ ∈ fixingSubgroup sU k GU := by
  intro P x
  set kb := Scheme.Hom.geometricFiberMap k hk
  have hsq : pU.geometricFiberProj ≫ k = kb ≫ q.geometricFiberProj :=
    (Scheme.Hom.geometricFiberMap_comp_geometricFiberProj k hk).symm
  -- the loop pushed down to `U₀` acts trivially on the fibres of `k^* P`
  let e := pullbackPathIso pU.geometricFiberProj σ ≪≫ eqToIso (congrArg fiber
    (rfl : B.t ≫ pU.geometricFiberProj = B.t ≫ pU.geometricFiberProj))
  have he (a) : e.hom.app ((pullback k).obj P) a = a := by
    simp only [e, eqToIso_refl, Iso.trans_refl, pullbackPathIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      ConcreteCategory.comp_apply]
    erw [app_apply_eq_of_pullbackPathIso_eq_refl kb hσ
      ((pullbackCompIso _ _ _).symm ≪≫ eqToIso (congrArg (fun m ↦ (pullback m).obj P) hsq) ≪≫
        pullbackCompIso _ _ _)]
    exact ConcreteCategory.congr_hom
      ((pullbackFiberIso pU.geometricFiberProj B.t).inv_hom_id_app _) a
  have key := B.toAutMulEquiv_toπ e
  change (show GU from B.toπ e) • x = x
  rw [← toAut_hom_app_apply, ← toAutMulEquiv_apply]
  erw [key]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, ConcreteCategory.comp_apply]
  rw [he]
  exact ConcreteCategory.congr_hom (B.path.inv_hom_id_app _) x

end AlgebraicGeometry.WeilGroup
