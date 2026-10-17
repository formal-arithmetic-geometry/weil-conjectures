/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.DenseOpen
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Inertia
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorCoefficients
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorResidue

/-!
# The residue sequence of an open curve

Let `U ⊆ C` be a nonempty open of a smooth connected curve over an algebraically closed field
`k`, with boundary `D = C ∖ U`, and let `N` be invertible in `k`. The residues
`res_z : H¹(U, ℤ / N) → Hom(μ_N(k), ℤ / N) = ℤ / N (-1)` at the boundary points
(`AlgebraicGeometry.Scheme.EtaleTorsor.residue`) fit in the exact sequence (5.1) of blueprint
`lem-wf-open-curve-residue-sequence`

`0 → H¹(C, ℤ / N) → H¹(U, ℤ / N) → ⊕_{z ∈ D} ℤ / N (-1)`.

In the torsor model of `H¹`:

* the residue of a torsor at `z` vanishes if and only if its monodromy is trivial on the kernel
  of `π₁(U) → π₁(U ∪ {z})`
  (`AlgebraicGeometry.Scheme.EtaleTorsor.residue_eq_zero_iff_forall_monodromy_eq_one`): by
  Kummer theory at the generic point, the inertia group at `z` fixes a Kummer element `x` of the
  torsor if and only if `N` divides `ord_z (x ^ N)`;
* a torsor on `U` extends to `C` if and only if all its residues vanish
  (`AlgebraicGeometry.Scheme.EtaleTorsor.exists_isIsomorphic_pullback_iff_residue_eq_zero`), and
  torsors on `C` with isomorphic restrictions to `U` are isomorphic
  (`AlgebraicGeometry.Scheme.EtaleTorsor.isIsomorphic_of_isIsomorphic_pullback_of_isCurve`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.EtaleTorsor

open FiniteEtale

section Residue

variable {C U : Scheme.{u}} [IsIntegral C] (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U]
  [IsLocallyNoetherian C] {k : Type u} [Field k] (p : C ⟶ Spec (.of k)) {N : ℕ} [NeZero N]
  [NeZero (N : k)] [HasEnoughRootsOfUnity k N]

local notation "Ω" => SeparableClosure (Scheme.functionField C)

lemma residue_apply (T : EtaleTorsor (ULift.{u + 1} (ZMod N)) U) (z : C)
    (ξ : Additive (rootsOfUnity N k)) :
    T.residue j p z ξ = kummerResidue C (T.galoisCharacter j) z
      (algebraMap C.functionField Ω (p.functionFieldConstants ((ξ.toMul : kˣ) : k))) :=
  rfl

/-- Isomorphic torsors have the same residues. -/
lemma residue_eq_of_isIsomorphic {T T' : EtaleTorsor (ULift.{u + 1} (ZMod N)) U}
    (h : T.IsIsomorphic T') : T.residue j p = T'.residue j p := by
  funext z
  refine AddMonoidHom.ext fun ξ ↦ ?_
  rw [residue_apply, residue_apply, galoisCharacter_eq_of_isIsomorphic j h]

/-- The residue against `ξ` is the order of vanishing of `x ^ N` for any Kummer element `x` of
the torsor against `ξ`. -/
lemma residue_eq_ord (T : EtaleTorsor (ULift.{u + 1} (ZMod N)) U) (z : C)
    (ξ : Additive (rootsOfUnity N k)) {x : Ω} {f : C.functionField} (hx : x ≠ 0)
    (hf : algebraMap C.functionField Ω f = x ^ N)
    (hχ : ∀ σ : Gal(Ω/C.functionField), σ x =
      algebraMap C.functionField Ω (p.functionFieldConstants ((ξ.toMul : kˣ) : k)) ^
        (T.galoisCharacter j σ).val * x) :
    T.residue j p z ξ = (C.ord f z : ZMod N) :=
  kummerResidue_eq z hx hf hχ

end Residue

section Curve

open WeilGroup

variable {k : Type u} [Field k] [IsAlgClosed k] {C U : Scheme.{u}} {p : C ⟶ Spec (.of k)}
  [IsCurve p] [SmoothOfRelativeDimension 1 p] [ConnectedSpace C] [ConnectedSpace U]
  {j : U ⟶ C} [IsOpenImmersion j] [Nonempty U] [IsIntegral C] [IsLocallyNoetherian C]

local notation "Ω" => SeparableClosure (Scheme.functionField C)


set_option synthInstance.maxHeartbeats 200000 in
-- instance search through `SeparableClosure` and its integral closures is slow
/-- Blueprint `lem-wf-open-curve-residue-sequence`: exactness of the residue sequence at one
boundary point.

Let `U ⊆ C` be a nonempty open of a smooth connected curve over an algebraically closed field
`k`, `V ⊆ C` an open with `V ∖ U = {z}`, and `N` invertible in `k`. The residue at `z` of a
`ℤ / N`-torsor `T` on `U` vanishes if and only if the monodromy of `T` is trivial on the kernel
of `π₁(U) → π₁(V)`, i.e. if and only if `T` extends over `z`. -/
theorem residue_eq_zero_iff_forall_monodromy_eq_one (V : C.Opens)
    (hV : Set.range j.base ⊆ V) (z : C) (hz : (V : Set C) \ Set.range j.base = {z})
    {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (s : Spec (.of Ω') ⟶ U)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]
    {N : ℕ} [NeZero N] [NeZero (N : k)] (T : EtaleTorsor (ULift.{u + 1} (ZMod N)) U) :
    T.residue j p z = 0 ↔ ∀ g ∈ fixingSubgroup s (IsOpenImmersion.lift V.ι j
      (by rwa [Scheme.Opens.range_ι])) G, T.monodromy s G g = 1 := by
  classical
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  obtain ⟨u₀⟩ := (inferInstance : Nonempty U)
  -- `V = U ∪ {z}`
  have hzV : z ∈ (V : Set C) \ Set.range j.base := hz ▸ rfl
  have hzj : z ∉ Set.range j.base := hzV.2
  have hVb : V = boundaryOpen (p := p) j z := by
    ext x
    rw [SetLike.mem_coe, SetLike.mem_coe, mem_boundaryOpen_iff]
    constructor
    · intro hx
      by_cases hxj : x ∈ Set.range j.base
      · exact Or.inl hxj
      · exact Or.inr (by simpa [hz] using (show x ∈ (V : Set C) \ Set.range j.base from ⟨hx, hxj⟩))
    · rintro (hx | rfl)
      · exact hV hx
      · exact hzV.1
  subst hVb
  have := connectedSpace_boundaryOpen (p := p) j z
  -- a chart at `z` and a point `Q` over it
  obtain ⟨c⟩ := nonempty_boundaryChart (p := p) j hzj
  have := c.isMaximal_ideal
  have := isDedekindDomain_of_isAffineOpen p c.isAffineOpen
  have : IsAlgClosed c.ideal.ResidueField := c.isAlgClosed_residueField hzj
  let τ : fiber (pointOfAlgebra Ω (genericPointLift j)) ≅ fiber s :=
    (nonempty_iso_of_fiberFunctor _ _).some
  let ρ := galoisToFundamentalGroup (genericPointLift j) τ G
  have hχ (σ : Gal(Ω/C.functionField)) :
      T.galoisCharacter j σ = (T.monodromy s G (ρ σ)).toAdd.down :=
    galoisCharacter_eq_monodromy j T τ G σ
  -- the image of inertia acts trivially on the covers extending over `z`
  have hIloc : ∀ σ ∈ c.point.inertia Gal(Ω/C.functionField),
      ρ σ ∈ fixingSubgroup s (toOpen j (boundaryOpen (p := p) j z)
        (opensRange_le_boundaryOpen j z)) G := by
    intro σ hσ P x
    obtain ⟨t, rfl⟩ : ∃ t, τ.hom.app _ t = x :=
      ⟨τ.inv.app _ x, ConcreteCategory.congr_hom (τ.inv_hom_id_app _) x⟩
    rw [galoisToFundamentalGroup_smul]
    congr 1
    exact galoisToAut_hom_app_pullback_eq_of_mem_inertia j c.isAffineOpen c.point
      (boundaryOpen (p := p) j z) (opensRange_le_boundaryOpen j z) c.le hσ P t
  have hN : (N : k) ≠ 0 := NeZero.ne _
  constructor
  · intro h0 g hg
    -- a Kummer element against a primitive root of unity
    obtain ⟨ζk, hζk⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k N
    let ζ : Ω := algebraMap C.functionField Ω (p.functionFieldConstants ζk)
    have hζ : IsPrimitiveRoot ζ N :=
      hζk.map_of_injective ((algebraMap C.functionField Ω).comp p.functionFieldConstants).injective
    obtain ⟨x, f, hx0, hf, hxσ⟩ := T.exists_kummerElement j p hζk.pow_eq_one
    have hf0 := ne_zero_of_algebraMap_eq_pow hx0 hf
    have hres := T.residue_eq_ord j p z (Additive.ofMul hζk.toRootsOfUnity) hx0 hf hxσ
    rw [h0] at hres
    have hdvd : (N : ℤ) ∣ C.ord f z :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (by rw [← hres]; rfl)
    -- inertia fixes the Kummer element, so the monodromy is trivial on inertia
    have hI : ∀ σ ∈ c.point.inertia Gal(Ω/C.functionField), T.monodromy s G (ρ σ) = 1 := by
      intro σ hσ
      have hfix : σ x = x := c.inertia_apply_eq_of_dvd_ord hzj c.point hσ hN hf0 hf hdvd
      rw [hxσ σ] at hfix
      have h1 : ζ ^ (T.galoisCharacter j σ).val = 1 := by
        have := mul_right_cancel₀ hx0 (hfix.trans (one_mul x).symm)
        exact this
      have h2 : T.galoisCharacter j σ = 0 := by
        rw [← ZMod.natCast_zmod_val (T.galoisCharacter j σ), ZMod.natCast_eq_zero_iff]
        exact hζ.pow_eq_one_iff_dvd _ |>.1 h1
      rw [hχ] at h2
      apply Multiplicative.toAdd.injective
      exact ULift.ext _ _ h2
    -- the kernel of the monodromy is a closed normal subgroup containing the image of inertia
    let K := (T.monodromy s G).toMonoidHom.ker
    have hKc : IsClosed (K : Set G) :=
      (isClosed_discrete {(1 : Multiplicative (ULift.{u + 1} (ZMod N)))}).preimage
        (T.monodromy s G).continuous
    have hsub : ((c.point.inertia Gal(Ω/C.functionField)).map ρ : Set G) ⊆ K := by
      rintro _ ⟨σ, hσ, rfl⟩
      exact hI σ hσ
    have hker := c.fixingSubgroup_le_topologicalClosure_normalClosure hzj c.point s G τ hg
    exact Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal hsub) hKc hker
  · intro h
    refine AddMonoidHom.ext fun ξ ↦ ?_
    have hξ : ((ξ.toMul : kˣ) : k) ^ N = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity N _).1 ξ.toMul.2, Units.val_one]
    obtain ⟨x, f, hx0, hf, hxσ⟩ := T.exists_kummerElement j p hξ
    rw [T.residue_eq_ord j p z ξ hx0 hf hxσ, AddMonoidHom.zero_apply]
    -- inertia fixes the Kummer element
    have hI : ∀ σ ∈ c.point.inertia Gal(Ω/C.functionField), σ x = x := by
      intro σ hσ
      have h1 := h _ (hIloc σ hσ)
      rw [hxσ σ, hχ, h1]
      simp
    have hdvd := c.dvd_ord_of_forall_inertia hzj c.point hx0 hf hI
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).2 hdvd

omit [IsCurve p] [SmoothOfRelativeDimension 1 p] [ConnectedSpace C] [IsIntegral C]
  [IsLocallyNoetherian C] [IsOpenImmersion j] [Nonempty U] in
/-- The monodromy of the base change of a torsor along `f` is trivial on the kernel of
`π₁(U) → π₁(Y)`. -/
lemma monodromy_pullback_eq_one_of_mem_fixingSubgroup {M : Type (u + 1)} [AddCommGroup M]
    [Finite M] [TopologicalSpace M] [DiscreteTopology M] {Y : Scheme.{u}} (f : U ⟶ Y)
    {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (s : Spec (.of Ω') ⟶ U)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]
    (T : EtaleTorsor M Y) {g : G} (hg : g ∈ fixingSubgroup s f G) :
    (T.pullback f).monodromy s G g = 1 := by
  obtain ⟨y⟩ := (T.pullback f).nonempty_fiber s
  exact ((T.pullback f).monodromy_eq_iff s G g y 0).mpr
    (by rw [fiber_map_vaddHom_zero]; exact (hg T.toFiniteEtale y).symm)

omit [IsCurve p] [SmoothOfRelativeDimension 1 p] in
/-- Blueprint `lem-wf-open-curve-residue-sequence`: injectivity of `H¹(C, M) → H¹(U, M)`.

Torsors on a connected regular locally noetherian scheme `C` (for instance a smooth connected
curve over a field) whose restrictions to a nonempty open `U` are isomorphic are isomorphic. -/
theorem isIsomorphic_of_isIsomorphic_pullback_of_isRegular [IsRegular C] {M : Type (u + 1)}
    [AddCommGroup M] [Finite M] {T₁ T₂ : EtaleTorsor M C}
    (h : (T₁.pullback j).IsIsomorphic (T₂.pullback j)) :
    T₁.IsIsomorphic T₂ := by
  let _ : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  let s := genericGeometricPoint (C := C) j
  obtain ⟨G, _, _⟩ := exists_isFundamentalGroup s
  obtain ⟨G', _, _⟩ := exists_isFundamentalGroup (s ≫ j)
  exact isIsomorphic_of_isIsomorphic_pullback j s
    (fundamentalGroupMap_surjective_of_isRegular j (pullbackFiberIso j s) G G') h

/-- Blueprint `lem-wf-open-curve-residue-sequence`: exactness of the residue sequence
`0 → H¹(C, ℤ / N) → H¹(U, ℤ / N) → ⊕_{z ∈ C ∖ U} ℤ / N (-1)` in the middle.

Let `U ⊆ C` be a nonempty open of a smooth connected curve over an algebraically closed field
`k`, and `N` invertible in `k`. A `ℤ / N`-torsor on `U` is the restriction of a torsor on `C` if
and only if its residues at all the boundary points vanish. -/
theorem exists_isIsomorphic_pullback_iff_residue_eq_zero {N : ℕ} [NeZero N] [NeZero (N : k)]
    (T : EtaleTorsor (ULift.{u + 1} (ZMod N)) U) :
    (∃ T' : EtaleTorsor (ULift.{u + 1} (ZMod N)) C, (T'.pullback j).IsIsomorphic T) ↔
      ∀ z ∉ Set.range j.base, T.residue j p z = 0 := by
  classical
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsRegular C := IsRegular.of_smooth p
  have := irreducibleSpace_of_smooth (p := p)
  let s := genericGeometricPoint (C := C) j
  obtain ⟨G, _, _⟩ := exists_isFundamentalGroup s
  -- the open `U ∪ {z}` for a boundary point `z`
  have hVz (z : C) (hz : z ∉ Set.range j.base) :
      ((boundaryOpen (p := p) j z : C.Opens) : Set C) \ Set.range j.base = {z} := by
    ext x
    simp only [Set.mem_sdiff, SetLike.mem_coe, mem_boundaryOpen_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h₁ | h₁, h₂⟩
      · exact absurd h₁ h₂
      · exact h₁
    · rintro rfl
      exact ⟨Or.inr rfl, hz⟩
  have hres (z : C) (hz : z ∉ Set.range j.base) :=
    residue_eq_zero_iff_forall_monodromy_eq_one (p := p) (boundaryOpen (p := p) j z)
      (fun x hx ↦ (mem_boundaryOpen_iff j).2 (Or.inl hx)) z (hVz z hz) s G (N := N) T
  constructor
  · rintro ⟨T', hT'⟩ z hz
    refine (hres z hz).2 fun g hg ↦ ?_
    have hg' := fixingSubgroup_le_comp s _ G (boundaryOpen (p := p) j z).ι hg
    rw [IsOpenImmersion.lift_fac] at hg'
    rw [← monodromy_eq_of_isIsomorphic s G hT']
    exact monodromy_pullback_eq_one_of_mem_fixingSubgroup j s G T' hg'
  · intro h
    -- the monodromy of `T` kills the kernel of `π₁(U) → π₁(C)`
    let S := boundaryFinset (p := p) j
    have hS := isClosed_of_mem_boundaryFinset (p := p) j
    have hSU := (coe_boundaryFinset (p := p) j).symm
    have hV : ∀ z ∈ S, ConnectedSpace (complOpens S hS {z}).toScheme := fun z hz ↦ by
      obtain ⟨u⟩ := (inferInstance : Nonempty U)
      have hne : ((complOpens S hS {z} : C.Opens) : Set C).Nonempty :=
        ⟨j u, range_le_complOpens j S hS hSU {z} ⟨u, rfl⟩⟩
      have hirr : IsIrreducible ((complOpens S hS {z} : C.Opens) : Set C) :=
        ⟨hne, (IrreducibleSpace.isIrreducible_univ C).isPreirreducible.open_subset
          (complOpens S hS {z}).isOpen (Set.subset_univ _)⟩
      exact isConnected_iff_connectedSpace.1 hirr.isConnected
    have hconn : ∀ z ∈ S, ∀ P : (complOpens S hS {z}).toScheme.FiniteEtale, IsConnected P →
        IsConnected ((FiniteEtale.pullback (toComplOpens j S hS hSU {z})).obj P) :=
        fun z hz P hP ↦ by
      have := hV z hz
      have := connectedSpace_of_isConnected P
      have : Etale P.obj.hom := P.obj.prop
      let q : P.obj.left ⟶ Spec (.of k) := P.obj.hom ≫ (complOpens S hS {z}).ι ≫ p
      have : Smooth q := inferInstance
      have := LocallyOfFiniteType.isLocallyNoetherian q
      have := IsRegular.of_smooth q
      have := IsRegular.irreducibleSpace P.obj.left
      exact isConnected_pullback_of_irreducibleSpace _ P
    have hkill : ∀ g ∈ fixingSubgroup s j G, T.monodromy s G g = 1 := by
      let K := (T.monodromy s G).toMonoidHom.ker
      have hKc : IsClosed (K : Set G) :=
        (isClosed_discrete {(1 : Multiplicative (ULift.{u + 1} (ZMod N)))}).preimage
          (T.monodromy s G).continuous
      have hle : (⨆ z : S, fixingSubgroup s (toComplOpens j S hS hSU {z.1}) G) ≤ K :=
        iSup_le fun z g hg ↦ by
          have hz : z.1 ∉ Set.range j.base := by
            change z.1 ∈ (Set.range j.base)ᶜ
            rw [hSU]
            exact z.2
          exact (hres z.1 hz).1 (h z.1 hz) g hg
      intro g hg
      exact Subgroup.topologicalClosure_minimal _ hle hKc
        (fixingSubgroup_le_topologicalClosure_iSup j S hS hSU s G hV hconn hg)
    -- so `T` comes from `C`
    obtain ⟨G', _, _⟩ := exists_isFundamentalGroup (s ≫ j)
    exact exists_isIsomorphic_pullback j s
      (fundamentalGroupMap_surjective_of_isRegular j (pullbackFiberIso j s) G G') T hkill

end Curve

end AlgebraicGeometry.Scheme.EtaleTorsor
