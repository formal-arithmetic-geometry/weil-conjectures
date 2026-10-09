/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusElement
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Basic

/-!
# The Weil group of a curve over a finite field

Let `p : C₀ ⟶ Spec 𝔽_q` be a curve which is geometrically connected. This file constructs a
`AlgebraicGeometry.WeilGroup` of `C₀` (`AlgebraicGeometry.WeilGroup.ofCurve`): the Weil group
`W(C₀, s) ⊆ π₁(C₀, s) × ℤ` of a fundamental group `π₁(C₀, s)` at a geometric point `s` with values
in `𝔽̄_q`, with the topology induced from `π₁(C₀, s) × ℤ`, `ℤ` being discrete. In this topology
the geometric part `ker deg` is open and is the subspace `ker (π₁(C₀, s) → Gal(𝔽̄_q / 𝔽_q))` of the
profinite group `π₁(C₀, s)`.

The degree is surjective since the geometric Frobenius lifts to `π₁(C₀, s)`
(`AlgebraicGeometry.Scheme.FiniteEtale.exists_smul_eq_geometricFrobenius`), and the local
Frobenius at a closed point `x` is a Frobenius element at `x`, of degree `e_x`
(`AlgebraicGeometry.Scheme.FiniteEtale.exists_isFrobeniusElement`).

## Main definitions

- `AlgebraicGeometry.WeilGroup.ofCurve`: the Weil group of a geometrically connected curve over a
  finite field.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry

namespace Scheme.FiniteEtale

section Topology

variable {K : Type u} [Field K] [Finite K] {X₀ : Scheme.{u}} (p : X₀ ⟶ Spec (.of K))
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X₀)
  (G : Type u) [Group G] [∀ P, MulAction G ((fiber s).obj P)] [TopologicalSpace G]

/-- The degree map of the Weil group is continuous for the topology induced from
`π₁(X₀, s) × ℤ`. -/
lemma continuous_weilGroupDeg : Continuous (weilGroupDeg p s G) :=
  continuous_snd.comp continuous_subtype_val

/-- The geometric part `ker deg` of the Weil group is open. -/
lemma isOpen_ker_weilGroupDeg :
    IsOpen ((weilGroupDeg p s G).ker : Set (weilGroup p s G)) :=
  (isOpen_discrete {(1 : Multiplicative ℤ)}).preimage (continuous_weilGroupDeg p s G)

/-- The inclusion of the geometric part `ker deg` of the Weil group into `π₁(X₀, s)` is an
embedding. -/
lemma isEmbedding_ker_weilGroupDeg :
    Topology.IsEmbedding fun g : (weilGroupDeg p s G).ker ↦ (g.1 : G × Multiplicative ℤ).1 := by
  have hι : Topology.IsEmbedding fun g : (weilGroupDeg p s G).ker ↦
      (g.1 : G × Multiplicative ℤ) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have heq : (fun g : (weilGroupDeg p s G).ker ↦ (g.1 : G × Multiplicative ℤ)) =
      (fun g : G ↦ (g, (1 : Multiplicative ℤ))) ∘
        fun g : (weilGroupDeg p s G).ker ↦ (g.1 : G × Multiplicative ℤ).1 := by
    funext g
    exact Prod.ext rfl g.2
  refine ⟨Topology.IsInducing.of_comp (continuous_fst.comp hι.continuous)
    (continuous_id.prodMk continuous_const) (heq ▸ hι.isInducing), fun g h hgh ↦ ?_⟩
  exact hι.injective (Prod.ext hgh ((MonoidHom.mem_ker.1 g.2).trans (MonoidHom.mem_ker.1 h.2).symm))

open scoped FintypeCatDiscrete in
/-- The geometric part `ker deg` of the Weil group is compact: it is the closed subset of the
compact group `π₁(X₀, s)` of the elements acting trivially on the constant covers. -/
lemma isCompact_ker_weilGroupDeg [CompactSpace G] [∀ P, ContinuousSMul G ((fiber s).obj P)] :
    IsCompact ((weilGroupDeg p s G).ker : Set (weilGroup p s G)) := by
  let T : Set G := {g | ∀ (A : FiniteEtaleAlgebra K) (y : (fiber s).obj (constantCover p A)),
    g • y = y}
  have hT : IsClosed T := by
    simp only [T, Set.ofPred_forall]
    exact isClosed_iInter fun A ↦ isClosed_iInter fun y ↦
      isClosed_eq (continuous_id.smul continuous_const) continuous_const
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  convert (hT.isCompact.prod isCompact_singleton : IsCompact (T ×ˢ {(1 : Multiplicative ℤ)}))
  ext ⟨g, n⟩
  simp only [Set.mem_image, SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_prod,
    Set.mem_singleton_iff, T]
  constructor
  · rintro ⟨w, hw, hwe⟩
    obtain rfl : (w : G × Multiplicative ℤ).1 = g := congrArg Prod.fst hwe
    obtain rfl : (w : G × Multiplicative ℤ).2 = n := congrArg Prod.snd hwe
    have h1 : (w : G × Multiplicative ℤ).2 = 1 := hw
    refine ⟨fun A y ↦ ?_, h1⟩
    rw [(mem_weilGroup_iff p s G).1 w.2 A y, h1]
    simp
  · rintro ⟨hg, rfl⟩
    refine ⟨⟨(g, 1), (mem_weilGroup_iff p s G).2 fun A y ↦ ?_⟩, rfl, rfl⟩
    simpa using hg A y

end Topology

end Scheme.FiniteEtale

/-- A nonempty quasi-compact scheme locally of finite type over a finite field `K` has a point
with values in the algebraic closure of `K`: the residue field at a closed point is finite over
`K`. -/
lemma Scheme.Hom.nonempty_algebraicClosure_point {K : Type u} [Field K] {C : Scheme.{u}}
    (p : C ⟶ Spec (.of K)) [LocallyOfFiniteType p] [QuasiCompact p] [Nonempty C] :
    Nonempty (Spec (.of (AlgebraicClosure K)) ⟶ C) := by
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace p
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := C)).exists_closed_singleton Set.univ_nonempty
  have : IsClosedImmersion (C.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  let f := C.fromSpecResidueField x ≫ p
  have : IsFinite f := isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective f
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  let := φ.hom.toAlgebra
  have : Module.Finite K (C.residueField x) := hfin
  let ι := IsAlgClosed.lift (M := AlgebraicClosure K) (R := K) (S := C.residueField x)
  exact ⟨Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ C.fromSpecResidueField x⟩

/-- A scheme which is geometrically connected over a field is connected. -/
lemma connectedSpace_of_geometricallyConnected {K : Type u} [Field K] {C : Scheme.{u}}
    (p : C ⟶ Spec (.of K)) [GeometricallyConnected p] : ConnectedSpace C :=
  GeometricallyConnected.geometrically_connectedSpace (f := p) (K := K) (𝟙 _) (𝟙 C) p
    (IsPullback.id_horiz p)

namespace WeilGroup

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} (p : C ⟶ Spec (.of K)) [IsCurve p]
  [GeometricallyConnected p] (s : Spec (.of (AlgebraicClosure K)) ⟶ C)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((Scheme.FiniteEtale.fiber s).obj P)]

open Scheme.FiniteEtale

variable [ConnectedSpace C] [IsFundamentalGroup (fiber s) G]

omit [Finite K] [IsCurve p] [GeometricallyConnected p] in
/-- A choice of Frobenius element of `π₁(C₀, s)` at a closed point `x`. -/
noncomputable def frobeniusElement (x : C.finitePoints) : G :=
  have : Finite (C.residueField x.1) := x.2
  (exists_isFrobeniusElement s G x.1).choose

omit [Finite K] [IsCurve p] [GeometricallyConnected p] in
lemma isFrobeniusElement_frobeniusElement (x : C.finitePoints) :
    have : Finite (C.residueField x.1) := x.2
    IsFrobeniusElement s G x.1 (frobeniusElement s G x) :=
  have : Finite (C.residueField x.1) := x.2
  (exists_isFrobeniusElement s G x.1).choose_spec

/-- The local Frobenius at a closed point `x`, as an element of the Weil group of degree `e_x`. -/
noncomputable def weilFrobenius (x : C.finitePoints) : weilGroup p s G :=
  have : Finite (C.residueField x.1) := x.2
  ⟨(frobeniusElement s G x, Multiplicative.ofAdd (p.degreeOver x.1 : ℤ)),
    (isFrobeniusElement_frobeniusElement s G x).mem_weilGroup p⟩

/-- **Chebotarev density** for the Weil group of a curve over a finite field: the local
Frobenius elements generate a dense normal subgroup. -/
theorem dense_normalClosure_range_weilFrobenius :
    Dense ((Subgroup.normalClosure (Set.range (weilFrobenius p s G)) :
      Subgroup (weilGroup p s G)) : Set (weilGroup p s G)) := by
  sorry

/-- **The Weil group of a geometrically connected curve over a finite field**, built from a
fundamental group `G = π₁(C₀, s)` at a geometric point `s` with values in `𝔽̄_q`: the subgroup
`W(C₀, s) ⊆ π₁(C₀, s) × ℤ` with the induced topology, the local Frobenius at a closed point
being a chosen Frobenius element. (blueprint `sk-d-real-weil`, `def-wf-weil-group`) -/
noncomputable def ofFundamentalGroup : WeilGroup p :=
  have : TotallyDisconnectedSpace G :=
    (toAutHomeo (fiber s) G).symm.totallyDisconnectedSpace
  have hcont : ∀ P, ContinuousSMul G ((fiber s).obj P) := fun P ↦
    IsFundamentalGroup.continuous_smul P
  let γ := (exists_mem_weilGroup_snd_eq_one p s G).choose
  have hγ := (exists_mem_weilGroup_snd_eq_one p s G).choose_spec
  { carrier := weilGroup p s G
    deg := weilGroupDeg p s G
    deg_surjective := fun n ↦ ⟨⟨(γ, Multiplicative.ofAdd 1), hγ⟩ ^ n.toAdd, by
      rw [map_zpow]
      change (Multiplicative.ofAdd 1) ^ n.toAdd = n
      rw [← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]⟩
    isOpen_ker := isOpen_ker_weilGroupDeg p s G
    compactSpace_ker := isCompact_iff_compactSpace.mp (isCompact_ker_weilGroupDeg p s G)
    totallyDisconnectedSpace_ker := inferInstance
    frobeniusLift := ⟨(γ, Multiplicative.ofAdd 1), hγ⟩
    deg_frobeniusLift := rfl
    frobenius := weilFrobenius p s G
    deg_frobenius _ := rfl
    basePoint := s
    fundamentalGroup := G
    weilGroupEquiv := MulEquiv.refl _
    deg_eq _ := rfl
    isEmbedding_ker := isEmbedding_ker_weilGroupDeg p s G
    isFrobeniusElement_frobenius := isFrobeniusElement_frobeniusElement s G
    dense_frobenius := dense_normalClosure_range_weilFrobenius p s G }

omit [ConnectedSpace C] [IsFundamentalGroup (fiber s) G] in
/-- A geometrically connected curve over a finite field has a Weil group. -/
theorem nonempty (p : C ⟶ Spec (.of K)) [IsCurve p] [GeometricallyConnected p] :
    Nonempty (WeilGroup p) := by
  have : ConnectedSpace C := connectedSpace_of_geometricallyConnected p
  obtain ⟨s⟩ := p.nonempty_algebraicClosure_point
  obtain ⟨G, _, _⟩ := exists_isFundamentalGroup s
  exact ⟨ofFundamentalGroup p s G⟩

end WeilGroup

end AlgebraicGeometry
