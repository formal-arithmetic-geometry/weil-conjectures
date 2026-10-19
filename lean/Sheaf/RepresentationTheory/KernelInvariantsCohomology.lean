/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module
public import Sheaf.RepresentationTheory.DiscreteContinuousCohomology
public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Data.Int.GCD
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
/-!
# Exact kernel invariants and comparison of continuous cohomology

Source: blueprint main-20261015, `lem-exc-dvr-galois.proof.md`, third paragraph;
DAG proof steps 3--5 of `lem-exc-dvr-galois`.
(blueprint: lem-exc-kernel-invariants-cohomology)
-/

@[expose] public section
set_option autoImplicit false
universe u v w z
open CategoryTheory
namespace Rep
variable {A : Type v} [Ring A]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {B : Type z} [Group B] [TopologicalSpace B] [IsTopologicalGroup B]

/-- The submodule fixed by the kernel of a homomorphism. -/
def kernelFixedSubmodule (π : G →* B) (M : DiscreteContinuousRep.{v, u, w} A G) :
    Submodule A M.obj.V :=
  ⨅ h : π.ker, LinearMap.ker (M.obj.ρ h - LinearMap.id)

omit [TopologicalSpace B] [IsTopologicalGroup B] in
theorem mem_kernelFixedSubmodule (π : G →* B)
    (M : DiscreteContinuousRep.{v, u, w} A G) (m : M.obj.V) :
    m ∈ kernelFixedSubmodule π M ↔ ∀ h : π.ker, M.obj.ρ h m = m := by
  simp [kernelFixedSubmodule, LinearMap.mem_ker, sub_eq_zero]

attribute [local irreducible] kernelFixedSubmodule

omit [TopologicalSpace B] [IsTopologicalGroup B] in
/-- Kernel invariants are stable under the ambient group action. -/
theorem kernelFixedSubmodule_stable (π : G →* B)
    (M : DiscreteContinuousRep.{v, u, w} A G) (g : G) :
    kernelFixedSubmodule π M ≤ (kernelFixedSubmodule π M).comap (M.obj.ρ g) := by
  intro m hm
  change M.obj.ρ g m ∈ kernelFixedSubmodule π M
  rw [mem_kernelFixedSubmodule] at hm ⊢
  intro h
  let k : π.ker := ⟨g⁻¹ * h * g, by
    change π (g⁻¹ * h * g) = 1
    rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp h.property,
      mul_one, inv_mul_cancel]⟩
  have hg : (h : G) * g = g * k := by simp [k, mul_assoc]
  calc
    M.obj.ρ h (M.obj.ρ g m) = M.obj.ρ ((h : G) * g) m := by simp
    _ = M.obj.ρ (g * k) m := by rw [hg]
    _ = M.obj.ρ g m := by simp [hm k]

/-- The quotient action on the actual kernel-fixed submodule. -/
noncomputable def kernelFixedRepresentation (π : G →* B) (hπ : Function.Surjective π)
    (M : DiscreteContinuousRep.{v, u, w} A G) :
    Representation A B (kernelFixedSubmodule π M) :=
  (Units.coeHom _).comp (π.liftOfSurjective hπ
    ⟨(M.obj.ρ.subrepresentation (kernelFixedSubmodule π M)
      (kernelFixedSubmodule_stable π M)).toHomUnits, by
        intro h hh
        apply Units.ext
        ext m
        exact (mem_kernelFixedSubmodule π M m.val).mp m.property ⟨h, hh⟩⟩)

omit [TopologicalSpace B] [IsTopologicalGroup B] in
theorem kernelFixedRepresentation_apply (π : G →* B)
    (hπ : Function.Surjective π) (M : DiscreteContinuousRep.{v, u, w} A G)
    (g : G) (m : kernelFixedSubmodule π M) :
    (kernelFixedRepresentation π hπ M (π g) m).val = M.obj.ρ g m.val := by
  dsimp only [kernelFixedRepresentation, MonoidHom.comp_apply, Units.coeHom_apply]
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  rfl

attribute [local irreducible] kernelFixedRepresentation

/-- Kernel invariants, with the quotient action and its discrete continuity proof. -/
noncomputable def kernelFixedDiscreteRep [CompactSpace G] [T2Space B]
    (π : G →* B) (hπ : Function.Surjective π) (hc : Continuous π)
    (M : DiscreteContinuousRep.{v, u, w} A G) : DiscreteContinuousRep.{v, z, w} A B :=
  ⟨Rep.of (kernelFixedRepresentation π hπ M), by
    intro m
    apply (Topology.IsQuotientMap.of_surjective_continuous hπ hc).isCoinducing.isOpen_preimage.mp
    convert M.property m.val using 1
    ext g
    change kernelFixedRepresentation π hπ M (π g) m = m ↔ _
    rw [Subtype.ext_iff, kernelFixedRepresentation_apply]
    rfl⟩

/-- Equivariant maps restrict to the kernel-fixed submodules. -/
private def kernelFixedLinearMap (π : G →* B)
    {M N : DiscreteContinuousRep.{v, u, w} A G} (f : M ⟶ N) :
    kernelFixedSubmodule π M →ₗ[A] kernelFixedSubmodule π N :=
  (f.hom.hom.toLinearMap.comp (kernelFixedSubmodule π M).subtype).codRestrict _ (by
    intro m
    rw [mem_kernelFixedSubmodule]
    intro h
    change N.obj.ρ h (f.hom.hom m.val) = f.hom.hom m.val
    rw [← f.hom.hom.isIntertwining, (mem_kernelFixedSubmodule π M m.val).mp m.property h])

/-- The functor of kernel invariants and the induced quotient action. -/
private noncomputable def kernelFixedFunctor [CompactSpace G] [T2Space B]
    (π : G →* B) (hπ : Function.Surjective π) (hc : Continuous π) :
    DiscreteContinuousRep.{v, u, w} A G ⥤ DiscreteContinuousRep.{v, z, w} A B where
  obj := kernelFixedDiscreteRep π hπ hc
  map {X Y} f := ⟨Rep.ofHom
    { toLinearMap := kernelFixedLinearMap π f
      isIntertwining' := by
        intro b
        obtain ⟨g, rfl⟩ := hπ b
        ext m
        change (kernelFixedLinearMap π f
          (kernelFixedRepresentation π hπ _ (π g) m)).val =
          (kernelFixedRepresentation π hπ _ (π g) (kernelFixedLinearMap π f m)).val
        simp only [kernelFixedLinearMap, LinearMap.codRestrict_apply, LinearMap.comp_apply,
          Submodule.subtype_apply, kernelFixedRepresentation_apply]
        exact Rep.hom_comm_apply f.hom g m.val }⟩
  map_id _ := by ext m; rfl
  map_comp _ _ := by ext m; rfl

/-- Inflation precomposes the action and keeps the coefficient module. -/
private def discreteInflation (π : G →* B) (hc : Continuous π) :
    DiscreteContinuousRep.{v, z, w} A B ⥤ DiscreteContinuousRep.{v, u, w} A G where
  obj M := ⟨Rep.of (M.obj.ρ.comp π), fun m ↦ (M.property m).preimage hc⟩
  map {M N} f := ⟨Rep.ofHom
    { toLinearMap := f.hom.hom.toLinearMap
      isIntertwining' := fun g ↦ f.hom.hom.isIntertwining' (π g) }⟩
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- Inflation is left adjoint to the actual kernel invariants. -/
private noncomputable def discreteInflationAdjunction [CompactSpace G] [T2Space B]
    (π : G →* B) (hπ : Function.Surjective π) (hc : Continuous π) :
    discreteInflation (A := A) π hc ⊣ kernelFixedFunctor π hπ hc :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N ↦
        { toFun := fun f ↦ ⟨Rep.ofHom
            { toLinearMap := f.hom.hom.toLinearMap.codRestrict _ (by
                intro m
                rw [mem_kernelFixedSubmodule]
                intro h
                change N.obj.ρ h (f.hom.hom m) = f.hom.hom m
                rw [← Rep.hom_comm_apply f.hom]
                change f.hom.hom (M.obj.ρ (π h) m) = f.hom.hom m
                rw [MonoidHom.mem_ker.mp h.property]
                simp)
              isIntertwining' := by
                intro b
                obtain ⟨g, rfl⟩ := hπ b
                ext m
                change f.hom.hom.toLinearMap (M.obj.ρ (π g) m) =
                  (kernelFixedRepresentation π hπ N (π g)
                    ⟨f.hom.hom.toLinearMap m, _⟩).val
                rw [kernelFixedRepresentation_apply]
                exact Rep.hom_comm_apply f.hom g m }⟩
          invFun := fun f ↦ ⟨Rep.ofHom
            { toLinearMap := (kernelFixedSubmodule π N).subtype.comp f.hom.hom.toLinearMap
              isIntertwining' := by
                intro g
                ext m
                change (f.hom.hom (M.obj.ρ (π g) m)).val =
                  N.obj.ρ g (f.hom.hom m).val
                rw [Rep.hom_comm_apply f.hom]
                exact kernelFixedRepresentation_apply π hπ N g _ }⟩
          left_inv := fun _ ↦ by ext; rfl
          right_inv := fun _ ↦ by ext; rfl }
      homEquiv_naturality_left_symm := by intros; ext; rfl
      homEquiv_naturality_right := by intros; ext; rfl }

attribute [local irreducible] discreteInflationAdjunction

omit [IsTopologicalGroup B] in
/-- Averaging over a finite quotient lifts invariant elements through an exact pair. -/
private theorem kernelFixed_exact_lift [CompactSpace G] [TotallyDisconnectedSpace G] [T2Space B]
    (π : G →* B) (hc : Continuous π)
    (l s : ℕ) (hA : (l ^ s : ℕ) • (1 : A) = 0)
    (hcop : ∀ (Q : Type u) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
      [Finite Q] (f : π.ker →* Q), Continuous f → Function.Surjective f →
        Nat.Coprime l (Nat.card Q))
    {M N : DiscreteContinuousRep.{v, u, w} A G} (f : M ⟶ N)
    (y : kernelFixedSubmodule π N) (x : M.obj.V) (hxy : f.hom.hom x = y.val) :
    ∃ z : kernelFixedSubmodule π M, f.hom.hom z.val = y.val := by
  classical
  have hclosed : IsClosed (π.ker : Set G) :=
    isClosed_singleton.preimage hc
  let : CompactSpace π.ker := isCompact_iff_compactSpace.mp hclosed.isCompact
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    ((M.property x).preimage
      (continuous_subtype_val : Continuous (Subtype.val : π.ker → G)))
      (by change M.obj.ρ ((1 : π.ker) : G) x = x; simp)
  let Q := π.ker ⧸ U.toSubgroup
  let : Fintype Q := Fintype.ofFinite Q
  have hq : Nat.Coprime l (Fintype.card Q) := by
    rw [← Nat.card_eq_fintype_card]
    exact hcop Q (QuotientGroup.mk' U.toSubgroup) continuous_quotient_mk'
      (QuotientGroup.mk'_surjective _)
  have horbit (a b : π.ker)
      (hab : (a : Q) = (b : Q)) : M.obj.ρ a x = M.obj.ρ b x := by
    have hu : a⁻¹ * b ∈ U := QuotientGroup.eq.mp hab
    have hx : M.obj.ρ (a⁻¹ * b : π.ker) x = x := hU hu
    calc
      M.obj.ρ a x = M.obj.ρ a (M.obj.ρ (a⁻¹ * b : π.ker) x) := by rw [hx]
      _ = M.obj.ρ b x := by simp [← Module.End.mul_apply, ← map_mul]
  let t : Q → M.obj.V := fun q ↦ M.obj.ρ q.out x
  have ht (a : π.ker) : t (a : Q) = M.obj.ρ a x :=
    horbit _ _ (Quotient.out_eq' _)
  have htact (a : π.ker) (q : Q) :
      M.obj.ρ a (t q) = t ((a : Q) * q) := by
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup q
    change M.obj.ρ a (t (b : Q)) = t ((a * b : π.ker) : Q)
    rw [ht, ht]
    simp [← Module.End.mul_apply, ← map_mul]
  let z := ∑ q : Q, t q
  have hz (a : π.ker) : M.obj.ρ a z = z := by
    simp only [z, map_sum, htact]
    exact Equiv.sum_comp (Equiv.mulLeft (a : Q)) t
  have hfy : f.hom.hom z = Fintype.card Q • y.val := by
    simp only [z, map_sum]
    have htmap (q : Q) : f.hom.hom (t q) = y.val := by
      dsimp only [t]
      rw [f.hom.hom.isIntertwining, hxy]
      exact (mem_kernelFixedSubmodule π N y.val).mp y.property q.out
    simp only [htmap, Finset.sum_const, Finset.card_univ]
  let a := Nat.gcdA (Fintype.card Q) (l ^ s)
  let b := Nat.gcdB (Fintype.card Q) (l ^ s)
  have hab : (1 : ℤ) = (Fintype.card Q : ℤ) * a + (l ^ s : ℕ) * b := by
    rw [← Nat.gcd_eq_gcd_ab, hq.symm.pow_right s, Nat.cast_one]
  have hkill : (l ^ s : ℕ) • y.val = 0 := by
    calc
      (l ^ s : ℕ) • y.val = ((l ^ s : ℕ) • (1 : A)) • y.val := by rw [smul_assoc, one_smul]
      _ = 0 := by rw [hA, zero_smul]
  have hav : a • (Fintype.card Q • y.val) = y.val := by
    have h := congrArg (fun k : ℤ ↦ k • y.val) hab
    simp only [one_smul, add_zsmul, mul_comm _ a, mul_comm _ b, mul_zsmul,
      natCast_zsmul, hkill, smul_zero, add_zero] at h
    exact h.symm
  refine ⟨⟨a • z, (mem_kernelFixedSubmodule π M _).mpr ?_⟩, ?_⟩
  · intro h
    simp only [map_zsmul, hz]
  · rw [map_zsmul, hfy, hav]

/-- Fixed elements for the whole group. -/
private def allFixedSubmodule (M : DiscreteContinuousRep.{v, u, w} A G) : Submodule A M.obj.V :=
  ⨅ g : G, LinearMap.ker (M.obj.ρ g - LinearMap.id)

private theorem mem_allFixedSubmodule (M : DiscreteContinuousRep.{v, u, w} A G) (m : M.obj.V) :
    m ∈ allFixedSubmodule M ↔ ∀ g : G, M.obj.ρ g m = m := by
  simp [allFixedSubmodule, LinearMap.mem_ker, sub_eq_zero]

/-- Taking kernel invariants and then quotient invariants is taking all invariants. -/
private noncomputable def kernelFixed_allFixed_equiv [CompactSpace G] [T2Space B]
    (π : G →* B) (hπ : Function.Surjective π) (hc : Continuous π)
    (M : DiscreteContinuousRep.{v, u, w} A G) :
    allFixedSubmodule M ≃ₗ[A] allFixedSubmodule (kernelFixedDiscreteRep π hπ hc M) where
  toFun m := ⟨⟨m.val, (mem_kernelFixedSubmodule π M _).mpr
    (fun h ↦ (mem_allFixedSubmodule M _).mp m.property h)⟩,
      (mem_allFixedSubmodule _ _).mpr (by
        intro b
        obtain ⟨g, rfl⟩ := hπ b
        apply Subtype.ext
        exact (kernelFixedRepresentation_apply π hπ M g _).trans
          ((mem_allFixedSubmodule M _).mp m.property g))⟩
  invFun m := ⟨m.val.val, (mem_allFixedSubmodule M _).mpr (by
    intro g
    have hm := congrArg Subtype.val ((mem_allFixedSubmodule _ _).mp m.property (π g))
    exact (kernelFixedRepresentation_apply π hπ M g m.val).symm.trans hm)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


/-- The underlying coefficient-module functor. -/
private abbrev discreteUnderlying : DiscreteContinuousRep.{v, u, w} A G ⥤ ModuleCat.{w} A :=
  ObjectProperty.ι _ ⋙ forget₂ (Rep.{w} A G) (ModuleCat.{w} A)

section Exactness
set_option linter.style.haveILetI false
variable {B₀ : Type} [Group B₀] [TopologicalSpace B₀] [IsTopologicalGroup B₀]
variable [Finite A] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable [CompactSpace B₀] [T2Space B₀] [TotallyDisconnectedSpace B₀]

/-- Exactness of kernel invariants, using finite-quotient averaging. -/
private theorem kernelFixed_preservesHomology
    (π : G →* B₀) (hπ : Function.Surjective π) (hc : Continuous π)
    (l s : ℕ) (hA : (l ^ s : ℕ) • (1 : A) = 0)
    (hcop : ∀ (Q : Type u) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
      [Finite Q] (f : π.ker →* Q), Continuous f → Function.Surjective f →
        Nat.Coprime l (Nat.card Q)) :
    let hG := (discreteModules_abelian.{u, v, w} G A).choose
    let hB := (discreteModules_abelian.{0, v, max u w} B₀ A).choose
    let := hG
    let := hB
    letI : Preadditive (DiscreteContinuousRep.{v, u, max u w} A G) := hG.toPreadditive
    letI : Preadditive (DiscreteContinuousRep.{v, 0, max u w} A B₀) := hB.toPreadditive
    letI : (kernelFixedFunctor (A := A) π hπ hc).IsRightAdjoint :=
      ⟨_, ⟨discreteInflationAdjunction (A := A) π hπ hc⟩⟩
    (kernelFixedFunctor (A := A) π hπ hc :
      DiscreteContinuousRep.{v, u, max u w} A G ⥤
        DiscreteContinuousRep.{v, 0, max u w} A B₀).PreservesHomology := by
  dsimp only
  let hG := (discreteModules_abelian.{u, v, w} G A).choose
  let hB := (discreteModules_abelian.{0, v, max u w} B₀ A).choose
  let := hG
  let := hB
  letI : Preadditive (DiscreteContinuousRep.{v, u, max u w} A G) := hG.toPreadditive
  letI : Preadditive (DiscreteContinuousRep.{v, 0, max u w} A B₀) := hB.toPreadditive
  have pG := (discreteModules_abelian.{u, v, w} G A).choose_spec
  have pB := (discreteModules_abelian.{0, v, max u w} B₀ A).choose_spec
  obtain ⟨h0G, _, hlimG, _, hexG⟩ := pG
  obtain ⟨h0B, _, hlimB, _, hexB⟩ := pB
  let V := kernelFixedFunctor (A := A) π hπ hc
  let adj := discreteInflationAdjunction (A := A) π hπ hc
  let : V.IsRightAdjoint := ⟨_, ⟨adj⟩⟩
  have hmap : ∀ S : ShortComplex (DiscreteContinuousRep.{v, u, max u w} A G),
      S.Exact → (S.map V).Exact := by
    intro S hS
    apply (hexB (S.map V)).mpr
    rw [ShortComplex.moduleCat_exact_iff]
    intro y hy
    have hex := (hexG S).mp hS
    obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).mp hex y.val
      (congrArg Subtype.val hy)
    obtain ⟨x0, hx0⟩ := kernelFixed_exact_lift π hc l s hA hcop S.f y x hx
    exact ⟨x0, Subtype.ext hx0⟩
  convert! Functor.preservesHomology_of_map_exact V ?_ using 1
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _
  · convert! hmap using 1
    rw [Subsingleton.elim
      (@Preadditive.preadditiveHasZeroMorphisms _ _ hG.toPreadditive)
      (ObjectProperty.instHasZeroMorphismsFullSubcategory _),
      Subsingleton.elim
        (@Preadditive.preadditiveHasZeroMorphisms _ _ hB.toPreadditive)
        (ObjectProperty.instHasZeroMorphismsFullSubcategory _)]

/-- Inflation preserves monos, so its right adjoint preserves injectives. -/
private theorem kernelFixed_preservesInjectives
    (π : G →* B₀) (hπ : Function.Surjective π) (hc : Continuous π) :
    let hG := (discreteModules_abelian.{u, v, w} G A).choose
    let hB := (discreteModules_abelian.{0, v, max u w} B₀ A).choose
    letI := hG
    letI := hB
    (kernelFixedFunctor (A := A) π hπ hc :
      DiscreteContinuousRep.{v, u, max u w} A G ⥤
        DiscreteContinuousRep.{v, 0, max u w} A B₀).PreservesInjectiveObjects := by
  dsimp only
  let hG := (discreteModules_abelian.{u, v, w} G A).choose
  let hB := (discreteModules_abelian.{0, v, max u w} B₀ A).choose
  let := hG
  let := hB
  obtain ⟨h0B, _, hlimB, _, _⟩ :=
    (discreteModules_abelian.{0, v, max u w} B₀ A).choose_spec
  letI : (discreteInflation (A := A) π hc).PreservesMonomorphisms := ⟨by
    intro M N f hf
    have hm : Mono ((discreteUnderlying (A := A) (G := B₀)).map f) := inferInstance
    have hi := (ModuleCat.mono_iff_injective _).mp hm
    constructor
    intro Z a b hab
    ext x
    apply hi
    exact congrArg (fun k ↦ k.hom.hom x) hab⟩
  apply Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (discreteInflationAdjunction (A := A) π hπ hc)


end Exactness

set_option linter.style.haveILetI false in
/-- Cohomology is unchanged by taking invariants under a prime-to-coefficient kernel.

Proof: construct the fixed submodule and descend the action through the surjection.
The quotient map of compact Hausdorff spaces makes this action discrete continuous.
For exactness, an open normal subgroup of the kernel fixes a chosen lift. Average its
finite quotient orbit and multiply by the Bezout coefficient of its order and `l^s`.
This is a fixed lift, since `l^s` kills every coefficient module. Exactness is detected
on underlying modules. Inflation is left adjoint to kernel invariants and preserves
monomorphisms, so invariants preserve injectives. Their composite with quotient
invariants is naturally isomorphic to all invariants, using the actual fixed submodules.
Apply kernel invariants to an injective resolution and use this natural isomorphism
termwise. Both cohomology functors are the homology of the resulting same complex.

Source: blueprint main-20261015, `lem-exc-dvr-galois.proof.md`, third paragraph;
DAG proof steps 3--5 of `lem-exc-dvr-galois`.
(blueprint: lem-exc-kernel-invariants-cohomology) -/
theorem kernelFixed_cohomology_iso [Finite A]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (B₀ : Type) [Group B₀] [TopologicalSpace B₀] [IsTopologicalGroup B₀]
    [CompactSpace B₀] [T2Space B₀] [TotallyDisconnectedSpace B₀]
    (π : G →* B₀) (hπ : Function.Surjective π) (hc : Continuous π)
    (l s : ℕ) (hA : (l ^ s : ℕ) • (1 : A) = 0)
    (hcop : ∀ (Q : Type u) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
      [Finite Q] (f : π.ker →* Q), Continuous f → Function.Surjective f →
        Nat.Coprime l (Nat.card Q))
    (M : DiscreteContinuousRep.{v, u, max u w} A G) (q : ℕ) :
    Nonempty ((discreteContinuousCohomologyFunctor.{u, v, w} G A q).obj M ≅
      (discreteContinuousCohomologyFunctor.{0, v, max u w} B₀ A q).obj
        (kernelFixedDiscreteRep π hπ hc M)) := by
  classical
  let hG := (discreteModules_abelian.{u, v, max u w} G A).choose
  let hB := (discreteModules_abelian.{0, v, max u w} B₀ A).choose
  letI := hG
  letI := hB
  letI : Preadditive (DiscreteContinuousRep.{v, u, max u w} A G) := hG.toPreadditive
  letI : Preadditive (DiscreteContinuousRep.{v, 0, max u w} A B₀) := hB.toPreadditive
  letI : Preadditive (ModuleCat.{max u w} A) :=
    (inferInstance : Abelian (ModuleCat.{max u w} A)).toPreadditive
  letI := (discreteModules_abelian.{u, v, max u w} G A).choose_spec.choose_spec.1
  letI := (discreteModules_abelian.{0, v, max u w} B₀ A).choose_spec.choose_spec.1
  let cG := continuousCochains_derived_invariants.{u, v, w} G A
  let cB := continuousCochains_derived_invariants.{0, v, max u w} B₀ A
  let VG := cG.choose
  let VB := cB.choose
  letI : VG.Additive := cG.choose_spec.choose
  letI : VB.Additive := cB.choose_spec.choose
  obtain ⟨tG, htG, _⟩ := cG.choose_spec.choose_spec
  obtain ⟨tB, htB, _⟩ := cB.choose_spec.choose_spec
  let T := kernelFixedFunctor (A := A) π hπ hc
  letI : T.IsRightAdjoint := ⟨_, ⟨discreteInflationAdjunction π hπ hc⟩⟩
  letI : T.Additive := Functor.additive_of_preserves_binary_products T
  letI : Limits.HasZeroMorphisms (DiscreteContinuousRep.{v, u, max u w} A G) :=
    @Preadditive.preadditiveHasZeroMorphisms _ _ hG.toPreadditive
  letI : Limits.HasZeroMorphisms (DiscreteContinuousRep.{v, 0, max u w} A B₀) :=
    @Preadditive.preadditiveHasZeroMorphisms _ _ hB.toPreadditive
  letI : T.PreservesHomology := by
    convert! kernelFixed_preservesHomology π hπ hc l s hA hcop using 1 <;>
      exact Subsingleton.elim _ _
  letI : T.PreservesInjectiveObjects := kernelFixed_preservesInjectives π hπ hc
  letI : Limits.PreservesFiniteLimits T := T.preservesFiniteLimits_of_preservesHomology
  letI : Limits.PreservesFiniteColimits T := T.preservesFiniteColimits_of_preservesHomology
  let e : VG ≅ T ⋙ VB := NatIso.ofComponents (fun N ↦
    ((tG N).trans ((kernelFixed_allFixed_equiv π hπ hc N).trans
      (tB (T.obj N)).symm)).toModuleIso) (by
    intro N P f
    ext x
    apply (tB (T.obj P)).injective
    apply Subtype.ext
    apply Subtype.ext
    change ((tB (T.obj P)) ((tB (T.obj P)).symm
      (kernelFixed_allFixed_equiv π hπ hc P (tG P ((VG.map f).hom x))))).val.val =
      ((tB (T.obj P)) ((VB.map (T.map f)).hom
        ((tB (T.obj N)).symm (kernelFixed_allFixed_equiv π hπ hc N (tG N x))))).val.val
    have hleft := (tB (T.obj P)).apply_symm_apply
      (kernelFixed_allFixed_equiv π hπ hc P (tG P ((VG.map f).hom x)))
    have hright := htB (T.obj N) (T.obj P) (T.map f)
      ((tB (T.obj N)).symm (kernelFixed_allFixed_equiv π hπ hc N (tG N x)))
    have hcancel := (tB (T.obj N)).apply_symm_apply
      (kernelFixed_allFixed_equiv π hπ hc N (tG N x))
    have hright' := (congrArg Subtype.val hright).trans
      (congrArg (fun m ↦ ((T.map f).hom.hom m.val).val) hcancel)
    exact (congrArg (fun m ↦ m.val.val) hleft).trans
      ((htG N P f x).trans hright'.symm))
  let I := injectiveResolution M
  let J : InjectiveResolution (T.obj M) :=
    { cocomplex := (T.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
      ι := T.mapResolution I.ι
      injective n := T.injective_obj _ }
  change Nonempty ((VG.rightDerived q).obj M ≅ (VB.rightDerived q).obj (T.obj M))
  exact ⟨Functor.rightDerivedObjIsoOfIso e q M ≪≫
    I.isoRightDerivedObj (T ⋙ VB) q ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{max u w} A) (.up ℕ) q).mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ VB)) (.up ℕ)).symm.app
        I.cocomplex) ≪≫
    (J.isoRightDerivedObj VB q).symm⟩

end Rep
