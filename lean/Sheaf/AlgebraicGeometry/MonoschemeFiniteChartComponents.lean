module

public import Sheaf.AlgebraicGeometry.MonoschemeToricRealization
public import Sheaf.AlgebraicGeometry.FineFanBlowup
public import Mathlib.Topology.Connected.Basic
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober

import Sheaf.AlgebraicGeometry.MonoidPrimeMinimalNeighborhood
import Sheaf.AlgebraicGeometry.MonoschemeGenericChartCompletion
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.GroupTheory.MonoidLocalization.Finite
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Topology.Connected.Clopen

/-!
# Components and dense generic tori of finite-chart monoschemes

Source: ILO, Travaux de Gabber, Exposé VIII, Remarks 3.1.4 and 3.1.10(ii),
3.1.9, Proposition 3.2.2, 3.2.4, and Lemma 3.2.12(ii), pp.98--104
(blueprint: lem-trf-monoscheme-finite-chart-components).

The affine monoid on an affine open is its intrinsic monoid of sections. Products
encode the additive sums in the source; the empty product is the identity.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Monoscheme

private theorem prime_ext {P : Type u} [CommMonoid P]
    {x y : FineFan.MonoidPrime P} (h : x.carrier = y.carrier) : x = y := by
  cases x
  cases y
  congr 1
  exact SetLike.coe_injective h

private theorem finite_monoidPrime (P : Type u) [CommMonoid P]
    (hP : FineFan.IsFine P) : Finite (FineFan.MonoidPrime P) := by
  classical
  obtain ⟨s, hs⟩ := hP.1.fg_top
  let e : Fin s.card → P := fun i ↦ (s.equivFin.symm i).val
  have he : Submonoid.closure (Set.range e) = ⊤ := by
    have hr : Set.range e = (s : Set P) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact (s.equivFin.symm i).property
      · intro hx
        exact ⟨s.equivFin ⟨x, hx⟩, by simp [e]⟩
    rw [hr, hs]
  let f : FineFan.MonoidPrime P → Set (Fin s.card) := fun x ↦ {i | e i ∉ x.carrier}
  apply Finite.of_injective f
  intro x y hxy
  have hx := FineFan.monoidPrime_minimal_neighborhood P hP s.card e he x _ rfl
  have hy := FineFan.monoidPrime_minimal_neighborhood P hP s.card e he y _ rfl
  have hsel : {a : P | ∃ i : Fin s.card, e i ∉ x.carrier ∧ e i = a} =
      {a : P | ∃ i : Fin s.card, e i ∉ y.carrier ∧ e i = a} := by
    ext a
    constructor <;> rintro ⟨i, hi, rfl⟩
    · exact ⟨i, (Set.ext_iff.mp hxy i).mp hi, rfl⟩
    · exact ⟨i, (Set.ext_iff.mp hxy i).mpr hi, rfl⟩
  have hc : Submonoid.closure {a : P | a ∉ x.carrier} =
      Submonoid.closure {a : P | a ∉ y.carrier} := by
    rw [← hx.2.2.2.1, hsel, hy.2.2.2.1]
  apply prime_ext
  have hsets := congrArg (fun S : Submonoid P ↦ (S : Set P)) hc
  rw [hx.1, hy.1] at hsets
  ext a
  exact not_iff_not.mp (Set.ext_iff.mp hsets a)

private noncomputable def chartHomeomorph {M : Fine.{u}} (U : AffineOpens M)
    (P : CommMonCat.{u}) (h : M.space.restrict U.1.isOpenEmbedding ≅ affine P) :
    U.1 ≃ₜ FineFan.MonoidPrime P :=
  TopCat.homeoOfIso ((SheafedSpace.forget CommMonCat).mapIso h)

private theorem finite_space (M : Fine.{u}) : Finite M.space := by
  classical
  obtain ⟨n, c, hc⟩ := M.finiteCover
  have hf (i : Fin n) : Finite (c i).openSet := by
    have := finite_monoidPrime (c i).monoid (c i).fine
    let e : (c i).openSet ≃ₜ FineFan.MonoidPrime (c i).monoid :=
      TopCat.homeoOfIso ((SheafedSpace.forget CommMonCat).mapIso (c i).iso)
    exact Finite.of_injective e e.injective
  have (i : Fin n) : Finite (c i).openSet := hf i
  apply Finite.of_surjective (fun z : Σ i : Fin n, (c i).openSet ↦ (z.2 : M.space))
  intro x
  obtain ⟨i, hi⟩ := hc x
  exact ⟨⟨i, x, hi⟩, rfl⟩

private def emptyPrime (P : Type u) [CommMonoid P] : FineFan.MonoidPrime P where
  carrier := ∅
  smul_mem' := by simp
  proper := by
    intro h
    have h1 : (1 : P) ∈ (∅ : Set P) := h.symm ▸ Set.mem_univ 1
    exact h1
  complement_mul := by simp

private theorem emptyPrime_specializes {P : Type u} [CommMonoid P]
    (x : FineFan.MonoidPrime P) : emptyPrime P ⤳ x := by
  apply specializes_iff_forall_open.mpr
  intro S hS hx
  change TopologicalSpace.GenerateOpen _ S at hS
  induction hS with
  | basic S hS =>
    obtain ⟨a, rfl⟩ := hS
    change a ∉ (∅ : Set P)
    exact fun h ↦ h
  | univ => trivial
  | inter S T hS hT ihS ihT => exact ⟨ihS hx.1, ihT hx.2⟩
  | sUnion S hS ih =>
    obtain ⟨T, hT, hx⟩ := hx
    exact ⟨T, hT, ih T hT hx⟩

private theorem monoidPrime_t0 (P : Type u) [CommMonoid P] :
    T0Space (FineFan.MonoidPrime P) := by
  refine ⟨fun x y h ↦ prime_ext ?_⟩
  ext a
  exact not_iff_not.mp (h.mem_open_iff (FineFan.basicOpen a).isOpen)

private theorem space_t0 (M : Fine.{u}) : T0Space M.space := by
  apply T0Space.of_open_cover
  intro x
  obtain ⟨n, c, hc⟩ := M.finiteCover
  obtain ⟨i, hi⟩ := hc x
  have := monoidPrime_t0 (c i).monoid
  let e : (c i).openSet ≃ₜ FineFan.MonoidPrime (c i).monoid :=
    TopCat.homeoOfIso ((SheafedSpace.forget CommMonCat).mapIso (c i).iso)
  exact ⟨(c i).openSet, hi, (c i).openSet.isOpen, e.symm.t0Space⟩

private theorem affineOpen_irreducible (M : Fine.{u}) (U : AffineOpens M) :
    IsIrreducible (U.1 : Set M.space) := by
  obtain ⟨P, _, ⟨h⟩⟩ := U.2
  let e := chartHomeomorph U P h
  have hg : IsGenericPoint (emptyPrime P) (Set.univ : Set (FineFan.MonoidPrime P)) :=
    isGenericPoint_iff_specializes.mpr fun x ↦
      ⟨fun _ ↦ Set.mem_univ x, fun _ ↦ emptyPrime_specializes x⟩
  have hirr := hg.isIrreducible.image (fun x ↦ (e.symm x).val)
    (continuous_subtype_val.comp e.symm.continuous).continuousOn
  have himage : (fun x ↦ (e.symm x).val) '' Set.univ = (U.1 : Set M.space) := by
    ext x
    constructor
    · rintro ⟨y, _, rfl⟩
      exact (e.symm y).property
    · intro hx
      refine ⟨e ⟨x, hx⟩, Set.mem_univ _, ?_⟩
      exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
  rwa [himage] at hirr

private theorem affineOpen_component (M : Fine.{u}) (hM : M.IsTorsionFree)
    (U : AffineOpens M) : ∃ C : ToricComponent M,
      ∀ x : M.space, x ∈ U.1 → ConnectedComponents.mk x = C.component := by
  obtain ⟨x, hx⟩ := (affineOpen_irreducible M U).nonempty
  refine ⟨⟨ConnectedComponents.mk x, fun z _ ↦ hM z⟩, fun y hy ↦ ?_⟩
  exact ConnectedComponents.coe_eq_coe'.mpr
    ((affineOpen_irreducible M U).isConnected.subset_connectedComponent hx hy)

private theorem exists_affineOpen (M : Fine.{u}) (x : M.space) :
    ∃ U : AffineOpens M, x ∈ U.1 := by
  obtain ⟨n, c, hc⟩ := M.finiteCover
  obtain ⟨i, hi⟩ := hc x
  exact ⟨⟨(c i).openSet, (c i).monoid, (c i).fine, ⟨(c i).iso⟩⟩, hi⟩

private theorem affineOpen_generic (M : Fine.{u}) (U : AffineOpens M) :
    ∃ η : M.space, η ∈ U.1 ∧ ∀ x : M.space, x ∈ U.1 → η ⤳ x := by
  obtain ⟨P, _, ⟨h⟩⟩ := U.2
  let e := chartHomeomorph U P h
  refine ⟨(e.symm (emptyPrime P)).val, (e.symm (emptyPrime P)).property, ?_⟩
  intro x hx
  have hspec := (emptyPrime_specializes (e ⟨x, hx⟩)).map e.symm.continuous
  simpa using hspec.map continuous_subtype_val

private theorem component_generic (M : Fine.{u}) (hM : M.IsTorsionFree)
    (C : ToricComponent M) :
    IsGenericPoint C.genericPoint {x : M.space | ConnectedComponents.mk x = C.component} := by
  have hη : ConnectedComponents.mk C.genericPoint = C.component :=
    (Classical.choose_spec (existsUnique_componentGenericPoint C).exists).1
  apply isGenericPoint_iff_specializes.mpr
  intro x
  constructor
  · intro h
    have hmem : x ∈ connectedComponent C.genericPoint :=
      (isConnected_singleton.closure.subset_connectedComponent (subset_closure (by simp)))
        h.mem_closure
    exact (ConnectedComponents.coe_eq_coe'.mpr hmem).trans hη
  · intro hx
    obtain ⟨U, hU⟩ := exists_affineOpen M x
    obtain ⟨D, hD⟩ := affineOpen_component M hM U
    have heq : D.component = C.component := (hD x hU).symm.trans hx
    let V : ComponentAffineOpens C := ⟨U, fun y hy ↦ (hD y hy).trans heq⟩
    obtain ⟨η, hηU, hηspec⟩ := affineOpen_generic M U
    have hηC : ConnectedComponents.mk η = C.component := V.2 η hηU
    have heqη : η = C.genericPoint := by
      apply (existsUnique_componentGenericPoint C).unique
      · refine ⟨hηC, fun W ↦ ?_⟩
        exact (hηspec C.genericPoint (C.generic V)).mem_open W.1.1.isOpen (C.generic W)
      · exact Classical.choose_spec (existsUnique_componentGenericPoint C).exists
    rw [← heqη]
    exact hηspec x hU

private theorem component_clopen (M : Fine.{u}) (hM : M.IsTorsionFree)
    (C : ToricComponent M) :
    IsClopen {x : M.space | ConnectedComponents.mk x = C.component} := by
  refine ⟨(component_generic M hM C).isClosed, isOpen_iff_mem_nhds.mpr ?_⟩
  intro x hx
  obtain ⟨U, hU⟩ := exists_affineOpen M x
  obtain ⟨D, hD⟩ := affineOpen_component M hM U
  have heq : D.component = C.component := (hD x hU).symm.trans hx
  exact Filter.mem_of_superset (U.1.isOpen.mem_nhds hU)
    (fun y hy ↦ (hD y hy).trans heq)

/-- Finite topology, unique maximal generalizations, and clopen irreducible components.
Source: ILO VIII, Remarks 3.1.4(i)--(ii), 3.1.10(ii), pp.98--100
(blueprint: lem-trf-monoscheme-finite-chart-components).

Proof: choose finite monoid generators on each of the finitely many charts. A prime
is determined by which generators lie in its complementary face
(lem-trf-monoid-prime-minimal-neighborhood), so each chart has finitely many points.
Its empty prime generalizes every point and has no proper generalization. Every
ambient generalization stays in any open chart containing the given point, so this
maximal generalization is unique independently of the chart. Charts having the same
maximal generalization form one open piece; its complement is the union of the
other charts. Each piece has a generic point, hence is irreducible and connected.
No connected or irreducible subset can cross this clopen partition. Thus the pieces
are exactly both kinds of component (def-weil-connected-scheme and
 def-weil-irreducible-components). The empty cover gives the empty partition. -/
theorem finite_chart_components (M : Fine.{u}) (hM : M.IsTorsionFree) :
    Finite M.space ∧ Finite (ConnectedComponents M.space) ∧
      (∀ x : M.space, ∃! η : M.space,
        η ⤳ x ∧ ∀ z : M.space, z ⤳ η → z = η) ∧
      (∀ C : ToricComponent M,
        IsClopen {x : M.space | ConnectedComponents.mk x = C.component} ∧
        IsGenericPoint C.genericPoint {x : M.space | ConnectedComponents.mk x = C.component} ∧
        IsIrreducible {x : M.space | ConnectedComponents.mk x = C.component} ∧
        ConnectedSpace {x : M.space // ConnectedComponents.mk x = C.component}) ∧
      Set.range (fun C : ToricComponent M ↦
        {x : M.space | ConnectedComponents.mk x = C.component}) =
          irreducibleComponents M.space ∧
      (∀ U : AffineOpens M, ∃ C : ToricComponent M,
        ∀ x : M.space, x ∈ U.1 → ConnectedComponents.mk x = C.component) := by
  classical
  have := finite_space M
  have := space_t0 M
  have hCfinite : Finite (ConnectedComponents M.space) :=
    Finite.of_surjective ConnectedComponents.mk ConnectedComponents.surjective_coe
  refine ⟨inferInstance, hCfinite, ?_, ?_, ?_, affineOpen_component M hM⟩
  · intro x
    let C : ToricComponent M := ⟨ConnectedComponents.mk x, fun z _ ↦ hM z⟩
    have hg := component_generic M hM C
    refine ⟨C.genericPoint, ⟨hg.specializes rfl, ?_⟩, ?_⟩
    · intro z hz
      have hη := hg.mem
      have hzmem : ConnectedComponents.mk z = C.component := by
        have hηz : C.genericPoint ∈ connectedComponent z :=
          ((isConnected_singleton (x := z)).closure.subset_connectedComponent
            (subset_closure (by simp))) hz.mem_closure
        exact (ConnectedComponents.coe_eq_coe'.mpr hηz).symm.trans hη
      exact (hz.antisymm (hg.specializes hzmem)).eq
    · intro η hη
      have hηC : ConnectedComponents.mk η = C.component := by
        have hmem : x ∈ connectedComponent η :=
          (isConnected_singleton.closure.subset_connectedComponent
            (subset_closure (by simp))) hη.1.mem_closure
        exact (ConnectedComponents.coe_eq_coe'.mpr hmem).symm
      exact (hη.2 C.genericPoint (hg.specializes hηC)).symm
  · intro C
    have hg := component_generic M hM C
    exact ⟨component_clopen M hM C, hg, hg.isIrreducible,
      isConnected_iff_connectedSpace.mp hg.isIrreducible.isConnected⟩
  · ext S
    constructor
    · rintro ⟨C, rfl⟩
      have hg := component_generic M hM C
      refine ⟨hg.isIrreducible, ?_⟩
      intro T hT hST x hx
      have hTC := hT.isConnected.subset_connectedComponent (hST hg.mem) hx
      exact (ConnectedComponents.coe_eq_coe'.mpr hTC).trans hg.mem
    · intro hS
      obtain ⟨x, hx⟩ := hS.1.nonempty
      let C : ToricComponent M := ⟨ConnectedComponents.mk x, fun z _ ↦ hM z⟩
      have hSC : S ⊆ {y : M.space | ConnectedComponents.mk y = C.component} :=
        fun y hy ↦ ConnectedComponents.coe_eq_coe'.mpr
          (hS.1.isConnected.subset_connectedComponent hx hy)
      refine ⟨C, ?_⟩
      exact Set.Subset.antisymm (hS.2 (component_generic M hM C).isIrreducible hSC) hSC


/-- Generic stalks are finite free lattices, canonically the chart group completions;
chart algebras are domains generated by the monomials of any monoid generators.
Source: ILO VIII 3.1.4(i), 3.1.9, 3.2.4 and Lemma 3.2.12(ii), pp.98--104
(blueprint: lem-trf-monoscheme-finite-chart-components).

Proof: the smallest neighborhood of the empty prime has sections P^gp by
lem-trf-monoid-prime-minimal-neighborhood. Its germ map therefore identifies P^gp
with the generic stalk, canonically and compatibly with restriction. This stalk
is already a group, so its completion changes nothing. Chart generators generate
its completion as a group; hM gives torsion-freeness. Apply
lem-trf-fg-torsionfree-group-free for a finite integral basis. Fineness gives
cancellation, and torsion-freeness gives unique sums by
lem-trf-affine-monoid-unique-sums. The domain assertion follows from
lem-trf-unique-sums-algebra-domain. Finally e^(sum n_i p_i) is the product of
(e^p_i)^n_i, and every monoid-algebra element is a finite linear combination
of monomials. These arguments include the zero-rank lattice and empty list. -/
theorem finite_chart_components_algebra (k : Type u) [Field k]
    (M : Fine.{u}) (hM : M.IsTorsionFree) :
    ∀ C : ToricComponent M,
      (∃ e : FineFan.stalk M.space.presheaf C.genericPoint ≃* C.lattice,
        e.toMonoidHom = Algebra.GrothendieckGroup.of) ∧
      (∃ r : ℕ, Nonempty (C.lattice ≃* Multiplicative (Fin r → ℤ))) ∧
      ∀ U : ComponentAffineOpens C,
        (∃ e : Algebra.GrothendieckGroup (M.space.presheaf.obj (op U.1.1)) ≃* C.lattice,
          ∀ p, e (Algebra.GrothendieckGroup.of p) = degree C U p) ∧
        IsDomain (MonoidAlgebra k (M.space.presheaf.obj (op U.1.1))) ∧
        ∀ (n : ℕ) (p : Fin n → M.space.presheaf.obj (op U.1.1)),
          Submonoid.closure (Set.range p) = ⊤ →
          Algebra.adjoin k (Set.range (fun i ↦ MonoidAlgebra.of k _ (p i))) = ⊤ := by
  classical
  intro C
  obtain ⟨hgeneric, hchart⟩ := generic_chart_completion M C
  have htf : IsMulTorsionFree C.lattice := by
    refine ⟨fun {n} hn x y hxy ↦ ?_⟩
    change x ^ n = y ^ n at hxy
    have hdiv : (x / y) ^ n = 1 := by
      rw [div_pow]
      exact div_eq_one.mpr hxy
    exact div_eq_one.mp (hM C.genericPoint (x / y) n (Nat.pos_of_ne_zero hn) hdiv)
  let := htf
  have hrank : ∃ r : ℕ, Nonempty (C.lattice ≃* Multiplicative (Fin r → ℤ)) := by
    obtain ⟨U, hU⟩ := exists_affineOpen M C.genericPoint
    obtain ⟨D, hD⟩ := affineOpen_component M hM U
    have hη := (component_generic M hM C).mem
    let V : ComponentAffineOpens C :=
      ⟨U, fun x hx ↦ (hD x hx).trans ((hD C.genericPoint hU).symm.trans hη)⟩
    obtain ⟨hP, e, _he⟩ := hchart V
    let := hP.1
    let : Monoid.FG C.lattice := Monoid.fg_of_surjective e.toMonoidHom e.surjective
    let b := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := Additive C.lattice)
    exact ⟨b.1, ⟨AddEquiv.toMultiplicativeRight b.2.equivFun.toAddEquiv⟩⟩
  refine ⟨hgeneric, hrank, ?_⟩
  intro U
  obtain ⟨hP, e, he⟩ := hchart U
  let P := M.space.presheaf.obj (op U.1.1)
  let : Monoid.FG P := hP.1
  let : CancelCommMonoid P := hP.2.cancelCommMonoid Algebra.GrothendieckGroup.of
    (map_one _) (fun x y ↦ map_mul _ x y) (fun x n ↦ map_pow _ x n)
  have hdegree : Function.Injective (degree C U) := by
    intro x y hxy
    apply hP.2
    apply e.injective
    simpa only [he] using hxy
  let : IsMulTorsionFree P := ⟨fun {n} hn x y hxy ↦ hdegree
    ((pow_left_inj hn).mp (by simpa only [map_pow] using congrArg (degree C U) hxy))⟩
  refine ⟨⟨e, he⟩, inferInstance, ?_⟩
  intro n p hp
  let A := Algebra.adjoin k (Set.range (fun i ↦ MonoidAlgebra.of k P (p i)))
  have hof (q : P) : MonoidAlgebra.of k P q ∈ A := by
    have hq : q ∈ Submonoid.closure (Set.range p) := hp.symm ▸ Submonoid.mem_top q
    induction hq using Submonoid.closure_induction with
    | mem q hq =>
      obtain ⟨i, rfl⟩ := hq
      exact Algebra.subset_adjoin ⟨i, rfl⟩
    | one => simpa only [map_one] using A.one_mem
    | mul x y _ _ hx hy => simpa only [map_mul] using A.mul_mem hx hy
  apply top_unique
  intro f
  have hf : f ∈ A := by
    induction f using MonoidAlgebra.induction_on with
    | of q => exact hof q
    | add x y hx hy => exact A.add_mem hx hy
    | smul r x hx => exact A.smul_mem hx r
  exact fun _ ↦ hf


/-- Inverting the product of the generators gives the generic lattice and its algebra.
The fraction formula and the common ambient torus embedding fix the canonical maps.
Source: ILO VIII 3.1.2--3.1.4, Proposition 3.2.2 and 3.2.4, pp.98,103
(blueprint: lem-trf-monoscheme-finite-chart-components).

Proof: write a as the sum of the generators. The inverse of p_i in P-Na is
(sum of the other generators)-a, so P-Na=P^gp. The prime-face criterion from
lem-trf-monoid-prime-minimal-neighborhood also gives D(a)={eta}; for an empty
list P is the zero monoid and a=0. Embed k[P] into k[L] by extension of finite
coefficient functions by zero. The monomial e^a becomes invertible, so the
localization-away fraction rules (def-weil-ring-localization-away) give the map
f/(e^a)^m to f*e^(-ma). It is injective by the coefficient embedding and
invertibility, and surjective since every l in L is p-ma. It is a k-algebra
isomorphism with the displayed formula. Further localization commutes with it:
all maps agree on monomials and their inverses. By
lem-weil-pbc-affine-open-section-vanishing-prime its Spec image is D(e^a).
The open {eta} lies in every overlap in its component, and the restriction maps
induce the identity on its intrinsic stalk. Thus the chartwise maps glue to the
same torusEmbedding, as prescribed by def-trf-monoscheme-toric-realization. -/
theorem finite_chart_components_localization (k : Type u) [Field k]
    (M : Fine.{u}) (hM : M.IsTorsionFree) (C : ToricComponent M)
    (U : ComponentAffineOpens C) (n : ℕ)
    (p : Fin n → M.space.presheaf.obj (op U.1.1))
    (hp : Submonoid.closure (Set.range p) = ⊤) :
    Algebra.faceLocalization (M.space.presheaf.obj (op U.1.1))
      (Submonoid.powers (∏ i, p i)) = ⊤ ∧
    (∃ e : Localization.Away (MonoidAlgebra.of k _ (∏ i, p i)) ≃ₐ[k]
        MonoidAlgebra k C.lattice,
      ∀ (q : M.space.presheaf.obj (op U.1.1)) (m : ℕ),
        e (IsLocalization.mk' (M := Submonoid.powers (MonoidAlgebra.of k _ (∏ i, p i)))
          _ (MonoidAlgebra.of k _ q)
          ⟨(MonoidAlgebra.of k _ (∏ i, p i)) ^ m, ⟨m, rfl⟩⟩) =
            MonoidAlgebra.of k C.lattice
              (degree C U q * (degree C U (∏ i, p i)) ^ (-(m : ℤ)))) ∧
    Set.range (Spec.map (CommRingCat.ofHom
      (MonoidAlgebra.mapDomainRingHom k (degree C U)))) =
        (PrimeSpectrum.basicOpen (MonoidAlgebra.of k _ (∏ i, p i))).1 ∧
    Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom k (degree C U))) ≫
      realizationι k M U.1 = torusEmbedding k C ∧
    (∀ (V : ComponentAffineOpens C) (h : V.1.1 ≤ U.1.1),
      (MonoidAlgebra.mapDomainRingHom k (degree C V)).comp
        (MonoidAlgebra.mapDomainRingHom k
          (M.space.presheaf.map (homOfLE h).op).hom) =
            MonoidAlgebra.mapDomainRingHom k (degree C U)) := by
  sorry

/-- Realization respects the finite clopen component decomposition, with integral
components and one nonempty dense irreducible torus open in each component.
Source: ILO VIII Proposition 3.2.2 and 3.2.4, Lemma 3.2.12(ii), pp.103--104
(blueprint: lem-trf-monoscheme-finite-chart-components).

Proof: charts from distinct monoid components have no intersection. The realization
quotient and matching-section sheaf therefore form their coproduct, and each summand
is clopen. The localization result identifies the common generic open in all charts.
Its group algebra is a nonzero domain. By
lem-weil-pbc-spec-irreducible-closed-subsets-primes, the zero prime in each domain
chart is generic and lies in the monomial basic open, so the torus is nonempty,
irreducible and dense in each chart and hence in its component. A space with a dense
irreducible subspace is irreducible. Each chart domain is reduced by
lem-weil-pbc-affine-scheme-reduced-iff; this passes to local rings and hence to the
whole realization and its components (def-pc-reduced-scheme). Reducedness and
irreducibility give integral components (def-pc-integral-scheme), exactly the
connected components since they form a clopen partition. The finite chart cover
and the finite monomial algebra generators give locally finite type and
quasi-compactness (def-weil-finite-type-morphism). An empty monoscheme glues an
empty diagram, giving an empty realization and no connected components. -/
theorem finite_chart_components_realization (k : Type u) [Field k]
    (M : Fine.{u}) (hM : M.IsTorsionFree) :
    IsReduced (realization k M) ∧
    LocallyOfFiniteType (realizationToBase k M) ∧ QuasiCompact (realizationToBase k M) ∧
    Finite (ConnectedComponents (realization k M)) ∧
    Nonempty (IsColimit (Cofan.mk (realization k M) (fun C ↦ componentι k C))) ∧
    (∃ e : ToricComponent M ≃ ConnectedComponents (realization k M),
      ∀ C, Set.range (componentι k C) = {x | ConnectedComponents.mk x = e C}) ∧
    (∀ C : ToricComponent M,
      IsClosed (componentOpen k C : Set (realization k M)) ∧
      IsIntegral (componentRealization k C) ∧
      IsOpenImmersion (torusEmbedding k C) ∧ Nonempty (torus k C) ∧
      IsIrreducible (Set.range (torusEmbedding k C)) ∧
      closure (Set.range (torusEmbedding k C)) = Set.range (componentι k C)) ∧
    (IsEmpty M.space → IsEmpty (realization k M) ∧
      IsEmpty (ConnectedComponents (realization k M))) := by
  sorry

end AlgebraicGeometry.Monoscheme
