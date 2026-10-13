/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.GenericFibreClosedAvoidance

/-! # A closed geometric cover on an étale model

Source: Stacks Project, Tags 0551, 054Y, 0559 and 054W.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry

/-- The model and closed-cover part of the geometric generic cover construction.

Source: Stacks Project, Tag 055G, model and closure construction before the fibre
irreducibility and intersection arguments.  The construction spreads the finite
étale generic extension and takes reduced closures of the supplied closed cover.
The open shrinking in Tags 054Y and 0559 is omitted here and supplied by the
refinement theorem below.

(blueprint: new-lem-sbc-geometric-generic-cover-model-data) -/
theorem exists_geometric_generic_cover_model_data {X S : Scheme.{u}}
    [IrreducibleSpace S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    {L : Type u} [Field L]
    (yη : Spec (CommRingCat.of L) ⟶
      Spec (CommRingCat.of (S.residueField (genericPoint S))))
    [IsFinite yη] [Etale yη] {I : Type u} [Finite I]
    (A : I → Set ↥(pullback (f.fiberToSpecResidueField (genericPoint S)) yη))
    (hclosed : ∀ i, IsClosed (A i)) (hcover : (⋃ i, A i) = Set.univ)
    (hgeom : ∀ i, ∀ (E : Type u) (_ : Field E)
      (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of L)),
      IsIrreducible ((pullback.fst
        (pullback.snd (f.fiberToSpecResidueField (genericPoint S)) yη) z) ⁻¹' A i)) :
    ∃ (T : Scheme.{u}) (g : T ⟶ S) (η : T)
      (C : I → Set ↥(pullback f g)), Etale g ∧ IsGenericPoint η Set.univ ∧
      g η = genericPoint S ∧ (∀ i, IsClosed (C i)) ∧
      (⋃ i, C i) = Set.univ := by
  classical
  have _hclosed := hclosed
  have _hgeom := hgeom
  cases isEmpty_or_nonempty I with
  | inr hI =>
    let := hI
    refine ⟨S, 𝟙 S, genericPoint S, fun _ ↦ Set.univ, inferInstance,
      genericPoint_spec S, ?_, fun _ ↦ isClosed_univ, ?_⟩
    · simp
    · exact Set.eq_univ_of_forall (fun x ↦ Set.mem_iUnion.mpr
        ⟨Classical.choice hI, Set.mem_univ x⟩)
  | inl hI =>
    let := hI
    have hempty : IsEmpty ↥(pullback (f.fiberToSpecResidueField (genericPoint S)) yη) := by
      constructor
      intro x
      have hx : x ∈ ⋃ i, A i := hcover ▸ Set.mem_univ x
      simp at hx
    have hgeneric : f ⁻¹' {genericPoint S} ⊆ (∅ : Set X) ∪ ∅ := by
      intro x hx
      let a := (f.fiberHomeo (genericPoint S)).symm ⟨x, hx⟩
      have ha : a ∈ Set.range (pullback.fst
          (f.fiberToSpecResidueField (genericPoint S)) yη) := by
        rw [Scheme.Pullback.range_fst]
        exact Function.surjective_to_subsingleton yη _
      obtain ⟨b, _⟩ := ha
      exact (hempty.false b).elim
    obtain ⟨V, hV, hηV, hvanish⟩ := exists_open_generic_fibre_closed_avoidance
      f (genericPoint S) Set.univ isClosed_univ (by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        simpa using hgeneric hx.1)
    let U : S.Opens := ⟨V, hV⟩
    let η : U.toScheme := ⟨genericPoint S, hηV⟩
    have hη : IsGenericPoint η Set.univ := by
      apply isGenericPoint_iff_specializes.mpr
      intro t
      simp only [Set.mem_univ, iff_true]
      exact (subtype_specializes_iff _ _).mpr (genericPoint_specializes t.1)
    have hemptyU : IsEmpty ↥(pullback f U.ι) := by
      constructor
      intro x
      have hx : f (pullback.fst f U.ι x) ∈ V := by
        have he := congrArg (fun k : pullback f U.ι ⟶ S ↦ k x) pullback.condition
        simpa only [Scheme.Hom.comp_apply] using he ▸ (pullback.snd f U.ι x).2
      exact Set.disjoint_left.mp hvanish
        ⟨hx, by rw [genericPoint_closure]; trivial⟩ (Set.mem_univ _)
    refine ⟨U.toScheme, U.ι, η, fun _ ↦ ∅, inferInstance, hη, rfl,
      fun _ ↦ isClosed_empty, ?_⟩
    apply Set.eq_univ_of_forall
    intro x
    exact (hemptyU.false x).elim

/-- Spread the closed cover and geometric irreducibility, before spreading intersections.

Source: Stacks Project, Tag 055G, the model and closure construction preceding the
intersection-image argument; Tags 0551, 054Y, 0559 and 054W.
Proof: on an affine neighbourhood of the generic point, realize the supplied finite
separable extension by the monic-polynomial construction of Tag 0551. Localize away
from the image of the non-étale locus. The resulting model has one generic point
with residue field L. Form the pullback of X and take closures of the supplied A_i.
On the reduction of the model their reduced closed subschemes have the given generic
fibres. Tag 054Y shrinks the base so their union covers, and Tag 0559, once for each
index, shrinks it so their fibres are geometrically irreducible and nonempty.
Represent this open in the original model using the reduction homeomorphism, and
restrict the model to it. The resulting map to S is étale; its generic point still
maps to the original generic point. The pulled-back closed subsets cover the total
space and have the asserted geometrically irreducible traces on all field fibres.
Their generic traces identify with A_i, giving the generic intersection implication.
For an empty index type use Tag 054W to make the whole pulled-back total space empty;
the geometric irreducibility and intersection assertions are then vacuous.
No persistence of intersections at nongeneric points is asserted here.

(blueprint: lem-sbc-geometric-generic-cover-model) -/
theorem exists_geometric_generic_cover_model {X S : Scheme.{u}}
    [IrreducibleSpace S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    {L : Type u} [Field L]
    (yη : Spec (CommRingCat.of L) ⟶
      Spec (CommRingCat.of (S.residueField (genericPoint S))))
    [IsFinite yη] [Etale yη] {I : Type u} [Finite I]
    (A : I → Set ↥(pullback (f.fiberToSpecResidueField (genericPoint S)) yη))
    (hclosed : ∀ i, IsClosed (A i)) (hcover : (⋃ i, A i) = Set.univ)
    (hgeom : ∀ i, ∀ (E : Type u) (_ : Field E)
      (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of L)),
      IsIrreducible ((pullback.fst
        (pullback.snd (f.fiberToSpecResidueField (genericPoint S)) yη) z) ⁻¹' A i)) :
    ∃ (T : Scheme.{u}) (g : T ⟶ S) (η : T)
      (C : I → Set ↥(pullback f g)), Etale g ∧ IsGenericPoint η Set.univ ∧
      g η = genericPoint S ∧ (∀ i, IsClosed (C i)) ∧ (⋃ i, C i) = Set.univ ∧
      (∀ i t, ∀ (E : Type u) (_ : Field E)
        (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of (T.residueField t))),
        IsIrreducible ((pullback.fst
          ((pullback.snd f g).fiberToSpecResidueField t) z ≫
          (pullback.snd f g).fiberι t) ⁻¹' C i)) ∧
      ∀ i j, (A i ∩ A j).Nonempty →
        (C i ∩ C j ∩ (pullback.snd f g) ⁻¹' {η}).Nonempty := by sorry

end AlgebraicGeometry
