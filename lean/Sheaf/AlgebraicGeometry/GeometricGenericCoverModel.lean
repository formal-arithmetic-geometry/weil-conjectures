/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # A closed geometric cover on an étale model

Source: Stacks Project, Tags 0551, 054Y, 0559 and 054W.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry

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
