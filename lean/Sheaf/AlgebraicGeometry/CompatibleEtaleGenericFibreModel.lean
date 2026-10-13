/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # A compatible étale generic-fibre model

Source: Stacks Project, Tags 0551 and 055G.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry

/-- Spread a specified finite étale generic field extension with compatible fibres.

Source: Stacks Project, Tag 0551, proof, monic polynomial construction, and
Tag 055G, model construction. This does not construct a closed cover or assert
anything about nongeneric fibres.
Proof: choose an affine open through the generic point of S. Its nilradical is
prime. A primitive element of L over the generic residue field has separable
minimal polynomial. Scale the primitive element and clear denominators to lift
this polynomial to a monic polynomial over the affine ring. Its discriminant is
nonzero at the generic point. Invert it; the monic quotient is finite étale and
its generic fibre is Spec L. It has one generic point, since the generic quotient
is a field and the quotient is flat over the base. Restrict to an irreducible open
neighbourhood of that point if necessary. Compose its map with the affine open
inclusion to obtain g. The residue field at its generic point is identified with L,
compatibly with yη. Pullback pasting identifies the generic fibre of X times_S T
with the supplied geometric generic fibre. Compose this isomorphism with the
fibre inclusion to obtain a. It is an embedding and its range is the entire fibre
at η. For every field-valued map z to the residue field at η, the residue-field
identification supplies zL and pullback pasting supplies e. Commutativity of these
pullback squares gives the stated equality of maps into X times_S T. This works
also for an empty X; no point of its generic fibre is chosen.

(blueprint: lem-sbc-compatible-etale-generic-fibre-model) -/
theorem exists_compatible_etale_generic_fibre_model {X S : Scheme.{u}}
    [IrreducibleSpace S] (f : X ⟶ S)
    {L : Type u} [Field L]
    (yη : Spec (CommRingCat.of L) ⟶
      Spec (CommRingCat.of (S.residueField (genericPoint S))))
    [IsFinite yη] [Etale yη] :
    ∃ (T : Scheme.{u}) (g : T ⟶ S) (η : T)
      (a : pullback (f.fiberToSpecResidueField (genericPoint S)) yη ⟶ pullback f g),
      Etale g ∧ IsGenericPoint η Set.univ ∧ g η = genericPoint S ∧
      IsEmbedding a ∧ Set.range a = (pullback.snd f g) ⁻¹' {η} ∧
      ∀ (E : Type u) (_ : Field E)
        (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of (T.residueField η))),
        ∃ (zL : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of L))
          (e : pullback ((pullback.snd f g).fiberToSpecResidueField η) z ≅
            pullback (pullback.snd (f.fiberToSpecResidueField (genericPoint S)) yη) zL),
          e.hom ≫ pullback.fst _ zL ≫ a =
            pullback.fst _ z ≫ (pullback.snd f g).fiberι η := by sorry

end AlgebraicGeometry
