/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
import WeilConjectures.AlgebraicGeometry.EtaleGenericResidueFieldModel
import Sheaf.TraceFormula.GenericFibreComponentLowerBound

/-! # Component lower bounds on an étale generic model

Source: literature/stacks-project/more-morphisms.tex, Tag 055A, proof,
using Tags 0551 and 0554, and varieties.tex, Tags 04KW and 04KX.
(blueprint: lem-trf-etale-generic-component-lower-bound).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicGeometry

/-- A prescribed finite étale generic field extension spreads to an irreducible étale
model on an open neighbourhood of whose generic point all ordinary and field-extended
fibres have at least the prescribed number of components.

Source: literature/stacks-project/more-morphisms.tex, Tag 055A, proof, the étale
model paragraph and the ordinary component lower bound; Tags 0551 and 0554;
varieties.tex, Tags 04KW and 04KX.
(blueprint: lem-trf-etale-generic-component-lower-bound).

Proof:
1. Apply exists_etale_generic_residue_field_model
   (lem-sbc-etale-generic-residue-field-model) to the prescribed finite étale map a.
   Its generic point has closure the whole model T, which is therefore irreducible.
   The residue-field point compatibility is exactly the equality supplied there.
2. Paste the defining pullback squares for the fibres and use r to identify the
   generic fibre of X times_S T with the supplied extension of the generic fibre.
   The inverse uses r.inv; uniqueness for pullbacks proves the inverse identities
   and the two displayed projection compatibilities.
3. Finite type is stable under arbitrary base change
   (lem-sfb-finite-type-composition-base-change, Stacks 01T4); thus q is finite type.
4. Apply generic_fibre_component_lower_bound
   (lem-trf-generic-fibre-component-lower-bound, Stacks 0554) to q and the transported
   generic component count. Its nonempty open contains the generic point: otherwise
   the closed complement contains that point and hence its closure, all of T.
5. For any t in this open and any field extension K of its residue field, the component
   map for field extension is surjective (lem-sfb-field-extension-irreducible-components,
   Stacks 04KW and 04KX). Lift n distinct ordinary components along this surjection;
   their lifts are distinct. For n = 0 both injections have empty domain. No geometric
   irreducibility, flatness, or Noetherian assumption is used.
-/
theorem etale_generic_component_lower_bound
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (hS : IsIrreducible (Set.univ : Set S))
    (η : S) (hη : IsGenericPoint η (Set.univ : Set S))
    {L : Type u} [Field L]
    (a : Spec (CommRingCat.of L) ⟶ Spec (S.residueField η))
    [IsFinite a] [Etale a] (n : ℕ)
    (hn : Nonempty
      (irreducibleComponents ↥(pullback (f.fiberToSpecResidueField η) a) ≃ Fin n)) :
    ∃ (T : Scheme.{u}) (g : T ⟶ S) (ξ : T)
      (r : Spec (T.residueField ξ) ≅ Spec (CommRingCat.of L)) (U : Set T),
      IsIrreducible (Set.univ : Set T) ∧ Etale g ∧
      IsGenericPoint ξ (Set.univ : Set T) ∧ g ξ = η ∧ IsOpen U ∧ ξ ∈ U ∧
      r.hom ≫ a ≫ S.fromSpecResidueField η = T.fromSpecResidueField ξ ≫ g ∧
      LocallyOfFiniteType (pullback.snd f g) ∧ QuasiCompact (pullback.snd f g) ∧
      (∃ e : (pullback.snd f g).fiber ξ ≅ pullback (f.fiberToSpecResidueField η) a,
        e.hom ≫ pullback.fst (f.fiberToSpecResidueField η) a ≫ f.fiberι η =
          (pullback.snd f g).fiberι ξ ≫ pullback.fst f g ∧
        e.hom ≫ pullback.snd (f.fiberToSpecResidueField η) a =
          (pullback.snd f g).fiberToSpecResidueField ξ ≫ r.hom) ∧
      (∀ t : T, t ∈ U →
        ∃ ι : Fin n → irreducibleComponents ↥((pullback.snd f g).fiber t),
          Function.Injective ι) ∧
      (∀ t : T, t ∈ U → ∀ (K : Type u) [Field K] [Algebra (T.residueField t) K],
        ∃ ι : Fin n → irreducibleComponents
            ↥(pullback ((pullback.snd f g).fiberToSpecResidueField t)
              (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) K)))),
          Function.Injective ι) := by
  sorry

end AlgebraicGeometry
