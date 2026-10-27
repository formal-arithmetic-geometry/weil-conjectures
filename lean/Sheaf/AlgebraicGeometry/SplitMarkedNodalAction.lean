module

public import Sheaf.AlgebraicGeometry.QuasiSplitNodalFibres
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.CategoryTheory.Endomorphism

/-! # Split marked nodal actions

Source: ILO, Travaux de Gabber, X Lemma 2.2 proof, p.149, with the split marked
dual-graph convention of the one-curve input
(blueprint: def-sfb-split-marked-nodal-action).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- Splitting of components, nodes and branches, and trivial action of point stabilizers
on vertices, edges, ends and marked legs. A self-node is permitted: its two ends are
the two normalization points above it. The condition on normalization automorphisms
uses their defining commutative square, so it applies to the uniquely induced lift
without choosing an action or an isomorphism of residue fields. These lifts exist by
functoriality of componentwise normalization under isomorphisms. No smoothness of an
individual component is imposed.
Source: ILO X Lemma 2.2 proof, p.149, the split marked one-curve convention
(blueprint: def-sfb-split-marked-nodal-action). -/
def IsSplitMarkedNodalAction {T S : Scheme.{u}} (f : T ⟶ S)
    {J : Type v} [Group J] (aT : J →* Aut T) (aS : J →* Aut S)
    (n : ℕ) (m : Fin n → (S ⟶ T)) : Prop :=
  HasQuasiSplitNodalFibres f ∧
    (∀ (y : S) (C : irreducibleComponents (f.fiber y)),
      GeometricallyIrreducible
        ((Scheme.IdealSheafData.vanishingIdeal
          ⟨C.1, isClosed_of_mem_irreducibleComponents _ C.2⟩).subschemeι ≫
            f.fiberToSpecResidueField y)) ∧
    ∀ (g : J) (y : S), (aS g).hom y = y →
      (∀ C : irreducibleComponents (f.fiber y),
        (aT g).hom '' (f.fiberι y '' C.1) = f.fiberι y '' C.1) ∧
      (∀ x : f.fiber y,
        (¬ ∃ U : (f.fiber y).Opens,
          x ∈ U ∧ Smooth (U.ι ≫ f.fiberToSpecResidueField y)) →
        (aT g).hom (f.fiberι y x) = f.fiberι y x ∧
          ∀ (b : Aut (f.fiber y)),
            b.hom ≫ f.fiberι y = f.fiberι y ≫ (aT g).hom →
            ∀ c : Aut (f.fiber y).reducedNormalization,
              c.hom ≫ (f.fiber y).fromReducedNormalization =
                (f.fiber y).fromReducedNormalization ≫ b.hom →
              ∀ z : (f.fiber y).reducedNormalization,
                (f.fiber y).fromReducedNormalization z = x → c.hom z = z) ∧
      ∀ i : Fin n, (aT g).hom (m i y) = m i y

end AlgebraicGeometry
