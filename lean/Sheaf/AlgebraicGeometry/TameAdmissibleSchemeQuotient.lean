/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.AdmissibleQuotientAffineIntegralCharts
import Sheaf.AlgebraicGeometry.FiniteSurjectiveAffineTargetNoetherian
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.RingTheory.TameInertiaSurjectiveGroupTrace
import Sheaf.RingTheory.TraceOneInvariantFiniteness

/-!
# Finite quotients of tame admissible actions

Source: ILO, Travaux de Gabber, Exposé VI 3.1--3.2 and proof 3.7(b), printed pp.73--75,
underlying scheme quotient (blueprint: lem-per-tame-admissible-scheme-quotient).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- A tame finite group action on a Noetherian scheme covered by invariant affine opens
has a Noetherian finite geometric categorical quotient, with canonical invariant affine
charts. The existing quotient predicate includes the invariant structure sheaf on every
open of the target. The geometric stabilizer is the subtype of elements fixing the actual
geometric point, and its order is required to be a unit in its field.

Source: ILO, Exposé VI 3.1--3.2 and proof 3.7(b), printed pp.73--75
(blueprint: lem-per-tame-admissible-scheme-quotient).

Proof, following the five DAG steps:
1. Every orbit lies in an invariant affine neighbourhood. Apply
   lem-per-admissible-quotient-affine-integral-charts to obtain the invariant affine
   integral surjection, orbit topology, geometric orbit fibres, categorical property,
   and invariant sections on affine target opens. The section description glues to all
   target opens, giving the invariant structure sheaf.
2. For every affine target open V, write its affine preimage as Spec R. By
   pqf-lem-affine-open-locnoeth, R is Noetherian. An algebraic closure of the residue
   field at a prime gives a geometric point. Injectivity of the residue-field embedding
   identifies its stabilizer with the inertia subgroup acting trivially on the residue
   field. The hypothesis therefore gives the assumption of
   lem-per-tame-inertia-surjective-group-trace, hence a trace-one element of R.
3. Apply lem-per-trace-one-noetherian-invariant-finiteness: the invariants R^G are
   Noetherian and R is finite over R^G. The every-affine characterization of
   def-weil-finite-integral-morphism makes the quotient finite.
4. These affine rings make the target locally Noetherian. Pull an open cover back to X,
   use quasi-compactness of X, and use surjectivity to descend the finite subcover.
   Thus the target is Noetherian, in the sense of pqf-def-locnoeth together with
   def-weil-pbc-quasi-compact-scheme.
5. For each invariant affine U, orbit fibres give q inverse q(U) = U and quotient
   topology makes q(U) open. The restricted quotient is finite surjective. Its target
   is Noetherian by lem-weil-pbc-noetherian-open-subscheme-noetherian, so
   lem-weil-pbc-finite-surjective-affine-target-noetherian makes it affine. Invariant
   sections identify its ring with the fixed subring of Gamma(U), and the section map
   with the inclusion. The affine-spectrum correspondence gives the chart equation
   below, including its specified morphism, not just an abstract isomorphism. -/
theorem exists_tame_admissible_scheme_quotient
    (X : Scheme.{u}) [IsNoetherian X] (G : Type v) [Group G] [Finite G]
    (a : G →* Aut X)
    (_hadmissible : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∀ (g : G) (z : X), (a g).hom z ∈ U ↔ z ∈ U)
    (_htame : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X),
      IsUnit (Nat.card {g : G // t ≫ (a g).hom = t} : Ω)) :
    ∃ (Y : Scheme.{u}) (q : X ⟶ Y),
      IsAdmissibleFiniteSchemeQuotient a q ∧ Surjective q ∧ IsNoetherian Y ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
        Function.Surjective (fun t : Spec (.of Ω) ⟶ X ↦ t ≫ q) ∧
        ∀ t s : Spec (.of Ω) ⟶ X,
          t ≫ q = s ≫ q ↔ ∃ g : G, t ≫ (a g).hom = s) ∧
      (∀ (Z : Scheme.{u}) (f : X ⟶ Z),
        (∀ g : G, (a g).hom ≫ f = f) → ∃! r : Y ⟶ Z, q ≫ r = f) ∧
      ∀ (U : X.Opens) (hU : IsAffineOpen U)
        (_hstable : ∀ (g : G) (z : X), (a g).hom z ∈ U ↔ z ∈ U),
        ∃ (V : Y.Opens) (hUV : U ≤ q ⁻¹ᵁ V),
          q '' (U : Set X) = (V : Set Y) ∧ q ⁻¹ᵁ V = U ∧
          ∃ C : Subring Γ(X, U),
            (∀ s : Γ(X, U), s ∈ C ↔
              ∀ (g : G) (D : X.Opens) (hD : D ≤ U) (hDg : D ≤ (a g).hom ⁻¹ᵁ U),
                ((a g).hom.appLE U D hDg).hom s =
                  (X.presheaf.map (homOfLE hD).op).hom s) ∧
            ∃ e : V.toScheme ≅ Spec (.of C),
              hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom C.subtype) =
                q.resLE V U hUV ≫ e.hom := by
  sorry

end AlgebraicGeometry
