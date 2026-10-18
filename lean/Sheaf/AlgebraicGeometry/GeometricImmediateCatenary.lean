/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.KrullDimension

/-!
# Geometric and Zariski immediate specializations

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XIV,
Definitions 2.1.1--2.1.2 and Proposition 2.1.4, printed pp. 209--211
(blueprint: lem-per-geometric-immediate-catenary).

A geometric specialization is expressed as a geometric point of the strict localization,
which is equivalent to a morphism between strict localizations (Definition 2.1.1).
The reduced closure is the subscheme of the vanishing ideal of the point's closure.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- On a Noetherian universally catenary scheme, absence of an intermediate point,
dimension one of the local ring of the reduced closure, and existence of an immediate
geometric specialization are equivalent. Every specified immediate geometric specialization
also gives a saturated prime inclusion on each affine neighbourhood.

Source: ILO, Expose XIV, Definitions 2.1.1--2.1.2 and Proposition 2.1.4, pp. 209--211
(blueprint: lem-per-geometric-immediate-catenary).

Proof:
1. Put Z = closure({y}) with its reduced induced structure. In any affine neighbourhood
   Spec A of x, y corresponds to p and x to q, and O_{Z,x} = (A/p)_{q/p}.
   Its primes are exactly the primes between p and q. Since y differs from x, it is a
   nonfield local domain. No intermediate point means its only primes are zero and the
   maximal ideal. This is equivalent to dimension one by the chain definition of
   def-weil-pbc-krull-dimension-ring.
2. Apply lem-per-immediate-specialization-criterion. Its hypotheses follow from the
   given Noetherianity and universal catenarity on every affine open. It identifies
   dimension one of O_{Z,x} with existence of a geometric specialization whose image
   has one-dimensional closure in the strict localization. Definition 2.1.1 identifies
   such specializations with geometric points of that strict localization over y.
3. For any specified geometric lift with one-dimensional closure, part (b) of the same
   criterion gives dimension one of O_{Z,x}. Step 1, on an arbitrary affine chart,
   excludes every prime strictly between p and q, proving the last clause. No regularity,
   coefficient, or field-of-definition hypothesis is used.

The existential point of the reduced closure is precisely x viewed on that closed
subscheme; the equality under its closed immersion fixes the point uniquely. -/
theorem geometricImmediate_iff_zariskiImmediate_of_universallyCatenary
    (X : Scheme.{u}) [IsNoetherian X]
    (hcat : ∀ U : X.affineOpens, IsUniversallyCatenary Γ(X, U))
    (y x : X) (hne : y ≠ x) (hyx : y ⤳ x) :
    ((∀ z : X, y ⤳ z → z ⤳ x → z = y ∨ z = x) ↔
      ∃ zx : (IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set X))).subscheme,
        (IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set X))).subschemeι zx = x ∧
        ringKrullDim
          ((IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set X))).subscheme.presheaf.stalk
            zx) = 1) ∧
    ((∀ z : X, y ⤳ z → z ⤳ x → z = y ∨ z = x) ↔
      ∃ (Ωx : Type u) (_ : Field Ωx) (_ : IsAlgClosed Ωx)
        (barX : Spec (.of Ωx) ⟶ X),
        barX (IsLocalRing.closedPoint Ωx) = x ∧
        ∃ (Ωy : Type u) (_ : Field Ωy) (_ : IsAlgClosed Ωy)
          (a : Spec (.of Ωy) ⟶ strictHenselizationScheme barX),
          strictHenselizationStructuralMap barX (a (IsLocalRing.closedPoint Ωy)) = y ∧
          topologicalKrullDim
            (closure ({a (IsLocalRing.closedPoint Ωy)} :
              Set (strictHenselizationScheme barX))) = 1) ∧
    (∀ (Ωx : Type u) [Field Ωx] [IsAlgClosed Ωx] (barX : Spec (.of Ωx) ⟶ X),
      barX (IsLocalRing.closedPoint Ωx) = x →
      ∀ (Ωy : Type u) [Field Ωy] [IsAlgClosed Ωy]
        (a : Spec (.of Ωy) ⟶ strictHenselizationScheme barX),
        strictHenselizationStructuralMap barX (a (IsLocalRing.closedPoint Ωy)) = y →
        topologicalKrullDim
          (closure ({a (IsLocalRing.closedPoint Ωy)} :
            Set (strictHenselizationScheme barX))) = 1 →
        ∀ (U : X.affineOpens) (p q : PrimeSpectrum Γ(X, U)),
          U.2.fromSpec p = y → U.2.fromSpec q = x →
          p.asIdeal < q.asIdeal ∧
          ¬ ∃ r : PrimeSpectrum Γ(X, U), p.asIdeal < r.asIdeal ∧ r.asIdeal < q.asIdeal) := by
  sorry

end AlgebraicGeometry.Scheme
