/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Sheaf.AlgebraicGeometry.LogDifferentialStalk
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Finite freeness of logarithmic differentials at a geometric point

Source: Illusie--Laszlo--Orgogozo, Exposé XVI Proposition 3.6.3 proof, printed
p.252, first paragraph; Kato, Logarithmic structures of Fontaine--Illusie, §3
(blueprint: lem-per-log-smooth-differential-local-freeness).

The module is the existing generators-and-relations quotient `EtaleLogHom.LogDifferential`.
The coefficient ring is the actual étale geometric ring stalk `strictLocalRing`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The logarithmic differential module of a log-smooth morphism at any geometric
point is free of finite rank, with rank zero allowed.
Source: ILO, Exposé XVI Proposition 3.6.3 proof, printed p.252, first paragraph;
Kato, Logarithmic structures of Fontaine--Illusie, §3
(blueprint: lem-per-log-smooth-differential-local-freeness).

Proof:
1. Apply `lem-per-log-smooth-infinitesimal-calculus` to the locally Noetherian fs
   log schemes and the chart-log-smooth morphism. Its finite-local-freeness clause
   gives a pointed étale neighbourhood and a trivialization of the logarithmic
   differential sheaf as a finite power of the structure sheaf. The sheaf relations
   are exactly those in `logDifferentialRelations`.
2. Identify the presented module with the geometric stalk of that sheaf. Send
   each ordinary or logarithmic symbol to its germ. Each germ has a representative
   by `def-weil-pbc-geometric-stalks`; any finite list has a common refinement by
   `lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`. Every relation involves
   finitely many sections, and membership in its span has a finite witness, so
   forming germs commutes with imposing the relations. Base sections are represented
   on neighbourhoods of the image point and pulled back to the source; these give
   exactly the two base relation families in the recorded quotient. Finally
   `lem-weil-pbc-sets-sheafification-geometric-stalk` ensures that sheafification
   preserves this stalk, together with addition and scalar multiplication.
3. Take germs of the trivialization and its inverse. Refinements of its pointed
   neighbourhood are cofinal by the same cofilteredness lemma. A finite tuple of
   germs has simultaneous representatives, and equality is checked after a common
   refinement coordinate by coordinate. Thus the stalk of the finite power is
   `Fin s → strictLocalRing X.scheme t`. Compose these linear isomorphisms. For
   `s = 0`, both modules are zero and the unique maps give the same conclusion.
-/
theorem EtaleLogHom.exists_logDifferential_linearEquiv
    {X Y : FineSaturatedLogScheme.{u}} (f : EtaleLogHom X Y)
    (hf : f.IsLogSmooth) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X.scheme) :
    ∃ s : ℕ, Nonempty (f.LogDifferential t ≃ₗ[strictLocalRing X.scheme t]
      (Fin s → strictLocalRing X.scheme t)) := by
  sorry

end AlgebraicGeometry
