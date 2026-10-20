/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.OpenDegreeZeroConstructible
import WeilConjectures.ConstructibleSheaf.Pullback
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Constructible
import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Constructibility of the boundary sheaf of an open immersion

Source: blueprint `sec-six-functors-basics/sk-prop-a1-kummer/lem-fin-boundary-sheaf.md`
and its proof, main-20261015 (blueprint: lem-fin-boundary-sheaf).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- For an open immersion into a finite-type scheme over a field, the restriction of
its direct image to the closed complement is a constructible etale module sheaf.
The coefficient predicate records the inherited positive annihilator and invertibility
conventions of `sbc-def-coefficient-conventions`.

Source: blueprint `sec-six-functors-basics/sk-prop-a1-kummer/lem-fin-boundary-sheaf.md`
and its proof, main-20261015 (blueprint: lem-fin-boundary-sheaf).

Proof plan:
1. Apply `thm-fin-open-degree-zero` to `X`, `j`, and `F` to obtain constructibility
   of `j_*F`, with the finite locally constant module values of
   `def-weil-pbc-constructible-complexes` and `def-constructible-finite-locally-constant`.
2. Use `prop-constructible-pullback` along `i`, with `Etale.upperStar` of
   `def-weil-pbc-inverse-image`. Pull back the finite locally closed stratification
   and its finite constant etale trivializations. This gives constructibility in the
   sense of `def-constructible-constructible`.
3. By `lem-weil-pbc-finite-type-over-noetherian`, `X` is Noetherian. Its closed
   subsets have the minimal condition by `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`.
   The same holds on the closed complement `Z`, hence `Z` is a Noetherian space.
   Every locally closed stratum is then constructible (`def-weil-constructible-subset`,
   Stacks Tag 005L). Thus the pulled-back partition proves the required module-sheaf
   constructibility, including its constructible-stratum clause. -/
theorem isConstructibleEtaleModuleSheaf_boundary_of_openImmersion_over_field
    {k : Type u} [Field k] {X U Z : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
    (hcomplement : Set.range i.base = (Set.range j.base)ᶜ)
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] (N : ℕ)
    (hcoeff : Etale.IsSmoothBaseChangeCoefficients N Λ X)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf F) :
    IsConstructibleEtaleModuleSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) j).obj F)) := by
  sorry

end AlgebraicGeometry.Scheme
