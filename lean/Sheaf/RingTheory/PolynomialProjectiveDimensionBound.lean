module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import WeilConjectures.RingTheory.GlobalDimension
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
import WeilConjectures.RingTheory.PolynomialRingMaximalLocalizationDimension
import WeilConjectures.RingTheory.RegularLocalFiniteGlobalDimension
import WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension
import WeilConjectures.RingTheory.GlobalDimensionFiniteModules

/-!
# Projective resolution bound for polynomial rings over fields

Source: Stacks Project, Algebra, Proposition 00OQ
(proposition-finite-gl-dim-polynomial-ring), upper bound in the second sentence
(blueprint: lem-sfb-polynomial-projective-dimension-bound).
-/

@[expose] public section

universe u v

namespace MvPolynomial

/-- Every module over a polynomial ring in `m` variables over a field has an actual
projective resolution of length at most `m`. No grading or finite generation is assumed,
and the projective terms need not be finitely generated. For `m = 0`, this is the
projectivity of every vector space.

Source: Stacks Project, Algebra, Proposition 00OQ, upper bound in its second sentence
(blueprint: lem-sfb-polynomial-projective-dimension-bound).

Proof:
1. The polynomial ring is Noetherian and regular by
   `lem-weil-pbc-polynomial-ring-field-regular-ring`. Each maximal localization has
   dimension `m` by `lem-weil-pbc-polynomial-ring-maximal-localization-dimension`.
   The regular-local bound `lem-weil-pbc-regular-local-finite-gl-dim` therefore gives
   a resolution of length at most `m` for every module over each maximal localization.
2. For a finite module, convert these local resolution bounds into Ext vanishing by
   `lem-weil-pbc-projective-resolution-ext-degree`. Apply
   `lem-weil-pbc-finite-module-pd-local-global` and convert back using the same bridge.
   Thus every finite module has an actual resolution of length at most `m`.
3. Implication (2) to (1) of `lem-weil-pbc-global-dimension-finite-modules-suffice`
   gives the bound for every module. Unpack `def-weil-pbc-finite-global-dimension`:
   the resolution is exact, its terms are projective, and terms above `m` vanish.
4. At `m = 0`, `def-weil-pbc-mv-polynomial-ring` identifies the ring with the field.
   A length-zero resolution identifies its degree-zero projective term with the module;
   compose the splitting into a free module with this isomorphism to obtain projectivity
   by `def-weil-pbc-projective-module`. The zero module is included. -/
theorem hasProjectiveResolutionLE {k : Type u} [Field k] (m : ℕ)
    (N : ModuleCat.{max u v} (MvPolynomial (Fin m) k)) :
    ModuleCat.HasProjectiveResolutionLE N m := by
  sorry

end MvPolynomial
