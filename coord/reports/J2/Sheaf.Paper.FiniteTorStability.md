## What changed

Completed three finite-coefficient theorems in `Sheaf.Paper.FiniteTorStability`:
`finiteTor_stability_exceptional_verdier`, `finiteTor_stability_verdier_intrinsic`,
and `finiteTor_stability_constructible_adjunction`.

The exceptional theorem uses `FiniteExceptional.operations_preserve` and the existing
natural dual formula. Applying the intrinsic finite Verdier bound on the target,
pullback preservation, and the bound on the source gives the requested interval
`[a-2dX,b+2dY]`. Both fixed-scalar canonical biduality conclusions are supplied by
`finite_stage_verdier_biduality`.

Two proved private comparisons identify the closed unit with the regular coefficient
sheaf in degree zero and the paper's Verdier functor with `FiniteExceptional.dual`.
The unit comparison uses uniqueness of left adjoints to the same internal Hom and
the two unitors, followed by the existing normalized coefficient-unit comparison.
The structural compactification choices agree because `HasCompactification` is a
proposition. No definition body or existing public signature changes.

The intrinsic equivalence is constructed from the existing finite signed biduality
maps. Their naturality gives identity isomorphic to double dual; the existing proved
categorical helper gives an equivalence. The finite internal-Hom exactness theorem
and transport of its shift comparison give precisely the distinguished-triangle
clause. This uses finite geometric biduality without a site-perfect premise.

The constructible adjunction is the existing finite exceptional adjunction. Its dual
formula is whiskered with the unit-induced comparisons, with opposite isomorphisms
in the contravariant positions, and reflected through the fully faithful inclusion.

Added five private proof imports and imported the existing integral Verdier module
with `import all` to reuse its proved private categorical and signed-naturality
helpers. Updated the node's proof, proof dependencies, and proof origin, and removed
one obsolete tool approval.
All source-library files, consumer files, public imports, and previous theorem proofs
are preserved. No new node or change record is needed.

## Proved and sorry left

The input module had 10 holes. Closed 3, added 0:

- `WeilConjectures.finiteTor_stability_exceptional_verdier`
- `WeilConjectures.finiteTor_stability_verdier_intrinsic`
- `WeilConjectures.finiteTor_stability_constructible_adjunction`

The private helpers `sfStabilityClosedUnitIso` and `sfStabilityVerdierComparison`
are fully proved. The proofs use existing named dependency theorems, including ones
whose own proofs remain unfinished; no claim of axiom-free target completion is made.

These 7 original holes remain unchanged, all with node `thm-sf-ctf-stability`:

- `WeilConjectures.finiteTor_stability_origin`
- `WeilConjectures.finiteTor_stability_quotients`
- `WeilConjectures.finiteTor_stability_geometric_quotients`
- `WeilConjectures.finiteTor_stability_integral_images`
- `WeilConjectures.finiteTor_stability_integral_adjunction`
- `WeilConjectures.finiteTor_stability_rational`
- `WeilConjectures.finiteTor_stability_algebraicClosure`

This is a partial delivery of the multi-hole module, with no split-off statements.
Validation: the final module compiled without warnings or errors through `lcompile.py`
in 48.9 seconds. Public declaration signatures match the input file, and all lines
meet the 100-character limit.
All five new direct DAG dependencies were checked to have no path back to this item;
the added Lean imports also have no import path back to this module.

## No longer needed

No module is withdrawn and no global module pruning is claimed. Removed the unused
private import `Sheaf.Paper.CompactificationCoherence`; none of its declarations
is used by the existing proofs or the new arguments. The exceptional argument applies its already assembled preservation and
dual-formula interfaces, so the following direct proof-dependency edges are removed:

- `cor-pur-general-admissibility-datum`
- `cor-pur-smooth-admissibility`
- `prop-exc-closed-tor`
- `thm-pur-general-admissibility`
- `thm-pur-open-complement-unconditional`
- `thm-sf-preservation-class`

Removed the obsolete `prop-exc-closed-tor` entry from top-level `tool_uses` as well.
Those results remain dependencies of the existing preservation and duality theory.
The local smooth/closed preservation argument is retained there. The node's own
statement and unit route are unchanged. The new direct dependencies are the existing
finite intrinsic bounds and biduality, normalized signed calculus, closed monoidal
coefficient-unit construction, and internal-Hom exactness at independent universes.

## Where the brief, the DAG or earlier work was wrong

The old direct proof plan expanded smooth/closed preservation even though the
published `FiniteExceptional.operations_preserve` already states the needed result.
The natural dual formula and intrinsic finite Verdier bounds make this a direct
application, with explicit functor and coefficient-unit comparisons.

The paper's closed unit is not definitionally the coefficient sheaf in degree zero.
Likewise, its Verdier functor and `FiniteExceptional.dual` need a natural comparison.
The added proved comparisons supply this glue without changing either definition.
Opposite-category shifts must use the triangulated opposite scope; the finite
internal-Hom exactness application also fixes all site and derived universes.

Edge cases: all bounds use supplied nonnegative dimension estimates; the argument
has no nonempty-scheme premise. Zero objects and degenerate ordered Tor intervals
are covered by the same finite-bound theorems. Positive level one and arbitrary
ramification are included by indexing the coefficient exponent as `n+1`.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
