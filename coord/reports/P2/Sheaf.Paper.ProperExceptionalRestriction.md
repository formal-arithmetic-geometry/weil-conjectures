## What changed

Proved AlgebraicGeometry.ProEtale.CondensedRing.proper_exceptional_restriction in
lean/Sheaf/Paper/ProperExceptionalRestriction.lean without changing its signature or any
public import. The identity compactification is identified with ambient derived pushforward
using CondensedRing.upperStarId, the existing open-module adjunction, uniqueness of left
adjoints, and the derived identity isomorphism. The comparison clause of
exceptionalInverseImage_exists supplies compactification independence directly.

Transported preservation of Dctf through this comparison and preservation by the Brown
adjoint through rightAdjointUniq. Constructed both restrictions using ObjectProperty.lift,
proved their required inclusion equalities by reflexivity, and restricted the caller's
adjunction through the fully faithful Dctf inclusions. Localizing-hull repleteness follows
directly from the intersection definition. Updated the item's DAG proof to this route.
The unit's identity-compactification, existence and restriction route is preserved.

Added the proof import
WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence and retained
Mathlib.CategoryTheory.Adjunction.Restrict. The final module compiled through lcompile.py
in 9.1 seconds after removing unused imports. On 2026-10-19 the retained proof was
rechecked against current sources and compiled cleanly through lcompile.py in 9.1 seconds.
The current signature and public imports are unchanged. No other Lean module is changed.

## Proved and sorry left

Closed 1 of 1 holes:
AlgebraicGeometry.ProEtale.CondensedRing.proper_exceptional_restriction
(node det-cor-existence-ii-restriction).

Holes added: 0. Holes left in delivered Lean files: 0. Split-offs: 0.
This is a proof from existing stated dependencies, including exceptionalInverseImage_exists
and constantModelConstructibleFiniteTor_wellDefined; their existing holes are unchanged.

## No longer needed

Removed the following direct proof imports:

- Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
- Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
- Mathlib.CategoryTheory.Adjunction.Basic
- Mathlib.CategoryTheory.Adjunction.Mates
- Sheaf.Compactification.BoundaryRefinement
- Sheaf.Paper.CompactificationLocalizing
- Sheaf.Paper.CompactificationCoherenceCocycle
- Sheaf.Paper.LocalizingClosureExistence
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Projection
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
- WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs

The item's proof no longer directly needs these original DAG dependencies:

- sk-def-sfb-dc-setting
- lem-weil-pbc-qcqs-over-affine
- sk-def-nagata-sketch-data
- def-sfb-finite-extension-by-zero
- def-sfb-module-open-lower-shriek
- def-sfb-module-linear-open-lower-shriek
- sk-def-sfb-coefficient-morphisms
- sk-def-sfb-pullback-from-point-comp
- def-sfb-finite-upper-star
- def-sfb-finite-upper-star-comp
- def-sfb-finite-lower-star-comp
- lem-sfb-open-projection-formula
- def-sfb-finite-upper-lower-star-adjunction
- def-weil-pbc-composite-adjunction
- def-weil-pbc-adjunction-mate
- det-sf-comp-coherence-single
- det-def-localizing-closure-existence
- det-sf-comp-coherence-cocycle

The existence theorem already supplies compactification comparison and preservation, so the
separate single-candidate and coherence-cocycle applications are unnecessary here. Direct
intersection reasoning replaces localizingClosure_exists. The source-library module identity
pullback and the module adjunction replace the expanded finite-sheaf Kan-extension,
coefficient-compositor and projection-formula calculations. No independent qcqs argument is
needed here: the existence theorem accepts exactly the standing scheme hypotheses.
Removed the item's obsolete tool_uses approval for lem-weil-pbc-qcqs-over-affine.
These are direct dependency removals; other target branches, including the existence theorem,
may still use the listed nodes and modules. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The planned proof repeated facts already
packaged in the existence theorem and proved module-object coherence API. The shorter proof
keeps the same source and unit route. All choices in this proof merely unpack existential
proof witnesses in a theorem; no definition or arbitrary object construction is introduced.
The zero coefficient ring, empty schemes, and identity proper morphism require no additional
hypotheses or case exclusion.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
