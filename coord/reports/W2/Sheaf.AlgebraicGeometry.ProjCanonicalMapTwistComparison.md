## What changed

Proved both holes of `Sheaf.AlgebraicGeometry.ProjCanonicalMapTwistComparison` without
changing any public signature, definition, attribute, or public import. The value lemma
is `rfl`. The main proof constructs a common-degree standard-open cover and glues the
normalized isomorphisms using the existing proved free-generator API.

Three proved private helpers implement the finite-subcover arithmetic, gluing from
matching section ratios, and preservation of sections under the canonical adjunction
comparison between tensor pullback and ordinary pullback. The main proof uses the
supplied map `r` and its fraction formula directly, with exponent one. It does not
construct another Proj map or require a uniqueness theorem identifying two maps.

Updated the item's DAG proof, proof dependencies, and proof origin to this direct
Stacks 01N8/01NK chart argument. No other module is changed.

The empty-scheme case is included: the product of an empty finite set of positive
degrees is one, and generator gluing and separatedness apply to empty covers. Degree
zero is never used as a chart degree: every chosen quotient exponent and every `d*k`
is proved positive.

## Proved and sorry left

Closed 2 of 2 holes, both attached to
`lem-trf-proj-canonical-map-twist-comparison`:

- `AlgebraicGeometry.Scheme.Modules.gradedSectionElement_val`.
- `AlgebraicGeometry.Scheme.Modules.exists_proj_canonical_map_twist_comparison`.

No sorry remains in the item. No holes are added and no results are split off.
All three new private helpers have complete proofs.

Validation: the item compiles cleanly through `lcompile.py` (9.2 seconds, exit 0).
Both added imports pass `tools/import_direction.py may`. Public signatures, public
imports, the definition body, and existing docstrings were compared with the source
and are unchanged. The file has no overlong lines and no `sorry` tokens.

## No longer needed

Removed the proof-only imports:

- `Sheaf.AlgebraicGeometry.ProjInvertibleMapTwistIso`, node
  `lem-trf-proj-invertible-map-twist-iso`.
- `Sheaf.TraceFormula.SpaceLineModuleProjMap`, node
  `lem-trf-space-line-module-proj-map`.

Neither declaration is used by the proof. The map and its chart formulas are already
hypotheses. The required fixed-degree comparison follows directly from
`Proj.map_unitToTwist_eq_smul`, pullback of free generators, and
`isoOfIsFreeGenerator`. These two nodes are removed from this item's proof dependencies;
no claim is made that their other consumers are unnecessary. No module is withdrawn.

The two new proof-only imports are
`WeilConjectures.AlgebraicGeometry.Modules.FreeGeneratorIso` and
`WeilConjectures.AlgebraicGeometry.NonvanishingGeneratingLocus`. Both are used.
All pre-existing public imports are retained.

## Where the brief, the DAG or earlier work was wrong

The statements are unchanged and no mathematical error was found. The old plan and
existing docstring describe an unnecessary construction of a second canonical map.
Moreover, the declared generated-open comparison chooses its own morphism and only
states its inverse-image formula, whereas the item supplies a morphism and a fraction
formula. Using the latter directly avoids this interface mismatch as well as transport
from the top open subscheme back to `Z`.

The unit `sk-i-curve-zero` has no realized statement or step attached to this item;
its route is unchanged. The new argument is the local frame-and-ratio proof of
Stacks Tag 01N8, with the section normalization of Tag 01NK.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
