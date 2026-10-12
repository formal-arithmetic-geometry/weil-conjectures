## What changed

Proved `AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFreeOfDegree_of_etale_cover`
without changing its signature, universes, hypotheses, definitions, or existing docstrings.
The jointly surjective etale family is fppf and hence fpqc by Mathlib's
`Scheme.ofArrows_mem_precoverage_iff` and `Scheme.fppfPrecoverage_le_fpqcPrecoverage`.
The existing theorems `isFinite_of_fpqc_cover`, `flat_of_fpqc_cover`, and
`locallyOfFinitePresentation_of_fpqc_cover` supply finite local freeness.
At each target point, joint surjectivity supplies a point of a covering member;
`Scheme.Hom.fiberDegree_of_isPullback` identifies the two fibre degrees, and the
hypothesis supplies degree d. This follows all five steps of Stacks 02VO and 022C.
Updated the node's proof and proof dependencies to describe these actual tools.

Sources read: Stacks Descent, `lemma-descending-property-finite-locally-free`,
lines 6225–6245, and Topologies, `lemma-zariski-etale-smooth-syntomic-fppf-fpqc`,
lines 3044–3063, in the local Stacks source mirror. Read the unit record
`dag/units/sk-thm-p1.json`: this node is not one of its realized statement/steps;
no unit route is bypassed. The proof also covers d = 0 and an empty index family:
no nonemptiness assumption is added; hcover supplies a covering point only when
there is a target point.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFreeOfDegree_of_etale_cover`
(node `lem-weil-pbc-finite-locally-free-degree-etale-descent`).
No sorry remains in the item's module. Added 0 holes and 0 intermediate declarations.
The three descent dependencies already have complete proofs. The source-library
fibre-degree base-change tool is proved, rather than a new assumption.
Local compilation passed with no errors or warnings after replacing letI by let
as requested by the linter. The delivery dry run also checks the axiom probe.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.FiberDegreeBound` (node `def-weil-pbc-fibre-degree-bound`).
- `Sheaf.AlgebraicGeometry.FiniteFiberDegreeBaseChange`
  (node `lem-weil-pbc-fibre-degree-base-change`).

Neither fibre bounds nor the general finite-fibre theorem are needed: h is globally
finite, so the existing affine fibre-degree base-change theorem applies directly.
Removed explicit proof dependencies `lem-weil-pbc-finite-morphism-permanence`,
`def-weil-residue-field`, and `def-pc-scheme-fibre`: the direct equality theorem
encapsulates these constructions. Removed explicit dependencies
`lem-weil-pbc-etale-morphism-open-map` and `lem-weil-pbc-affine-scheme-qcqs`:
Mathlib's fppf-to-fpqc inclusion already supplies this argument.
These nodes remain available elsewhere; this report asserts only that this proof
has no separate need for them. Retained both public imports and all three
fpqc descent proof imports.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The DAG's degree step plans to use a general
finite-fibre base-change lemma, but its existing search record already identifies
`Scheme.Hom.fiberDegree_of_isPullback`. After finiteness descends, its global
IsAffineHom hypothesis is satisfied, so this proved tool suffices and avoids the
remaining sorry in `finite_fiber_degree_pullback`. The cover step similarly has
an existing Mathlib inclusion theorem. No definition or statement was changed.

## Second reading by U1

1. PASS: compared the sole delivered Lean module and node with the repository by
   `diff -u`. The theorem signature, universes, hypotheses, conclusion, and docstring
   are byte-for-byte unchanged. No definitions or other modules changed; no change
   record is needed. Only the proof and two private proof imports changed.
2. PASS: compiled the module locally with lcompile.py, with no errors or warnings.
   An independent scratch copy with `#print axioms` reports only `propext`,
   `Classical.choice`, and `Quot.sound` for
   `AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFreeOfDegree_of_etale_cover`.
   The delivered module contains no sorry or forbidden declaration or bypass.
   Its finite, flat and finite-presentation instances really fill all the inherited
   fields of IsFiniteLocallyFreeOfDegree; the remaining field is the fibre equality.
3. PASS: no statements were split off and no new declarations or holes were added.
   Checked degree zero and empty covers: the proof never assumes a positive degree
   or a nonempty index type; joint surjectivity supplies a covering point precisely
   when a target point is present. No witness is chosen from an unproved theorem.
4. PASS: independently searched Lean and Mathlib for fixed-degree covering/descent
   results and read the three fpqc descent modules, Mathlib's fppf-to-fpqc inclusion,
   and the source-library fibre-degree base-change proof. The direct proved tools
   already used are appropriate; no shorter matching fixed-degree descent theorem
   was found. Both retained public imports are needed by the signature; all three
   private imports supply descent lemmas used in the proof. The report lists every
   removed old proof dependency and both removed imports. The sk-thm-p1 realized
   statement and steps contain neither this node nor any removed dependency, so
   the unit route is preserved and its record needs no change.
5. PASS after metadata repair: the node's five steps and proof_deps follow the
   Lean proof, and proof_origin names the actual proved tools. The degree step uses
   a substantive proved base-change theorem, so changed its elementary flag to
   false. Replaced that step's stale source reference to the pruned finite-fibre
   lemma with the exact fibre-degree theorem used. The old proof docstring is kept
   as required; the current route is recorded in the node and this report.

Second reading changed only the node's degree-step elementary flag and source
explanation, and appended this review. No Lean repair was needed. Confirmed net
one hole closed, zero holes added; there is no decomposition.
