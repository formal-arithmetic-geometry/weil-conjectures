## What changed
The original module now proves `AlgebraicGeometry.existsUnique_etaleSections_equal_open`
from an existence obligation and an explicit proof of uniqueness. The target's declaration
signature and docstring are byte for byte unchanged. Its two plain proof imports were
replaced by the plain import of `EtaleSectionsEqualOpenExistence`; public imports are unchanged.
The existence module states only existence, with the original predicate written out verbatim.
No shared predicate definition or standalone uniqueness theorem is delivered.

## Proved and sorry left
`AlgebraicGeometry.existsUnique_etaleSections_equal_open` has a complete Lean proof conditional
on `AlgebraicGeometry.exists_etaleSections_equal_open`. Uniqueness is proved directly: each
candidate's open immersion factors through the other candidate, hence both subset relations.
The only direct `sorry` in this delivery is `AlgebraicGeometry.exists_etaleSections_equal_open`,
node `lem-weil-pbc-etale-sections-equal-open-existence`. Thus 1 of 1 original theorems has its
proof opened and reduced, with 1 strict existence obligation remaining; the target still has
`sorryAx` transitively and is not axiom-closed.

## No longer needed
The target no longer directly imports `Sheaf.AlgebraicGeometry.EtaleSetInverseImageStalkGerm`
or `Sheaf.AlgebraicGeometry.EtaleSubsheafFinalOpen`; both are relocated to the existence module
as its proof-plan imports. Every old target proof dependency is now an existence-plan
dependency rather than a direct dependency of the combining proof:
`def-weil-pbc-etale-sheaf-of-sets`, `lem-weil-pbc-etale-subsheaf-final-open`,
`lem-weil-pbc-sets-etale-inverse-image-stalk-germ`,
`lem-weil-pbc-sets-etale-inverse-image-composition-units`, and
`def-weil-pbc-geometric-stalks`. None is globally pruned or falsely declared unnecessary:
all remain required by the existence argument. The undelivered predicate and uniqueness
modules and the undelivered uniqueness node were removed from the first worker's sandbox.

## Where the brief, the DAG or earlier work was wrong
The first worker's combining proof compiled but postponed elementary uniqueness. Its shared
predicate module had no DAG node; its split docstrings did not contain complete proofs, its
new nodes recorded no Mathlib searches, their Lean signatures were prose rather than Lean,
and their blueprint ancestry and proof dependencies were incomplete. These have been repaired.
The full existence construction remains substantial; this delivery does not claim to have
formalized it. The new obligation removes uniqueness rather than renaming the entire target.

## New nodes
`lem-weil-pbc-etale-sections-equal-open-existence` is the existence part of the exact original
property, a strict subclaim of unique existence. It inherits the original existence route:
sheaf equalizer construction, Tag 04HV open representability, and Tag 03Q1 stalk comparison
with inverse-image unit compatibility. The node has a self-contained statement, exact Lean
signature, complete source-based proof steps, original dependencies, blueprint ancestry,
and recorded searches. No change record is needed: no existing signature, definition or
public import changed.

## Second reading by S2
1. Compared the delivered target module with the repository using `diff`, and checked its
   signature byte for byte by extracting the text before `:=`. Only proof imports and the
   proof body changed. No original declaration or definition was weakened or altered.
2. Both delivered modules compile locally through `lcompile.py`. Text scanning finds only
   the one named existence `sorry` and no forbidden declarations or hollow definitions.
   Scratch `#print axioms` checks for both declarations returned exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The delivery tool's full axiom probe
   and local/server compilation passed; the dry-run preflight printed OK (class CODEX).
3. Reviewed existence against [Stacks Tag 09XM](https://stacks.math.columbia.edu/tag/09XM)
   and [Tag 04HV](https://stacks.math.columbia.edu/tag/04HV), and read the actual imported
   stalk/germ and composition-unit statements. It quantifies over arbitrary scheme morphisms,
   preserving the precise restriction formula. Small cases: s=t gives W=V; the empty scheme
   gives the empty open; distinct constant sections have empty agreement locus (and agree
   on empty test schemes). No separation or finiteness assumption is needed. Searches with
   LeanFinder, Loogle, and source grep found no matching theorem; LeanSearch was attempted but
   returned HTTP 500, recorded honestly as unavailable. Upstream geometric-point extensionality
   concerns module-sheaf morphisms and does not construct this open. The existence docstring
   now gives the full construction and both implications. Elementary uniqueness is closed.
4. Used the shortest route for uniqueness: identities, factorization, point evaluation, and
   antisymmetry. The original existence route and all its dependencies remain. Checked
   `dag/units/sk-thm-iff.json`: this item is not a realized unit statement/step, and no
   realized node is bypassed. Public imports remain for the target's signature, and new
   proof imports are plain. The no-longer-needed section accounts for every old proof edge.
5. The target node now records exactly the existence application and open-immersion
   uniqueness proof; the new node records the complete original existence plan, its union
   of proof dependencies, source, exact declaration, searches, and inherited unit/chapter.
   The target's proof origin is marked agent for the new elementary reduction.

Second reading changes: proved uniqueness directly; removed the unused predicate definition
and uniqueness split; restored the original predicate verbatim in the existence declaration;
repaired its docstring and node metadata and the target node's proof; rewrote the report.
