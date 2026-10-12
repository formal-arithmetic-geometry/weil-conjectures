## What changed
The proof of `AlgebraicGeometry.exists_isProper_baseChange_of_isLimit` now explicitly applies
`Scheme.exists_isSeparated_overPullbackMap`, then `exists_chow_finite_type` at the separated
stage, then the new `exists_closed_chow_stage` to that fixed Chow diagram. A closed
projective embedding makes the composite proper; `UniversallyClosed.of_comp_surjective`
and `isProper_iff` finish the proof. The original statement and its public imports are
unchanged. No definitions or existing signatures were changed.

The new module `Sheaf.AlgebraicGeometry.ClosedChowStage` states only the descent of a
specified Chow diagram, with the source explicitly the base change of the given T₁ and
the same number of projective coordinates. Its private proof import is
`Sheaf.AlgebraicGeometry.DescendClosedImmersion`. In the item, that direct import is
replaced by the private import `Sheaf.AlgebraicGeometry.ClosedChowStage`; the redundant
private import `WeilConjectures.AlgebraicGeometry.ProjectiveSpace` is removed.

## Proved and sorry left
`AlgebraicGeometry.exists_isProper_baseChange_of_isLimit` has a complete proof term and
no local `sorry`. It still depends on the open separatedness and Chow theorems in the
existing library, and on the single new split
`AlgebraicGeometry.exists_closed_chow_stage` in `Sheaf.AlgebraicGeometry.ClosedChowStage`,
node `lem-weil-pbc-closed-chow-stage`. This theorem is the only `sorry` in the delivery.
The item is not yet axiom-free: `#print axioms` for both the item and the split reports
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. No other axiom is used.

The first worker's generic `isProper_of_surjective_of_comp_isProper` helper was removed:
its mathematical content is already `UniversallyClosed.of_comp_surjective` followed by
`isProper_iff`, used inline here. The initial `exists_stage_factorization_of_isLimit` and
its node `lem-weil-pbc-eventually-proper-factorization` were removed as a restatement.

## No longer needed
The item's direct private imports of `Sheaf.AlgebraicGeometry.DescendClosedImmersion`
and `WeilConjectures.AlgebraicGeometry.ProjectiveSpace` are removed. Closed-immersion
descent stays in the new split module, and projective-space properness remains used,
available through `ChowFiniteType` and `ClosedChowStage`.

Every old direct proof dependency absent from the new item's `proof_deps` is listed here:
- `def-weil-finite-type-morphism`
- `def-weil-surjective-morphism`
- `def-weil-closed-immersion`
- `def-nagata-projective-space-base-change`
- `lem-weil-pbc-immersion-base-change-lft`
- `lem-weil-pbc-surjective-base-change`
- `lem-weil-pbc-proper-over-separated`
- `lem-weil-pbc-proper-immersion-closed`
- `lem-weil-pbc-descend-closed-immersion`
- `lem-pod-separated-finite-type-base-change`

These are moved below the new geometric diagram split or are statement notions already
provided by the unchanged existing declarations; they are not claimed globally pruned.
No unit or globally reachable module is removed. The unit `sk-thm-p1`'s `realized`
statement and four groups of steps are kept unchanged; the item is not a unit's key node.

## Where the brief, the DAG or earlier work was wrong
The first delivery had four issues: its split was equivalent to the original target
(take the witness π to be the identity in the converse direction); the original target's
six-step docstring had accidentally become the helper's docstring; the new node lacked
statement dependencies, genuine Mathlib searches, actual proof dependencies and a
verbatim Lean signature; and the original node had not been updated to the new proof.
Compilation also emitted four `letI` style warnings. All of these were repaired.

The replacement does real work before applying the split: finite-stage separatedness
and the actual Chow modification are obtained from existing declarations. The split
cannot be manufactured merely by taking an arbitrary identity witness; it accepts the
specific Chow diagram and returns a closed immersion of its fixed base-changed source
into projective space of the prescribed dimension. The remaining argument is the
base-change/pasting and closed-immersion descent part of Stacks 081F, not a new name
for properness descent.

## New nodes
`lem-weil-pbc-closed-chow-stage` records Stacks 081F's fixed Chow-diagram descent after
a separated stage and a Chow modification have been chosen, using 01ZP. Its four proof
steps cite qcqs and affine permanence, pullback pasting, properness composition and
base change, immersion permanence, properness over a separated target, proper immersion
closedness, closed-immersion descent, projective-space properness, and surjective and
separated base change. Its docstring supplies the complete natural-language argument.
It uses the item's chapter and unit and has a verbatim signature and real searches.
No change record is needed, since existing statements, definitions and public imports
are unchanged.

## Second reading by N2
1. Compared the delivered item with the repository by `diff` and checked its theorem
   signature as an exact byte string up to `:= by`: identical. The original docstring is
   again attached to the original theorem. Public imports and all definitions are
   unchanged. The only added statement is in its own new module.
2. Compiled both modules in import order through `lcompile.py`: no errors or warnings.
   Scanned both for forbidden declarations and sorry in definitions: none. The single
   sorry is precisely the named theorem listed above. An appended `#print axioms` in a
   scratch copy showed only the three permitted axioms and `sorryAx` for both declarations.
3. Rejected the original split as logically equivalent to the target. Read Stacks
   `lemma-eventually-proper` (081F), including the passage from Chow's immersion at the
   limit to a finite-stage closed immersion, in the local Stacks source. The replacement
   has the same qcqs, affine-transition, proper-limit and local-finite-type hypotheses,
   and additionally consumes the separated stage and a specified Chow diagram rather
   than asserting their existence. The fixed-source conclusion is true by the four
   documented steps. Tested singleton directed systems (the existing immersion becomes
   closed at that stage), empty source and target (empty pullbacks and vacuous
   surjectivity), zero-dimensional projective space (n = 0), nonleast i₀, and i₁ = i₀:
   none excludes a legitimate case or requires a new hypothesis. The index type cannot
   be empty because i₀ is supplied. Searched LeanFinder, Loogle and grep through
   `msearch.py`, and searched `lean/` and the upstream source for Chow/stage/properness
   variants. No existing theorem states the fixed diagram's finite-stage conclusion.
   LeanSearch returned an internal server error, recorded as unavailable. Existing
   component lemmas are reused, including `UniversallyClosed.of_comp_surjective`.
4. Read from the target downward. The explicit separatedness and Chow steps and final
   Mathlib properness argument are now in the item. Only the intervening fixed-diagram
   descent is split off. All removed imports and old direct proof dependencies are
   accounted for above. The geometric route follows 081F and retains 01ZQ, 0202 and
   01ZP; no chapter or unit route is bypassed. The remaining split needs substantial
   rebasing and pullback comparisons and cannot be closed in a few minutes.
5. Opened the original node, its twenty proof dependencies and the new node. Replaced
   the original node's `proof`, `proof_deps` and `proof_origin` to follow the four Lean
   steps. The new node's `proof_deps` is exactly the union of its four steps' uses, and
   its signature is verbatim from the new module. Confirmed its dependency closure
   does not return to the item. `dag/units/sk-thm-p1.json` and its `realized` route are
   unchanged. Verdict: genuine partial reduction, with one clearly specified open lemma.

Changed in this second reading: replaced the restatement with the fixed Chow-diagram
lemma in a new module; wrote the real separatedness/Chow/properness reduction; removed
the duplicate helper, corrected docstring attachment, imports, style warnings, node
metadata, dependency records and this report.
