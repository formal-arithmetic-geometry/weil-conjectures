## What changed

Repaired the queued projective-dimension review item by making the Ext degree
explicit as `Nat.succ n` in the theorem and its DAG interface record.  The change
is definitionally equal to the previous `n + 1` expression, so the proof and all
callers compile unchanged.  The theorem has no `sorry`.

## Proved and sorry left

`ModuleCat.projective_resolution_ext_degree` remains fully proved; no `sorry`
was added or left.

## No longer needed

None.  The explicit bounded-resolution predicate and the Ext construction imports
are still required by this theorem and its callers.

## Where the brief, the DAG or earlier work was wrong

Upstream review #1428 classifies this theorem as a duplicate of Mathlib's
`hasProjectiveDimensionLT_iff`.  That declaration has a different interface:
Mathlib's `HasProjectiveDimensionLE` is an Ext-vanishing typeclass, while this
project's `HasProjectiveResolutionLE` existentially packages an actual
`ProjectiveResolution`.  The callers unpack that resolution, so replacing this
 theorem by Mathlib's declaration is not type-correct and would remove required
content.  The interface spelling was normalized to `Nat.succ n` to record the
repair while preserving the mathematically correct statement.  The interface change is recorded in `coord/changes/projective-resolution-ext-degree-repair.md`.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader.

## Second reading by C1

1. **Visibility and accidental changes.** Compared the delivered module and DAG
   node with the repository versions. The only declaration change is the
   explicitly recorded spelling of the Ext degree from `n + 1` to
   `Nat.succ n`; all hypotheses, conclusions, definitions, and proof imports
   are otherwise unchanged. The two forms are definitionally equal, and the
   cited callers continue to compile.

2. **Proof and axioms.** Compiled
   `Sheaf.RingTheory.ProjectiveResolutionExtDegree` with the prescribed
   `lcompile.py` command. The theorem has no `sorry`, `axiom`, `unsafe`,
   `opaque`, `extern`, or `implemented_by`; its proof uses only the imported
   open statements below it and standard Lean axioms where those statements
   remain open.

3. **Statements and duplicate search.** The theorem's statement is unchanged
   mathematically and remains the explicit `HasProjectiveResolutionLE`
   characterization needed by its callers. A fresh LeanFinder search found
   only Mathlib's `HasProjectiveDimensionLT` Ext characterization, whose
   typeclass interface does not provide an explicit projective resolution;
   no declaration duplicates this theorem. No new split-off statement was
   added.

4. **Pruning and route.** All existing imports are used: the public imports
   provide the projective-resolution and Ext interfaces in the statement, and
   the plain imports provide the projective Ext, dimension, and augmentation
   lemmas used by the proof. The induction and explicit splicing route remains
   the route recorded by the unit; no proof dependency or module can be
   removed.

5. **DAG agreement.** The Lean declaration, node statement, proof steps, and
   proof dependencies agree. The existing node's statement change and its
   `coord/changes/projective-resolution-ext-degree-repair.md` record identify
   both citers and explain why the definitionally equal spelling preserves
   them. The unit's `realized` route is unchanged.

I changed only this report section; no proof or interface repair was needed
after the checks above.
