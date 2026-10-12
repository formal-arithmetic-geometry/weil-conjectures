## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_dim_le_one` from the
existing reduction, reduced ampleness, PicardLift, invertible pullback, and reduction
ampleness declarations. Added private proof imports `AmpleIso` and the already proved
`WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian` convenience theorem.
The target signature and definitions are unchanged. All six steps of the existing
geometric plan are implemented; only isomorphism transport is a new remaining item.

## Proved and sorry left

The item's sole sorry, `AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_dim_le_one`,
is replaced by a complete Lean proof, compiling without warnings.
The delivery adds one sorry: `AlgebraicGeometry.Scheme.Modules.isAmple_iff_of_iso`
in `Sheaf.AlgebraicGeometry.AmpleIso`, node `lem-sc-ample-iso`.
Its docstring gives the complete section-transport proof. This generic statement
is strictly step 5's isomorphism transport, with no field, dimension, reducedness,
Noetherianity, or existence conclusion. It is not a repackaging of the target.
The existing imported reduced ampleness, PicardLift, reduction ampleness, and
invertible pullback declarations remain dependencies as intended by stage 3.

## No longer needed

No original imports were removed: all four original proof imports are used.
The direct dependency `lem-weil-pbc-closed-immersion-finite` is unnecessary: the
closed immersion supplies finite type and quasi-compactness directly by instances.
`lem-weil-pbc-finite-over-separated-finite-type` is unnecessary as a separate node:
composition instances supply separatedness, and Noetherianity of the reduction
is proved over X directly. `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`
is unnecessary: IsNoetherian X already supplies NoetherianSpace X to PicardLift.
These are Mathlib leaves with no dedicated library module to remove. They may
remain reached elsewhere; this report only prunes the item's direct proof edges.
The old direct edge `def-weil-pbc-ample-invertible-module` is also removed from
the parent proof: the section-transport argument now belongs to `lem-sc-ample-iso`,
which retains that dependency. The ampleness definition remains a statement
dependency and its public import remains necessary.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The DAG omitted a declared lemma for
step 5's section transport across an isomorphism; it is now an explicit independent
item. Mathlib and upstream searches found no existing theorem for the absolute
ampleness predicate. LeanSearch returned Internal Server Error; LeanFinder, Loogle
and local searches worked. The empty case is preserved: no nonempty instance is used.
During development I mistakenly wrote temporary copies in the read-only repository;
I restored the original target text and removed the temporary auxiliary file.
All delivery files are in the designated sandbox.

## New nodes

`lem-sc-ample-iso`, in `lean/Sheaf/AlgebraicGeometry/AmpleIso.lean`, states isomorphism
invariance of the absolute ampleness predicate. It is the section-transport part
of the parent node's step 5, with searches, source, full proof, and unchanged unit route.
No change record is needed: no existing public interface changed.

## Second reading by H2

1. **Visibility and statements.** Compared both delivered modules with the repository
versions. The target theorem signature and all existing declarations are unchanged;
the new `AmpleIso` declaration is recorded by its node. Verdict: pass.
2. **Proof and axioms.** Compiled all sandbox modules with `lcompile.py --all`.
The target has no `sorry`; the only remaining `sorry` is the named split theorem
`isAmple_iff_of_iso`, with its node and proof docstring. No forbidden declarations
were found. Verdict: pass subject to the split theorem remaining open.
Scratch-copy `#print axioms` for both delivered theorems showed exactly `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx`; the latter comes from open
dependencies, including the split theorem. Removed the scratch copy afterward.
3. **Split statements.** Checked `isAmple_iff_of_iso` against the definition of
`IsAmple`: it is the generic isomorphism-transport step, with no extra hypotheses or
weakened conclusion, and local searches found no existing duplicate. Verdict: pass.
An independent LeanFinder search for sheaf isomorphisms transporting nonvanishing
loci found restriction/basic-open results and `Hom.isIso_iff_isIso_app`, but no
absolute ampleness transport theorem. Loogle did not know `IsAmple`. The empty
scheme case has a vacuous point condition; for the identity isomorphism this is
reflexivity. No nonempty hypothesis is needed in either case.
4. **Route and pruning.** The unit route and all six geometric steps remain. The
proof uses the shorter direct Noetherian and homeomorphism instances and records the
four obsolete direct proof edges listed above. The unit's `realized` statement
is `thm-sc-proper-cohomology` and its steps list is empty; neither is bypassed or
changed by this local six-step reduction. Verdict: pass.
5. **DAG agreement.** The parent node's proof and `proof_deps` match the Lean proof,
and `lem-sc-ample-iso` contains the required metadata, source, searches, and Lean
record. Verdict: pass.

Changed this report section and completed the list of removed direct proof edges;
no Lean declarations or statements were changed.
