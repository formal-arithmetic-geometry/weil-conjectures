## What changed

Retained the private theorem `commShift_of_localization` in
`Sheaf.CategoryTheory.ExtExactFunctorIdentityComparison`, restoring it relative to the
previous rejected delivery. Against the current repository, the sole Lean difference is
a comment documenting its downstream use. The public theorem
`CategoryTheory.Abelian.Ext.exactFunctorIdentityComparison`, its signature, docstring,
and proof are unchanged. The restoration is required by the importer
`HigherDirectImageRawPullbackIdentity`, which imports this module with `import all` and
calls the helper at line 56. Reproducing the prior deletion produced the compiler error
`Unknown constant CategoryTheory.Abelian.Ext.commShift_of_localization`.

## Proved and sorry left

Verified the existing proof of
`CategoryTheory.Abelian.Ext.exactFunctorIdentityComparison`. The repository baseline
already proves it: holes closed by this delivery: none (0 of 0); holes added: none;
split-off statements: none. No `sorry` remains in the module. This is a repair cleanup,
not additional proof progress. A scratch copy with `#print axioms` compiled and reported
exactly `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

No imports, proof dependency nodes, or modules were pruned. The private helper
`commShift_of_localization` is retained because HigherDirectImageRawPullbackIdentity imports it with import all and calls it at line 56. Both old proof dependencies remain used:
`lem-weil-pbc-exact-functor-derived-factorization` and `def-pc-ext`, through Mathlib.

## Where the brief, the DAG or earlier work was wrong

The repository already contains the completed proof. The repair queue's upstream review
#1424 suggests `mapExactFunctor_eq_of_iso` and `mapExactFunctor_id`, but neither exists
in the pinned Mathlib or upstream sources. The upstream Ext/Map extension contains
vanishing/lifting criteria rather than the suggested API. The direct localization proof
therefore stays; no unproved substitute or stronger hypothesis is introduced.

## Earlier second reading (a previous round; superseded)

The earlier report said the existing proof compiled after pruning the unused private
localization helper. The independent checks below supersede that report.

## Earlier second reading (a previous round; superseded)

1. Compared the repaired module against the repository using `diff -u`: the private
   helper `commShift_of_localization` is retained, since deleting it reproduces
   `Unknown constant CategoryTheory.Abelian.Ext.commShift_of_localization` when
   `HigherDirectImageRawPullbackIdentity` is compiled. All public signatures, proof
   bodies, visibility, imports, and definitions are otherwise unchanged. No change
   record is needed. Recompiled the unchanged importer against the restored delivered
   module successfully (41.2 seconds). Verdict: pass.
2. Compiled the delivered file with `lcompile.py` without errors or warnings. Scanned
   for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, and `extern`: none.
   Compiled a scratch copy ending in `#print axioms` for the public theorem: only
   `propext`, `Classical.choice`, and `Quot.sound`. There are no local data definitions
   and no witnesses chosen from an unproved existence theorem. Verdict: pass.
3. There are no new statements or split-off holes. Checked the existing statement's
   degree-zero case (naturality of e), identity-functor case, and zero class: all agree
   with the displayed Ext square. Verdict: pass; split-off requirements are vacuous.
4. Read the proof from its conclusion backward: `Ext.ext` reduces to shifted morphisms;
   `equiv_smallShiftedHomMap` with the identity functor computes the action; `hx` checks
   the component in degree zero and uses zero objects otherwise; `hy` cancels inverses.
   The composite termwise isomorphism is checked for shift compatibility before
   localization. Searched pinned Mathlib, upstream Ext/Map, and repository Lean for the
   suggested iso/identity API and alternative Ext map comparisons. No applicable shorter
   existing theorem was found. The sole public import supplies `Ext.mapExactFunctor`
   in the signature as well as proof tools, so it is correctly public. The two old
   proof dependencies remain used; `dag/units/sk-thm-p1.json` realized route is unchanged,
   and this auxiliary node is below the unit level. Verdict: pass.
5. Read `lem-weil-pbc-ext-exact-functor-identity-comparison.json` and both dependency
   nodes. Its two proof steps describe exactly the termwise shift check, localized
   comparison, single-complex calculation, and cancellation in Lean. `proof_deps`
   and `proof_origin` already describe this unchanged proof; the recorded Lean statement
   matches its signature. There are no new nodes. Verdict: pass.

Second reading changes: corrected the report's account of the baseline, stated zero
holes closed and added explicitly, documented the unavailable suggested upstream API,
and recorded these independent checks. The returned delivery required restoring the
private helper; the restoration is now verified against its unchanged importer.

Repair validation: the deleted-helper regression reproduced the unknown-constant error
at importer line 56. The restored module and unchanged importer compile together. A
comment records why the private helper must remain; no importer adaptation is delivered.

## Second reading by B4

1. Compared the complete delivered module against the current repository with `diff -u`.
   The only difference is the retention comment above `commShift_of_localization`.
   Both theorem signatures, both proofs, visibility, imports, and docstrings are byte
   for byte unchanged. The earlier deleted-helper delivery is not the current baseline.
   No interface change or change record is needed. Verdict: pass.
2. Independently compiled the delivered module with `lcompile.py`; no errors or warnings.
   Scanned the delivered Lean for forbidden declarations and `sorry`: none. A fresh
   scratch copy includes both helpers and prints axioms for both declarations, rather
   than reusing the earlier scratch copy which omitted the helper. There are no local
   data definitions or arbitrary witnesses selected from unproved existence statements.
   Verdict: pass. Both fresh axiom checks report only propext, Classical.choice,
   and Quot.sound (2.4 seconds). The unchanged downstream importer compiled against
   this scratch module without errors or warnings (52.4 seconds).
3. No statement or split-off theorem is added. The unchanged public statement matches
   the node: arbitrary abelian C with small Ext, additive exact endofunctor F, natural
   isomorphism e to identity, all X and Y, and all natural degrees. Degree zero is the
   naturality square for e; a zero class gives zero on both sides; identity F with
   identity e gives identity transport. No case is excluded. Verdict: pass.
4. Read the proof backward from Ext.ext: shifted composition rewrites reduce the goal
   to hmap, hx, and hy. The Mathlib lemma equiv_smallShiftedHomMap (read at
   Localization/SmallShiftedHom.lean:421) accepts the identity localized functor and
   the shift-compatible comparison delta. The termwise composite eta commutes with
   shifts degreewise; hx checks its single-complex component at zero and uses the
   actual zero-object theorem in other degrees; hy cancels the corresponding inverses.
   Read pinned Ext/Map.lean and upstream WeilConjectures/Mathlib/.../Ext/Map.lean and
   searched pinned Mathlib, upstream derived-category extensions, and repository Lean
   for identity/iso mapExactFunctor comparisons. The proposed mapExactFunctor_eq_of_iso
   and mapExactFunctor_id API is absent. The existing localization reduction stays.
   The sole public import supplies mapExactFunctor in the public signature, so it must
   remain public. The private localization helper is required by the import-all user
   HigherDirectImageRawPullbackIdentity at line 56; it must remain too. Neither old
   dependency is pruned. The unchanged sk-thm-p1 realized route remains intact.
   Verdict: pass.
5. Read lem-weil-pbc-ext-exact-functor-identity-comparison and its two dependency nodes,
   def-pc-ext and lem-weil-pbc-exact-functor-derived-factorization, together with the
   unit's realized record. The node's two steps describe precisely eta/delta/hmap,
   single-complex evaluation, and inverse cancellation. Both dependencies are provided
   through Mathlib. Its recorded Lean statement agrees with the complete signature;
   proof_deps and proof_origin remain accurate for the unchanged proof. There are no
   delivered node files and no new node fields to validate. Verdict: pass.

Second reading changes: clarified the actual current-baseline difference in What changed
and appended this independent review. The Lean proof needs no repair. Holes closed: none
(0 of 0); holes added: none; split off: none; pruned: none.
