## What changed

Repair of the return for reviewed head `7a2981396` (reviewer X-7a298):
the sole return point was a connection closure during landing, after proof review
passed. The proof, node, and change record remain as reviewed. The delivery tool
reconstructs the commit on current `sheaf-dag` and repeats local compilation, the
axiom probe, server compilation, and preflight before the second reader delivers.

Proved all four original proof gaps in
`Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage`, with signatures unchanged.
Additivity follows sectionwise by extensionality and reflexivity. Inversion follows
naturality, two-out-of-three, and preservation of homotopy equivalences. The natural
factorization composes the localized resolution map, the derived unit on K-injectives,
and canonical quotient comparisons. Any resolution computes the functor by mapping
its localized quasi-isomorphism and using `rightDerivedFunctorObjQIso`.

Added proof-only imports of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective` and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`.
Replaced the proposition-valued Grothendieck instance proof by the existing source
library theorem and updated the node proof to record this route. See
`coord/changes/P1-ringed-space-direct-image-grothendieck.md`.

## Proved and sorry left

Proved:
- `AlgebraicGeometry.RingedSpace.moduleDirectImage_additive_proof`.
- `AlgebraicGeometry.RingedSpace.resolvedModuleDirectImage_inverts`.
- `AlgebraicGeometry.RingedSpace.derivedModuleDirectImageFactorization`.
- `AlgebraicGeometry.RingedSpace.derivedModuleDirectImage_computed_by_resolution`.

No sorry remains in the item, and none was added. No new modules or statements.
Local single-file compilation succeeds. The source-derived-category section parameter
of the inversion theorem is retained for signature compatibility, with the unused-section
parameter linter disabled only for that theorem.

## No longer needed

Removed import `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions` and the former
instance body's use of `prop-pur-kinjective-resolutions-exist`. The old node had empty
`proof_deps`, so no old recorded proof-dependency edge was removed. The stronger existence theorem's
specified generator and injective terms are unnecessary here: the source library
proves Grothendieckness and supplies the functorial K-injective replacement directly.
Its descendant nodes and modules are not required through this removed edge; they may
remain required elsewhere. The source Grothendieck resolution module stays, realizing
`lem-weil-pbc-kinjective-functorial-existence`, and Mathlib's K-injective homotopy theorem
stays, realizing `lem-weil-pbc-kinjective-hom-derived`.

For computation by an arbitrary resolution, no separate lifting/comparison construction
is needed: the existing derived-unit computation API gives it directly. No additional
DAG node or import is required for that construction. No unit statement or step is
bypassed (the unit's realized lists are empty).

## Where the brief, the DAG or earlier work was wrong

The item's node had empty proof/proof_deps despite the detailed construction in its
statement and docstrings. It now records the Lean argument. Earlier work used a stronger
unfinished sheaf-resolution theorem for Grothendieckness although the source library
already proves exactly that property. The original theorem statements are correct.
Searches used Lean Finder, Loogle, and local ripgrep; the shortest applicable result
was the existing source-library K-injective computation isomorphism.


## Earlier second reading (a previous round; superseded)

1. Compared the entire delivered module with the repository version and checked the
   declaration tables: every existing signature is byte-for-byte unchanged; no new
   declaration exists. The only changed instance body proves the identical proposition,
   so proof irrelevance preserves all definitions using it. Its change record is
   `coord/changes/P1-ringed-space-direct-image-grothendieck.md`. Verdict: pass.
2. Independently compiled the module with `lcompile.py` without errors or warnings.
   Compiled a scratch copy with `#print axioms` for the changed instance and all four
   formerly open theorems: each uses only `propext`, `Classical.choice`, and `Quot.sound`.
   No sorry, forbidden declaration, or hollow definition occurs. Read the naturality,
   two-out-of-three, homotopy-equivalence, and natural-isomorphism compositions in full,
   including their directions. Verdict: pass.
3. No statements were split off, and no new statements or nodes were added. Checked
   the existing quasi-isomorphism/homotopy-equivalence theorem and upstream computation
   isomorphism against their actual types. Identity and zero-complex cases need no
   extra hypotheses; no boundedness or nonzero assumption slipped in. Verdict: pass.
4. Independently searched Lean Finder for the unbounded natural comparison, Loogle
   for the K-injective homotopy criterion, and the local library for computation and
   pushforward APIs. The classical degreewise right-derived hits do not replace this
   unbounded construction. The existing upstream computation isomorphism is already
   used. Retained imports supply moduleRings, the functorial resolution definition,
   K-injectivity, and rightDerivedFunctor; both added imports are proof-only.
   Checked `dag/units/sk-thm-picard-duality.json`: its realized statement and sole step
   lists are empty, and no recorded unit realization is bypassed. The pruning list
   covers the removed resolution import. Verdict: pass.
5. Compared the node JSON with the repository: only proof, proof_deps, and proof_origin
   changed. The two recorded dependencies are precisely the functorial replacement
   and K-injective homotopy criterion used in Lean; the proof text also names the
   proved upstream Grothendieck and derived-unit APIs. No node statement changed.
   Verified downstream textual uses of the changed instance: only its own declaration,
   with no downstream source use. Verdict: pass.

Second reading changed only this report: clarified that the removed resolution import
had been used by the old instance body, while the old node's proof_deps was empty.
No Lean repair was needed.

## Second reading by P1

1. Compared the complete module with the current repository version, and checked
   every declaration with the delivery parser: no signature changed, no declaration
   was added, and all non-proof definition bodies are unchanged. The proposition-valued
   Grothendieck instance replacement is covered by the change record; proof irrelevance
   preserves the definitions using it. Verdict: pass.
2. Independently compiled the delivered file, then a fresh scratch copy with
   `#print axioms` for all nine declarations. All use only `propext`,
   `Classical.choice`, and `Quot.sound`. No sorry or forbidden construct occurs.
   Read the naturality/two-out-of-three argument and each of the five natural
   isomorphisms in the factorization, including their directions. Verdict: pass.
3. No split-off statement, new module, or new node exists. All four original holes
   are closed, with no hole added. The arbitrary-resolution argument uses the
   actual upstream computation isomorphism, with exactly the given K-injectivity
   and quasi-isomorphism assumptions. Identity maps and zero complexes require
   no additional boundedness or nonzero assumption. Verdict: pass.
4. Repeated Lean Finder search for the natural unbounded comparison, Loogle search
   for `CochainComplex.IsKInjective.quasiIso_iff`, and local searches for computation
   and additive pushforward APIs. The existing upstream computation isomorphism
   already supplies the shortest computation proof. The original proof_deps list
   is empty; the report covers the removed resolution import and its former use.
   Checked the unit's realized statement and step lists: both are empty, so no
   recorded unit route is bypassed. Retained public imports supply the public
   definitions and signatures. Corrected the direct Mathlib K-injective import
   to a plain proof import; its types are already public through the derived-functor
   definitions module. Verdict: pass after this import repair.
5. Compared the complete node JSON with the repository: only proof, proof_deps,
   and proof_origin differ. Read both dependency nodes and their actual source
   declarations: they match functorial replacement and the K-injective homotopy
   criterion used by Lean. The proof text accurately records the upstream
   Grothendieck and derived-unit APIs. The node statement and unit are unchanged.
   Local search confirms no downstream textual user of the replaced instance.
   Verdict: pass.

Second reading changed the direct Mathlib K-injective import from public to plain,
documented that repair in the change record, and added this independent review.
No proof or signature repair was needed.
