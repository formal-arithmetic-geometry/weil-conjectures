## What changed

Proved the target theorem using the derived internal-Hom comparison. Added a bounded exact-term Hom lemma as a separate intermediate theorem. The finite-free exactness result is transported to each strictly perfect term by an explicit retract of short complexes.

## Proved and sorry left

`AlgebraicGeometry.Scheme.isIso_homComplex_resolution_of_isStrictlyPerfect` has its original hole closed by a reduction. One hole is added: `CategoryTheory.quasiIso_homComplex_map_of_bounded_exact_terms`, node `lem-pc-bounded-exact-term-hom-quasi-iso`, remains `sorry`. This is a decomposition (one hole closed, one added; net zero), not an unconditional proof: its axioms still include `sorryAx` through the new lemma and open dependencies. No hole remains in the item module. The finite-free retract and short-exact retract helpers are fully proved.

## No longer needed

No old `proof_deps` node or module is pruned. The direct proof-only import `Sheaf.Algebra.Homology.HomComplex` is replaced by `Sheaf.Algebra.Homology.BoundedExactTermHomQuasiIso`; HomComplex remains reachable and is used. The new module omits redundant `Mathlib.Algebra.Category.Ring.Limits` and uses the smaller `Mathlib.Algebra.Homology.ShortComplex.ShortExact` in place of `Mathlib.CategoryTheory.Abelian.ShortExact`. Its remaining public imports provide signature types or instances. The canonical finite-free identifications returned by `finiteFreeInternalHomExact` are not used; only its short-exactness conclusion is needed.

## Where the brief, the DAG or earlier work was wrong

The original plan omitted a formal intermediate theorem for the bounded stupid-truncation induction. That argument is isolated as `lem-pc-bounded-exact-term-hom-quasi-iso`. The first worker's item proof steps omitted `elementary` flags and did not have `proof_deps` equal to the union of `uses`. The new node's proof mentioned the long exact sequence and five lemma without citing their existing nodes. These records are repaired. Tag 08DM proves the representation via local homotopy-category comparison; the finite-filtration proof is an adaptation, not a verbatim argument of that source. The source checkout is absent locally, so the second reader read the Stacks tag pages.

## New nodes

`lem-pc-bounded-exact-term-hom-quasi-iso` records the finite-filtration quasi-isomorphism argument and is implemented by `Sheaf.Algebra.Homology.BoundedExactTermHomQuasiIso`.

## Earlier second reading (a previous round; superseded)

The intermediate statement is strictly smaller than the target: it only asserts preservation of quasi-isomorphisms by a bounded Hom complex. The target retains the stated affine, strictly perfect, K-injective, and derived-category hypotheses.


## Second reading by S2

1. **Interface: pass.** Compared the entire item module with the read-only repository
   using `diff -u`, then compared the existing public theorem signature byte for byte.
   It is identical after restoring one extra space before `:= by`. Its affine-open,
   derived-category, strictly-perfect, arbitrary-second-complex, and universally
   quantified functorial K-injective-replacement hypotheses and both conclusions
   are unchanged. No existing definition changes and no change record is needed.
   The only additional declarations in the item are private proved helpers.
2. **Proof and trust: pass as a decomposition.** Compiled both delivered modules in
   import order through `lcompile.py --all`: no errors or warnings (6.8 s and 36.0 s).
   The item contains zero `sorry`; the new module contains exactly its reported
   named theorem's `:= by sorry`. No forbidden declarations, data definitions, or
   witnesses chosen from unproved existence statements are added. Compiled a scratch
   copy with `#print axioms` for the public theorem, the new theorem, and both private
   helpers. The short-exact retract helper uses only `propext`, `Classical.choice`,
   and `Quot.sound`. The other three use those axioms and `sorryAx`, as expected
   from the open finite-free theorem and new filtration lemma. This does not certify
   the target without `sorryAx` and is not reported as net proof progress.
3. **Split statement: pass.** Read the new Lean statement, its full docstring proof,
   and node `lem-pc-bounded-exact-term-hom-quasi-iso`. Its boundedness and preservation
   of every short exact sequence are precisely what the reduction supplies; no
   boundedness of M or N is used. Checked P=0 (including b<a), a one-degree P, free
   rank zero, and negative degree shifts. A one-degree source is shifted degreewise
   exact Hom; successive stupid tails give the correctly oriented sequence
   Hom(G_k,-) to Hom(T_k,-) to Hom(T_{k+1},-). Only finitely many factors survive,
   so exactness of infinite products is not assumed. This is strictly the
   filtration part: it supplies neither exactness of projective-term Hom nor the
   K-injective/derived-category comparison, both handled in the item.
   Read [Stacks 08DM](https://stacks.math.columbia.edu/tag/08DM) and
   [Stacks 0117](https://stacks.math.columbia.edu/tag/0117); the latter supplies
   the natural long exact sequence used in the adapted filtration argument.
   Searched Mathlib through msearch with the new query
   “An exact functor applied degreewise to complexes preserves quasi-isomorphisms;
   bounded source internal Hom”, Loogle `"QuasiIso", "map"`, and grep
   `quasiIso.*(hom|total)|preserv.*quasi|map.*quasiIso` in Algebra/Homology.
   Read `HomologicalComplex.quasiIso_map_of_preservesHomology` (QuasiIso.lean:280)
   and the natural long exact sequence maps (HomologySequenceLemmas.lean:82–115).
   These address the graded pieces and induction, not the complete Hom-complex
   result. Searches of repository Lean, upstream WeilConjectures, and DAG nodes
   found no duplicate. Existing bounded-above finite-free Hom results impose a
   bounded-below target and do not close this arbitrary-target statement. The
   imported blueprint source directory is absent here; the available blueprint
   unit and ancestor records were read. Ran the read-only blueprint index search
   for “bounded Hom” and the ancestor query for the item. No few-minute direct proof was found.
4. **Route and pruning: pass after import repair.** Read PerfectComplex,
   FiniteFreeInternalHomExact, HomComplex, and DerivedInternalHom. The retract maps
   precompose with π and ι in the correct contravariant order, with composite
   homObjMap(ι ≫ π,id)=id. Homology, mono and epi retract calculations are explicit.
   The bounded lemma applies to η.app M; Q then inverts the resulting quasi-isomorphism.
   The representation composes this isomorphism with the inverse component of
   derivedInternalHom_comparison. The actual K-injective replacement is constructed
   by the upstream resolution functor. No old proof dependency is removed or unit
   bypassed. Read `dag/units/sk-thm-picard-duality.json`: its `realized` lists are
   empty and are not modified. Retained the finite-free and derived-Hom route.
   Removed the redundant Ring.Limits import in the new module and replaced
   Abelian.ShortExact with ShortComplex.ShortExact. Verified that omitting
   Grp.FilteredColimits fails the signature's homology instance, then restored it;
   all remaining public imports serve signature types or their required instances.
5. **Nodes: pass after repair.** Item proof steps now have `elementary` flags and
   their `uses` union is exactly `proof_deps`, retaining every old dependency.
   The new node has a self-contained statement matching Lean, source and adapted
   proof origin, creation/module records, and logged Mathlib searches. Corrected its blueprint ancestry to
   `lem-sc-finite-duality`, through the item and its parent comparison node.
   Expanded
   its proof to single-degree base, split filtration, and finite induction, citing
   existing nodes `lem-sp-exact-functor-preserves-homology`,
   `lem-weil-pbc-exact-functor-complex-cohomology`,
   `lem-weil-pbc-complex-ses-homology-long-exact`, and `lem-weil-pbc-five-lemma`.
   Read their statements and Mathlib matches: they supply exactly the exactness
   criterion, natural cohomology comparison, long exact sequence and five lemma
   used. These are Mathlib tools, not replacement unit routes. Existing node
   signatures and definitions remain unchanged.

Second-reading changes: restored signature whitespace; minimized the new module's
imports; repaired and expanded DAG proof steps/citations and the adapted proof origin;
corrected the report to count one closed hole and one added hole as a decomposition.
The existing Lean proof bodies were retained.
