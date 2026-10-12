## What changed

Proved `CategoryTheory.siteHigherDirectImageSheafifiedPresheaf` without changing its
signature. Lifted the sheafification counit natural isomorphism to complexes using
`NatIso.mapHomologicalComplex`, registered its `IsIso` instance, and used preservation
of isomorphisms by homology and composition. Both outside factors already are inverse
isomorphisms. The covering witnesses are explicitly retained to avoid unused-variable
warnings; continuity is supplied by the existing instance hypothesis.

Updated the existing node's proof route and proof dependencies. No new statements,
definitions, modules, or proof obligations were introduced. The node is below the unit's
realized statements and steps; the unit route is unchanged.

## Proved and sorry left

Proved `CategoryTheory.siteHigherDirectImageSheafifiedPresheaf`
(blueprint: lem-weil-pbc-site-higher-direct-image-sheafified-presheaf): 1 of 1 original
sorries removed. No sorry remains in the delivery and none is split off.
Local compilation passes without warnings. The delivery dry run checks local and server
compilation, the axiom probe, and preflight before reporting OK.

## No longer needed

Removed redundant direct public imports:

- `Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck`
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
- `Mathlib.CategoryTheory.Sites.Sheafification`
- `Mathlib.CategoryTheory.Sites.Abelian`
- `Mathlib.CategoryTheory.Sites.Continuous`
- `Mathlib.Algebra.Homology.Additive`
- `Mathlib.CategoryTheory.Sites.LeftExact`
- `Mathlib.Algebra.Category.Grp.Colimits`
- `Mathlib.Algebra.Category.Grp.FilteredColimits`
- `Mathlib.CategoryTheory.Abelian.Injective.Resolution`

The other nine removed modules remain publicly available through the retained imports.
The removed SheafCohomology.Basic is explicitly publicly imported by both direct
importers, which import this item privately. No downstream adaptation is needed.
The public-import pruning is recorded in
`coord/changes/site-higher-direct-image-imports.md`.

The proof no longer needs the separate nodes
`lem-weil-pbc-abelian-presheaves-evaluation-exact` and
`lem-weil-pbc-left-exact-injective-resolution-degree-zero`; removed these from
`proof_deps`. Their modules are Mathlib leaves, not project modules to delete.
Evaluation is unnecessary because the statement defines its presheaf by complex
homology already. Degree-zero resolution construction is unnecessary because a
resolution is supplied and `isoRightDerivedObj` works in every degree.
The other original dependencies remain in the node as the source of the notions,
instances, and isomorphisms actually used. No Sheaf or WeilConjectures dependency
modules were imported or are newly eligible for removal on this item's evidence.

## Where the brief, the DAG or earlier work was wrong

The existing signature already packages the exact-functor homology comparison and
resolution comparison as isomorphisms. Its missing proof is consequently only the
counit's passage to complexes, rather than the full construction of cocycle maps in
the five-step natural-language plan. No false statement or definition was found.
The covering witnesses and pullback exactness hypotheses are stronger than this
isomorphism proof needs, but all binders and the signature have been kept unchanged.
The docstring's separate identification with `Sheaf.H'` is still a bridge outside
this theorem, as the original docstring explicitly records.

Read the source proof at https://stacks.math.columbia.edu/tag/072W, since the local
literature checkout does not include the cited TeX file. Searched with LeanFinder
(natural isomorphisms on complexes), Loogle (`mapHomologicalComplex`, `IsIso`), and
grep, plus source-library searches. LeanFinder found `NatIso.mapHomologicalComplex`;
Mathlib also has `sheafification_reflective` and `isoRightDerivedObj`. Checked the
zero degree, zero sheaf, and arbitrary resolution cases: the proof uses only
isomorphisms, so it excludes none of them.


## Second reading by Q2

1. PASS. Compared the sole delivered Lean module with the repository using `diff`
   and checked the complete existing theorem signature byte for byte. All binders,
   hypotheses, and the conclusion are unchanged. No definitions or new declarations
   occur. The public import removals have the supplied change record; read both direct
   importers and verified their own public import of SheafCohomology.Basic.
2. PASS. Compiled the module using lcompile.py without errors or warnings. A scratch
   copy with `#print axioms CategoryTheory.siteHigherDirectImageSheafifiedPresheaf`
   reports exactly propext, Classical.choice, Quot.sound. No sorry, axiom, unsafe,
   opaque, implemented_by, extern, or hollow definition occurs. Read the Mathlib
   definitions of NatIso.mapHomologicalComplex and sheafification_reflective: the
   local IsIso witness has exactly the mapped counit as its hom, so infer_instance
   proves the displayed composite without an additional assumption.
3. PASS (no split statements). No new theorem, module, node, or sorry was introduced.
   Checked degree zero and the zero sheaf: each of the three factors is an isomorphism
   uniformly in q and in the supplied resolution, without a positivity or nonzero
   requirement. Searched the library and Mathlib with rg and repeated a Loogle search
   for mapHomologicalComplex; the existing NatIso construction is the needed lemma.
4. PASS after one import repair. Tested deletion of each of the six retained imports
   in scratch copies. PrecoverageToGrothendieck alone was redundant; the other five
   are required for the signature's notions or instances (sheafPullback,
   InjectiveResolution, abelian sheaves, HasInjectiveResolutions, AddCommGrpCat).
   Removed that redundant import: its public path is Pullback -> Continuous ->
   Hypercover.IsSheaf -> Hypercover.One -> Coverage -> PrecoverageToGrothendieck.
   Updated the change record's New imports and the No longer needed list. The two
   removed proof dependencies exhaust the old proof_deps missing from the new list.
   Read dag/units/sk-thm-p1.json: this item and the two pruned nodes are below its
   realized statement and steps; no realized node or unit route is bypassed.
5. PASS. The node's statement, stmt_deps, and lean signature are unchanged. Read all
   retained dependency records: they supply the Mathlib notions, exactness instances,
   homology comparison, enough injectives, and counit isomorphism used by the signature
   and proof. The union of the proof steps' uses equals proof_deps. The worker's new
   proof and proof_origin accurately describe the Mathlib route. No new node requires
   the stage-3 new-node fields.

Second reading changed only the redundant PrecoverageToGrothendieck direct public
import, its change record and pruning report, and added this review. The proof was
left intact. Final local/server compilation and preflight are checked by deliver3.py.
