## What changed

Replaced the hole in `CategoryTheory.homComplex_restrict_open` with the degreewise
product construction, proved product preservation under restriction, constructed
inverse product maps, proved their projection equations, and assembled the chain
isomorphism with `HomologicalComplex.Hom.isoOfComponents`.

Added proof-only imports of
`Sheaf.Algebra.Homology.HomComplexRestrictOpenDifferential`,
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`, and
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products`. Existing public imports,
existing declaration signatures, and definitions are unchanged. Updated the parent
node's proof route and added the differential-compatibility node and module.

## Proved and sorry left

Closed the original hole in `CategoryTheory.homComplex_restrict_open`
(`lem-sc-hom-complex-restrict-open`). The item's module now contains no `sorry`.

Added one hole: `CategoryTheory.homComplex_restrict_open_differential`
(`lem-sc-hom-complex-restrict-open-differential`). Its entire proof is `:= by sorry`.
It assumes the already constructed degreewise isomorphisms and their equations
against every factor projection, and asserts only differential compatibility.
It does not assert existence of the degreewise maps or construct a chain
isomorphism. This delivery is a decomposition, not a net hole reduction.

Private helpers `over_products` and `fan_iso` are proved without holes.
The two delivered modules compile cleanly in dependency order with `lcompile.py --all`.

## No longer needed

Removed the direct import
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`; its declarations
remain available through `InternalHomOver`, which the product comparison needs.
Thus this removes a redundant direct import, not that module from the import closure.
Also removed the redundant direct imports
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomOver` and
`Sheaf.Algebra.Homology.HomComplexProjections`: the new differential module publicly
imports both because its statement uses their declarations. They remain in the
import closure. No mathematical dependency node or required unit step is pruned.
Every old `proof_deps` node remains used; `def-pur-hom-complex` is retained explicitly.

The earlier sandbox report described an obsolete component-existence module and
node, neither of which is delivered. The full degreewise product argument is now
proved, so no component-existence obligation is needed.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox report did not match its Lean files and lacked the new node
files. It referred to a component-existence statement instead of the remaining
differential-compatibility statement. This delivery replaces that report and supplies
the node files matching the actual construction.

The planned mathematics remains valid for the empty open, zero complexes, and
unbounded complexes: products use every integer factor; no exactness of infinite
products, finite truncation, boundedness, or K-injectivity is assumed. The new
statement was checked against these cases. The unit's `realized` record is empty,
and no blueprint unit statement or proof step is bypassed.

The source files under `literature/stacks-project/` are absent in this clone.
Read the authoritative online versions of Stacks Tags 0A8X and 08DL instead.
Tag 0A8X gives the precise signed differential; 08DL uses compatibility of the
underlying construction with restriction. The new obligation is the projectionwise
verification of that compatibility, described completely in its docstring and node.

Attempts to expand the existing iterated-site comparison or the large chosen
Hom-complex types while rewriting reached deterministic or single-file timeouts.
No definitions were changed to conceal this issue. The delivered proof uses the
existing projection interface and compiles without these expansions.

## New nodes

`lem-sc-hom-complex-restrict-open-differential`, in
`dag/nodes/sec-picard-framework/lem-sc-hom-complex-restrict-open-differential.json`,
states only the third step of the parent argument. Its module is
`Sheaf.Algebra.Homology.HomComplexRestrictOpenDifferential`; its declaration is
`CategoryTheory.homComplex_restrict_open_differential`. Its source is Stacks
Tag 0A8X, with the restriction construction of Tag 08DL. Searches through msearch
and local repository rg found no existing theorem for this equation; LeanSearch
was unavailable. No change record is needed: no existing statement, definition,
or public import was changed.

## Second reading by G1

1. Compared the delivered main module against the repository with `diff`, then
   compared its existing theorem signature byte for byte by extraction. Verdict:
   identical signature and docstring, no changed definition, no added hypothesis,
   no weakened conclusion, and unchanged existing public imports. The new module
   has no repository predecessor. Only `proof`, `proof_deps`, and `proof_origin`
   differ in the existing node. No change record is required.
2. Compiled both delivered files in import order using `lcompile.py --all`, then
   compiled scratch copies with `#print axioms` for the main theorem, differential
   theorem, and both private helpers. Verdict: clean compiles; helpers use only
   `propext`, `Classical.choice`, `Quot.sound`; the two public theorems additionally
   use `sorryAx` from the reported differential obligation. There is exactly one
   delivered hole, the whole proof of the named differential theorem. No forbidden
   axiom or implementation directive, no data hole, and no holed definition occurs.
   The chosen projections come from the already proved
   `homComplex_projections_exists`, whose underlying `homComplex_exists` is also
   proved in the repository. The isomorphisms are built by actual product lifts;
   the new holed theorem supplies only a proposition about those maps.
3. Read the complete differential statement, its docstring, its node, and the
   projection theorem's product and signed-differential clauses. Read Stacks
   [0A8X](https://stacks.math.columbia.edu/tag/0A8X) and
   [08DL](https://stacks.math.columbia.edu/tag/08DL), and inspected the source
   implementations `overHomObjIso` and `restrictOverHomObjFwd`. Verdict: the
   indices `p+n`, `p+m`, and `p+m-n` agree with both summands of the differential;
   the sign is the degree-n sign on both sides. The hypothesis fixes the maps by
   all product projections; the conclusion asks only that these given maps commute
   with adjacent differentials. This is strictly a part of the original argument,
   not a renamed existence-of-chain-isomorphism theorem. Zero complexes make both
   sides zero; an empty open needs no nonemptiness; arbitrary integer degrees
   require no finite support or boundedness. New msearch queries through LeanFinder
   (naturality of internal Hom under slice restriction), Loogle (`"homObjMap"`),
   and grep (`HomologicalComplex.*over|over.*HomologicalComplex|homObjMap.*over`),
   plus repository/upstream rg, found no theorem closing this obligation. The
   remaining source-level naturality verification requires more than a few-minute
   repair, so its named obligation is retained with its complete proof in words.
4. Read the argument downward: restriction preserves products by reflection from
   presheaves; factorwise `overHomObjIso` gives inverse product lifts; their
   equations feed differential compatibility; `isoOfComponents` assembles and
   reverses the chain isomorphism. Verdict: genuine reduction, with one hole closed
   and one strictly smaller hole added, hence decomposition and net zero holes.
   Removed two additional redundant direct imports and recompiled. No module is
   removed from the targets' import closure. The unit `sk-thm-picard-duality` has
   empty realized statement and step lists; no unit route or realized node is
   bypassed. All old mathematical dependencies remain used.
5. Compared both node records with the actual Lean declarations and proof.
   Verdict: new module, declaration, verbatim statement, source, docstring proof,
   created record, blueprint ancestry, chapter, unit, and search records agree.
   Parent steps match product preservation, factor lifts, and chain assembly.
   Restored `def-pur-hom-complex` in step 1 and `proof_deps`, since the proof still
   uses that definition; the original report's implicit deletion was inaccurate.

Changed only redundant direct imports, the parent dependency accounting, and this
report. Kept the correctly written product proofs and the differential statement.
