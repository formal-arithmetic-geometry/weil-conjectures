## What changed

Second reading replaced the first worker's injectivity/surjectivity split with a genuine
reduction of `AlgebraicGeometry.Etale.bijective_cohomologyMap_one_constantSheaf_of_henselianRing`.
The proof first obtains the existing finite etale pullback equivalence from the proper
henselian-pair hypotheses, then applies the general categorical H¹ implication in the new
`Sheaf.AlgebraicGeometry.FiniteEtaleEquivalenceH1` module. That implication has no ring,
properness, or closed-fibre hypotheses. The original two new modules and their nodes were
removed from this sandbox. All existing declaration signatures, definitions, docstrings and
other proofs are preserved byte for byte. No change record is required.

## Proved and sorry left

Newly reduced in the item:
`AlgebraicGeometry.Etale.bijective_cohomologyMap_one_constantSheaf_of_henselianRing`
(`lemma-weil-pbc-h1-torsor-comparison`). Its proof has no local sorry and actually uses
`Scheme.isEquivalence_pullback_finiteEtale_of_henselianRing`.

The four previously reduced theorems (finite locally constant representability, idempotent
lifting, finite etale equivalence, and its local-ring corollary) retain their existing proofs.
Their remaining upstream sorries are not new progress by K1.

One new named theorem remains entirely `:= by sorry`:
`AlgebraicGeometry.Etale.bijective_cohomologyMap_one_of_finiteEtale_equivalence`, node
`lem-weil-pbc-finite-etale-equivalence-h1`. It is the categorical part of the argument and has
a source, complete docstring proof, and matching node. This is a reduction, not an axiom-free
completion of H¹ comparison. All five theorems in the item still reach sorryAx upstream.

## No longer needed

Removed proof-only imports from the item:

- `Sheaf.AlgebraicGeometry.GaloisCategories`
- `WeilConjectures.CategoryTheory.Sites.Torsor`
- `WeilConjectures.ConstructibleSheaf.Defs`
- `WeilConjectures.Mathlib.RingTheory.Henselian`

The superseded sandbox imports `HenselianFiniteEtaleH1Injective` and
`HenselianFiniteEtaleH1Surjective` are replaced by `FiniteEtaleEquivalenceH1`; neither former
module nor former node is delivered.

Every old direct proof dependency removed from `lemma-weil-pbc-h1-torsor-comparison`:

- `def-weil-pbc-henselian-terminology`
- `def-weil-pbc-scheme-conventions`
- `def-galois-categories`
- `def-weil-pbc-finite-torsors`
- `thm-galois-torsor-h1`
- `lemma-constructible-pullback-constant`
- `def-weil-pbc-cohomology-pullback`
- `thm-galois-lc-etale`
- `def-weil-etale-morphism`
- `lem-weil-pbc-flat-lfp-open`
- `lem-weil-pbc-finite-proper`

These are removals from the combining proof only. The classification, constant-sheaf
coefficient identification, and open/closed-image facts remain in the general intermediate's
proof plan. No mathematical node or unit is declared globally obsolete.

## Where the brief, the DAG or earlier work was wrong

The first worker merely divided the original bijectivity goal into injectivity and
surjectivity under exactly the same hypotheses. That does not expose the existing finite
etale lifting theorem as a proved step, and leaves the same entire argument unresolved.
Its node signatures were not verbatim, its natural-language statements were not
self-contained, proof_deps were empty despite using torsor classification and lifting,
blueprint parents were absent, and the original H¹ node was not updated.

The short surjectivity docstring omitted lifting the M-action equations, reflection of the
simple-transitivity isomorphism, and surjectivity of the lifted structure map. The replacement
spells out these checks and the inverse-image coefficient codomain. It uses the categorical
last implication in Stacks Tag 0A5G; the actual henselian equivalence stays in the item's proof.

Existing `EtaleTorsorDescent`, `EtaleTorsorCohomology`, and
`FundamentalGroup.LocallyConstantEquivalence` import this item, so they cannot simply be
imported to discharge its remaining categorical helper. Their classifications/naturality
explain the intended argument but require resolving module direction before reuse. The
replacement helper can be stated without importing the item. No route through Gabber or
proper base change is taken: those later theorems use this comparison.

LeanFinder returned only unrelated cotangent/group-cohomology results; Loogle and the Mathlib
source grep found no match. LeanSearch returned Internal Server Error, recorded as unavailable
rather than a successful search. All searches were run through msearch.py and their actual
records are used in the new node.

## New nodes

`lem-weil-pbc-finite-etale-equivalence-h1`, module
`Sheaf.AlgebraicGeometry.FiniteEtaleEquivalenceH1`: the general implication from equivalence
of finite etale pullback to finite constant H¹ comparison. The hypothesis supplies exactly
the categorical input, independent of its henselian/proper proof. Its source is Stacks 0A5G's
last paragraph, with the action and open/closed-image details supplied explicitly. No change
records were needed.

## Second reading by K1

1. Used diff on each existing delivered module and parsed all declarations against the
   repository. Verdict: every existing signature and definition is byte-for-byte identical;
   only H¹'s body and plain proof imports differ. Restored the worker's incidental signature
   whitespace changes. Existing proofs and target statements are unchanged.
2. Ran lcompile.py --all on both final modules: no errors or warnings. Compiled scratch
   copies with #print axioms for every declaration, including the instance and definition.
   Only propext, Classical.choice, Quot.sound and the explicitly unresolved sorryAx occur.
   Scanned for forbidden axiom/unsafe/opaque/implemented_by/extern/debug.skipKernelTC constructs;
   none occur. There is exactly one new sorry, in the named categorical theorem, and no sorry
   in any definition. Verdict: checked reduction with the remaining gap honestly reported.
3. Read the first split and rejected it as an uninformative division of the original goal.
   Read Stacks 0A5G and 03AJ online and searched the library with finite-etale invariance and
   torsor pullback terminology, independently of the worker's queries. The replacement follows
   the source's categorical implication. Tested empty bases, the zero group, and a non-surjective
   closed immersion: reflection of the clopen image inclusion supplies surjectivity upstairs,
   so the proof never assumes i is surjective. For a finite group in Type (u+1), its finite
   indexing set can be resized into Type u before forming the scheme coproduct. Naturality
   includes the coefficient isomorphism, so the exact inverse-image codomain is respected.
   Verdict: the new statement is true and isolates the categorical step; not closable in a
   few minutes from the present upstream modules because their classification imports cycle.
4. Read the repaired proof from the top: the existing henselian finite etale equivalence
   is used before the general H¹ implication. Only statement notions are public imports
   in the helper, and its import in the item is plain. Reviewed sk-thm-p1.realized: its
   strict-henselian torsor route is retained, with no realized node removed. The new proof
   uses the unit's finite etale lifting theorem, not a stronger later cohomology comparison.
   Listed every removed original direct proof dependency above, distinguishing these from
   globally obsolete nodes. Verdict: route kept and pruning report complete.
5. Compared the changed existing node with the repository: changes are restricted to proof,
   proof_deps and proof_origin. Its two steps name exactly the Lean declarations applied.
   Checked the new node's self-contained statement, cited notions, union of step dependencies,
   source, honest search records, creation data, parent blueprint, unit/chapter and verbatim
   Lean signature. Its steps match the docstring including action laws, simple transitivity,
   open/closed-image surjectivity and coefficient transport. Verdict: metadata repaired.

Second reading changed the uninformative split into a reduction through the already proved
finite etale equivalence, replaced two proposed helpers with one general categorical helper,
completed its mathematical proof explanation, repaired all affected node metadata and the
pruning report, and restored incidental whitespace in existing signatures.
