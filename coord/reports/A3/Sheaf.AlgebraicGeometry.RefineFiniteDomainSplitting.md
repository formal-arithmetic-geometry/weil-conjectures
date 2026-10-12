## What changed

Replaced the first worker's restatements by a real reduction in
`Sheaf.AlgebraicGeometry.RefineFiniteDomainSplitting`. The existing declaration
`exists_refinement_of_finite_domain_splitting` keeps its signature byte for byte.
Its proof constructs `t = ∏ j, s j`, its numerator `a`, `d = c * a`, and
`T = Localization.Away (algebraMap A (Localization.Away c) a)`. Mathlib proves
that `T` localizes at `t` and at `d`; its canonical equivalence with `A[1/d]`
provides the base algebra structure. The proof constructs
`A'' = T ⊗[A[1/c]] A'` and `E j = A'' ⊗[A'] D j` and combines two genuine
intermediate property theorems, each in its own module.

Added plain proof imports of `Mathlib.RingTheory.Localization.BaseChange`,
`Sheaf.AlgebraicGeometry.RefinementLocalizationGeometry`, and
`Sheaf.AlgebraicGeometry.ReducedProductLocalization`. The original public
imports and all existing public signatures remain unchanged. The two new
modules publicly import only what their statements need. No definition or
existing statement changed; no change record or forced adaptation is needed.
The original node's proof, proof_deps and proof_origin now follow the Lean proof.

## Proved and sorry left

Hole closed: `exists_refinement_of_finite_domain_splitting`
(node `lem-weil-pbc-refine-finite-domain-splitting`). The common-denominator
construction, nonvanishing, localization identification, scalar towers and
explicit witness packaging are proved in its body.

Holes added:

- `refinement_localization_geometry`, node
  `lem-weil-pbc-refinement-localization-geometry`, in
  `Sheaf.AlgebraicGeometry.RefinementLocalizationGeometry`.
- `reduced_product_localization`, node
  `lem-weil-pbc-reduced-product-localization`, in
  `Sheaf.AlgebraicGeometry.ReducedProductLocalization`.

These are the only two remaining sorries in the delivered files. This is a
**decomposition**, not a completed axiom-free proof: one hole closed and two
added, net -1 relative to the item's baseline. Neither lemma includes the
whole target conclusion: the first proves only geometric properties of fixed,
explicit tensor products and does not mention `B` or a reduced splitting; the
second proves only preservation of a splitting under a given localization and
has no domain, finite, Noetherian, etale or homeomorphism hypotheses. No data is
chosen from either unproved theorem. Both only prove properties of rings
already constructed by Mathlib.

## No longer needed

The discarded provisional module
`Sheaf.AlgebraicGeometry.RefineFiniteDomainSplittingData` and its provisional
nodes `lem-weil-pbc-refine-finite-domain-data` and
`lem-weil-pbc-refine-finite-domain-transport` are not delivered. These were not
in the repository, so their removal claims no library pruning credit.

The repository node's old proof_deps was empty: there are no old proof
dependency nodes or library modules to prune. No existing public import was
removed. Unrelated geometric imports were removed from the newly generated
reduced-product theorem, and unused nilradical/base-change imports from the
new geometric theorem. Library modules pruned: none.

## Where the brief, the DAG or earlier work was wrong

The first worker's `exists_refinement_data` repeated the target's entire
statement and was unused. `complete_refinement_from_data` repeated it again,
adding only a `True` argument. The target applied this second sorry with
`True.intro`, so it proved no reduction. The earlier report's claim that these
were strict intermediates was false. Their docstrings did not describe their
actual conclusions, and no existing target node update accompanied the proof.
All these faults are repaired in this delivery.

Read the cited blueprint text from the local literature mirror at
`/home/ubuntu/work-bp/sheaf/literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/lem-weil-pbc-finite-pushforward-generic-constructible.md`:
its finite-algebra calculation uses common localization, finite domain factors,
universal homeomorphisms and reduction. The delivered decomposition keeps
that route. It makes no change to a unit or chapter.

## New nodes

`lem-weil-pbc-refinement-localization-geometry` states properties of the explicit
rings `C' = T ⊗[S] C` and `E j = C' ⊗[C] D j`, where `T` localizes at the product
of the `s j` and `U -> T` is a bijective base-ring map. Its proof uses injection
from spectrum surjectivity, localization of domains, preservation of finite
etale surjective covers, and universal-homeomorphism base change.

`lem-weil-pbc-reduced-product-localization` isolates localization of the reduced
product equivalence, independent of the geometric part. Its docstring explains
tensor associativity, localization of the nilradical and finite products,
including the empty product. Mathlib provides relevant infrastructure
(`IsLocalization.map_radical`, Localization/Pi and localization base change),
but the searches found no theorem combining it in this exact algebra-equivalence
statement. Neither remaining proof is a short direct application of a found
lemma. No change records are needed.

## Second reading by A3

1. Compared the delivered target file against the repository using `diff`.
   Every original binder, instance, hypothesis, universe and conclusion is
   byte for byte unchanged: Noetherian domain `A`, finite `B`, nonzero `c`, the
   finite etale domain cover `A'`, the surjective spectrum map, all finite
   domain factors with injective maps and scalar towers, the reduced splitting,
   the nonzero `s j` and the specified universal homeomorphisms. The conclusion
   still supplies a nonzero `d`, a finite etale surjective cover over `A[1/d]`,
   finite domain factors with both surjectivity and universal homeomorphism,
   and the same reduced algebra equivalence. Verdict: pass after replacing
   the vacuous proof. No other existing module is adapted.
2. Compiled every delivered file locally through `lcompile.py` in import order.
   Only the two named intermediate theorems contain `sorry`; no `axiom`,
   `unsafe`, `opaque`, `implemented_by`, `extern`, holed definition or local
   anonymous sorry exists. Explicit `#print axioms` probes are checked for
   all three delivered declarations; inherited `sorryAx` is expected until
   the two property lemmas are proved. All ring data in the proof is built by
   localization and tensor products, or by Mathlib's proved localization
   universal property and section. Verdict: valid conditional reduction.
3. Checked both new statements clause by clause and their natural-language
   proofs. In the geometric lemma spectrum surjectivity and reducedness of S
   justify injection, so nonzero denominators survive in all D_j. Units s_j
   allow the correct homeomorphism base changes. The reduced-product lemma
   concerns only an already specified localization, and localization commutes
   with reduction and finite products. For r=0 the product denominator is 1,
   the geometric factor assertion is vacuous, and the reduced product is the
   zero ring; for r=1 it is the usual single-factor localization. Characteristic
   is unrestricted. S is a domain in the geometric lemma, while zero rings
   are permitted in the reduced-product lemma. Searched with new terms using
   LeanFinder, grep of Mathlib, and `rg` over both library roots and upstream.
   LeanSearch returned Internal Server Error and is recorded as unavailable;
   no successful verdict is invented. Verdict: true strict intermediate
   statements, no duplicate theorem found.
4. Read the proof top downward. Mathlib now handles the denominator construction,
   the associated numerator, successive localization and canonical equivalence;
   the two remaining lemmas address separate later steps only. Proof-only
   imports are plain. New theorem imports were reduced and compilation checked.
   The old node had no proof dependencies, so No longer needed is complete.
   `dag/units/sk-prop-sf-cbc.json` has empty `realized.statement` and
   `realized.steps`; none is bypassed. The finite-algebra localization route
   is kept, and no chapter or unit file is changed. Verdict: pass.
5. Matched the original node's new proof steps to the actual numerator,
   localization, geometric-properties and splitting steps in Lean. Its
   proof_deps is precisely the two new node ids. Both new nodes have the
   complete required fields, actual searches, source, full proof plan,
   exact Lean signature and the original chapter/unit. Verdict: pass.

Changes made by this second reading: removed both whole-target restatements
and their unused module/nodes; proved the actual common-denominator reduction;
constructed every witness explicitly; separated the geometric and algebraic
property holes; minimized the new imports; supplied matching DAG nodes and
corrected this report's proof and net-hole accounting.
