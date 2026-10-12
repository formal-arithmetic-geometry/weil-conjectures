## What changed

The existing theorem `AlgebraicGeometry.Etale.etale_mayerVietoris` retains its original
signature and docstring byte for byte. Its proof now combines comparison isomorphisms with
a raw right-derived-evaluation exact sequence and proves the vanishing consequence in Lean.
At degree zero this uses the initial injection; at positive degree it uses exactness and
subsingletonness of the preceding intersection group. All transport uses the component
additive equivalences. No definition or existing statement changed.

Two proper subproblems are in their own modules:
`Sheaf.AlgebraicGeometry.EtaleMayerVietorisComparisons` contains the four functor
isomorphisms, without an unnecessary cover hypothesis, and
`Sheaf.AlgebraicGeometry.EtaleMayerVietorisExact` contains the connecting maps and exactness,
without either the comparisons or the vanishing conclusion. The item imports these only
for its proof. The original public imports stay unchanged.

## Proved and sorry left

The one original sorry, `AlgebraicGeometry.Etale.etale_mayerVietoris`, is replaced by a
complete Lean reduction. It still rests on two explicitly named open theorems, so this is
partial progress, not an axiom-free proof of the full Mayer–Vietoris result.

- `AlgebraicGeometry.Etale.etale_mayerVietoris_comparisons` remains `sorry` in
  `Sheaf.AlgebraicGeometry.EtaleMayerVietorisComparisons`;
  node `lem-weil-pbc-etale-mayer-vietoris-comparisons`.
- `AlgebraicGeometry.Etale.etale_mayerVietoris_exact` remains `sorry` in
  `Sheaf.AlgebraicGeometry.EtaleMayerVietorisExact`;
  node `lem-weil-pbc-etale-mayer-vietoris-exact`.

These are the only delivered sorry occurrences. Both have their own source, complete
natural-language proof, and matching DAG record. No forbidden declaration or hollow
definition is present.

## No longer needed

Removed the following proof imports from the item:
- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`.
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`.
- `Sheaf.CategoryTheory.InjectiveSheafCechAcyclic`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`.

Every old direct `proof_deps` entry has been replaced by the two split nodes. The complete
list of old direct dependencies no longer used directly by the item is:
- `lem-weil-pbc-etale-composition-cancellation`.
- `def-weil-pbc-etale-site`.
- `lem-weil-pbc-open-fibre-product`.
- `def-weil-pbc-abelian-etale-sheaves`.
- `def-sp-injective-resolutions`.
- `def-weil-pbc-cech-complex`.
- `lem-weil-pbc-injective-sheaf-cech-acyclic`.
- `lem-weil-pbc-module-sheaves-enough-injectives`.
- `lem-weil-pbc-left-exact-injective-resolution-degree-zero`.
- `lem-weil-pbc-dplus-injective-representative`.
- `def-weil-pbc-etale-cohomology`.
- `lem-weil-pbc-complex-ses-homology-long-exact`.
- `lem-weil-pbc-cohomology-pullback-functorial`.
- `lem-weil-pbc-etale-inverse-image-restriction`.
- `def-weil-pbc-cohomology-pullback`.
- `lem-weil-pbc-inverse-image-composition`.
- `lem-weil-pbc-complex-ses-long-exact-naturality`.

All except the following three remain in the split nodes' proof dependencies and are not
claimed as globally pruned: `lem-weil-pbc-cohomology-pullback-functorial`,
`def-weil-pbc-cohomology-pullback`, `lem-weil-pbc-inverse-image-composition`.
These three are not required by the new proof route: the unchanged Lean statement uses
right derived restriction maps and existence of comparison isomorphisms, without asserting
compatibility of those isomorphisms with the separate Ext-based pullback maps.
Pruning from other targets' closures remains the maintainer's job.

## Where the brief, the DAG or earlier work was wrong

The first delivery split off two sorry declarations without nodes; the exactness declaration
had no docstring, and the original target's docstring had been attached to the comparison
helper. Its report called a conjunction assembly a proof without noting that all substantive
steps were still postponed. The second reading repaired these defects and proved the
vanishing step instead of postponing it in the exactness helper.

The old DAG step 6 cites clause 5 of the cohomology-pullback-functorial node, but its current
Lean theorem has only three conjunction clauses and does not state restriction preserves
injectives or comparison of resolutions. The comparison node now cites the actual
injective-restriction and inverse-image-restriction results, rather than that unavailable
clause. The unchanged item is below the unit level; `sk-thm-p1.realized` and its route are
preserved. The existing etaleCohomologyOverOpen theorem is about Ext-based `Sheaf.H` and
does not provide this right-derived-evaluation versus total-derived-global-sections bridge.

## New nodes

`lem-weil-pbc-etale-mayer-vietoris-comparisons` formalizes the resolution comparison in
Stacks 03F3(2), using injective restriction and the equality of evaluated section complexes.
It is stated in `lean/Sheaf/AlgebraicGeometry/EtaleMayerVietorisComparisons.lean`.

`lem-weil-pbc-etale-mayer-vietoris-exact` formalizes the raw exact sequence from Stacks
0A50, via the injective section sequence and its homology sequence. It is stated in
`lean/Sheaf/AlgebraicGeometry/EtaleMayerVietorisExact.lean`.

No change record is needed: no existing interface, signature, definition, or public import
is changed. Searches were executed through msearch.py and recorded in searches.jsonl;
LeanSearch was unavailable (HTTP Internal Server Error), while LeanFinder, Loogle and local
grep searches ran. Mathlib's MayerVietorisSquare.sequence_exact is for Ext-based H-prime;
it still requires the comparison with the displayed right derived evaluation functors.

## Second reading by U1

1. Compared all delivered files with the read-only repository. The original declaration
   signature and docstring are byte for byte identical. The original public imports are
   unchanged; the new modules are used by plain, proof-only imports. Verdict: pass.
2. Checked the complete proof reduction, the two named sorry gaps, and the absence of
   axiom, unsafe, opaque, implemented_by, extern, and sorry in definitions. Local compilation
   and explicit scratch #print axioms checks passed. All three modules compile without
   warnings; all three declarations use only propext, Classical.choice, Quot.sound, and
   the expected sorryAx from the two gaps. Verdict: structurally sound,
   conditional on the two explicitly listed open theorems.
3. Checked both intermediate claims against the source proofs, and searched independently
   using evaluation, localized sections, right derived functors, and the functorial exact
   sequence terminology. Small cases: zero coefficient sheaf, empty X, U=V=X, U=X and
   V=empty, and disjoint opens are consistent with the claims. The comparisons do not need
   the cover; only the exactness claim uses it. The intersection hypothesis is not used at
   degree zero; at degree m+1 it is used in degree m. Both new claims are strict parts of
   the argument, and the item now proves vanishing from them. Verdict: pass.
4. Read the proof from its conclusion downward. The elementary exactness/injection route
   is implemented directly; no new helper for vanishing was added. No existing Mathlib or
   upstream theorem found gives the exact displayed comparisons. Imports and direct versus
   transitive dependency pruning are accounted for above. The unit realized route is kept.
   Verdict: pass.
5. Compared the Lean statements with their matching node records and checked that the
   existing node's proof names exactly the two lemmas used by the new proof. Its second
   step records the actual subsingleton argument. New proof_deps are the union of each
   node's step uses, and source/proof_origin/chapter/unit/created/search/lean fields are
   filled. Verdict: pass.

Second reading changed: split modules and source docstrings restored/repaired; two missing
nodes created; unnecessary cover hypothesis removed from the new comparison theorem;
vanishing proved in the original module; proof imports and DAG dependency route pruned;
report corrected to identify the two remaining proof gaps honestly.

Validation: three warning-free local compiles (2–4 seconds per module), explicit axiom
prints for all three theorems, and a DAG traversal of 166 reachable nodes with no cycles
or missing dependencies. Proof dependency unions checked for all three delivered nodes.
