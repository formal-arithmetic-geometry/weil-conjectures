## What changed

The signature and existing docstring of
`AlgebraicGeometry.Scheme.finiteLocalModels_descentDatum` are unchanged. Its proof now
constructs `U` from `Cover.sigma`, proves that its codiagonal is surjective using Mathlib's
instance for `Sigma.desc` of a scheme cover, obtains a finite etale model and its isomorphism,
constructs compatible transport, and packages the object, datum and both morphism properties
into `FiniteEtaleDescentData`. The last witnesses are definitionally the required ones.

Two smaller construction steps are isolated in new modules. The first fixes the actual
coproduct covering object and asserts only a representation there, with no descent datum.
The second takes a fixed finite etale representation and constructs its datum and transport
compatibility, with neither a cover nor surjectivity hypothesis. Both are needed; neither
repackages the entire original theorem. Their docstrings contain full mathematical proofs
and the DAG copies record this route. Only regular imports of the two new modules were added to the item's module.
The sigma-cover API is exported by the existence module because its statement needs it. No target, definition or
existing public interface changed.

All three modules compile locally in import order with no errors or warnings. The complete
Lean combination is in the item, with no remaining partial proof or private sorry.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.finiteLocalModels_descentDatum`
(node `lem-weil-pbc-finite-local-models-descent-datum`). No sorry remains in the item's module.

Added two whole public theorem holes:

- `AlgebraicGeometry.Scheme.finiteLocalModels_descentDatum_exists`, node
  `lem-weil-pbc-finite-local-models-descent-datum-existence`, in
  `Sheaf.AlgebraicGeometry.FiniteLocalModelsDescentDatumExistence`.
- `AlgebraicGeometry.Scheme.finiteLocalModels_descentDatum_compatibility`, node
  `lem-weil-pbc-finite-local-models-descent-datum-compatibility`, in
  `Sheaf.AlgebraicGeometry.FiniteLocalModelsDescentDatumCompatibility`.

This is a decomposition, not a complete proof independent of new intermediate holes:
1 original hole closed, 2 holes added, net -1. No definition contains a hole.

## No longer needed

None of the original statement imports was removed. The original proof-only import
`WeilConjectures.CategoryTheory.Comma.Over.DescentDatum` is removed from the item;
its definitions remain available through `FiniteEtaleDescentData` and its construction is
needed only by the compatibility step. The redundant regular import
`Mathlib.AlgebraicGeometry.Cover.Sigma` was removed from the item during second reading.
The compatibility module does not need `WeilConjectures.ConstructibleSheaf.Defs`, so its
public import was removed. The existence module retains that import because its statement
uses `Cover.etalePrecoverageToEtale`, declared there.

The complete list of old direct `proof_deps` absent from the new upper proof is:
`def-weil-pbc-etale-site`, `lem-weil-pbc-finite-local-on-target`,
`def-weil-pbc-etale-sheaf-of-sets`, `lem-galois-yoneda-fully-faithful`, and
`def-pd-descent-datum`. They remain needed by the intermediate constructions or signatures;
none is claimed pruned from the targets' import closure. No original dependency module is
claimed pruned from the target closure: the geometry and sheaf gluing are now needed by the
assembly node, and Yoneda and descent-datum machinery by the compatibility node. The upper
node no longer directly cites finite target locality, the sheaf axiom or Yoneda; those uses
are accurately recorded in the two intermediate nodes instead. This is relocation of needed
work, not pruning.

Neither `FiniteEtaleDescent`, an effective realization, nor the theorem
`finiteLocallyConstant_descent_of_local_models` is imported: they would not give a shorter
noncircular construction at this stage. The fixed coproduct construction and the compatible
datum route preserve the original unit route; this item is not itself a node listed in
`sk-thm-p1.realized`.

## Where the brief, the DAG or earlier work was wrong

No established mathematical error in the original statement or route was found. The original
plan names the geometric locality and Yoneda primitives, but none of their existing Lean
signatures directly performs the small-site assembly and transport constructions. These are
the two strictly smaller outstanding steps, not consequences of the primitives in one line.

In particular, the existing proved `Functor.RepresentableBy.overDescentDatum` takes a
presheaf on the whole over-category of schemes. The given `E` is only on the small etale
site, so applying that theorem directly would silently assume a big-site extension. The
compatibility node explicitly constructs the comparison on an etale overlap and then base
changes the comparison scheme isomorphism to arbitrary test schemes; it does not evaluate
`E` on non-etale schemes. Compatibility is asserted for a datum constructed from `e`, not
for an arbitrary datum.

The local literature checkout is absent. Read Stacks Tags 03RV and 02W5 online; the latter
is the big-site comparison construction that 03RV cites for the small-site argument with
its details omitted. The added docstrings expand exactly those small-site details.
LeanFinder searches for assembly and compatible descent, Loogle for `Scheme.Etale`, and
grep for `overDescentDatum|sigmaDesc|sigmaOpenCover` found supporting interfaces but no exact
remaining construction. LeanSearch returned Internal Server Error; this unavailability is
recorded without treating it as a negative mathematical search result.

Edge cases checked mathematically: the empty cover forces the base empty and gives empty
coproducts; the sheaf axiom gives the unique empty sections. Empty representatives, arbitrary
infinite covers and unbounded finite ranks cause no change: finiteness is local on target
components, not a finiteness assertion for the full family over T. The compatibility lemma
needs no surjectivity and is valid for a representation after any etale base morphism.

## New nodes

`lem-weil-pbc-finite-local-models-descent-datum-existence` states representation over the
specific collapsed cover only. Its proof uses scheme coproducts, finite target locality,
etale source locality, disjoint-cover sections and representable sheaf gluing. It retains
the localized-site equivalence and the empty case, without descent data or compatibility.

`lem-weil-pbc-finite-local-models-descent-datum-compatibility` constructs transport from one
fixed representation. It compares the two pullback representatives by Yoneda on the small
etale overlap, proves identity and cocycle there, then base changes to arbitrary schemes.
It has no cover hypothesis and does not assemble representatives. Both modules contain a
single public theorem with whole proof `:= by sorry`, source, blueprint id and proof in words.
No change record is needed because no existing signature, definition or public import changed.

## Second reading by S1

1. **Unchanged interfaces — pass.** Compared the item's complete module against the
repository with `diff -u`. The only existing-declaration change is the proof after `:= by`;
the full theorem signature and existing docstring are byte for byte unchanged. No definition,
target, hypothesis, conclusion, or pre-existing public import changed. The two other modules
are new; there is no statement-change record to require.

2. **Lean and axioms — pass as a decomposition.** Compiled all three final modules locally
in import order, without errors or warnings. Independently appended `#print axioms` to
scratch copies of all three declarations: only `propext`, `Classical.choice`, `Quot.sound`
and `sorryAx` occur. Exactly two `sorry` tokens remain, both the whole proof of the named
public theorems reported above. No definition holes, partial or private holes, axioms,
unsafe declarations, opaque declarations, externs or implementation overrides occur.
The original theorem still depends on the two open construction theorems, so this is one
upper hole closed, two lower holes added, net -1; it is not a completed foundational proof.

3. **Split statements and search — pass.** Read both new signatures, complete proof
 docstrings and nodes against [Stacks 03RV](https://stacks.math.columbia.edu/tag/03RV)
and [02W5](https://stacks.math.columbia.edu/tag/02W5). Assembly asserts representation over
a fixed coproduct, without a datum. Compatibility asserts a datum for a fixed representation,
without any cover or surjectivity assumption. Each is strictly one part of the original
argument, and neither restates the original result. Checked empty base and cover, empty
representatives, arbitrary infinite covers, unbounded ranks, and non-surjective U. Finiteness
is local on target components; there is no uniform-rank or finite-family assumption.
For compatibility the comparison represents the restriction to the small etale overlap;
Yoneda gives an actual scheme isomorphism, which can subsequently be pulled back along
arbitrary scheme maps. Thus no unprovided extension of E to the big site is used.
Second-reader LeanFinder search for canonical overlap descent from a sheaf represented on
a small-site slice, Loogle search for `CategoryTheory.uliftYoneda`, and grep search for
`coproduct.*represent|represent.*coproduct|descent.*[Yy]oneda|[Yy]oneda.*descent`
returned supporting APIs but no exact construction. Also searched `lean/` and read the
existing `overDescentDatum`, `Etale.overEquiv`, `Etale.overSheafEquiv`, disjoint-cover product
and representable-sheaf declarations. `overDescentDatum` requires big-site input;
`etaleRepresentable_descentGlue` assumes the datum already exists. Neither closes these
small-site construction holes directly, and neither hole has a short available proof.

4. **Route and pruning — pass after reporting repair.** The upper proof fixes U by
`Cover.sigma`, proves surjectivity by the existing instance, combines the two construction
steps and packages the finite/etale properties definitionally. Checked the exact existing
signatures behind every old dependency and both new proof plans. Removed redundant imports;
retained those required by statements. The no-longer-needed section now explicitly names all
five removed direct proof dependencies and the removed original proof import. They are
relocated, not pruned from target closure. Read `dag/units/sk-thm-p1.json`: this item is not
in its `realized` statement or steps, and the delivery changes no unit record or unit route.

5. **DAG correspondence — pass after metadata repair.** The original node changes only
`proof`, `proof_deps` and `proof_origin`. Its two steps match the actual combination and their
uses have precisely the recorded union. Both new nodes have source, complete proof steps,
searches, creation/blueprint/chapter/unit fields and matching declaration/module records.
Replaced their normalized `lean.statement` strings with the exact multiline signatures from
Lean, including the newline required by the existence theorem's `let` expression.

Changes by this second reader: removed the item's redundant Sigma import and the
compatibility module's unused ConstructibleSheaf.Defs public import; made both new-node
signatures verbatim; completed the exact dependency/import removal list; appended this
review. No theorem statement, definition or proof body was changed.
