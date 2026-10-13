## What changed

Replaced the proof of
`AlgebraicGeometry.SingleComplexBaseChange.nonempty_stalkComparison_open_arrow_iso`
without changing its signature, universes or public imports. Added the proof-only
import `Sheaf.AlgebraicGeometry.OpenComparisonIntoPullbackTransport`.

The proved private helper `open_stalkComparison_normalized` identifies each
coordinate comparison, after its target normalization, with the comparison into
derived pullback followed by cohomology of the represented coefficient morphism.
Its argument follows the existing proved normalization in
`StalkComparisonCoordinateInvariance`; it uses exact-stalk homology naturality,
the invertible counit, and `Coordinates.represents`.

The new module states transport **before** the final coefficient morphism. Its
natural target isomorphism is independent of that morphism and the final target
complex. The original module supplies the nontrivial remaining argument:
naturality with respect to the coefficient morphism, both target normalization
equations, the specified composition defining `φU`, cancellation of target
isomorphisms, and `Arrow.isoMk`.

Updated the original node's proof route and added one new node. There are no
changed definitions, adapted modules, or change records. The unit's realized
statement/step bindings are unaffected.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.SingleComplexBaseChange.nonempty_stalkComparison_open_arrow_iso`
(node `lem-pc-single-complex-open-stalk-conjugacy`). No `sorry` remains in the
item's module, including its private helper.

Added one hole:
`AlgebraicGeometry.SingleComplexBaseChange.exists_open_comparisonIntoPullback_transport`
(node `lem-pc-open-comparison-into-pullback-transport`), in the new module
`Sheaf.AlgebraicGeometry.OpenComparisonIntoPullbackTransport`.

This is a decomposition, not a completed proof of open stalk transport: one
upper hole is closed and one strictly earlier comparison-transport hole is added.
The new statement has neither `K'`, `φ`, final target representative `N`, chain
map `t`, nor `Coordinates`; it concerns the comparison into derived pullback
alone. The proof of the original statement from it is complete. No arbitrary
existence witness is used to define any data.

## No longer needed

No original imports were removed: both public imports are required by the
unchanged statement. The route no longer uses
`lem-pc-affine-derived-pullback-tensor-tilde` or imports
`Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`: the needed fact is
identification of derived pullback along an open immersion with exact restriction,
obtained from the adjunction and universal derived counit, rather than the
module's affine/tilde computations.

The explicit auxiliary coordinate system `r` of the old plan is not constructed
in the original proof. Representative transport is handled before coefficients
in the new lemma. The other old proof dependencies are either still used for
normalization or retained in the new node's transport proof; none is claimed
pruned from the entire library. In particular K-flat restriction, restriction
stalk extension, the tensor-cohomology model, pullback-stalk comparison, source
transport, and comparison-into-pullback naturality remain needed below the new
node. The removed direct proof dependencies are explicitly:

- `lem-pc-affine-derived-pullback-tensor-tilde`: bypassed altogether.
- `lem-pc-kflat-open-restriction`: moved below the new transport node.
- `lem-pc-open-restriction-stalk-extension-iso`: moved below the new transport node.
- `lem-weil-pbc-module-stalk-pullback`: moved below the new transport node.
- `def-pc-base-derived-tensor-cohomology-model`: moved below the new transport node.

Only the first is pruned from this proof route; the other four remain transitive
proof dependencies. No delivered module removes an import.

## Where the brief, the DAG or earlier work was wrong

No disputed mathematical statement was found. The old plan did not provide a
named theorem comparing the actual derived tensor-cohomology maps under source
restriction; the underived stalk isomorphisms and coordinate-invertibility theorem
alone do not supply arrow conjugacy. The new node isolates this missing step
before the final coefficient morphism, so that the upper coefficient argument
is now checked by Lean.

The sandbox source collection does not contain `literature/stacks-project/perfect.tex`.
Read the source directly at https://stacks.math.columbia.edu/tag/0DJ8 and
https://stacks.math.columbia.edu/tag/0DJ9. The new proof sketch is explicitly an
agent expansion of the locality step; it does not claim those sources already
state the exact Lean transport interface. LeanSearch returned Internal Server
Error and is recorded as unavailable, not as a negative search result.

## New nodes

`lem-pc-open-comparison-into-pullback-transport` states the natural additive
open-restriction target-cohomology isomorphism together with source transport
and commutation for the comparison into derived pullback. Its self-contained
statement and Lean signature omit all final coefficient data. Its source is
Tag 0DJ8's locality paragraph and Tag 0DJ9's source-open restriction paragraph.
The proof sketch constructs target transport from exact restriction, source
transport from stalk ring identifications and the model counits, and proves
compatibility using pullback composition and representative naturality. Edge
cases checked: empty opens have no points; top opens reduce to the same canonical
ring/derived transports; zero complexes and zero rings require no nonzero or
invertibility assumption on either horizontal comparison. Semantic searches
found only underived restriction/stalk isomorphisms, grep found no transport
statement, and LeanSearch was unavailable. There is no blueprint duplicate and
no changed unit route. No change record is needed.


## Second reading by H1

1. **Visible interface: PASS.** Compared both delivered modules with the repository.
   The original public theorem signature is byte-for-byte identical, including
   universes, hypotheses, the specified `φU`, and its conclusion. Its public
   imports and docstring are unchanged. The only new original-module declaration
   is a proved private helper. No definitions or other modules were adapted and
   no change record is necessary.
2. **Proof and hygiene: PASS.**
   Read the normalization proof and the coefficient-naturality calculation in full.
   The counit inverse cancels only under the coordinates' `counit_isIso` field;
   both target normalizations are actual isomorphisms. `Arrow.isoMk` uses the
   source isomorphism and the composite target isomorphism in the correct direction.
   The original module has no `sorry`; the new module has exactly the one named
   public theorem listed above, with whole proof `:= by sorry`. No forbidden
   declaration or hollow definition occurs. Existential transport data are
   eliminated inside this theorem proof; they do not define arbitrary data.
3. **Split statement: PASS as a decomposition.** Read the new statement, its
   docstring argument, both cited Stacks pages, the source-transport theorem and
   pullback-naturality theorem. The new statement is the comparison square before
   coefficients, uniformly natural in the target derived object. It omits the
   original final target, coefficient morphism, target representative and chain map;
   it does not merely rename the original theorem. The upper proof checks the
   remaining coefficient argument. Open-immersion stalk maps are ring isomorphisms,
   so restriction identifies the source derived tensor and its algebra actions;
   exact restriction identifies the target cohomology. Empty opens have no point;
   top opens and zero complexes require no invertibility of a comparison or nonzero
   condition. Different representatives are handled by source transport and
   comparison naturality. Independent searches used “derived pullback along an
   open immersion ... stalk cohomology ... derived tensor base change” (LeanFinder),
   `CategoryTheory.Functor.mapIso` (Loogle), and
   `restrictFunctorIsoPullback|restrictStalkNatIso` (grep), plus rg on both library
   roots. The hits supply underived restriction and categorical packaging, not the
   required derived comparison square. The existing private coordinate-normalization
   lemma cannot be imported as a public theorem. No duplicate or short proof of
   the substantial remaining transport hole was found.
4. **Route and pruning: PASS.** Both original public imports occur in its
   signature, and its new transport import is proof-only. The new module's public
   imports provide `comparisonIntoPullback`, derived stalk cohomology and `Arrow.mk`
   in its signature. Enumerated all five removed old direct proof dependencies
   above, distinguishing the affine lemma bypassed from four dependencies moved
   below the new node. Read `dag/units/sk-thm-picard-semicon.json`; its `realized`
   fields and chapter/unit route are unchanged. No unit step is bypassed.
5. **DAG: PASS.** The original node changes only `proof`, `proof_deps` and
   `proof_origin`, matching normalization, pre-coefficient transport and coefficient
   naturality. The new node has its source, complete argument, searches, creation
   and blueprint provenance, correct chapter/unit, and a verbatim Lean signature.
   Its `proof_deps` is exactly the union of its steps' `uses`.

Second-reading changes: clarified `## No longer needed` by listing every removed
old direct proof dependency and its disposition; added this independent review.
No Lean proof, statement or definition required repair. This remains one hole
closed and one hole added, with net zero, rather than a completed transport proof.


Validation: `lcompile.py --all` compiled both delivered modules without errors or
warnings. A scratch copy with explicit `#print axioms` compiled cleanly: the
private normalization helper uses only `propext`, `Classical.choice`, `Quot.sound`;
the original theorem and new transport theorem use those three plus `sorryAx`,
as expected from the one remaining transport hole and open dependencies. The
delivery tool also checks every added declaration with its axiom probe.
