## What changed

Replaced the single `sorry` in `AlgebraicGeometry.Scheme.adic_stratified_perfect`
with a complete Lean assembly. Its signature is byte-identical to the shared source.
The geometric forward and reverse arguments of Bhatt–Scholze Proposition 6.6.11
are separate named statements; the tensor and categorical closure arguments are proved.
This is a decomposition of the original hole, not a claim to have finished the
geometric lifting and descent arguments.

Moved the original eleven supporting declarations, including their definition and
instance bodies, verbatim to `Sheaf.Paper.AdicStratifiedPerfectData`. The original
module publicly reexports it. A byte comparison confirms the entire declaration block
is unchanged, and all original public imports remain publicly visible. This prevents
cycles between the theorem and its new proof dependencies. No target or definition
meaning changes, no adopted source module is edited, and no quarantine is changed.

`Sheaf.Paper.AdicResidueFieldTensor` proves exactness of tensor by an arbitrary
field-valued etale sheaf and preservation of homological bounds. The proof uses
pointwise flatness, the sheaf tensor comparison, reflected monoidal closure and the
exact-functor homology isomorphism. It needs neither finite fields nor constructibility.

`Sheaf.Paper.AdicConstructibleTriangulated` proves residue closure. It proves exactness
of fixed-scalar restriction by forgetting to additive sheaves, realizes bounded
constructible etale origin as the essential image of a full triangulated functor,
and identifies the residue predicate with its inverse image under derived reduction.
The explicit comparison uses canonical quotient-functor preimages, their isomorphisms,
and homology factor isomorphisms. No chosen arbitrary unproved witness defines data.

Added the proved global extension consequence
`IsConstructibleSheaf.of_shortExact_of_isNoetherianRing` to the unclaimed
`Sheaf.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre`. Its existing private
finite-locally-constant argument supplies the proof on the common stratification.
All old declarations and public imports of that module remain verbatim.

The main module independently proves completeness closure: exact slice restriction
followed by derived internal Hom preserves zero objects, shifts and distinguished
triangles. Transport through an explicit small-site module equivalence identifies the
vanishing predicate with `IsSfbAdicComplete`. Intersection with the proved residue
property then gives zero, isomorphism invariance, shifts and all three triangle clauses,
without using either new geometric statement. Finite-projective self-witnesses and the
proved field tensor bound assemble the geometric statements into the equivalence and
boundedness clauses.

All seven Lean modules compiled together through `lcompile.py --all`. A correction to
an explicit constructibility instance was checked by compilation. Final delivery checks
also compile the current packet. Definitions and the original theorem signature were
compared byte-for-byte, all Lean lines are at most 100 characters, and every dependency
id in the delivered nodes exists. The literature proof was read in the sandbox copy of
arXiv:1309.1198, Definition 6.5.1, Lemma 6.5.3 and Proposition 6.6.11.

## Proved and sorry left

Original holes: one, `AlgebraicGeometry.Scheme.adic_stratified_perfect`.
Its body now contains no `sorry`, and the complete assembly compiles. The two geometric
subresults below remain admitted, so this closes one upper hole by adding two strictly
partial, source-backed geometric results. It is a decomposition, not a net proof gain;
the local arithmetic is one hole closed minus two added = minus one. The ledger tool
remains authoritative for the targets' actual import closure. No definition has a hole.

New proved declarations, with no added holes:

- `AlgebraicGeometry.Scheme.sfbFieldTensor_bounds`
  (`lem-sfb-etale-field-tensor-bounds`).
- `AlgebraicGeometry.Scheme.adicConstructible_residueTriangulated`
  (`lem-sfb-adic-constructible-triangulated`).
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_shortExact_of_isNoetherianRing`
  (additional global realization of `lem-sfb-discrete-noetherian-constructible-serre`).
- The main module's private completeness-closure and small-site-equivalence helpers.

Every remaining `sorry` added by this packet:

- `AlgebraicGeometry.Scheme.adicConstructible_localModels`, in
  `Sheaf.Paper.AdicConstructibleLocalModels`, node
  `lem-sfb-adic-constructible-local-models`. This is only the forward geometric
  construction from complete constructible residue to raw finite-projective local
  representatives. It proves neither the reverse implication, global bounds nor
  triangle closure. Its source is Proposition 6.6.11 forward, using Lemma 6.6.8.
  The substantial remaining interface work is transport between the actual ringed
  pro-etale restrictions in the parent and the small-site input and output of the
  lisse-residue lifting theorem, together with finite common stratification.
- `AlgebraicGeometry.Scheme.adicPerfectModels_residueOrigin`, in
  `Sheaf.Paper.AdicPerfectModelsResidueOrigin`, node
  `lem-sfb-adic-perfect-models-residue-origin`. This is the reverse geometric
  completeness, local-to-global bounds and etale residue-descent calculation. It
  does not assert Tor amplitude, the forward implication or any closure clause.
  Its source is Proposition 6.6.11 reverse and Lemma 6.5.3. Its remaining work is
  the coefficient/site comparison needed to apply perfect-model reduction,
  completeness detection and stratified local bounds, then bounded constructible
  comparison. Both nodes retain the existing stated dependencies and give complete
  natural-language proofs; neither statement is the parent under another name.

No other `sorry` occurs in the seven delivered Lean files.

## No longer needed

No module is withdrawn, and no global pruning is claimed. The original public API
imports are retained through the data module. The geometric children's dependency
imports are not added prematurely: their statements import only the data module;
their nodes retain all geometric dependencies required for their future proofs.

The original parent's direct plan used the following nodes that the new parent no
longer needs directly. Their replacements and retained uses are explicit:

- `lem-exc-constant-field-module-flat`,
  `lem-exc-constant-field-sheaf-tensor-cohomology`, and
  `lem-pc-bounded-above-flat-kflat-site`: the new proved exact sheaf tensor argument
  gives the literal termwise Tor condition directly, without constructing a
  bounded K-flat representative or using geometric stalks.
- `lem-sfb-ringed-complete-triangulated`
  (`Sheaf.CategoryTheory.RingedCompleteTriangulated`): direct vanishing under exact
  slice restriction and internal Hom proves the complete locus triangulated.
  The larger result constructing a completion presentation, its unit and reflector
  is unnecessary for this argument; it is not imported.
- `lem-sbc-cohomology-in-weak-serre-subcategory`
  (`Sheaf.Paper.CohomologyInWeakSerreSubcategory`): the adopted source already gives
  triangulatedness of bounded constructible etale complexes, and full derived
  comparison gives the essential image. This extra weak-Serre wrapper is not imported.
- The geometric nodes formerly used directly by the parent remain in the new forward
  or reverse node: finite stratification pullback, stratum completion units, residue
  lisse perfect lift, perfect-model complete reduction, stratified local bounds,
  Noetherian global constructibility, constructible comparison, actual comparison
  pullback and the underlying Noetherian/finite-presentation tools. They have not been
  declared unused. In particular the residue closure proof uses full bounded-below
  comparison; the geometric reverse proof still needs constructible comparison.

The proved categorical closure requires neither derived countable products nor a
Koszul completion reflector, and no finiteness of the residue field. These theories
may remain needed by the geometric dependencies and by other consumers. No adopted
source declaration is removed or reverted to `sorry`, and unit realization is unchanged.

## Where the brief, the DAG or earlier work was wrong

The declared dependency signatures use different presentations of the relevant module
categories. The source of `adicResidueLissePerfectLift` uses small-site completed and
finite intrinsic ring sheaves and a K-flat representative Tor test. The parent uses
fixed-scalar etale complexes and the actual immersion-and-slice ringed restriction.
Consequently the parent cannot be closed by merely applying that theorem without the
finite-stratification and coefficient-comparison construction. The two geometric
nodes record this remaining work rather than disguising it as an exact application.

The planned ringed completion theorem constructs much more data than is needed for
triangulatedness. The parent uses only exactness and vanishing and proves that directly.
The source global constructible-extension API for module sheaves imposes a finite ring,
whereas residue fields here can be infinite. The unclaimed Noetherian Serre module
already contained the needed private argument; its new proved global consequence
avoids any extra coefficient hypothesis. No false statement or unit-route error was
found, and no target has changed.

The original missing-module history was checked against current rework and claim
records: the item is restored in the live tree and claimed by U2. The quarantined
archives are preserved. No missing path is treated as a withdrawal.

## New nodes

`lem-sfb-adic-constructible-local-models` is Proposition 6.6.11's forward construction
of actual bounded finite-projective representatives, with the omitted separate
perfectness witness inserted by the parent's proved Lean assembly. It has its own
module, source and complete proof plan. Its single theorem remains `sorry`.

`lem-sfb-adic-perfect-models-residue-origin` is the reverse model calculation and
residue descent, excluding Tor amplitude and all categorical closure. It has its own
module, source and complete proof plan. Its single theorem remains `sorry`.

`lem-sfb-etale-field-tensor-bounds` is a proved exact-tensor consequence over arbitrary
fields. It handles the uniform Tor interval in both the reverse assembly and residue
closure, for all complexes and degree-zero sheaves, including zero complexes.

`lem-sfb-adic-constructible-triangulated` is a proved closure statement for the residue
condition alone. It uses exact fixed-scalar restriction, the full derived comparison,
and a quotient-functor representative comparison. It imposes no completeness or
Noetherian assumption on A and only maximality on I.

All four nodes inherit the original chapter and unit, have recorded semantic, type and
source searches, and have blueprint ancestry from the first sentence of
`det-lem-integral-models-stacks` through the existing integral criterion. Blueprint
searches for adic/perfect, stratified perfect, constructible residue and tensor
cohomology found no duplicate node. The main node's proof and proof dependencies now
follow the actual Lean assembly. The existing data node's Lean attachment follows the
unchanged definitions into the data module, and the existing Serre node additionally
records its global consequence.

Change records:
`coord/changes/sfb-adic-stratified-perfect-data-relocation.md` and
`coord/changes/sfb-noetherian-global-extension-api.md`. Both contain downstream user
tables and status `open`. No forced adaptations or consumer statement changes occur.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
