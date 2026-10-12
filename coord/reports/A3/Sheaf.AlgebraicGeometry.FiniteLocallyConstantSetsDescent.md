## What changed

Replaced the sorry of `AlgebraicGeometry.Scheme.finiteLocallyConstant_descent_of_local_models`
without changing its signature. The proof follows the original route: finite constant
representatives, compatible descent data, effective finite etale descent, and sheaf gluing.

The proved private helper `finiteConstant_localRepresentative` resizes an arbitrary finite
value in universe u+1 to a double ULift of Fin n. It transports the constant sheaf through
`Etale.overSheafEquiv`, uses `constantSheaf_sets_representable`, proves the coproduct
codiagonal finite and etale using the existing sigmaDesc results, and explicitly compares
the Over representation to small-site uliftYoneda. Thus the new remaining obligation
assumes finite etale local representatives, not the original constant local values.

Added `FiniteLocalModelsDescentDatum`, which states only the assembly of those local
representatives into a compatible finite etale descent datum on a cover. It neither
descends the scheme nor asserts a global representation.

Added and proved `EtaleRepresentableDescentGlue`. Its private helper
`iso_of_over_compatible` constructs a global map by sheaf amalgamation and proves it is
an isomorphism by `Sheaf.isIso_of_coversTop`. The public theorem explicitly constructs
inverse local representation maps from a pullback square and checks compatibility using
the transport equation. No finiteness assumptions are needed for this theorem.

The main proof applies the existing `finiteEtaleDescent`, chooses a preimage of the datum,
projects its isomorphism to Over U, transports the pullback square with `IsPullback.of_iso'`,
and proves projection invariance from the morphism-of-data compatibility equation. It
then applies the proved gluing theorem and packages the finite etale subtype fields.
All three delivered modules compile without warnings with lcompile.py --all.

Added only proof imports to the existing module. Updated its node's proof route and
proof dependencies. Statements, definitions, target signatures, and unit routes are unchanged.

## Proved and sorry left

Reduced `AlgebraicGeometry.Scheme.finiteLocallyConstant_descent_of_local_models`
(node `lem-weil-pbc-finite-locally-constant-sets-descent`): its proof contains no sorry.
It still depends on the existing finite etale descent theory and the new obligation below.

Proved `AlgebraicGeometry.Scheme.etaleRepresentable_descentGlue`
(node `lem-weil-pbc-etale-representable-descent-glue`), together with the private generic
gluing helper. Its proof has no sorry and uses sheaf amalgamation, pullback universal
properties, and existing subcanonicity.

Proved private helper `AlgebraicGeometry.Scheme.finiteConstant_localRepresentative`.

The only sorry in the delivery is
`AlgebraicGeometry.Scheme.finiteLocalModels_descentDatum`
(node `lem-weil-pbc-finite-local-models-descent-datum`). It is exactly the public named
whole theorem proof `:= by sorry`, with source and complete natural-language construction.
Empty finite values, empty covers/bases, arbitrary covers, and unbounded local ranks are
included; no quasi-compactness assumption was added.

## No longer needed

No original import was removed. Two old direct proof-dependency edges are no longer
needed by the main theorem: `lem-galois-yoneda-fully-faithful` is delegated to
`lem-weil-pbc-finite-local-models-descent-datum`, and
`def-weil-pbc-etale-sheaf-of-sets` to the assembly and gluing nodes. Both remain
transitive dependencies; neither node nor its module is globally pruned.

The new gluing module does not need `WeilConjectures.ConstructibleSheaf.Defs` or
`Sheaf.AlgebraicGeometry.FiniteEtaleDescentData`; it imports the actual
`Over.DescentDataCategory` provider, `Sheaf.AlgebraicGeometry.FpqcSingletonFullyFaithful`.
Its proof uses Mathlib subcanonicity directly, so the unused planned edge to
`lem-weil-pbc-small-etale-representable-presheaf-sheaf` was removed. The node's
finite-etale definition dependencies were also removed: its statement has no
finiteness assumption. The constant-sheaf comparison and effective finite etale
descent remain used explicitly.

## Where the brief, the DAG or earlier work was wrong

The original node has no proof-dependency imports although the standing brief says those
imports are already present. Its stated dependencies are usable but do not provide the
interface assembling local representatives into compatible descent data; that step has
now been made explicit. The generic RepresentableBy.overDescentDatum declaration works
on the big Over site and cannot directly be applied to E on the small etale site.
The assembly proof must compare the two etale representatives on the overlap and use
Yoneda there, then base change the resulting scheme isomorphism for arbitrary test schemes.

The local literature checkout lacks `literature/stacks-project/etale-cohomology.tex`.
WANTED: that file, Tag 03RV, and descent.tex, Tag 02W5, for both new nodes.
The online Stacks texts at https://stacks.math.columbia.edu/tag/03RV and
https://stacks.math.columbia.edu/tag/02W5 were read and checked. New proof_origin records
are marked agent, documenting the expanded small-site details. Tag 02W5, rather than
023U (a section on descent data), is the Yoneda/sheaf descent lemma cited by 03RV.
LeanSearch returned Internal Server Error, recorded as unavailable; LeanFinder and
Mathlib grep ran and provided supporting interfaces but no direct assembly theorem.
Blueprint searches for 03RV, 023U, and representable descent found no additional exact
node. Existing full representability theorems depend on this item and cannot replace it.

## New nodes

`lem-weil-pbc-finite-local-models-descent-datum`, module
`Sheaf.AlgebraicGeometry.FiniteLocalModelsDescentDatum`: assembly of already represented
finite etale local models into a datum over an etale surjection, with the precise section
compatibility equation used by gluing. This is strictly the construction-before-effectivity
part of the argument. It does not restate the item's conclusion.

`lem-weil-pbc-etale-representable-descent-glue`, module
`Sheaf.AlgebraicGeometry.EtaleRepresentableDescentGlue`: representation from an already
effective compatible datum. Fully proved, including the generic sheaf-gluing helper.

Both node files and the updated item node are under `dag/nodes/sec-proper-base-change/`.
There are no change records because no existing signature or definition changed.


## Second reading by A3

1. Compared every delivered module with the repository. The two added modules are
   absent there. The existing module has only proof/helper and plain proof-import
   changes; its public theorem signature and existing docstring are byte-for-byte
   unchanged. No target or definition was altered, and no change record is needed.
2. Compiled all three modules with lcompile.py in import order, without warnings.
   Inspected all declarations and searched for forbidden constructs. There is one
   whole named theorem with sorry, finiteLocalModels_descentDatum; no definition
   contains sorry. Explicit #print axioms checks in disposable scratch copies show
   only propext, Classical.choice and Quot.sound for both private helpers and
   etaleRepresentable_descentGlue. The main theorem and assembly obligation additionally
   use sorryAx, as reported; no other axiom appears. The main theorem is a reduction,
   not a claim of transitive axiom-free completion.
3. Read the assembly theorem, its full docstring construction, and its node against
   the local representative interface. Coproducts allow arbitrary covers and ranks;
   finiteness is local on the target components. Empty finite values give the empty
   coproduct, and an empty cover forces the empty base. The overlapping finite etale
   representatives are objects of the small overlap site, so Yoneda determines their
   comparison and cocycle before arbitrary scheme base changes define transport.
   This obligation supplies neither an effective scheme over T nor a global
   representation, hence is strictly one part of the original argument. Repeated
   LeanFinder, Loogle and Mathlib grep searches with different queries, and rg on
   both library roots. The big-site overDescentDatum cannot directly take the
   small-site input. No existing exact assembly theorem or short closure was found.
   The fully proved gluing theorem needs only an effective pullback and transport
   compatibility, and is valid without finiteness.
4. Read the main proof from local finite constant representatives through effective
   descent and the explicit gluing helper. The universe resizing, pullback transport,
   and projection invariance are actual proved reductions. No shorter existing route
   bypasses the missing assembly. Reviewed imports and removed the two unnecessary
   imports in the new gluing module. The original mathematical route remains, and
   sk-thm-p1's realized statement and steps are untouched. Completed No longer needed
   with the old direct edges now delegated, distinguishing them from global pruning.
5. Checked every node against its Lean declaration and proof; proof_deps equals the
   union of proof-step uses. Corrected the gluing node to describe its direct Mathlib
   subcanonicity proof rather than cite an unused library theorem. Removed unused
   finite-etale statement dependencies there. Stored the new Lean signatures verbatim
   rather than normalized onto one line. New nodes have source, complete proof steps,
   searches, split status, creation, blueprint, chapter/unit and Lean records.

Second reading changed imports, DAG dependency bookkeeping and signature formatting,
and this report. No Lean statement, definition, or proof body needed repair.
