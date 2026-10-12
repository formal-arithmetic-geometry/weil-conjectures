## What changed

Repair of the landing return at head `f24743109`: generalized both private
exact-sequence helpers in place to cohomology over an arbitrary open `U : Opens X`.
The main proof specializes them at `U = ⊤`. These are strictly stronger statements
than the whole-space helpers in `Sheaf.Topology.NoetherianExtensionByZeroReduction`,
so neither duplicates an existing statement word for word. The generalization uses
the same Mathlib Ext exactness declarations and adds no sorry or public interface.

Importing the existing helpers is impossible: they are private, and their module
imports this item's module already. The import-direction tool confirms the cycle.
This repairs the duplicate declarations using the return's generalization option.
Only a dry run is prepared here; the second reader performs delivery.

Replaced the sole sorry in `Sheaf.Topology.CohomologyReductionConstantSubsheaves` with
an explicit proof from finite-generation exhaustion and the existing filtered-cohomology
comparison. The original theorem signature, public imports, and docstring are unchanged.

The proof first handles a one-generator quotient. Its kernel embeds in the constant integer
sheaf; every finitely generated stage of the kernel satisfies the original `hsub`. Apply the
filtered comparison in degree `p + 1`, then the long exact sequence in degree `p`.

Finite-generator induction is proved directly in Lean. At the successor step, take the image
of the first `n` generators and its cokernel. The last generator maps epimorphically onto that
cokernel: cancellation of the coproduct presentation and the cokernel map proves this using
`Fin.lastCases` and coproduct extensionality. The long exact sequence combines the two vanishings.
Finally exhaust the original sheaf and apply the filtered comparison again.

Added `Sheaf.Topology.AbelianIntegerExtensionMono`, with a proved monomorphism theorem. Its
private restriction isomorphism uses the source library's `overPullbackConstantSheafIso`,
Mathlib's equivalence of the slice site and the open subspace, and compatibility of
sheafification with that equivalence. The extension-by-zero counit's stalk formula and the
stalkwise monomorphism criterion prove the embedding. No new definition is left open.

Added `Sheaf.Topology.AbelianSheafFiniteGenerationExhaustion`, containing the remaining
structural theorem. Its statement has no cohomological hypothesis or conclusion. It supplies
a directed presentation by finitely generated subsheaves, including the monomorphisms needed
to apply `hsub`. Its docstring and node give the section/image construction and the colimit
universal property by local gluing.

The new imports in the original module are proof imports. Both new modules have only the
public imports needed to state their results. Updated the item's node to match the shorter
kernel argument and the explicit finite-generator induction.

## Proved and sorry left

Reduced `TopCat.noetherian_vanishing_of_constant_subsheaves`: its proof has no direct sorry.
It depends on the one new structural theorem below and the existing named open comparison
`TopCat.topological_filtered_cohomology` (`lem-sc-topological-filtered-cohomology`). Thus this
is a stage-3 reduction, not a claim that the entire target closure is axiom-free.

Proved `TopCat.abelianIntegerExtension_exists_mono`
(`lem-sc-abelian-integer-extension-mono`) and its private restriction isomorphism. The original
module's private helpers for the middle/right long exact segments and zero filtered colimits
are all proved. The finite-generator induction, including the zero-generator case, is proved
inside the original theorem.

The only direct sorry in the delivery is:

- `TopCat.abelianSheaf_finiteGeneration_exhaustion`, in
  `Sheaf.Topology.AbelianSheafFiniteGenerationExhaustion`, node
  `lem-sc-abelian-sheaf-finite-generation-exhaustion`.

Local compilation of the three delivered modules in import order passes without warnings.
The delivery dry run supplies the additional axiom probes, server compiles and preflight.

## No longer needed

Removed the item's direct proof dependency
`lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact`
(Mathlib's `CategoryTheory.Sheaf.hasExactColimitsOfShape`). The proof does not construct a
filtered diagram of quotients or use exactness of its colimit. It instead computes kernel
cohomology from the directed union itself. The exhaustion node uses the direct colimit
universal property by local gluing, so does not introduce this dependency again.

The former direct dependency `lem-sc-topological-extension-by-zero-stalks` is now used
through both new nodes; it is retained in the proof closure and is not pruned. The exact
filtered-colimit dependency is also still used by the existing filtered-cohomology comparison,
so its removal here is only from this item's direct route.

No existing public import was removed. No source module can be declared globally unnecessary
from this delivery alone. No separate finite-generator-filtration or quotient-approximation
node/module is delivered: the former is replaced by the explicit Lean induction and the
latter is bypassed by the kernel argument. All final proof imports are used.

## Where the brief, the DAG or earlier work was wrong

The previous delivery duplicated two private whole-space exact-sequence helpers.
The repair generalizes them to every open; their arbitrary-open proofs also cover
empty opens and require no compactness assumption. No existing public statement
was changed. No statement error was found. The planned quotient-stage construction is unnecessary because
`hsub` holds in every degree above `d`: the filtered comparison applied directly to the kernel
in degree `p + 1` gives the right term required by the long exact sequence.

The Stacks source was read at https://stacks.math.columbia.edu/tag/02UX; the local checkout
omits `literature/stacks-project/cohomology.tex`. The first three proof paragraphs match the
construction and induction used here. No unit statement or realized unit step is bypassed.
The unit `sk-thm-curveestimate` records only `thm-sc-proper-cohomology` as its own statement
and no realized steps; all changes here remain below that level.

Edge cases checked from the constructions: empty space, empty open, whole open, zero sheaf,
and zero generators. The exhaustion index contains the empty finite subset even when there
are no nonzero sections; the zero-generator presentation has zero target. Integer-extension
monicity requires neither compactness nor Noetherianity. The original degree argument uses
`d < p < p + 1`, including `d = 0`; no positivity or connectedness assumption was added.

LeanSearch was unavailable with HTTP Internal Server Error and is recorded as unavailable.
LeanFinder and source grep found no existing theorem with either new statement. Searches
of the DAG and imported blueprint found no duplicate statement; the generic site and
scheme-specific statements inspected have different conclusions or categories.

## New nodes

`lem-sc-abelian-sheaf-finite-generation-exhaustion`: the structural directed presentation of
an arbitrary abelian sheaf on a quasi-compact-open basis; one remaining public named theorem,
with its complete source proof. It is strictly the exhaustion part of the original argument.
It does not assume compactness of the whole space or compactness of pairwise intersections.

`lem-sc-abelian-integer-extension-mono`: the proved embedding of an open integer extension
into the constant integer sheaf. It is valid for every open, and uses the already proved
extension-by-zero stalk/counit theorem and existing Mathlib/source-library sheafification
interfaces. No change record is needed: existing signatures and public imports are unchanged,
and new interfaces belong to new modules with their own nodes.

## Second reading by M1

1. Compared the delivered main module with the repository version using diff and
   checked the original theorem signature byte for byte, from `theorem` to `:=`.
   Verdict: unchanged; no existing definition or public import changed, and the
   three additional imports are proof-only. The other two modules are new.
2. Independently compiled all three modules in import order: no errors or warnings.
   Scanned every delivered Lean file: the only direct sorry is the named public
   exhaustion theorem listed above; no forbidden trust mechanism or hollow definition.
   Compiled scratch copies with `#print axioms` for every declaration. The integer
   restriction isomorphism, integer-extension embedding and both exact-sequence
   helpers use only propext, Classical.choice and Quot.sound. The colimit helper,
   original theorem and exhaustion additionally use sorryAx, exactly as expected
   from the named open dependencies. Verdict: a valid reduction, not an axiom-free
   proof of the full closure.
3. Read the exhaustion statement, docstring and node together against Stacks 02UX
   (https://stacks.math.columbia.edu/tag/02UX), including its first paragraph.
   Finite subsets of all compact-open sections form a small directed index even
   for arbitrarily large section groups in the given universe. The empty subset
   supplies a zero stage, so empty spaces, zero sheaves and zero generators work.
   The local gluing argument needs a compact-open basis but not compact overlaps.
   The embedding proof works for empty, whole and arbitrary nonclosed opens via
   the counit's interior stalk isomorphism and zero exterior stalks. Verdict: both
   new statements are true; the sole split-off is strictly the structural
   exhaustion step, with no cohomological hypotheses or conclusion. It is not a
   restatement of the item and is not a small remaining proof.
   Independent searches used LeanFinder for filtered unions of images of finite
   sums of free abelian sheaves supported on basis opens, Loogle for sheaf colimit
   images, and grep for generation/subobjects/colimits in Mathlib's site files.
   Inspected the resulting SheafOfModules.GeneratingSections machinery and searched
   lean/Sheaf and the upstream topology/site files: no existing theorem supplies
   this exhaustion conclusion; the related module-sheaf generators do not assert
   this directed presentation. Queries are recorded in searches.jsonl.
4. Read the proof from its conclusion back through the final exhaustion, the
   explicit finite-generator induction and the one-generator kernel argument.
   The p+1 kernel argument avoids quotient-stage colimit exactness. Every proof
   import is used, and the new modules' public imports support their signatures.
   Compared old and new direct proof dependencies: the sole removed old dependency
   is the filtered-colimit exactness node already listed under No longer needed;
   the stalk theorem remains through the new nodes. The unit sk-thm-curveestimate
   realizes thm-sc-proper-cohomology and no steps, so no unit route is bypassed.
   Verdict: the reduction and pruning are correct.
5. Read all three delivered nodes and their Lean records. The main node records
   precisely the kernel comparison, long exact sequences, induction and final
   comparison used in Lean. New nodes have sources, complete proof plans, searches,
   provenance and matching signatures; their proof_deps are the unions of their
   step uses. Verdict: the DAG agrees with the code, with no statement change.

Second reading changes: added this independent review and independent search/axiom
verification. No Lean or node repair was necessary; retained the correct worker
implementation and the one explicitly documented structural split-off.
