## What changed

Repair of the landing-tool return at d243fb710: generalized the delivered
private helper in place, replacing
`pushforward_ideal_map_eq_zero_of_generic_stalk` with
`pushforward_ideal_sum_map_eq_zero_of_generic_stalk`. The new statement takes
an arbitrary finite rank r and a map into the pushforward of r copies of an
ideal; it proves the whole map zero from its zero generic stalk. This is a
strict generalization, not a renaming of the rejected rank-one statement.
Moved the finite-biproduct comparison and coordinate argument into that helper.
`mono_of_pushforward_ideal_sum_generic_iso` now applies it directly to the
kernel inclusion. No additional hole, import, or existing interface change.


Replaced the single sorry in `Sheaf.AlgebraicGeometry.CoherentGenericFilteredSource`
with a complete Lean proof assembling two strictly partial construction theorems.
The original public signature, definitions, and public imports are unchanged.
All additional imports are proof-only. No other existing module is adapted.

The construction is split before and after clearing denominators:
`coherent_generic_local_free_model` produces only an open free model, with no
ideal and no global map; `coherent_local_free_ideal_lattice` extends an arbitrary
supplied finite closed free local map, with no annihilation hypothesis, generic
isomorphism, injectivity, nonzero ideal, or filtration conclusion. The latter
works even for nonintegral Z and an empty open U. Its conclusion records the
actual agreement needed to combine the parts, rather than the original theorem
under a new name.

The original module proves that the extended map is generically bijective and
mono. The injectivity proof applies the generalized finite-sum generic-stalk
vanishing lemma to the kernel inclusion. That lemma uses the generic-germ
argument coordinatewise in a finite biproduct. It also proves that both the ideal and the rank are nonzero,
gets coherence of the pushed ideal as a quasi-coherent submodule of F, and
constructs the integral filtration by induction using the already proved empty
sum, successor sum comparison, and split-biproduct filtration lemmas. The
filtration's top stage then supplies coherence of the whole source.

All three delivered modules compile with lcompile.py --all, with no warnings.
Checked r=0 and I=0 explicitly in Lean: both contradict the original hx.
The new local-model theorem allows a zero generic stalk and r=0; the extension
statement allows a zero local map, empty U, U=X, r=0, and nonintegral Z. Neither
chooses data in a definition. The source was read online at Stacks Tags 01YE,
01YB and 01YF. The unit `sk-thm-picard-coherence` has no realized node binding
for this subordinate construction; its higher-direct-image route is unchanged.

## Proved and sorry left

Holes closed in the item: 1, by declaration
`AlgebraicGeometry.Scheme.Modules.coherent_generic_filtered_source`, node
`lem-pc-s3-coherent-generic-filtered-source`. There are no sorries in the item.
Its three private helpers are fully proved.

Holes added: 2, each in its own new module with a source, complete proof in words,
and matching node:

- `AlgebraicGeometry.Scheme.Modules.coherent_generic_local_free_model`, node
  `lem-pc-c3-coherent-generic-local-free-model`, module
  `Sheaf.AlgebraicGeometry.CoherentGenericLocalFreeModel`.
- `AlgebraicGeometry.Scheme.Modules.coherent_local_free_ideal_lattice`, node
  `lem-pc-c3-coherent-local-free-ideal-lattice`, module
  `Sheaf.AlgebraicGeometry.CoherentLocalFreeIdealLattice`.

This is a decomposition, not an axiom-closed proof. Net holes for the delivered
construction are 1 closed minus 2 added = -1; the repository ledger determines
its full import-closure figures. Existing imported theorems may still rest on
sorry; this delivery adds no holes to those modules.

## No longer needed

No original import was removed: the original file had only statement imports.
Removed the trial proof import of `Sheaf.Algebra.Homology.ModuleStalkExact`;
the restriction-to-stalk comparison is already in the source-library module
exported by the ideal-module interface.

The revised top-level proof does not import or invoke these original planned
modules/nodes:

- `Sheaf.AlgebraicGeometry.CoherentGenericPointIdealInclusion`,
  `lem-weil-pbc-coherent-generic-point-ideal-inclusion`: replaced its construction
  with the local-model and specific-map extension steps, proving generic
  injectivity directly.
- `Sheaf.AlgebraicGeometry.CoherentIntegralFiltrationIdealSum`,
  `lem-weil-pbc-coherent-integral-filtration-ideal-sum`, and its successor module
  `Sheaf.AlgebraicGeometry.CoherentIntegralFiltrationIdealSumStep`,
  `lem-weil-pbc-coherent-integral-filtration-ideal-sum-succ`: reconstruct the
  induction from the split-biproduct and pushforward sum comparison lemmas,
  using coherence of the summand obtained from its inclusion into F.
- `Sheaf.AlgebraicGeometry.FinitePushforwardCoherent`,
  `lem-weil-pbc-finite-pushforward-coherent`: no invocation in the original
  module's proof. Coherence is obtained from the quasi-coherent submodule
  criterion. Finite closed pushforward remains mathematical background for
  the local-model step; it is not falsely claimed to disappear from all lower
  natural-language proofs or from the entire target closure.
- `Sheaf.AlgebraicGeometry.CoherentIdealSumCokernelReduction`,
  `lem-weil-pbc-coherent-ideal-sum-cokernel-reduction`, used in the earlier
  attempted shortcut: no cokernel or support-reduction fact is needed here.

No global-closure pruning count is claimed; other targets may still use these
modules. The original node's proof_deps now records the actual assembly route.

## Where the brief, the DAG or earlier work was wrong

The returned version restated a rank-one private theorem already proved in
`Sheaf.AlgebraicGeometry.GenericIdealStalkEmbeddingExtension`. It cannot be
called through an import because it is private. This repair takes the return's
alternative of generalizing the helper in place to a finite-sum codomain;
the rank-one declaration and its duplicate signature are removed. The finite
sum vanishing statement is used directly, including rank zero (the empty
biproduct detects every map as zero). The earlier independent reading of the
returned version is omitted here so the second reader can review this repair.


The planned generic-inclusion and ideal-sum-filtration imports close a source
import cycle through FinitePushforwardCoherent, AffineMorphism, FiniteFreeComplex,
FinitePresentationIntegralFiltration, FinitePresentationSupportReductionFiltration,
CoherentIntegralFiltrationIrreducibleSupport and CoherentGenericFilteredExtension.
This is an import-organization issue, not a mathematical obstacle. Compiling
against cached oleans alone does not detect it; the delivery dry run checks
sources. No existing module is modified to work around its ownership.

The earlier two proposed holes duplicated the whole generic inclusion and
filtration assembly. They are absent. The new statements divide actual steps
of Tag 01YE: an open model and extension of a specified local map. Neither
contains the original conjunction of mono, coherent filtered source, and generic
surjectivity. The report from the rejected attempt, including its second-reading
section, was replaced; this report leaves the independent second reading to
the next worker.

The item has no recorded imported blueprint ancestor: ancestor lookup returns
None because its creator was recorded as a module name. The new nodes preserve
that fact explicitly instead of inventing an ancestor.

## New nodes

`lem-pc-c3-coherent-generic-local-free-model` states the local free model from
Tag 01YE before denominator clearing. Its proof uses annihilator descent,
the integral generic free neighbourhood and the local coherent isomorphism
criterion. It does not state or choose a global ideal lattice.

`lem-pc-c3-coherent-local-free-ideal-lattice` states the finite closed-source
extension clause of Tag 01YB with the affine identification of its source as
an ideal sum. The arbitrary local map is a hypothesis, agreement is a conclusion,
and the ideal inclusion is invertible on the supplied open. It needs no generic
point or integral-scheme assumption. Its proof spells out the affine ideal
construction and localization compatibility. No change records are required,
since no existing interface changes.

## Second reading by C3

Independent second reader, 2026-10-13. Read all three delivered Lean modules,
the three node files, the repository versions, the original four proof dependencies,
and the statements used in the new assembly. Read Stacks Tags
[01YE](https://stacks.math.columbia.edu/tag/01YE),
[01YB](https://stacks.math.columbia.edu/tag/01YB), and
[01YF](https://stacks.math.columbia.edu/tag/01YF).

1. Interface check: PASS. The diff adds proof-only imports, three private proved
   helpers, and the proof of `coherent_generic_filtered_source`. Its existing
   signature is byte-identical, including Noetherian X, closed integral Z, coherent
   F, nonzero generic stalk, maximal-ideal annihilation, and all four conclusions.
   Existing public imports, definitions, and docstrings are unchanged. No existing
   declaration in another module is changed. The existing node changes only
   `proof`, `proof_deps`, and `proof_origin`; there is no unrecorded interface change.
2. Proof check: PASS as a decomposition. Recompiled all three modules in import
   order with lcompile.py, with no errors or warnings. Scanned every delivered
   source: exactly the two reported public theorems have `:= by sorry`; there are
   no new definitions or forbidden declarations. Fresh scratch-copy `#print axioms`
   checks show only propext, Classical.choice and Quot.sound for the finite-sum
   vanishing and mono helpers. The filtration helper, original theorem, and two
   construction theorems additionally use sorryAx, as expected from open imported
   results. In the vanishing helper every pushed coordinate embeds into the
   integral structure sheaf; a zero generic germ vanishes on a smaller nonempty
   inverse-image open, and integral restriction injectivity kills the original
   section. Biproduct projections then kill the map, also at rank zero. Kernel
   cancellation against the generic isomorphism proves mono without assuming
   exactness of the stalk functor.
3. Split statements: PASS. `coherent_generic_local_free_model` retains precisely
   the annihilation hypothesis needed for closed descent and asserts only a local
   free model. Its docstring supplies annihilator descent, a finite generic basis,
   shrinking, and the ambient open X minus i(Z minus V). Integral Z and closed i
   ensure the generic local ring is a field and the indicated complement is open.
   It works for F with zero generic stalk using r=0, and does not assume support
   on Z. `coherent_local_free_ideal_lattice` starts with a supplied arbitrary local
   map; Tag 01YB applies to its coherent closed free source and quasi-coherent
   target. On Spec A with Z cut out by L, the source ideal is the image of K^n in
   A/L in each coordinate, so one coherent ideal works for every coordinate.
   Localization preserves these images and their inclusions, proving the stated
   agreement. No integrality is needed. Checked r=0, zero phi, empty U (take the
   zero ideal, with the empty restriction), U=X (unit ideal), empty Z, and a
   nonreduced/nonintegral affine closed subscheme: none invalidates the statement.
   Both holes are strictly partial: neither asserts generic injectivity and the
   filtration conclusion, and the extension theorem has no generic hypothesis.
   Independent LeanFinder searches used different wording about ideal-annihilated
   closed pushforwards and extending finitely many structure-sheaf copies; they
   returned local generators and affine ideal comparisons, not these statements.
   Loogle `SheafOfModules.free` returned free-sheaf constructors and universal
   properties, not either construction. The earlier broad Loogle query containing
   unqualified `IsIso` was rejected as an unknown identifier and is not an absence
   result. Also searched repository Sheaf/WeilConjectures and upstream
   WeilConjectures by generic/free, local/free/model, and ideal/lattice. Inspected
   `exists_generic_free_neighbourhood`, `exists_generic_ideal_extension`,
   `local_closed_ideal_map_extension`, and the closed-structure extension/product
   bridges. Their domains or conclusions differ: respectively a map on Z with
   generic isomorphism only, a global map on integral Z with no agreement clause,
   or rank-one extension. No exact replacement was found. Closing either new
   theorem requires more than a short application of these statements; in
   particular the closed-descent route imports the finite-pushforward cycle
   already reported above. No additional holes were introduced by this reading.
4. Route and pruning: PASS. The generic stalk is bijective because the extended
   map agrees with the local isomorphism after the invertible lattice inclusion.
   The proof explicitly rules out I=0 and r=0 using hx. Closed pushforward is qcqs;
   its ideal summand embeds into coherent F, so the quasi-coherent submodule
   theorem gives precisely the coherence needed for the filtration induction.
   The zero-sum theorem handles the base; the successor comparison and split
   filtration theorem append the pushed ideal with witness Z,i,I. The top stage
   gives coherence of the entire source. Each added proof import supplies a
   construction, coherence result, comparison, or Noetherian instance used here.
   All three removed original planned dependencies are listed under No longer
   needed; the fourth, coherent_kernel_cokernel_sum, is still used. The unit
   sk-thm-picard-coherence has realized.statement=[] and realized.steps=[[]];
   this subordinate construction bypasses no recorded unit realization or
   higher-direct-image step. No claim of whole-closure pruning is made.
5. DAG check: PASS. The existing node's five steps match respectively the two
   construction calls, proved generic mono argument, nonzero checks, coherent
   submodule argument, and finite-sum filtration induction. Its proof_deps are
   exactly the nine listed construction/coherence/filtration nodes. Each new node
   has its own verbatim Lean statement, source, written proof, dependency union,
   actual search records, split status, creation/blueprint metadata, and matching
   chapter/unit. The local-model dependencies provide closed descent, generic
   basis extension, local isomorphism, and coherent closed pushforward. The lattice
   dependencies provide quasi-coherence/coherence, the complement ideal, extension
   from ideal powers, and coherence of the resulting ideal submodule. No data is
   chosen in a definition. The reported absence of a recorded blueprint ancestor
   is kept explicit. The d243fb710 return is repaired: the duplicate rank-one
   theorem is absent, and the finite-sum generalization is applied directly to the
   kernel inclusion, including the empty-sum case.

Changes by the second reader: added this independent review and fresh scratch
axiom checks/searches. No Lean or node repair was needed. The delivery remains
one upper hole closed and two lower holes added, not an axiom-closed proof.
