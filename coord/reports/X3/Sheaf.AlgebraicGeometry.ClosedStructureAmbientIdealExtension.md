## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.Modules.closed_structure_ambient_ideal_extension`
with a complete Lean combination of the tensor-extension and multiplication-image
parts of Stacks Tag 01YB. The original theorem signature and visibility are unchanged.
The closed structure pushforward is proved coherent using the existing, proved
finite-pushforward theorem and the locally Noetherian coherence criterion. The
structure module is invertible, hence finitely presented and finite type. The
coherence of G supplies its quasi-coherence.

Added two theorem modules, `Sheaf.AlgebraicGeometry.CoherentOpenMapTensorExtension`
and `Sheaf.AlgebraicGeometry.IdealPowerTensorImageLift`, for the two geometric
steps. The first extends to a tensor product; it does not descend to the
multiplication image. The second lifts a higher multiplication image into that
tensor product; it has no target module, open subset, or local map. The main proof
composes their witnesses and uses their two equations, functoriality, and
associativity to prove the required restriction equality at exponent n + m.
All added imports of the item's module are proof-only imports. No other existing
module is changed. Updated the item's DAG proof to the actual Lean route.

The three modules compile locally without errors or warnings. The new statements
were checked against the tensor-Hom and second Artin-Rees paragraphs of Stacks
01YB (https://stacks.math.columbia.edu/tag/01YB). In particular, the kernel of
I^n tensor H -> H is annihilated by I^n, by tensor balancing on affine opens;
Artin-Rees therefore makes its intersection with I^m(I^n tensor H) zero.
These are source-backed intermediate assertions, not copies of the item's theorem.

## Proved and sorry left

Closed the item's only hole:
`AlgebraicGeometry.Scheme.Modules.closed_structure_ambient_ideal_extension`
(node `lem-pc-closed-structure-ambient-ideal-extension`). There are no sorries
left in the item's module.

Added two holes, each exactly `:= by sorry` in a named public theorem:

- `AlgebraicGeometry.Scheme.Modules.coherent_open_map_tensor_extension`
  (node `lem-pc-coherent-open-map-tensor-extension`).
- `AlgebraicGeometry.Scheme.Modules.ideal_power_tensor_image_lift`
  (node `lem-pc-ideal-power-tensor-image-lift`).

This is a decomposition: one upper hole closed, two strictly distinct lower
steps added. It is not a complete sorry-free proof of ambient extension and is
not positive net-hole progress. The coherence preparation and the combination
of the two steps are proved in Lean.

Edge cases checked in the new statements: n = 0 uses the left unitor; unit ideals
have invertible multiplication; zero ideals allow a positive exponent and a zero
product; empty U has its unique local map; zero H or F causes no exception.
No integral or generic-point hypothesis was introduced.

## No longer needed

No existing import was removed: the original public imports support the unchanged
signature. Added proof imports were retained only for constants used by the proof.
The tensor-extension module imports the tensor definition directly, without the
unnecessary ideal-module-product-stalk module.

The proof no longer calls the full node `lem-weil-pbc-coherent-homs-over-open`
or its module `Sheaf.AlgebraicGeometry.CoherentHomsOverOpen`; it uses only the
two relevant parts of that proof. In particular the injectivity and transition
system/colimit-data clauses of that theorem are not needed here. It does not
use `Sheaf.AlgebraicGeometry.ModulePullbackIdealPowerProductImage` or its
private power-comparison helpers: the new assertions are formulated directly
with ideal-sheaf-data powers.

The original direct dependency
`lem-weil-pbc-closed-immersion-affine-cover-criterion` is unnecessary for the
coherence preparation, replaced by the proved finite-pushforward theorem
`lem-pc-f3-finite-pushforward-finite-type`. The separate direct use of
`pqf-lem-pushforward-qcoh` and
`lem-weil-pbc-quasi-coherent-finite-type-affine` is replaced by this packaged
finite-pushforward result; these facts remain its transitive dependencies.
The zero-set and affine ideal-product formulas remain needed in the proofs of
the new nodes, not direct imports of the item's proof. No claim is made that
any of these modules is globally unreachable from all targets.

For completeness, the old direct proof dependencies removed from the item node are
`pqf-lem-pushforward-qcoh`,
`lem-weil-pbc-closed-immersion-affine-cover-criterion`,
`lem-weil-pbc-quasi-coherent-finite-type-affine`,
`lem-weil-pbc-coherent-homs-over-open`,
`lem-weil-pbc-quasi-coherent-ideal-zero-set-affine`, and
`lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`.
The last two remain planned dependencies of the tensor-extension split; the
last remains a planned dependency of the image-lift split.

## Where the brief, the DAG or earlier work was wrong

The planned application of `coherent_homs_over_open` cannot be imported here.
The required import-direction check returned NO. Its exact cycle-closing path is:

CoherentHomsOverOpen -> Modules.IdealTimesQuasiCoherentAffineSections ->
WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion ->
WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage ->
WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex ->
IntegralIdealProperCohomology -> IntegralIdealComparisonFiltrations ->
IntegralIdealCommonSubmodule -> RankOneGenericIdealInclusion ->
GenericIdealStalkEmbeddingExtension -> LocalClosedIdealMapExtension ->
ClosedStructureAmbientIdealExtension.

`ModulePullbackIdealPowerProductImage` reaches the same path through
`ClosedImmersionIdealPowerImage` and the upstream closed-immersion module.
The dependency declarations being sorry is not the obstacle; the import cycle
is. No existing dependency was edited or worked around. The two new nodes
expose the exact source steps separately without importing those cycles.
Their future proof workers may also encounter the overly broad upstream
closed-immersion import, which should be pruned by its holder.

The unit `sk-thm-picard-coherence` has empty realized statement and step lists;
this lower-level split does not bypass a unit realization. The same ambient
ideal extension step of the Picard coherence devissage remains proved.

LeanFinder and Mathlib grep found no matching sheaf-level tensor extension or
image-lift theorem. The Artin-Rees search found
`Ideal.exists_pow_inf_eq_pow_smul`, the affine algebra ingredient, rather than
the global sheaf lift. LeanSearch returned HTTP Internal Server Error and is
recorded as unavailable, not a negative search. Blueprint searches for
'homs over open', 'ideal tensor', and 'homomorphisms' found no duplicate of the
two intermediate assertions. The existing umbrella result is retained in the
library and explicitly identified above as cyclic for this item.

## New nodes

`lem-pc-coherent-open-map-tensor-extension` is stated in
`lean/Sheaf/AlgebraicGeometry/CoherentOpenMapTensorExtension.lean`.
It isolates internal-Hom extension and tensor-Hom evaluation from 01YB, before
any image descent. Its node records the finite-type submodule extension,
torsion stabilization, sections comparison, tensor-Hom, support, and affine
power ingredients. Its docstring gives the full argument and edge cases.

`lem-pc-ideal-power-tensor-image-lift` is stated in
`lean/Sheaf/AlgebraicGeometry/IdealPowerTensorImageLift.lean`.
It isolates the second Artin-Rees argument of 01YB independently of any local
map or target. Its node records tensor coherence, annihilation of the kernel,
Artin-Rees, and the affine product-image calculation. Its docstring gives the
balancing argument and the inclusion-compatible construction of the lift.

There are no statement/definition changes, change records, or forced adaptations.


## Second reading by X3

1. Compared the item module with the repository using diff and compared the
   theorem signature programmatically with both the repository and its node.
   Verdict: byte-for-byte identical existing signature and visibility; only six
   proof imports and the proof body changed. No existing definition or target
   changed, and no forced adaptations or change records are needed. The two new
   theorem signatures also equal their node lean.statement fields exactly.
2. Compiled all three modules in import order through lcompile.py: clean, with
   no errors or warnings. Compiled an additional scratch copy with #print axioms
   for all three declarations: only propext, Classical.choice, Quot.sound and
   sorryAx occur. The only two admitted proofs are the named new theorems listed
   above. There are no definitions, arbitrary data choices, forbidden axioms,
   unsafe declarations, opaque declarations, extern or implemented_by attributes.
   Verdict: sound Lean combination conditional on the two reported open lemmas.
3. Independently read Stacks Tag 01YB, including its two tensor paragraphs, and
   checked the affine balancing argument: for a in I^n, a times sum(b_j tensor h_j)
   equals a tensor sum(b_j h_j). Thus I^n kills the multiplication kernel, and
   Artin-Rees gives the claimed inclusion-compatible lift. The first statement
   is the internal-Hom/tensor-Hom extension before this descent. Checked n=0,
   zero/unit ideals, zero modules and empty U; no extra hypothesis is needed.
   Each lemma is a distinct strictly smaller step, not a renamed ambient
   extension theorem. Each has its own module, source, proof docstring and node.
   Repeated LeanFinder, Loogle and Mathlib grep with different descriptions
   (extending internal-Hom sections; tensor/ideal kernels), and searched both
   source roots. No directly applicable duplicate was found. The existing
   umbrella result is explicitly accounted for. Neither global geometric lemma
   can be closed in a few minutes from the available affine ingredients.
4. Checked the top-down composition and coherence preparation. The direct
   coherence and finite-pushforward results are already proved. Confirmed with
   import_direction.py that importing CoherentHomsOverOpen closes a cycle.
   The unit realized statement and step lists are empty, so this decomposition
   keeps the unit route. Imports supply signature constants or named proof
   ingredients; a scratch removal of the Quasicoherent proof import fails at
   isQuasicoherent_unit, so it is needed. Existing public imports were preserved.
   Verdict: no shorter available acyclic route found. Completed the explicit
   list of all six removed direct DAG dependencies under No longer needed;
   no globally unreachable module is claimed.
5. Compared all node fields and proof steps against Lean. Only proof,
   proof_deps and proof_origin change in the existing node; proof_deps is exactly
   the union of step uses. New nodes have source, search records (including the
   unavailable service), split status, creation, blueprint, chapter/unit and
   verbatim Lean records. Their planned proofs agree with the two admitted
   statements and the source. Verdict: nodes and Lean agree.

Second reading changed only this report: added the complete explicit removed
node list and this independent review. No Lean repair was necessary. This
remains a decomposition of one original hole into two lower holes (net -1),
not a sorry-free proof or positive net-hole progress.
