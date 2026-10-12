## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.ModuleSubobjectGenericNeighbourhood`
with a complete Lean reduction. The existing theorem's name, universes, hypotheses and
conclusion are unchanged. Added proof-only imports of `KernelCokernel`, `GenericConstancy`,
`ModuleGenericGenerators`, and `LocalSystemGenericZeroMap`; existing public imports stay.

The proof lifts generic generators on an irreducible etale neighbourhood Y, obtaining
H -> F_Y -> G_Y. The cokernel Q of H -> G_Y is finite locally constant by the existing
source-library theorem. The map F_Y -> Q vanishes on generic stalks by epi cancellation,
and generic detection makes it zero. Abelian.monoLift then supplies an inverse to H -> F_Y;
two monic cancellations prove both inverse identities. The resulting local constancy of
F_Y descends to U using upperStarComp and IsLocallyConstantSheaf.of_cover for a singleton
surjective etale cover. The updated original node follows these exact steps.

This retains the generic-neighbourhood route of [Stacks 09BH (3)]
(https://stacks.math.columbia.edu/tag/09BH), and uses the persistence argument of
[Stacks 09BG (3)](https://stacks.math.columbia.edu/tag/09BG). Both source proofs were read
in etale-cohomology.tex and checked against the tag pages. The unit's realized statements
and steps are preserved.

## Proved and sorry left

Proved (from named intermediate statements):
`AlgebraicGeometry.Scheme.exists_open_locallyConstant_of_mono_at_genericPoint`
(node `lem-weil-pbc-module-subobject-generic-neighbourhood`). No sorry remains in the
original module, including inside its proof.

Two new public theorem proofs are exactly `:= by sorry`:

- `AlgebraicGeometry.Scheme.exists_generic_generating_locallyConstant_subsheaf`,
  node `lem-weil-pbc-module-generic-generators`, module
  `Sheaf.AlgebraicGeometry.ModuleGenericGenerators`.
- `AlgebraicGeometry.Scheme.eq_zero_of_generic_sheafFiber_eq_zero`,
  node `lem-weil-pbc-local-system-generic-zero-map`, module
  `Sheaf.AlgebraicGeometry.LocalSystemGenericZeroMap`.

Each has a complete proof in words and a source in its docstring and node. The first
asserts only generic generation on an etale chart; it does not assert equality with F.
The second is an independent generic zero-map criterion with arbitrary source and a
locally constant target, requiring no finiteness or Noetherian hypotheses. Neither is
a restatement of the delivered theorem.

Validation: all three modules compile locally without errors or warnings. Edge cases
checked mathematically: empty X supplies no eta; F = 0 uses H = 0; an identity inclusion
uses H equal to the local system; over Lambda = Z the submodule 2Z of Z is finitely
generated without a finite underlying set. Generic detection includes the zero source
and target. An extension by zero from a proper dense open shows why the generation
lemma asserts equality of generic stalks only, leaving the global comparison to the
separate detection argument. All definitions are existing library definitions.

## No longer needed

No original import is removed, and no module is pruned from the transitive route.
The following old direct `proof_deps` are no longer used directly by the original
proof (all remain in the proof dependencies of one or both split-off lemmas):

- `def-constructible-constant`
- `def-constructible-finite-locally-constant`
- `lem-weil-pbc-flat-lfp-open`
- `lem-weil-pbc-noetherian-finitely-many-components`
- `lem-weil-pbc-noetherian-submodule-finite`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `prop-weil-pbc-geometric-stalks-exact`

The original direct proof dependencies for component finiteness, Noetherian submodule
finiteness, stalk exactness and conservativity are now used inside the two intermediate
nodes, rather than re-proved inside the original module. Their need is retained.
`Sheaf.AlgebraicGeometry.ConstantSubsheafGeneric` is not imported: it requires a finite
coefficient ring and finite underlying module, whereas this theorem permits Z and
finitely generated infinite modules. `Sheaf.AlgebraicGeometry.LisseGenericKernel` is not
imported: it concerns abelian-group sheaves with another local-constancy predicate and
monicity of a map out of a local system. These were search candidates, not pruned
original dependencies. The new zero-map module needs only Defs and has no unnecessary
Noetherian import.

## Where the brief, the DAG or earlier work was wrong

No statement correction or definition change is needed. The previous proof description
mixes descent of individual generators on a constant chart with descent of local
constancy to the original open. The delivered reduction keeps the generator construction
on the irreducible etale chart and uses the already-proved etale-local constancy theorem
for the latter descent. This avoids requiring a globally constant submodule on the open.
The source 09BG is Lemma 59.73.12. LeanSearch was attempted separately for both new nodes
and returned Internal Server Error; LeanFinder, Loogle and source grep found no suitable
existing statement. The tool unavailability is recorded in the nodes.

## New nodes

`lem-weil-pbc-module-generic-generators` records component isolation, a pointed etale
trivialization, and lifting finitely many generators of the generic submodule. Its
module is `lean/Sheaf/AlgebraicGeometry/ModuleGenericGenerators.lean`. It concludes a
monomorphism H -> F_Y with generically epimorphic stalk maps, and supplies a surjective
etale chart above an open containing eta. Its source is 09BH (3), the paragraphs before
the application of 09BG.

`lem-weil-pbc-local-system-generic-zero-map` records the persistence of a nonzero image
germ in a locally constant target at a geometric generic point of an irreducible scheme.
Its module is `lean/Sheaf/AlgebraicGeometry/LocalSystemGenericZeroMap.lean`; its source is
09BG (3), made etale local as in 09BH. It is used on the map to a locally constant cokernel.
No change records are needed because no existing statement or public import changed.

## Second reading by K2

1. **Interfaces: pass.** Compared the original module against the repository with
   `diff` and checked its theorem signature byte for byte: unchanged. The only
   additions are the four proof-only imports and the proof body. No target,
   definition, existing docstring, or public import changes. No relevant change
   record was found in `coord/changes/`.
2. **Lean proof: pass as a reduction.** All three delivered modules compile cleanly
   through `lcompile.py`. The only two remaining sorries are precisely the named
   split-off theorems listed above, both exactly `:= by sorry`. No forbidden code
   or hollow definition occurs. A scratch module explicitly importing all three
   modules prints axioms for all three declarations: only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. Thus the original theorem has a
   checked reduction, not a completed axiom-free proof of its dependency closure.
   Read the epi cancellation, cokernel factorization, both monic cancellations,
   upperStarComp orientation, and singleton-cover descent against their declarations.
3. **Split-off statements: pass.** Read both complete natural-language proofs and
   their nodes against Stacks 09BH (3) and 09BG (3). Checked the zero source/target,
   empty scheme, zero ring, identity inclusion, and the finitely generated infinite
   module example `2Z ⊆ Z`. Component isolation is justified by Noetherianity of X;
   finite generation of the generic submodule uses Noetherianity of the ring.
   Generic detection needs neither finiteness nor Noetherianity. Neither new lemma
   restates the target: one constructs a subsystem only generically, the other is
   a zero-map criterion with arbitrary source. Independent LeanFinder searches
   used “injectivity of restriction” and “spread a finitely generated submodule”;
   Loogle searched `"sheafFiber"`, and Mathlib grep searched generic faithfulness,
   injectivity, constancy, and local generators. Read the upstream and Sheaf
   candidates: the Tilde results concern structure modules, ConstantSubsheafGeneric
   requires a finite underlying module, and LisseGenericKernel uses a different
   abelian-sheaf predicate and proves monicity. No suitable shorter reduction or
   split-off theorem that could be closed in a few minutes was found.
4. **Top-down route and pruning: pass after report repair.** The original proof
   genuinely combines the two strictly partial lemmas with existing proved
   kernel/cokernel and cover-descent results. Every added import provides a used
   declaration; existing public imports provide signature notions. The seven
   removed direct dependencies are now explicitly listed under No longer needed;
   all remain below the split-off nodes, so no module is pruned from the transitive
   route. Read `dag/units/sk-thm-p1.json`, including every `realized` entry: neither
   the unit's statement nor any realized step is replaced or bypassed.
5. **DAG agreement: pass after metadata repair.** Each proof_deps is exactly the
   union of its proof steps' uses, and all referenced nodes exist. The original
   node describes the reduction actually written in Lean. Both new nodes have
   source, proof in steps, search records, split status, creator, blueprint origin,
   chapter, unit, and Lean records. The new Lean statement fields now preserve the
   actual signatures verbatim, including newlines. The new generic-generator
   proof text now explicitly transports epimorphy between geometric points over
   the same residue field through compatible separable closures.

Changes by this reading: clarified the new generic-generator docstring and its
node's proof at the all-geometric-points step; made both new node signatures
verbatim; completed the removed-direct-dependency list; appended this review.
No Lean proof or existing signature was changed. Two split-off theorems remain.
