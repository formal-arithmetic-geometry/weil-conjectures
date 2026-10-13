## What changed
Reduced `AlgebraicGeometry.Scheme.Modules.moduleCup_resolution_realization` to two
strictly smaller cochain obligations, in separate modules:
`Sheaf.Paper.ModuleCupResolutionExistence` constructs a realizing morphism, and
`Sheaf.Paper.ModuleCupResolutionAugmentation` states its compatibility with coefficient
augmentations before localization. The parent proof uses lax monoidal naturality,
functoriality and cancellation of the target augmentation to establish equality of the
derived maps themselves, then applies H-zero. No flat-model calculation is needed.

The existing integerComplex, derivedAugmentation (including its proved IsIso instance),
Realizes and derivedMap definitions are relocated verbatim into
`Sheaf.Paper.ModuleCupRealizationComplexData` and publicly reexported by the original module.
This permits the two new theorem modules to import the constructions without an import
cycle. No existing mathematical signature or definition body changes, and no arbitrary
data is chosen from an unproved existence statement. The change record is
`coord/changes/module-cup-realization-complex-data.md`.

## Proved and sorry left
Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.moduleCup_resolution_realization`.
Added two holes, each exactly a whole public theorem proof:
- `AlgebraicGeometry.Scheme.Modules.moduleCup_resolution_realization_exists`, node
  `lem-sc-module-cup-resolution-existence`;
- `AlgebraicGeometry.Scheme.Modules.moduleCup_resolution_augmentation`, node
  `lem-sc-module-cup-resolution-augmentation`.

This is a decomposition (one original hole closed, two strictly smaller holes added),
not a net reduction of the hole count. The data module contains no sorry. The original
proved instance `CupAcyclicResolution.derivedAugmentation_isIso` remains proved.

## No longer needed
The original public imports `Sheaf.Paper.ModuleCupResolutionData`,
`Sheaf.AlgebraicGeometry.DerivedTensorStructure`,
and `Mathlib.Algebra.Homology.Embedding.CochainComplex` are now obtained through the public
data-module import, which reexports them unchanged. The canonical single-tensor comparison
module stays a direct public import of the parent and augmentation theorem, whose
statements use its definition; it is not an import of the data or existence module. Removed the redundant direct proof import
`Mathlib.Algebra.Homology.Embedding.ExtendHomology` (used only by the relocated IsIso proof).
Removed the direct proof import `Sheaf.Paper.ModuleCupHZeroIdentification` from the item.
Its theorem (`lem-sc-module-cup-hzero-identification`) is not used in this argument.
The flat-model transport theorem `moduleCup_canonical_hzero_identification` is also not
used: only the actual `moduleCup_singleTensorIso` definition from that module is needed.
Consequently its module remains a public interface dependency, and no claim is made that
it or its transitive H-zero module leaves the target import closure.
The sheaf tensor and total complex nodes remain needed for the new cochain obligations.
No unit statement or unit proof step is bypassed.

For completeness, of the six old parent proof dependencies,
`lem-sc-module-cup-hzero-identification` and the theorem
`lem-sc-module-cup-canonical-hzero-identification` are unused by the new proof.
The latter node still supplies the single-tensor definition needed in the statement.
`def-pc-scheme-derived-tensor-structure` and `def-sc-module-cup-resolution-data`
are retained via the unchanged data constructions; `def-pc-tensor-complex-sheaves`
and `def-pur-sheaf-tensor-product` remain the infrastructure used by the two
split cochain obligations. None of these modules is claimed pruned from the target closure.

## Where the brief, the DAG or earlier work was wrong
The planned flat-model H-zero calculation is unnecessary here. Naturality transports the
cochain augmentation identity directly to an equality of derived morphisms; applying the
homology functor gives the required equality. The two new lemmas are distinct strict
parts of this argument: one only asserts existence, the other an equality of cochain maps
for a chosen realization. Neither restates the parent's existential/H-zero conclusion.
For zero coefficient sheaves the augmentations have zero source, so the augmentation
identity is zero on both sides; the chosen acyclic resolutions need not themselves be
zero. Negative extension terms are zero factors; degree zero uses augmentation_pair. Equality on
elementary sections is justified by sheafification's universal property, not by an
assumption that arbitrary tensor-sheaf sections are global elementary tensors.

## New nodes
`def-sc-module-cup-realization-complex-data` records the unchanged constructions in their
new data module; it adds no hole or new mathematical notion.
`lem-sc-module-cup-resolution-existence` records the coproduct/sheaf tensor construction,
with the Leibniz condition giving the cochain-map equation.
`lem-sc-module-cup-resolution-augmentation` records the degree-zero calculation before
localization, using Realizes and augmentation_pair. Each new theorem has its own module,
source and proof in words. The parent node now follows the actual two cochain obligations
and the proved localization glue. The change record is
`coord/changes/module-cup-realization-complex-data.md`.

## Earlier second reading (a previous round; superseded)

I independently reread the source cited by the nodes, Stacks Project tag 0FKU,
section `section-cup-product`, especially the construction preceding Lemma 20.31.3
and its global specialization. I also reread the delivered declarations in
`lean/Sheaf/Paper/ModuleCupRealizationComplexData.lean`,
`ModuleCupResolutionExistence.lean`, `ModuleCupResolutionAugmentation.lean`, and
`ModuleCupResolutionRealization.lean`, together with the source declarations
`CupAcyclicResolution.integerComplex`, `CupAcyclicResolution.derivedAugmentation`,
`CupResolutionPairing.Realizes`, `CupResolutionPairing.derivedMap`,
`moduleCup_resolution_realization_exists`, and
`moduleCup_resolution_augmentation`. I searched `lean/Sheaf/Paper/ModuleCupResolutionData.lean` for
`CupResolutionPairing.pair`, `restriction`, `leibniz`, and `augmentation_pair`;
`lean/WeilConjectures/AlgebraicGeometry/Modules/TensorSection.lean` for
`SheafOfModules.tensorObjIsoSheafification`, `sheafificationAdjunction`,
`tmulSection`, `tmulSection_map`, and `tensorHom_app_tmulSection`;
`lean/Sheaf/Paper/ModuleCupCanonicalHZeroIdentification.lean` for
`DerivedCategory.moduleCup_singleTensorIso`; and Mathlib
`Algebra/Homology/Bifunctor.lean`, `Monoidal.lean`, `TotalComplex.lean`,
and `ComplexShapeSigns.lean`
for `mapBifunctorDesc`, `d₁_eq`, `d₂_eq`, and `ιTensorObj`.
The unit realization record
`dag/units/sk-prop-av-cube.json` and the corresponding target record
`dag/nodes/sec-abelian-varieties/lem-sc-module-cup-resolution-realization.json`
were inspected as well. The unit record has `realized.statement = []` and
`realized.steps = [[]]`; its one written step applies the general cube theorem
to the seven-factor invertible sheaf. These empty realization lists do not
license a different unit route.

The naive total-tensor map in 0FKU, followed by its compatibility diagram
with localization, is the source construction being formalized. Restriction
compatibility and bilinearity in `CupResolutionPairing` first give linear
maps from the presheaf tensor over every open. `D.restriction` makes these
maps natural, so the sheafification adjunction extends them uniquely to
morphisms from the tensor sheaf. For equality, precompose with the
sheafification unit: pure tensors generate that presheaf tensor, and
adjunction uniqueness then gives equality of the sheaf morphisms. This
does not assume global elementary tensors generate tensor-sheaf sections.
On a tensor summand `(r,s)`, the total differential is
`d(a) tensor b + (-1)^r (a tensor d(b))`. Applying the descended pairing
gives the right side of `D.leibniz`, including its degree-identification
`eqToHom` terms, and `D.leibniz` identifies it with `d(D.pair r s a b)`.
`ComplexShapeSigns` defines the first sign as 1 and the second as the
first index's sign, confirming this convention. Thus the descended maps
assemble to a cochain morphism. In bidegree `(0,0)`,
`Realizes` applied to the augmented sections evaluates the left composite
as `D.pair 0 0 (aF a) (aG b)`; `augmentation_pair` identifies this with
`aT (tmulSection a b)`, which evaluates the right composite. This gives the
pre-localization identity used by the augmentation theorem. The canonical degree-zero
single-tensor identification is the one recorded by
`lem-sc-module-cup-canonical-hzero-identification`.

I checked edge cases explicitly in the statements and proof plans: negative
integer degrees of each extended resolution are zero. A total summand with
one negative index is zero, even if the total degree is nonnegative, so its
component is the unique zero map; the boundary from degree -1 has zero source.
A zero coefficient sheaf does not force its resolution to be termwise zero:
existence still uses the given bilinear pairing on its possibly nonzero terms.
For augmentation compatibility a zero coefficient factor makes the source
single tensor zero, and both composites vanish. Finally,
`moduleCup_singleTensorIso` is the composite of
`map₂HomologicalComplexFlipObjSingleIso` and
`singleMapHomologicalComplex`; at degree zero these are the identity
identifications of `F tensor G`, with no additional sign or symmetry twist.
These checks do not require an assumption about sections being elementary tensors. The two split-off theorems are strictly
smaller obligations than the target and preserve the unit's realization route;
the target's final step is the general theorem-of-the-cube application and its
downstream module-cohomology cup-product compatibility.

This reading records the requested metadata corrections: each new node now has
`blueprint.from.node = thm-sc-theorem-of-cube`, the seven stated `via` nodes,
and the sole-proof-step `place`; the new node statements cite their definition
and theorem dependencies, including `def-sc-module-cup-resolution-data`,
`def-pc-scheme-derived-tensor-structure`,
`def-sc-module-cup-realization-complex-data`, and
`lem-sc-module-cup-canonical-hzero-identification` where used.

Validation after repair: `lcompile.py --all` compiled all four sandbox modules
with exit code 0. No Lean proof, signature, or definition body was edited for
this return; the corrections concern node metadata and this source reading.

## Second reading by A2

1. Interface preservation: PASS. Read the diff against the repository before the
   delivery tool prepared its branch. The parent theorem signature is byte for byte
   unchanged. The four extracted definitions and the proved augmentation IsIso
   instance retain their signatures and bodies; independently checked the declaration
   reader against the old verbatim block in the change record. Local instance bodies
   are also unchanged and are reactivated locally, not made global. The extraction
   is declared in the change record. No coefficient hypotheses or conclusions change.
2. Proof and trust: PASS as a decomposition. All four files compile locally. An
   independent scratch copy with eight explicit `#print axioms` commands shows only
   propext, Classical.choice and Quot.sound for the four definitions and the IsIso
   instance, and those three plus sorryAx for the two split lemmas and their parent.
   Only the two reported whole public theorem proofs contain sorry. There is no
   prohibited declaration, hollow definition or choice of an arbitrary unproved
   existence witness. The parent's existential elimination chooses t inside a proof,
   not in a data definition. Its naturality/cancellation proof is a real reduction.
3. Split statements: PASS. Independently read Stacks 0FKU, the naive total tensor
   construction and Lemma 20.31.3; checked TensorSection's sheafification tensor and
   section formulas, the resolution pairing's restriction/Leibniz/augmentation fields,
   and Mathlib's bifunctor descent and total differential signs. Existence is just
   construction of t, whereas augmentation compatibility is a degree-zero cochain
   identity for any realizing t. Neither restates the parent. Negative factors are
   zero objects; the boundary from degree -1 has zero source. Zero coefficients do
   not imply termwise zero resolutions, but the augmentation source then vanishes.
   In bidegree (0,0) the single/tensor comparison has no sign or symmetry twist.
   Equality is checked after precomposing with the sheafification unit, where pure
   tensors generate; no global generation of sheaf tensor sections is assumed.
   Fresh leanfinder, loogle and grep searches with different queries found only
   tensor/sheafification infrastructure, no existing theorem solving either hole.
   Both holes require actual sheaf and cochain assembly and did not have a quick
   existing-lemma closure. Their docstrings give source and complete proof plans.
4. Route and pruning: PASS after import repair. The parent first reduces to equality
   of derived maps, using lax monoidal naturality, Q functoriality and the inverse
   target augmentation; applying H-zero finishes. It uses neither flat-model H-zero
   theorem. The report now accounts explicitly for all six old proof dependencies.
   The unit's realized record and its sole general-cube application step are kept;
   no unit route is bypassed. The data module's unused public canonical-comparison
   import was removed and placed directly in the parent and augmentation modules,
   whose statements use that definition. Proof-only lemma imports remain plain.
   No entire module is claimed removed from the targets' import closure.
5. DAG agreement: PASS after metadata repair. The parent proof and proof_deps name
   the two cochain obligations and extracted data. New theorem nodes have their
   matching statements, named holes, source, proof steps, searches and blueprint
   ancestry. Removed the unused canonical-comparison dependency from the new data
   node. No existing statement or unit record changes. The three direct consumers
   (ModuleCupRealizationEvaluation, ModuleCupResolutionInvariance and
   ModuleCupEqualDerivedMapsClass) compiled individually against the sandbox overlay
   before the import repair; they are checked again against the final overlay.

Changes in this second reading: corrected placement of the canonical-comparison
public import and its new data-node dependency, added independent search evidence,
completed the pruning inventory, repaired the change record's users-table spacing,
and recorded this five-point review. No proof body, signature or mathematical
construction was changed. One original hole is closed and two lower holes remain
added: net minus one, a decomposition rather than a completed axiom-free proof.
