## What changed

`AlgebraicGeometry.Scheme.pur_twist_sheaf_locally_free` now has a complete Lean
assembly proof with its exact original statement. The proof combines concrete root
local models, integral scalar-extension models, and the proved arbitrary completed-line
completeness lemma. It explicitly derives rank one from covering unit models,
composes the derived and ordinary scalar reductions, and proves the uniform support
interval [0,0], including the empty-scheme correction.

The original concrete definitions and their already complete action proofs moved to
`Sheaf.Paper.PurTwistSheaves` to permit these independent arguments without an import
cycle. The original module publicly reexports them. All original public imports,
signatures and construction bodies remain unchanged. The extraction change record is
`coord/changes/pur-twist-sheaves-extraction.md`.

Eight additional public lemmas have complete proofs: finite integral coefficient bases;
sectionwise pushouts of sheaves; the canonical coefficient pushout comparison;
constructibility and cohomological support of singles; derived finite reductions of a
completed line; epimorphic transitions of the actual root tower; finite local models
of an arbitrary rank-one finite coefficient line; and completeness of any completed
coefficient line. The basis proof
reuses the already proved private arithmetic argument in PurTwistCoefficientTensor.
The derived-reduction proof uses the existing
`integralLineTensorComparison_representative`, the canonical K-flat reduction counit,
and a proved identity comparison between the two ordinary scalar-extension APIs.
The transition proof constructs the actual local root sections on Kummer covers.

Every packet module has been compiled through lcompile.py. The independent basis,
sectionwise-pushout, single-support, finite-line-model and root-transition proofs are audited separately
with `#print axioms`. The coefficient comparison retains the existing dependency
purTwistCoefficientTensor (now proved in the shared checkout), and the derived reduction retains the existing K-flat
representative lemma; neither is represented as a new hole in this packet.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.Scheme.pur_twist_sheaf_locally_free` (one
of one in the assigned module). This is a decomposition into two independent
source results, not a net closure proof: two holes are added, so the packet's
closed-minus-added count is -1 before the maintainer's import-closure ledger.

The two remaining `sorry` declarations are exactly:

- `AlgebraicGeometry.Scheme.purTwistRootLocalModels`, node
  `lem-pur-twist-root-local-models`, in `Sheaf.Paper.PurTwistRootLocalModels`.
  This concerns only finite root covers and their compatible completed local basis
  and quotients. It has neither an extension field nor derived conclusions.
- `AlgebraicGeometry.Scheme.purTwistIntegralLocalModels`, node
  `lem-pur-twist-integral-local-models`, in `Sheaf.Paper.PurTwistIntegralLocalModels`.
  This is the ordinary scalar-extension and finite local-model argument, assuming
  the already obtained completed-root rank. It has no derived conclusions.

No hole is left in a definition or a private declaration. The split statements have
complete source proof descriptions and their own nodes. The following new theorems
have no `sorry` in their proof bodies:
`purTwistIntegralBasis`, `CategoryTheory.sheaf_isPushout_of_sectionwise`,
`purTwistCoefficientComparison_isIso`, `constructible_single_support`,
`completedLine_derived`, `purTwistRootTransitions_epi`,
`finiteLocallyFreeLine_models`, and `completedLine_complete`.
The derived-reduction, transition-epimorphy and derived-completeness assertions
are removed from the retained holes. Integral finite-line local constancy, constructibility and finite
stalks are also derived from rank one instead of retained as hypotheses. The generic
finite-line theorem reuses complete finite-line and constant-scalar comparison proofs.

## No longer needed

No existing module or declaration is withdrawn. No global pruning claim is made:
the old geometric proof dependencies still support the two source lemmas, and the
source library remains intact. The original public imports of the assigned module
remain verbatim.

The main module's former private imports of `ProEtaleSiteComparison`,
`IntrinsicFiniteTorsionConstructibility`, `PurTwistCoefficientTensor`, and
`TensorPushoutAction` are replaced by the eight proof modules for the new route.
The coefficient tensor and tensor-action imports remain where their construction
proofs actually use them, in PurTwistSheaves; coefficient tensor is also used in the
proved pushout comparison. The root geometric dependencies are recorded on the
root-model node rather than on the assembled theorem. The arithmetic DVR/basis
argument is recorded on the proved basis node. The original local restriction and Roos-tower plan is
replaced by proved perfect
duality and the existing constant-coefficient and internal-Hom completeness theorems.
The new completeness proof builds a strict-perfect local single model and transports
the augmented reduction triangle along its bidual isomorphism. These are dependency transfers,
not assertions that the old source mathematics is unnecessary.

From the extracted construction module, remove its unused imports of
`DerivedCompleteIntegralDetailed`, `ProEtaleCohomologicalSupport`,
`Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle`, and the source
`ModuleCat.Sheaf.LocallyFree`, as well as the unused private site-comparison and
intrinsic-constructibility imports. None is needed for the actual constructors.
The root-model signature imports the geometric stalk API directly; integral
models need only the concrete sheaves and ordinary scalar-extension interfaces.
The new single-support proof uses the zero-sheaf stratum and explicit isomorphism
transport, without the general triangulated constructibility closure result.
No approval entry in the original node's tool_uses list is removed: those geometric
results remain in the lower source arguments.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed or weakened. The original theorem combines several genuinely
separate geometric and homological source arguments. Keeping its concrete definitions
in the theorem's module creates an import cycle for independent lemmas that use those
definitions; the extraction resolves this without changing any mathematical object.
The DAG now follows the actual complete assembly proof and records each independent
source argument on its own node. The blueprint unit has no realized proof steps to
bypass; its coefficient-twist definitions and route remain present.

The derived-completeness proof uses the existing constant-coefficient and internal-Hom
completeness declarations (their existing holes remain dependencies), and the completely
proved perfect-duality and intrinsic/legacy comparison declarations. No copy of either
existing completeness hole is introduced.

The generic derived-reduction computation requires an explicit essentially-small
instance in the K-flat resolution and tensor comparison applications. The two
ordinary scalar-extension APIs are not definitionally equal; their presheaf
restrictions agree on pure tensors, giving the proved comparison used here.

## New nodes

`lem-pur-finite-locally-free-line-models`: proved local constancy, constructibility
and finite stalks for an arbitrary finite constant coefficient line.

`def-pur-twist-sheaves`: the unchanged concrete construction block, with all fifteen
existing public names attached to its new acyclic owner.

`lem-pur-twist-root-local-models`: the finite and compatible root local models,
source steps 1, 3 and 4; open geometric proof.

`lem-pur-twist-integral-local-models`: ordinary integral and finite scalar models,
source steps 6--8 and 10; open scalar-model proof.

`lem-pur-twist-integral-basis`: the proved finite Z_l basis of O_E, source step 5.

`lem-pur-sectionwise-pushout`: proved reflection of sectionwise pushouts to sheaves.

`lem-pur-twist-coefficient-comparison`: the proved canonical coefficient pushout
comparison, using the existing normalized coefficient tensor theorem.

`lem-pur-constructible-single-support`: proved constructible homology and finite
support for every derived object isomorphic to a constructible sheaf in degree zero.

`lem-pur-completed-line-derived`: the proved K-flat computation of finite derived
reductions, combined with the separate completeness source lemma.

`lem-pur-completed-line-complete`: the augmented Roos completeness argument for an
arbitrary completed coefficient line; proved from perfect biduality, constant
coefficient completeness and ambient internal-Hom completeness.

`lem-pur-twist-root-transitions`: the proved Kummer-cover epimorphy statement for the
actual prime-power root transitions, source step 2.

Every new node carries three recorded Mathlib-search kinds. The change record is
`coord/changes/pur-twist-sheaves-extraction.md`.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
