## What changed

Repair of C-72ecd against the current source and its landed human four-node split.
The theorem `external_rhom_cone_pairing` keeps its signature and has a complete
assembly proof with zero local holes. The original definitions are extracted to
ExternalRHomConePairingDefs and publicly re-exported by the item. The existing
seven direct consumers now import that definitions module, breaking the source
cycle. GlobalHomEvaluationFlatLift and LiftedExternalEvaluationChainModel retain
all their declarations and signatures, and ExternalEvaluationTransposeNatural
retains its entire unrestricted five-conjunct theorem.

The item obtains its shift witness and every-source normalized Hom models from
`lifted_external_evaluation_derived_hom_shift`; its chain normalization is the
third conjunct of `lifted_external_evaluation_chain_model`. Open restriction is
projected from conjuncts 4 and 5 of the existing
`external_evaluation_transpose_natural`. The proved generic specialization
`external_evaluation_pairing_natural` is attached to that same existing node.
The native localization braiding and the generic adjunction/evaluation
naturality calculations remain completely proved.

The rejected cochain-model, restriction and native-naturality modules/nodes are
omitted. The remaining new cone obligation is narrowed to a *given* S satisfying
HasSignedHomShift; it no longer asks for the shift witness already supplied by
the existing lifted-chain declaration. All four human-extracted source nodes
are preserved and used by the revised argument, directly or in the remaining
cone-transport plan.

The previous successful check of the refreshed thirteen-module packet compiled
in dependency order through lcompile.py
(Defs 34.0 s, V6 consumer 56.0 s, assembly 9.4 s). `homComplex` retains its
original concrete construction verbatim: removing the earlier wrapper around
homComplexOf restores the reduction behavior required by V6's new proofs.
No source-library module is changed, no existing declaration is withdrawn,
and no target statement changes. Definition changes still require the
independent meaning review recorded in the change record.

The current repair retry compared all thirteen delivered modules with the shared
sources. The V5/V6 adaptations still match the exact lines documented below;
no newly landed proof is overwritten. A fresh dependency-order check using
`LCOMPILE_NO_LOCAL=1 python3 /home/ubuntu/weil-launcher/lcompile.py --all
/home/ubuntu/weil-sandbox/J7/Sheaf.Paper.ExternalRHomConePairing` accepted all
thirteen modules with exit code 0 and no diagnostics. The complete compile is
saved in scratchpad/repair-current-compile.log. The documented remote-only
compiler route uses the project server's published build.

Earlier submission attempts terminated with SIGTERM and no delivery result.
This retry retains the repaired packet and reruns the required delivery tool.

## Proved and sorry left

One original hole closed:
`AlgebraicGeometry.Etale.ExternalRHom.external_rhom_cone_pairing`
(`lem-pur-external-rhom-cone-pairing`). Zero holes remain in the item module.

Complete additional proofs include `external_rhom_derived_braiding`,
`GenericTranspose.ev_naturality`, `GenericTranspose.source`,
`GenericTranspose.target`, `GenericTranspose.parameter`,
`GenericTranspose.pairing_naturality`, `GenericExternal.pairing_eq_pairingOf`,
`GenericExternal.naturality` and `external_evaluation_pairing_natural`, all
under `AlgebraicGeometry.Etale.ExternalRHom` and its indicated subnamespaces.

One new hole is retained:
`AlgebraicGeometry.Etale.ExternalRHom.external_rhom_coefficient_cones`
(`lem-pur-external-rhom-signed-cones`, ExternalRHomSignedCones).
This is the separate native triangle transport for the fixed normalized S.
It is a decomposition, not a net axiom-free proof: one original hole closed,
one new hole added. No definition or private helper has a hole.

Six pre-existing holes are preserved in adapted existing modules, with no
new restatement of them (all names below share the ExternalRHom namespace):

- `external_evaluation_transpose_natural`
  (`lem-pur-external-evaluation-transpose-natural`).
- `globalHom_evaluation_model`
  (`lem-pur-global-hom-evaluation-model`, preserved in the new V5 consumer).
- `lifted_external_evaluation_chain_model`,
  `lifted_external_evaluation_source_model`,
  `lifted_external_evaluation_shifted_lift`, and
  `lifted_external_evaluation_derived_hom_shift`
  (all `lem-pur-lifted-external-evaluation-chain-model`).

Thus the delivered thirteen modules contain seven named theorem holes in total:
six existing and one added. The external two-shift-squares theorem is an
unchanged dependency, outside the delivered set; its existing hole is not a
new hole of this packet. The proved braiding and generic naturality proofs use
only the standard axioms; the assembly also depends on the listed source holes.

## No longer needed

No module is withdrawn or claimed globally pruned. The unit route remains. The human-extracted global-evaluation, lifted-chain-model,
transpose/restriction and two-chain-shift-square nodes remain needed.

The public imports `Sheaf.AlgebraicGeometry.OrdinaryKunnethFiniteRing`,
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and
`Sheaf.Paper.FiniteFieldFiber` are removed: no finite-ring, coefficient-extension
or finite-field assertion is used here. The only construction formerly obtained
through OrdinaryKunnethFiniteRing is the canonical constant-pullback comparison,
whose exact composite is now named directly.

The additional public imports `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`,
`WeilConjectures.Algebra.Homology.HomComplex`, `Sheaf.Paper.KFlatMapFactorization`,
`WeilConjectures.SixFunctors.Etale.Derived.Coefficients` and
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary` are removed from the
interface. Native closed Hom and Mathlib Hom cochains supply its constructions;
the predicates quantify over lifts without constructing them. The ringed and
factorization results remain in the unfinished obligations' DAG dependencies.
The precise public import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat` supplies inverse
image's flatness instance. `EtaleConstantProjectionMap` is public because its
adjunction and tensor comparison occur in definitions. The new generic modules
are public where their data or predicates occur in definitions; only the native
assembly proofs are private imports.

The following original private imports are removed as direct imports, either
because the native structures already expose the definitions' requirements or
because the results belong to the remaining source obligations:

- `Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `Sheaf.Algebra.Homology.KFlat`
- `Mathlib.Algebra.Homology.BifunctorShift`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`
- `WeilConjectures.Algebra.Homology.HomTensorTotal`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`
- `Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel`
- `Sheaf.SixFunctors.GeometricInverseImageConstantModule`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `Sheaf.Paper.CoefficientRingedTensorHomModel`
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`
- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`

The returned unlanded `ExternalRHomCochainModels`,
`ExternalRHomRestrictionNaturality`, and `ExternalRHomNaturality` modules and
nodes are removed from this packet. They are not claimed as globally pruned:
their intended work is supplied by the existing human-extracted nodes.
No deleted.txt is needed because these rejected additions do not exist in the
current library. The quarantined originals are preserved, not deleted.

## Where the brief, the DAG or earlier work was wrong

C5 is repaired: the previous restriction hole duplicated a weaker form of
conjuncts 4--5 of external_evaluation_transpose_natural. The separate native
naturality node duplicated its third conjunct. The item now imports the existing
transpose module and projects its restriction squares; the proved generic
naturality specialization belongs to its existing node. No restriction node or
module is introduced.

Points 5--6 are repaired by rebasing the node proof on the current five assembly
steps and comparing each of the human's four extracted results:

1. GlobalHomEvaluationFlatLift is preserved, with its definition import and the
   single counit-unfolding proof step adapted as documented below. It supplies the resolving evaluations
   for the cone-transport proof plan and remains a proof dependency of the lifted
   chain-model declaration. It is not replaced by a new existence statement.
2. LiftedExternalEvaluationChainModel is preserved with all six signatures. Its
   derived_hom_shift declaration already supplies arbitrary-source Hom models
   and the single signed shift S; its chain_model declaration already supplies
   HasChainNormalization. The item uses these exact declarations. The rejected
   cochain-model obligation is removed entirely.
3. ExternalEvaluationTwoShiftSquares is preserved unchanged. It asserts chain
   equalities in the constant-ring module-sheaf encoding. The residual cone lemma
   imports it and cites both equalities, with their signs, to transport them to
   the native image triangles and the chosen S. It does not restate the chain
   equations or their representative constructions.
4. ExternalEvaluationTransposeNatural is adapted only to the extracted
   definitions and canonical local instances, with a completely proved generic
   specialization added. Its original unrestricted statement and hole remain.
   The item uses the existing open-restriction conjuncts with no new assumption.

The only divergence is the explicitly separate native cone transport. None of
the four source statements asserts native distinguishedness for the given S or
constructs the native coefficient triangle morphism. In particular the derived
Hom shift statement asserts CommShift and normalization, not IsTriangulated,
and the chain two-shift-squares statement does not mention derived triangles.
The remaining lemma combines those existing results with the exactness tools
already cited by the human's assembly steps 3--5. It no longer bundles any of
the results the human extracted. Its docstring and node spell out the target
transport, both shift squares, and the connecting-arrow argument. This is a
mathematical boundary between ordinary chain identities and native derived
triangles, not a split justified by elapsed time.

Points 2--8 are repaired: the change record's Users table now lists the current direct importers ExternalEvaluationTransposeNatural,
GlobalHomEvaluationFlatLift, LiftedExternalEvaluationChainModel and V5's four
new supporting consumers, including the V5/V6 ownership recorded by the return
and the exact import adaptations. SupportedProductLocalization
and KunnethSupported are not current importers and were incorrectly listed.
The two consumers retain the import substitutions and the single V5
counit-unfolding adaptation documented below.

The current item and transpose sources agree with their quarantined originals;
no quarantine path or dependency is withdrawn. Interface extraction and native
structure caches address the previously profiled definitional-comparison cost;
the retained scalar-realization additivity proof is unchanged. All definitions
still construct actual data, with no arbitrary witness chosen from a holed
existence theorem.

## Forced adaptations

This repairs the return at head 12fb362d355. At that returned head,
`Sheaf.Paper.GlobalHomEvaluationFlatLift` was held by V5 and
`Sheaf.Paper.LiftedExternalEvaluationChainModel` was held by V6. Both were
incorrectly described as unclaimed in the returned report and change record.
Their claims have since closed with their landings; the packet preserves those
landed proofs and records the original holders explicitly.

`Sheaf.Paper.GlobalHomEvaluationFlatLift` (V5): line 8 changes from
`public import Sheaf.Paper.ExternalRHomConePairing` to
`public import Sheaf.Paper.ExternalRHomConePairingDefs`. Restoring the original
source while keeping the other delivered sources makes lcompile.py --all refuse:

```text
the modules import one another in a cycle: Sheaf.Paper.ExternalRHomConePairing,
Sheaf.Paper.ExternalRHomSignedCones, Sheaf.Paper.GlobalHomEvaluationFlatLift
```

The concrete cycle is ExternalRHomConePairing -> ExternalRHomSignedCones ->
GlobalHomEvaluationFlatLift -> ExternalRHomConePairing. The last edge must go
to the shared definitions instead: this consumer uses the definitions, while
the new assembly needs the evaluation result below its cone transport. This
import substitution preserves all existing declaration signatures, visibility,
file options and local-instance setup. The current landed proof also needs line
212 to unfold `leftDerivedModelOf` alongside `pullModel`: the unadapted line
`dsimp only [pullModel]` followed by `infer_instance` fails at line 213 with:

```text
failed to synthesize instance of type class
  IsIso (leftDerivedModelOf (f)^*[ModuleCat A] T)
```

The changed line is `dsimp only [pullModel, leftDerivedModelOf]`. It exposes
the same canonical left-derived counit to the existing IsIso instance; the
proof and statement are otherwise unchanged.

`Sheaf.Paper.LiftedExternalEvaluationChainModel` (V6): the sole changed line is
line 18, the same public import substitution. Restoring its original source
while keeping the other delivered sources makes lcompile.py --all refuse:

```text
the modules import one another in a cycle: Sheaf.Paper.ExternalRHomConePairing,
Sheaf.Paper.ExternalRHomSignedCones, Sheaf.Paper.LiftedExternalEvaluationChainModel
```

There is also the direct cycle ExternalRHomConePairing ->
LiftedExternalEvaluationChainModel -> ExternalRHomConePairing. Its statements
need the shared interface, so replacing the assembly import is necessary.
Every existing signature, visibility, body, option and local instance is
unchanged. The previous additional private GlobalHomEvaluationFlatLift import,
transparency-option change and local-instance additions have been removed.
Those changes were unnecessary: each consumer compiles with just the import
substitution and its original options and instance setup.

During the repair retry, current main gained V6's complete proofs of
`lifted_external_evaluation_chain_evaluation` and
`lifted_external_evaluation_hom_shift`, with their private helpers and proof
import. The consumer was refreshed from current main and all this work is
preserved verbatim; its only delivery edit remains the line-18 import change.
The wrapped Hom construction was restored to its original concrete body in the
shared definitions module, so those consumer proofs compile without option,
instance or tactic edits. These two closures belong to V6 and are not counted as J7 proof progress.

V5 subsequently landed the complete assembly proof of
`globalHom_evaluation_flat_lift` and four supporting modules. Its current proof
and proof imports are preserved, with the line-8 interface import change and
the single necessary counit-unfolding adaptation just documented. The four modules are
`Sheaf.Paper.CoefficientPointFlatKFlatComparison`,
`Sheaf.Paper.EtaleScalarFlatKFlatComparison`,
`Sheaf.Paper.GlobalHomChainEvaluation`, and
`Sheaf.Paper.GlobalHomEvaluationModel`. Each receives only the same line-8
public import substitution. Otherwise every line is unchanged. They are
unclaimed in the current claim records. Their old imports close a source cycle
ExternalRHomConePairing -> ExternalRHomSignedCones ->
GlobalHomEvaluationFlatLift -> that supporting module ->
ExternalRHomConePairing. None uses the assembly theorem. They therefore need
the definitions interface instead. The existing hole in
`globalHom_evaluation_model` is preserved, not added by J7. The earlier
claim snapshots named V5/V6; those claims have since closed with their landings.

These are source import-cycle failures reported by lcompile.py's dependency
ordering, before invoking Lean. For completeness, the two original consumers
also compile individually against already-built delivery artifacts (7.8 s and
19.6 s) before their new proofs landed; this does not validate the cyclic
source graph. The additional current V5 elaboration error and its exact
unfolding fix are documented above. The complete adapted source packet is compiled in dependency order,
so both source cycles are checked as well as the individual Lean files.

## New nodes

`def-pur-external-rhom-pairing-interface` attaches the retained concrete interface
and native canonical-data caches to ExternalRHomConePairingDefs. The change record
is coord/changes/J7-external-rhom-pairing-interface.md.

`lem-pur-external-rhom-derived-braiding` attaches the completely proved native
localization/Koszul equation NativeBraidingAt.

`lem-pur-external-rhom-adjunction-naturality` attaches the proved composite
adjunction, transpose and evaluation naturality calculations.

`lem-pur-external-rhom-evaluation-naturality` attaches the original generic
factories and their proved four-variable equation.

`lem-pur-external-rhom-signed-cones` now states only native coefficient-cone
transport for an already fixed normalized signed shift S. Its proof plan uses
the current four human-extracted results, and retains the native exactness and
connecting-square steps. It has one named theorem hole, with source and full
proof in words. It does not assert construction of S, Hom-model existence,
lifted external evaluation normalization, or either chain shift square.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
