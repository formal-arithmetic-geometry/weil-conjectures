## What changed

The exact statement of `WeilConjectures.integral_verdier_biduality` is unchanged.
Its combining proof supplies all clauses of `IntegralVerdier.Conclusion`
from the existing ambient Hom comparison, Roos completeness, residue Tor, exactness,
and four separate finite/structural inputs. All seven delivery modules compile together
in import order. It includes proved private arguments for
complete-cone conservativity, biduality naturality, and anti-equivalence from a natural
invertible double dual. Evaluation and arbitrary-transpose compatibility are proved
by adjunction; reconstruction transports the actual Roos triangle with its first legs.

The fourteen model declarations moved with identical signatures to `IntegralVerdierModels`, publicly
reexported by the item. This avoids an import cycle for the four finite/structural
lemmas. The change record is `coord/changes/integral-verdier-models.md`; its user table
lists all 63 transitive consumers and the item. No consumer source was adapted.
Thirteen bodies are verbatim; comparison expands its old evaluation transpose and uses
the scalar-reduction wrapper consistently, with the identical morphism. Definition
docstrings now name their precise owner nodes. No adopted source-library file or target signature was changed.

The unclaimed module `Sheaf.Paper.IntegralDerivedReduction` now implements its existing
`integralDerivedReduction` wrapper by the definitionally identical
`scalarReductionDerivedExtension`. This avoids repeatedly unfolding the completed-ring
limit in adjunction matching. Its signature and all other existing declaration bodies
are unchanged. The added public import is acyclic. The change record
`coord/changes/integral-derived-reduction-wrapper.md` lists all 3,683 transitive consumers
and current claim holders; none needs a source adaptation.

## Proved and sorry left

Closed the original hole of `WeilConjectures.integral_verdier_biduality` by a complete,
compiling combining proof. The item and model module contain no `sorry`. This is a decomposition,
not a net proof or a claim that the target has only the permitted axioms.

The new theorem `WeilConjectures.IntegralVerdier.finiteIntrinsicVerdier_bounds`
is proved from constructible descent, etale Verdier preservation, normalized site
Hom comparison, and the flat-model theorem. Its complete proof compiled successfully.

Three new, strictly separate result holes remain:

- `WeilConjectures.IntegralVerdier.finiteIntrinsicVerdier_biduality`:
  `lem-sf-finite-intrinsic-verdier-biduality`, geometric biduality after constant-ring realization.
- `WeilConjectures.IntegralVerdier.signedCalculus`:
  `lem-sf-integral-verdier-signed-calculus`, structural presentations and first-input naturality.
- `WeilConjectures.IntegralVerdier.reductionPairing`:
  `lem-sf-integral-verdier-reduction-pairing`, the transition square and reduced signed delta.

Original holes closed: 1. New holes added: 3. The new finite-bounds lemma is proved.
Packet net: -2. Each added hole is exactly a named
public theorem, with its source and full proof in words, in its own module and node.
There are no holes in definitions or private helpers. The three remaining results are distinct
parts of the two source paragraphs: none has the integral theorem's hypotheses and
conclusion. Finite bounds and finite biduality do not assume integral completeness;
structural calculus has no geometric dualizing object; pairing compatibility does
not assert any geometric biduality, constructibility, or Tor bound.

## No longer needed

No module is withdrawn. No unit statement or realized proof step is bypassed.
The theorem uses the existing split Hom-isomorphism and Roos-transport interfaces
directly. The bundled integralHomReduction theorem is not used by this proof; its
module stays available through the unchanged public model imports.
The old direct private imports removed from the item are:

- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Paper.ComparisonTorAmplitude`
- `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude`
- `Sheaf.Paper.IntegralReductionTowerCanonical`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `Sheaf.Paper.FiniteFieldFiber`
- `Sheaf.Paper.FiniteTorAmplitude`
- `Sheaf.Paper.SfIntegralConstructible`
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`
- `Sheaf.Paper.SfDerivedComplete`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Sheaf.Paper.WeilVerdierPreservationStrata`
- `Sheaf.Paper.FiniteStageVerdierBiduality`
- `Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `Sheaf.Paper.CoefficientRingedTensorHomModel`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`
- `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`
- `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory`
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.Paper.FiniteTorAmplitudeSites`
- `Sheaf.SixFunctors.FiniteDualitySiteComparison`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`

These removals are direct-import pruning only: definitions remain publicly available
through their unchanged public dependencies, and the finite inputs retain the
geometric arguments. In the DAG the main proof now cites the four separate lemmas;
its former finite-origin, finite-preservation, fixed-scalar-biduality and chain-pairing
steps are dependencies of those lemmas, not mathematics withdrawn from the project.
No global closure-pruning count is claimed.

Former direct proof dependencies have these dispositions (none is withdrawn):

| Nodes | Why no longer direct dependencies of the combining proof |
| --- | --- |
| `lem-coef-integral-hom-reduction` | Its Hom-isomorphism and Roos-transport constituents are used directly. |
| `lem-sf-proetale-constructible-origin`, `lem-sf-comparison-tor-amplitude`, `lem-weil-verdier-preservation-strata`, `lem-weil-finite-duality-site-comparison` | The proved finite-bounds argument uses the normalized site-descent interface; finite geometric transport remains in the separate biduality input. |
| `thm-fix-general-biduality` | The separate intrinsic finite-biduality input records the realization needed to use fixed-scalar geometric biduality. |
| `lem-pc-sheaf-modules-tensor-closed`, `lem-pur-rhom-global-sections`, `lem-weil-pbc-ringed-internal-hom-exact-restriction` | Structural calculus is isolated in signedCalculus; exactness uses the existing independent-universe theorem. |
| `lem-weil-duality-pairing` | Its evaluation-transpose definition is retained in the model API; naturality and anti-equivalence are proved categorically here. |
| `lem-kun-distinguished-cone-zero`, `lem-pur-derived-change-of-rings` | The combining proof uses Mathlib triangle zero criteria and the existing exactness witness of scalar reduction directly. |
| `prop-coef-integral-dualizing` | The integral object and its reductions are supplied arguments; their definitions remain statement dependencies. |
| `def-pc-tensor-complex-sheaves`, `def-weil-derived-complete`, `def-weil-derived-complete-integral-detailed`, `def-weil-derived-limit`, `def-weil-finite-tor-amplitude`, `def-weil-integral-reduction-tower`, `def-weil-pbc-proetale-site`, `def-weil-proetale-tor-amplitude` | These definitions remain in the unchanged public statement/model dependencies. They are not additional lemmas to prove. |

The main node drops these obsolete direct `tool_uses` approvals: `lem-weil-pbc-ringed-internal-hom-exact-restriction`, `lem-sf-proetale-constructible-origin`, `lem-pur-rhom-global-sections`, `lem-pc-sheaf-modules-tensor-closed`. The existing dimension approval stays in its original order; no approval is added.

## Where the brief, the DAG or earlier work was wrong

The stated finite duality comparison concerns fixed-scalar module sheaves, whereas
the item's finite dual is ambient Hom over the constant ring sheaf. They cannot be
identified by applying the theorem verbatim. The finite lemmas record the needed
closed realization and evaluation-normalization arguments explicitly.

TensorPresentation supplies separate adjunctions for each first input, and
SignedSymmetry supplies objectwise swaps normalized on representatives. Neither
record includes first-input naturality as a field. The combining proof therefore
uses explicit first-input evaluation and swap naturality supplied by signedCalculus;
it does not infer naturality for arbitrary unrelated adjunction choices.

The complete-cone proof needs no additional geometric Nakayama assumption: exact
reduction kills the cone, and its recorded Roos triangle with zero reductions kills
it. The natural double-dual isomorphism alone yields full faithfulness and essential
surjectivity by an elementary categorical argument.

Edge cases checked in the new statements and proofs in words: n=0 is the residue
quotient; the dimension bound may be zero and the scheme empty; zero inputs are
allowed; Tor amplitude already includes ordering; no site-perfectness is inferred
from constructibility. The unit route is unchanged.

## New nodes

`def-sf-integral-verdier-models` owns the thirteen moved model declarations other
than Conclusion; the existing Conclusion owner is relocated to the same module.
These are the same constructions; the comparison body spells out its original
evaluation transpose using the common scalar-reduction wrapper. No theorem data are chosen.

`lem-sf-finite-intrinsic-verdier-bounds` realizes the first paragraph's finite
preservation and sharp interval after intrinsic coefficient realization.

`lem-sf-finite-intrinsic-verdier-biduality` realizes the second paragraph's finite
geometric invertibility for the actual signed evaluation transpose.

`lem-sf-integral-verdier-signed-calculus` records the coherent normalized
structural tensor-Hom calculus used to define and prove naturality of delta.

`lem-sf-integral-verdier-reduction-pairing` records the two coefficient pairing
identities used for transition compatibility and reduction of the actual delta.

Change record: `coord/changes/integral-verdier-models.md`.

Change record: `coord/changes/integral-derived-reduction-wrapper.md`.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
