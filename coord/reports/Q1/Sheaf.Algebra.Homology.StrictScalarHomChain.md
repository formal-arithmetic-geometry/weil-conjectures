## What changed

Complete proof of the assigned existence theorem, preserving all public
signatures. Private helpers construct the ordinary scalar adjunction and slice
Hom equivalence, assemble the actual product-Hom isomorphism, and verify its
signed differential. The tensor comparison is natural and lifted termwise.
Sigma is the scalar-adjunction transpose of postcomposition with the scalar
unit and q; alpha is assembled from sigma, theta and nu. Normalized formulas,
uniqueness, the strict square and all input naturalities follow from these maps.
The coefficient square uses the existing scalar tower isomorphisms and an
adjunction-defined restriction mate; its four compatibility equations are checked
on nested unit tensors using adjunction and product extensionality.

No helper has a postponed proof. The maps are explicit constructions; no arbitrary
witness is selected from a postponed existence assertion. The complete coefficient coherence argument is
proved first for arbitrary normalized Data and CoefficientSquare records and
then specialized. This avoids expensive conversion between large concrete
sheafification constructions. The focused generic proof compiled in 28.1 seconds.
The complete module with the current declarations and generated-helper settings
compiled in 48.1 seconds with no errors or warnings.
`#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`;
there is no `sorryAx`. All five original direct downstream modules compiled
against this candidate: FlatScalarEvaluationModel (44.0 seconds),
SliceScalarHomChainAdjunction (10.0 seconds), ScalarHomChainEvaluation
(6.1 seconds), LatticeSupportedHomFiniteComparison (43.7 seconds), and
ScalarHomChainCoefficientCoherence (13.9 seconds). The byte-identical temporary
consumer copies were removed after testing; they are not part of this delivery.
A later delivery compile exceeded 60 seconds. The private proof section now
disables the unused-tactic linter to avoid traversing its large tactic trees;
this changes neither elaboration nor kernel checking. Delivery compiles the
final source and also runs preflight.

Performance repairs include shared slice-adjunction equivalences, abstract
functor-square lifts, categorical Hom-map laws, an explicit tensor/sheafification
comparison equation, explicit universe and tensor-presheaf parameters, and local
opacity around completed constructions. Public definitions, signatures,
attributes, and public imports retain their current source form. Optional
automatic size specifications and constructor injectivity lemmas are disabled
to reduce compile work; all five original downstream modules compiled against
this setting. The DAG copy records
the construction and the abstract generator calculation. The preflight-requested
change record `coord/changes/strict-scalar-hom-proof-commands.md` documents the
proof-only commands and the five unchanged downstream modules. The additivity
helper is a proved private theorem activated only as a local instance.

## Proved and sorry left

The original sorry body of
`SheafOfModules.StrictScalarHom.exists_scalarHomChainIdentification` is replaced
by a complete proof from the existing library declarations: one of one holes
closed. There are zero sorries left in the delivered Lean file, zero holes added,
and zero split-off statements. No new module or public declaration is added.

## No longer needed

Removed proof import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction` and
proof dependency `lem-sfb-localized-site-tensor-restriction`. Direct descent
of the scalar-extension unit after restriction to each slice replaces this
separate comparison. No module is withdrawn; other users may still need it.
The current DAG also plans three intermediate nodes:
`lem-sfb-slice-scalar-hom-chain-adjunction`,
`lem-sfb-scalar-hom-chain-evaluation`, and
`lem-sfb-scalar-hom-chain-coefficient-coherence`. The private constructions here
supply the mathematical content needed here directly, so this proof does not import or
require those separate intermediate declarations. All three modules now have
Lean attachments and depend on this item's interface, so none can be imported
here without a cycle.
No blueprint unit record
names this node or those three intermediates in its realized route.

The node copy updates proof, proof_deps and proof_origin. The obsolete tool_uses entry for
`lem-sfb-localized-site-tensor-restriction` is removed, as permitted by the current
stage-3 pruning rule.

The ordinary scalar map and tower normalization use the already proved
`ScalarExtensionBinaryCoherence` and `ScalarExtensionDualTowerCore`; the existing
`HomotopyCategory.Adjunction` supplies the termwise additive adjunction lift.
These private import directions were checked. No public imports are changed.
Six redundant private imports were also removed from the retained candidate;
the public import closure already supplies them:

- `Mathlib.CategoryTheory.Sites.PreservesLocallyBijective`
- `Mathlib.RingTheory.TensorProduct.Basic`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`
- `Mathlib.LinearAlgebra.TensorProduct.Defs`


## Where the brief, the DAG or earlier work was wrong

The blueprint's mathematics is retained. Its separate localized tensor comparison
is unnecessary: local bijectivity of the actual sheafification unit gives the
slice adjunction directly. Defining sigma by the lifted adjunction also makes
its chain condition formal after theta's differential has been checked.

Earlier retained attempts reported unknown module-prefix errors. The resumed
attempt initially received busy responses. The server now resolves the imports
and compiles the unchanged baseline. No launcher script or shared repository
file was modified.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
