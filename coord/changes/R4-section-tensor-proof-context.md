# section_tensor_normalized_of_normalized proof context

## Reason

Construct the comparison isomorphisms explicitly without changing the existing public theorem
signature or any existing definition. Private helpers express equivalence cancellation,
ordinary generator naturality and the derived conjugation identity. Local irreducibility
keeps elaboration from repeatedly expanding chosen derived functors and tensor equivalences.
These attributes are local and export no instance or reducibility changes.

## Old

The original context was:

```lean
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct ChangeOfRings
namespace AlgebraicGeometry.ProEtale.QuotientChange
```

The existing theorem signature remains verbatim. Its old proof was `by sorry`.

## New

The added proof-only imports expose the ordinary section tensor comparison and its proved
naturality API. The new computation theorem is a private import, used only by the proof.
The complete local attributes and options are listed in the delivered Lean source.
Private `run_tac` blocks assign already established proofs of definitionally equal equations,
using the pattern already used in `ModuleRingedToposDerivedComparison.ordinary_monoidal`.
The Lean kernel checks these terms normally; no trusted axiom or checking override is added. No existing
public definition, public import or theorem signature changes. The new public theorem is
recorded separately by its new DAG node.

## Users

The scan `tools/downstream.py Sheaf.Paper.SectionTensorNormalizationTransport --uses
AlgebraicGeometry.ProEtale.QuotientChange.section_tensor_normalized_of_normalized` found 2588
transitive importers and two textual uses, including the declaration itself. The only external
textual user is below. Since this changes only a theorem proof and private proof context,
all 2588 importers retain their public interface and require no edits. No target definition
or statement changes meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SectionTensorNormalizationTransport | R4 | Proof and private helpers only. |
| Sheaf.Paper.InternalScalarPullbackNormalization | unclaimed | Same signature; no edit. |

## Status

landed 20261025T210243-L-3501642 2026-10-25 (merge of deliver/R4/Sheaf.Paper.SectionTensorNormalizationTransport)
