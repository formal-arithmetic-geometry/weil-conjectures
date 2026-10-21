# SheafOfModules.OpenTensorNormalization.normalizedOperations_exists

## Reason

The complete proof adds private categorical and sectionwise helpers, private proof
imports, namespace openings, additional universe names, local variable sections,
and local transparency attributes. Server preflight conservatively classifies the
file commands as a change to what importers see and requires this record. This is
an elaboration-environment record: the existing public theorem signature and public
import are unchanged, and no existing public definition is modified.

The local irreducibility of `SheafOfModules.monoidalCategory` and the proved private
`exactTensorTotalIso_hom_app` API avoid expanding concrete sheaf tensor constructions.
A generic section-map lemma avoids expensive reductions of level coefficient
identifications. A further generic cancellation lemma and the identity-pushforward API remove
expensive conversion steps in the concrete systems proof; the corresponding
diagnostic module compiles in 11.4 seconds.
The complete delivered proof passed compilation before the
change-record requirement was reported by server preflight.

## Old

The original file environment, verbatim:

```lean
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization
```

The original public theorem signature, verbatim (its proof was `by sorry`):

```lean
theorem normalizedOperations_exists {m : Mode} (d : Input.{u} m) (t : SiteSquare d)
    (tx : TensorModel d.R) (tu : TensorModel (restrictRing m d.j d.R))
    (tx' : TensorModel d.S) (tu' : TensorModel (restrictRing m d.j' d.S))
    (s : direct m d.g d.R d.S d.coefficient ⋙ restrict m d.j d.R ≅
      restrict m d.j' d.S ⋙ direct m d.gU _ _ (cornerCoefficient t))
    (hs : ∀ (N : Mod d.S) (W : (Site m d.U)ᵒᵖ)
      (x : N.val.obj ((openInclusion m d.j ⋙ baseChange m d.g).op.obj W)),
      (s.hom.app N).val.app W x = N.val.map (t.iso.inv.app W.unop).op x) :
    ∃ o : Operations d t, o.tensorX = tx ∧ o.tensorU = tu ∧
      o.tensorX' = tx' ∧ o.tensorU' = tu' ∧ o.rightSquare = s
```

## New

The new file environment, verbatim:

```lean
@[expose] public section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization
```

Additional openings are confined to this module or explicit `in` commands:
`CategoryTheory.Functor`, `MonoidalCategory`,
`SheafOfModules.GeometricConstruction`,
`SheafOfModules.CanonicalTensorPullbackOfUniverses`,
`CategoryTheory.Functor.sheafPullbackConstruction`, `WeilConjectures`,
`WeilConjectures.SemilinearSections`, and scoped `ChangeOfRings`.
The private helper namespaces are `GeneralizedRinged`, `SystemPresentation`, and
`SiteRestriction`. Their local `variable` declarations are closed with their
sections/namespaces. The additional universe names
`u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄` are used only by private helpers.

Both concrete tensor-comparison sections contain exactly this local command:

```lean
attribute [local irreducible] SheafOfModules.monoidalCategory
```

`exactTensorTotalIso` and `pushforwardCompOfEq` are new fully constructed private definitions marked
`@[irreducible]`; the tensor component equation is proved by unfolding it. No imported
attribute is changed globally. Local `set_option ... in` commands control
elaboration and heartbeats only; no compiler time limit is raised.
The quoted public signature stays byte-identical, and its proof is now complete.
There are no new public declarations, instances, notation, axioms or holes.
No target meaning changes, and no consumer needs adaptation.

## Users

A read-only traversal of source imports found the following complete transitive
consumer closure (18 consumers plus the item), and a textual declaration-name
search found the sole external use in `OpenTensorNormalization`.
The shared checkout must remain read-only; this traversal avoids the cache writes
and git operations of `tools/downstream.py`. Claim holders below are the current
claim records at preparation time. Only the item is changed in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OpenBaseChangeSiteTransport | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CanonicalRingedRefinementShape | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CanonicalRingedRefinementSquare | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RingedRefinementClopen | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RingedRefinementCoefficientSquare | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RingedRefinementConstruction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RingedRefinementCore | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RingedRefinementData | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RingedRefinementFinite | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCompactProjectionBaseChange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCompactProjectionData | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCompactProjectionFinitePresentation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCompactProjectionTensorSquare | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCompactProjectionTowerOperations | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCompactProjectionTowerPresentation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SystemTensorMateArrows | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenOperationModels | F9 | Private proof helpers and file-local elaboration commands; public signature unchanged. |
| Sheaf.SixFunctors.OpenTensorNormalization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | T3 | Public interface unchanged; no adaptation. |

The `OpenTensorNormalizationData` sandbox overlay is byte-identical to the shared
source and only supplies its missing published artifact; it makes no source or
interface change. No source-library module is edited or adapted.

## Status

landed 20261021T020120-L-2586500 2026-10-21 (merge of deliver/F9/Sheaf.SixFunctors.OpenOperationModels)
