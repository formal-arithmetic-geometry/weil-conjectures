# IntegralCompactSupport.baseChange

## Reason

Direct component invertibility of the published proper/open composite repeatedly exceeded
60 seconds in kernel type checking (about 95 seconds). The profiler and fully explicit
types isolated a definitional conversion between the scheme `(c.ofIsPullback sq).Z` and
`pullback c.g v` underneath the whole module-object derived category. The existing
`Functor.CompactSupportExchangeData` already packages the same two-factor composite and
its proved component/isomorphism API. Instantiate it once, specifying the pullback source
scheme explicitly, and project the map and the isomorphism theorem. No transparency
respect option is disabled, no object is selected from an unproved existence theorem,
and no mathematical functor, normalization or statement is changed.

This changes a definition used by target statements, so their statement/definition
meaning review is reopened. The new map is the identical proper exchange followed by
proper pushforward of the inverse specified open exchange. The old associators have
identity components; the generic API's proved associator equality justifies their omission.

`IntegralCompactSupportDefs` was unclaimed when repaired. No source-library module changes.

## Old

```lean
def baseChange {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (c : Compactification f) (sq : IsPullback u' f' f v)
    (h : IsIso (openExchange Λ (c.isPullback_i_ofIsPullback sq).toCommSq)) :
    image Λ c ⋙ pull Λ v ⟶ pull Λ u' ⋙ image Λ (c.ofIsPullback sq) :=
  @id _ (by
    letI := h
    exact (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (extend Λ c.i)
        (pushExchange Λ (c.isPullback_g_ofIsPullback sq).flip.toCommSq) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (asIso (openExchange Λ (c.isPullback_i_ofIsPullback sq).toCommSq)).inv
        (push Λ (c.ofIsPullback sq).g) ≫
      (Functor.associator _ _ _).hom)

```

## New

Added public import `Sheaf.SixFunctors.DetSfCompBaseChangeDefs` for the generic structure
used by the public definition. All existing imports and declaration signatures are retained.

```lean
/-- The specified proper/open exchange and its component API, kept as one structure.
The source of the proper pullback is explicitly the base-changed compactification,
so its module-object category is shared by the two exchange factors.
Source: blueprint sk-prop-int-brown-construction, final base-change composite
(blueprint: def-sfb-integral-compact-support-interface). -/
def baseChangeData {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (c : Compactification f) (sq : IsPullback u' f' f v)
    (h : IsIso (openExchange Λ (c.isPullback_i_ofIsPullback sq).toCommSq)) :=
  letI := h
  (Functor.compactSupportExchangeData (extend Λ c.i) (push Λ c.g) (pull Λ v)
    (pull Λ (X := (c.ofIsPullback sq).Z) (pullback.fst c.g v))
    (push Λ (c.ofIsPullback sq).g) (pull Λ u')
    (extend Λ (c.ofIsPullback sq).i)
    (pushExchange Λ (c.isPullback_g_ofIsPullback sq).flip.toCommSq)
    (asIso (openExchange Λ (c.isPullback_i_ofIsPullback sq).toCommSq)).symm)

/-- The compact-support base-change map: proper exchange followed by inverse open
exchange, with the latter inverse specified by an `IsIso` proof, never chosen freely.
Source: blueprint sk-prop-int-brown-construction, last paragraph
(blueprint: det-prop-int-brown-construction). -/
def baseChange {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (c : Compactification f) (sq : IsPullback u' f' f v)
    (h : IsIso (openExchange Λ (c.isPullback_i_ofIsPullback sq).toCommSq)) :
    image Λ c ⋙ pull Λ v ⟶ pull Λ u' ⋙ image Λ (c.ofIsPullback sq) :=
  (baseChangeData Λ c sq h).map

/-- Componentwise invertibility of the compact-support exchange composite.
Proof: the proper exchange component is invertible by hypothesis; functors preserve
isomorphisms, so the proper image of the inverse open exchange is invertible too.
Their composite is the specified base-change component.
Source: blueprint sk-prop-int-brown-construction, final base-change composite
(blueprint: def-sfb-integral-compact-support-interface). -/
theorem baseChangeIsIsoOfProper
    {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (c : Compactification f) (sq : IsPullback u' f' f v)
    (ho : IsIso (openExchange Λ (c.isPullback_i_ofIsPullback sq).toCommSq))
    (K : Ambient Λ X)
    (hp : IsIso ((pushExchange Λ
      (c.isPullback_g_ofIsPullback sq).flip.toCommSq).app ((extend Λ c.i).obj K))) :
    IsIso ((baseChange Λ c sq ho).app K) := by
  exact (baseChangeData Λ c sq ho).isIso K hp

```

The concrete coefficient statement also needed a named cache of the canonical ring
multiplication. Without that cache, the profiler showed repeated expansion of E's
valuation ring, sheafification and the induced module categories even while elaborating
the unchanged statement. These two new declarations construct no new data: the first
names the existing canonical instance, and the second proves its commutativity by
unfolding the name. They are registered only locally in the item module. The four
functor abbreviations (`pull`, `push`, `extend`, `image`) are unchanged.

```lean
-- This class-valued definition is intentionally semireducible: it caches the data.
set_option warn.classDefReducibility false in
/-- A named copy of the canonical coefficient-ring multiplication.

Keeping this instance named prevents repeated expansion of the valuation ring and
its sheafification when checking derived comparison components.
Source: the canonical condensed ring of integers of E
(blueprint: def-sfb-integral-compact-support-interface). -/
def integralCoefficientMonObj (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    MonObj (Profinite.padicIntegersRingObj.{u} ℓ E.val) := inferInstance

set_option warn.classDefReducibility false in
attribute [local instance 6000] integralCoefficientMonObj

/-- The cached coefficient multiplication is the usual commutative multiplication.
Source: the canonical condensed ring of integers of E
(blueprint: def-sfb-integral-compact-support-interface). -/
theorem integralCoefficientIsComm (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    IsCommMonObj (Profinite.padicIntegersRingObj.{u} ℓ E.val) := by
  unfold integralCoefficientMonObj
  infer_instance

```

## Users

`tools/downstream.py Sheaf.SixFunctors.IntegralCompactSupportDefs --uses
AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.baseChange` reports 298
transitive downstream modules and the four textual users below. The two Paper modules
use unrelated scalar `baseChange` declarations, as their actual source contexts show.
The five other direct importers are also listed. No companion source adaptation is needed.
Their statements keep the same functors and exchange map, so none is weakened or strengthened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.IntegralCompactSupportDefs | unclaimed | Same map, new component API; repaired definition. |
| Sheaf.SixFunctors.IntegralCartesianCompactSupport | N3 | Proof uses the component API. Existing signature unchanged. |
| Sheaf.Paper.TensorHomCoefficientTransposes | P3 | Unrelated `LinearEquiv.baseChange`; no effect or edit. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Unrelated `LinearMap.baseChange`; no effect or edit. |
| Sheaf.SixFunctors.IntegralCompactSupportPreservation | unclaimed | Direct importer; no edit or statement change. |
| Sheaf.SixFunctors.IntegralCompactSupportPullback | unclaimed | Direct importer; no edit or statement change. |
| Sheaf.SixFunctors.IntegralCompatibleComposition | unclaimed | Direct importer; no edit or statement change. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Direct importer; no edit or statement change. |
| Sheaf.SixFunctors.IntegralNormalizedComparisons | M6 | Direct importer; no edit or statement change. |

An earlier check of the exchange-data repair compiled all five companion importers
without adaptations. In the final check with the canonical coefficient caches, the
repaired definition module, new boundary-exchange module and unchanged preservation
consumer compiled. Recompiling the unchanged pullback consumer then failed because the
library object for `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal`
was unavailable; this prevented the remaining consumer checks. The full main proof
compiled separately in 30.8 seconds. See report.md for the validation limits.
No consumer source is adapted. The interface node retains every existing attachment
and adds the two proved API declarations and two canonical coefficient-cache declarations.

## Status

landed 20261026T023617-L-586756 2026-10-26 (merge of deliver/N3/Sheaf.SixFunctors.IntegralCartesianCompactSupport)
