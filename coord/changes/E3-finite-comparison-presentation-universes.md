# AlgebraicGeometry.ProEtale.finiteComparisonPresentation

## Reason

Restore the quarantined, complete presentation proof and repair ambiguous site
size inference. `WeilConjectures.scalarReductionSiteSmall` uses a maximum with an
unconstrained universe. Supply a private local canonical coefficient-size
instance and explicitly specialize the private pro-etale helper's size universe. Keep the existing integral-operations import:
import-all consumers refer to its instance names in their proof exclusion lists.
No shared definition or target statement changes.

The restored proof typechecked but took approximately 82 seconds. Command-level
checkpoints located cost in general section-monoidal and constant-model helpers
and the later realization isomorphisms. Attempts to seal large private
constructions did not improve the time. The completed general helper proofs are
therefore separated into a support module, with no mathematical obligation or
hole added. Five private entry points used by existing import-all consumers stay
in the item with identical signatures.

## Old

The private pro-etale monoidal construction was:

```lean
private local instance proSites_monoidal (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (proSites X A).functor.Monoidal := by
  let G : Scheme.coefficientProEtaleSiteModel.{u, u + 1} X ⥤ X.ProEt := AsSmall.down
  letI : G.IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).isEquivalence_inverse
  let J := Scheme.coefficientProEtaleModelTopology.{u, u + 1} X
  let K := (Scheme.ProEt.topology X)
  let L := Functor.sheafPullbackConstruction.sheafPullback G (ModuleCat.{u + 1} A) J K
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G
    (ModuleCat.{u + 1} A) J K
  letI : L.Monoidal :=
    Functor.sheafPullbackConstruction.sheafPullbackMonoidal G (ModuleCat.{u + 1} A) J K
  exact monoidalOfAdjointEquivalence (proSites X A) L adj
```

The two scoped exclusion lists contained seven integral-operations and completed
coefficient instances, but did not exclude `scalarReductionSiteSmall`. Complete
general helper proofs preceded `namespace AlgebraicGeometry.ProEtale` in this
file. Two file-local settings disabled transparency checking.

## New

```lean
private local instance proSites_monoidal (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (proSites X A).functor.Monoidal := by
  let G : Scheme.coefficientProEtaleSiteModel.{u, u + 1} X ⥤ X.ProEt := AsSmall.down
  letI : G.IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).isEquivalence_inverse
  let J := Scheme.coefficientProEtaleModelTopology.{u, u + 1} X
  let K := (Scheme.ProEt.topology X)
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  let L := Functor.sheafPullbackConstruction.sheafPullback G (ModuleCat.{u + 1} A) J K
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G
    (ModuleCat.{u + 1} A) J K
  letI : L.Monoidal :=
    Functor.sheafPullbackConstruction.sheafPullbackMonoidal G (ModuleCat.{u + 1} A) J K
  exact monoidalOfAdjointEquivalence (proSites X A) L adj
```

The following private local instance supplies the fixed coefficient universe
without changing registration of imported instances:

```lean
private local instance (priority := 2000) presentationSiteSmall
    (X : AlgebraicGeometry.Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0} _
```

It is active in the private proof section and enabled explicitly through the
existing `attribute [local instance] ... in` wrapper of the public theorem.
The original seven exclusions and integral-operations import remain. The two
transparency overrides are removed.

The completed general helper proofs are in
`Sheaf.Paper.FiniteComparisonPresentationSupport` inside
`FiniteComparisonPresentationSupport`; the section-monoidal existence theorem is
public and proved with its own node, and the other helpers are private. The item
imports them with `import all`. The original bodies of `localFinite` and
`finiteModelSieve` remain in the item. The three theorem entry points
`sectionMonoidal_exists`, `localFinite_iso`, and `localFinite_iff_sieve` keep their
signatures and apply the moved proofs. The coefficient realization monoidal
instance remains in the item, where its existing realization dependency is used.
The public theorem, public imports, statement, and node's Lean attachment and
original dependencies remain unchanged. The extracted proved existence lemma is
added as a dependency. File-local `Elab.async false` keeps elaboration scheduling
predictable. No other existing module is changed.

## Users

The delivery tool checks current server claims. These are the four direct
consumers, including the preserved quarantine sources.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteComparisonPresentation | E3 | Assigned restoration and private proof repair. |
| Sheaf.Paper.FiniteComparisonLocalizing | unclaimed in shared snapshot | Signatures, private entry points and imported instance names retained. |
| Sheaf.AlgebraicGeometry.DiscreteCoefficientModel | unclaimed in shared snapshot | Signatures, private entry points and imported instance names retained. |
| Sheaf.AlgebraicGeometry.FixedScalarEtaleConstructibleSheaf | unclaimed in shared snapshot | Signatures, private entry points and imported instance names retained. |
| Sheaf.Paper.EmbeddedFiniteHeartMonoidalPresentation | unclaimed in shared snapshot | Signatures, private entry points and imported instance names retained. |

The final item, support module, and all four original direct consumers compile
without warnings under the normal file limits. All consumer sources are unchanged
and their temporary checking copies are not part of this delivery. The public
theorem statement and the three public imports match the archive verbatim.

## Status

landed 20261026T152357-L-1102031 2026-10-26 (merge of deliver/E3/Sheaf.Paper.FiniteComparisonPresentation)
