# CategoryTheory.principalKoszul

## Reason

The cone and its component lemmas repeatedly reconstructed the same preferred single
functor map, including its shift-coherence record. Give that actual map a shared name.
The underlying map, all existing signatures and imports, the cone, transitions and
augmentations are definitionally unchanged. Cache the existing sheaf-composition
proof to avoid repeated instance search. No adopted-source declaration is changed.
The target statements are untouched; the definition review is reopened for this
presentation change. The source module is unclaimed.

## Old

```lean
noncomputable def principalKoszul
    (t : (SheafOfModules.unit 𝓞).sections) (m : ℕ) :
    CochainComplex (𝒜) ℤ :=
  CochainComplex.mappingCone
    ((CochainComplex.singleFunctor (𝒜) 0).map
      (endoPow (globalSectionMultiplication R t) (m + 1)))
```

## New

```lean
noncomputable def principalKoszulScalarComplex
    (t : (SheafOfModules.unit 𝓞).sections) (m : ℕ) :=
  (CochainComplex.singleFunctor (𝒜) 0).map
    (endoPow (globalSectionMultiplication R t) (m + 1))

noncomputable def principalKoszul
    (t : (SheafOfModules.unit 𝓞).sections) (m : ℕ) :
    CochainComplex (𝒜) ℤ :=
  CochainComplex.mappingCone (principalKoszulScalarComplex R t m)
```

The added, proved `principalKoszulHasSheafCompose` names the instance already used
by these definitions; it is installed only locally in this module. The proof of
`koszulRepresentativeAugmentation_naturality` additionally unfolds
`principalKoszulScalarComplex` before its existing cone-map simplification.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers --uses
principalKoszul principalKoszulTransition` gives the following union of textual
users. The four new comparison modules also use the shared parameter.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Algebra.Homology.KoszulRoosComparisonData` | unclaimed | Unchanged; final original code compiled in 58.2 s. |
| `Sheaf.Algebra.Homology.KoszulRoosProjectionComparison` | unclaimed | Add the shared parameter to two existing unfolding lists; Compiled in 46.2 s. |
| `Sheaf.Algebra.Homology.NilpotentKoszulCoordinates` | unclaimed | Unchanged. Compiled in 19.7 s. |
| `Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers` | unclaimed | Shared scalar map and local instance cache; compiled in 0.1 s. |
| `Sheaf.Algebra.Homology.RegularScalarQuotientExactRow` | unclaimed | Unchanged. Compiled in 13.2 s. |
| `Sheaf.Algebra.Homology.RegularScalarQuotientNotation` | unclaimed | Unchanged. Compiled in 9.2 s. |
| `Sheaf.Algebra.Homology.SignedDoubleRoosTensorExchange` | unclaimed | Unchanged. Compiled in 25.8 s. |
| `Sheaf.Algebra.Homology.SignedDoubleRoosTensorExchangeTensor` | unclaimed | Unchanged. Compiled in 11.1 s. |
| `Sheaf.Paper.EllCoefficientFiber` | unclaimed | Unchanged. Compiled in 32.2 s. |
| `Sheaf.Paper.NormalizedErrorTowerData` | unclaimed | Unchanged. Compiled in 33.1 s. |
| `Sheaf.Paper.NormalizedStrictTensorFiber` | unclaimed | Unchanged; compiled in 21.8 s. |
| `Sheaf.Paper.PrincipalConeKoszulRoosComparison` | unclaimed | Share the scalar in private cone comparisons, specify derived universes and cache limit proofs; clean check 58.1 s. |
| `Sheaf.Paper.PrincipalKoszulStrictReplacement` | unclaimed | Cache the sheaf instance; generic augmentation proof and explicit inference arguments; clean check 2.1 s. |
| `Sheaf.Paper.RoosIntrinsicUnitComparison` | unclaimed | Original proof retained; baseline already exceeds the limit (118.7 s), mathematically valid with the changed definitions too. |
| `Sheaf.SixFunctors.RegularRoosKoszulUnit` | unclaimed | Cache the existing instance and use the shared scalar in the augmentation proof; clean check 0.7 s. |

The unclaimed strict-replacement consumer also installs the named sheaf-composition
proof locally, refers to the shared map in its private flatness calculation, and
uses a proved private arbitrary-ring augmentation lemma before specializing to
the completed coefficient ring. Its final proofs explicitly unfold tower wrappers
to avoid costly definitional equality searches. Public signatures are unchanged.

The regular-Roos consumer originally exceeded 60 seconds (70 seconds). Its
private augmentation-naturality proof now instantiates the cone inclusion with
`principalKoszulScalarComplex` rather than reconstructing the same single map.
Its local instance cache avoids the repeated sheaf-composition search.

The principal-cone consumer shares the scalar parameter in its private finite
cone isomorphisms and uses functorial congruence for the transition square. It
fixes the universes of both generic comparison applications, respects the local
irreducibility boundaries in its public proof, and caches the existing countable
product and small discrete colimit proofs. Its original clean check took 65 s;
the initial clean check passed in 58.1 s, but the delivery compile exceeded the
limit under load. The scalar conjugacy equation now uses the shared scalar parameter
too, and the final generic application supplies its category and site instances
explicitly. Elaboration is serialized with Elab.async false; kernel checking and
the public signature are unchanged. Local opacity for globalSectionMultiplication
and respectTransparency.types true avoid expanding the concrete scalar during
conjugacy checks. The final profiled check passed in 55.8 s; profiling options
are removed from the delivery.


The original `RoosIntrinsicUnitComparison` compiled mathematically against the
published library but exceeded 60 seconds (118.7 s; result
`3eb30bd7192803b74c7020e3`). A small cache plus the same original construction
remained mathematically valid against this refactor (99.7 s,
`dbc3486f37efd2951547de9f`). No Roos statement, definition or proof is delivered;
this pre-existing performance issue is outside the singleton comparison repair.

## Status

landed 20261026T092722-L-3459472 2026-10-26 (merge of deliver/T9/Sheaf.Paper.PrincipalKoszulDualTowerComparison)
