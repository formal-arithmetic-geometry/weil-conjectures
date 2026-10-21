# AlgebraicGeometry.exists_affineBaseChangeIntoPullback_representativeIso

## Reason

The assigned rework row preserves this module in quarantine following a failed
cluster restore. Its archived implementation already has zero holes, but it
locally redeclares the theorem that is also proved in the adopted source module.
Restoring the archived body would retain two declaration providers, which cannot
be imported into one environment. Restore the historical path as a public
re-export of the canonical proved implementation instead. Retain the public
KFlat import for consumers of the historical predicate spelling.

This is an environment/interface repair, not a claim to close a proof hole.
The adopted source library is unchanged, and the quarantine archive is preserved.

## Old

The archived module has these imports:

```lean
public import WeilConjectures.Algebra.Homology.AffineBaseChangeIntoPullback
import Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality
```

It locally declares a proved private localization helper and the following proved
public theorem:

```lean
theorem exists_affineBaseChangeIntoPullback_representativeIso
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (K : schemeDerivedCategory X)
    (P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsAcyclicTensorKFlat) (hQ : Q.IsAcyclicTensorKFlat)
    (eP : DerivedCategory.Q.obj P ≅ K) (eQ : DerivedCategory.Q.obj Q ≅ K)
    (hcP : IsIso ((SingleComplexBaseChange.counit g').app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (hcQ : IsIso ((SingleComplexBaseChange.counit g').app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj Q))) (p : X') (i : ℤ) :
    ∃ t : (Arrow.mk (affineBaseChangeIntoPullback f f' g g' sq K Q eQ hcQ p i)).left ≃+
        (Arrow.mk (affineBaseChangeIntoPullback f f' g g' sq K P eP hcP p i)).left,
      ∀ x, affineBaseChangeIntoPullback f f' g g' sq K Q eQ hcQ p i x =
        affineBaseChangeIntoPullback f f' g g' sq K P eP hcP p i (t x)
```

Its private helper descends the composite exact-stalk homology isomorphism along
DerivedCategory.Q using Localization.liftNatIso. The public proof constructs source
transport, uses pullback naturality, and conjugates by that isomorphism.

## New

```lean
public import WeilConjectures.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso
public import Sheaf.Algebra.Homology.KFlat
```

The historical module re-exports the existing declaration rather than declaring it
a second time. The canonical theorem has exactly the old signature displayed
above with `P.IsKFlatTensor` and `Q.IsKFlatTensor` in place of
`P.IsAcyclicTensorKFlat` and `Q.IsAcyclicTensorKFlat`. Both predicate definitions
quantify over the same acyclic complexes F and assert acyclicity of the same
`mapBifunctor F K (curriedTensor _)`, using the same sheaf-module monoidal
structure. This is definitional equality. The canonical proof is the archived
proof with the same private helper, source transport, counit square and final
additive equivalence. No hypothesis, universe, degree or comparison map changes.

The node's Lean attachment points to the canonical provider. Its mathematical
statement, statement dependencies, proof steps, proof dependencies and unit route
are preserved. No target statement or definition changes. Empty schemes and zero
complexes are unaffected; every integer degree and arbitrary schemes remain allowed.

Validation: the restored module compiles in 2.2 seconds. A separate probe imports
both historical and canonical module paths and the canonical source-model
consumer. It repeats the full archived theorem signature, proves it by applying
the canonical theorem with every argument unchanged, and proves the two K-flat
predicates equal by rfl. The probe compiles in 4.6 seconds. Both the canonical
theorem and the old-signature probe print exactly propext, Classical.choice and
Quot.sound as axioms. Probes live only in the sandbox scratchpad.

## Users

The source-only downstream query with --allow-missing finds no live importers of
the missing historical module. Searching the quarantine finds the one archived
consumer listed below. Its original call has the exact signature checked by the
compatibility probe. The canonical source consumer is already on the adopted
module path and continues using the same declaration. No user needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso | V8 | Restore as canonical public re-export; preserve old K-flat spelling. |
| Sheaf.Algebra.Homology.AffineBaseChangeSourceModel | quarantined; unclaimed | Same declaration and definitionally equal hypotheses; no adaptation. |
| WeilConjectures.Algebra.Homology.AffineBaseChangeSourceModel | unchanged source library | Same canonical declaration; no adaptation. |

## Status

landed 20261021T172406-L-3366097 2026-10-21 (merge of deliver/V8/Sheaf.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso)
