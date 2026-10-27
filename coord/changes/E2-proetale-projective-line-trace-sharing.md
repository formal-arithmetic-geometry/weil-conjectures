# AlgebraicGeometry.ProEtale.SpP1DiagonalIntegralsAt

## Reason

Restore the quarantined module within the 60-second single-file limit. Profiling the
archived file identifies kernel checking of `SpP1DiagonalIntegralsAt`, its generated
Ext-smallness proofs, and `diagonalIntegralsAt_generic` as the cost. Repeated concrete
projective-line product expressions make the general smallness proofs expensive to check.
Name the product scheme and diagonal as local let-bindings in the definition.
These are explicit constructions; zeta reduction gives the old formula. Ext smallness
proofs are proposition-valued, so their changed elaboration does not change any Ext data.
No hypothesis, class, comparison map, trace, integral condition or public signature changes.

## Old

```lean
def SpP1DiagonalIntegralsAt (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (b : SpP1TwistedFamily A N hA) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) : Prop :=
  ∃ (hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible)
    (κ : Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} A)
        (pullback.diagonal (ProjectiveLine S ↘ S))).obj
          (Etale.ordinaryFiniteConstant A (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2)
    (cΔ : GeoCartierClass A N hA (pullback.diagonal (ProjectiveLine S ↘ S))),
    (Etale.SupportedKummerBoundary A N hA (pullback.diagonal (ProjectiveLine S ↘ S)) hI
      ((map_natCast ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
        (ProjectiveLine S ↘ S)).appTop.hom N) ▸
          hS.map ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom) κ) ∧
    (SpP1CartierCompatibility
      (comparisonUpperStar (ModuleCat.{u + 1} A)
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))
      (geoCartierSourceComparison A (pullback.diagonal (ProjectiveLine S ↘ S))) κ cΔ) ∧
    ∃ hE : PreservesFiniteColimits
        (lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S))),
      DiagonalIntegralCondition
        (@geoP1DiagonalKernelData A inferInstance N hN hA S hS hE cΔ)
        (geoP1Trace A N hA (ProjectiveLine S)
          (b (ProjectiveLine S)
            ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
              hS.map (ProjectiveLine S ↘ S).appTop.hom)))
```

## New

```lean
def SpP1DiagonalIntegralsAt (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (b : SpP1TwistedFamily A N hA) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) : Prop :=
  let W : Scheme.{u} := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)
  let i : ProjectiveLine S ⟶ W := pullback.diagonal (ProjectiveLine S ↘ S)
  ∃ (hI : i.ker.IsInvertible)
    (κ : Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj
        (Etale.ordinaryFiniteConstant A (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine W N A hA) 2)
    (cΔ : GeoCartierClass A N hA i),
    (Etale.SupportedKummerBoundary A N hA i hI
      ((map_natCast ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
        (ProjectiveLine S ↘ S)).appTop.hom N) ▸
          hS.map ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom) κ) ∧
    (SpP1CartierCompatibility
      (comparisonUpperStar (ModuleCat.{u + 1} A) W)
      (geoCartierSourceComparison A i) κ cΔ) ∧
    ∃ hE : PreservesFiniteColimits
        (lowerStar (ModuleCat.{u + 1} A) i),
      DiagonalIntegralCondition
        (@geoP1DiagonalKernelData A inferInstance N hN hA S hS hE cΔ)
        (geoP1Trace A N hA (ProjectiveLine S)
          (b (ProjectiveLine S)
            ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
              hS.map (ProjectiveLine S ↘ S).appTop.hom)))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace | E2 | Restore the module; definitionally identical predicate. All three existing public theorem proofs check against it. |

There are no direct Lean importers in the current `lean/` tree or the quarantine archive,
as checked by import-line search. The DAG parents, including `det-sp-p1-adjunction`,
retain their dependencies and their unit route. No consumer is removed or adapted;
the archived item and all its Lean attachments and dependencies are preserved.
The target statements and their mathematical meaning are unchanged.

## Status

landed 20261026T181624-L-3475364 2026-10-26 (merge of deliver/E2/Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace)
