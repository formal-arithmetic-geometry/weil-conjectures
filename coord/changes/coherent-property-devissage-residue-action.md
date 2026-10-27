# AlgebraicGeometry.coherent_property_devissage

## Reason

Match Stacks Tag 01YI, coherent.tex lines 3270–3304. The old Lean required a
witness at every point of an integral closed subscheme, whereas the source uses
only its generic point. It also allowed an arbitrary residue-field Module
structure independent of the original stalk-ring action. Such a structure does
not express the dimension of the quotient action meant in the source. The
irreducible-support lemma already requires the correct compatibility equation.
For a diagnostic counterexample to the old unrelated-action condition, on
Spec Q(t) take P to mean even canonical dimension. The additive groups of Q(t)
and Q(t)^2 are isomorphic, so transporting the action makes the latter
one-dimensional for an unrelated action while its canonical dimension stays two.
This gives the old witness but does not force P for the canonical rank-one module.
Add genericity and require the compatibility equation. The conclusion, zero hypothesis and
two-out-of-three hypothesis stay unchanged. No target statement or definition
changes. This is a repair of a non-target statement, followed by its full proof
from existing dependencies; it adds no holes.

The only direct importer, CurveEulerTensorGenericRank, has a sorry body. Its
source argument supplies the structure module at the generic point or the
pushforward of a closed point's structure module, with their canonical scalar
actions, so the repaired criterion proves precisely the same consumer statement.
There is no existing application to adapt. All 11 downstream modules were
checked for textual occurrences; none calls the repaired theorem.

## Old

```lean
theorem coherent_property_devissage
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (P : X.Modules → Prop)
    (hP_zero : ∀ F : X.Modules, IsZero F → P F)
    (hP_seq : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      RingedSpace.IsCoherent X.toRingedSpace S.X₁ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₂ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₃ →
      ((P S.X₁ ∧ P S.X₂) ∨ (P S.X₁ ∧ P S.X₃) ∨ (P S.X₂ ∧ P S.X₃)) →
      P S.X₁ ∧ P S.X₂ ∧ P S.X₃)
    (hP_integral : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsIntegral Z]
      [IsClosedImmersion i] (ξ : Z),
      ∃ G : X.Modules,
        RingedSpace.IsCoherent X.toRingedSpace G ∧
        (∀ x : X, (¬ Subsingleton (G.presheaf.stalk x)) ↔
          x ∈ Set.range i.base) ∧
        (∀ (r : X.presheaf.stalk (i.base ξ)),
          r ∈ IsLocalRing.maximalIdeal _ →
            ∀ m : (PresheafOfModules.stalkObj X.ringCatSheaf.presheaf (i.base ξ) G.val),
              r • m = 0) ∧
        (∃ hκ : Module (X.residueField (i.base ξ))
            (PresheafOfModules.stalkObj X.ringCatSheaf.presheaf (i.base ξ) G.val),
          @Module.finrank _ _ _ _ hκ = 1) ∧
        P G)
    : ∀ F : X.Modules, RingedSpace.IsCoherent X.toRingedSpace F → P F
```

## New

```lean
theorem coherent_property_devissage
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (P : X.Modules → Prop)
    (hP_zero : ∀ F : X.Modules, IsZero F → P F)
    (hP_seq : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      RingedSpace.IsCoherent X.toRingedSpace S.X₁ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₂ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₃ →
      ((P S.X₁ ∧ P S.X₂) ∨ (P S.X₁ ∧ P S.X₃) ∨ (P S.X₂ ∧ P S.X₃)) →
      P S.X₁ ∧ P S.X₂ ∧ P S.X₃)
    (hP_integral : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsIntegral Z]
      [IsClosedImmersion i] (ξ : Z) (_hξ : IsGenericPoint ξ Set.univ),
      ∃ G : X.Modules,
        RingedSpace.IsCoherent X.toRingedSpace G ∧
        (∀ x : X, (¬ Subsingleton (G.presheaf.stalk x)) ↔
          x ∈ Set.range i.base) ∧
        (∀ (r : X.presheaf.stalk (i.base ξ)),
          r ∈ IsLocalRing.maximalIdeal _ →
            ∀ m : (PresheafOfModules.stalkObj X.ringCatSheaf.presheaf (i.base ξ) G.val),
              r • m = 0) ∧
        (∃ hκ : Module (X.residueField (i.base ξ))
            (PresheafOfModules.stalkObj X.ringCatSheaf.presheaf (i.base ξ) G.val),
          (∀ (r : X.presheaf.stalk (i.base ξ))
            (m : PresheafOfModules.stalkObj X.ringCatSheaf.presheaf (i.base ξ) G.val),
            r • m = (X.residue (i.base ξ)) r • m) ∧
          @Module.finrank _ _ _ _ hκ = 1) ∧
        P G)
    : ∀ F : X.Modules, RingedSpace.IsCoherent X.toRingedSpace F → P F
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AmpleIffNormalizedComponentDegreePos | unclaimed | Transitive importer; no occurrence of the repaired declaration, unchanged statement and proof. |
| Sheaf.AlgebraicGeometry.CurveDegreeTensorAdditive | unclaimed | Transitive importer; no occurrence of the repaired declaration, unchanged statement and proof. |
| Sheaf.AlgebraicGeometry.CurveEulerTensorGenericRank | unclaimed | Only direct importer; proof is sorry and contains no call; unchanged statement and source proof uses canonical actions at generic points. |
| Sheaf.AlgebraicGeometry.CurveRiemannHurwitzNumerical | unclaimed | Transitive importer; no occurrence of the repaired declaration, unchanged statement and proof. |
| Sheaf.AlgebraicGeometry.DegreeWeightedIrreducibleComponents | unclaimed | Transitive importer; no occurrence of the repaired declaration, unchanged statement and proof. |
| Sheaf.AlgebraicGeometry.ProjectiveCurveIsomGraphs | unclaimed | Transitive importer; no occurrence of the repaired declaration, unchanged statement and proof. |
| Sheaf.AlgebraicGeometry.ProperCurveAutomorphismScheme | T9 | Transitive importer; no occurrence of the repaired declaration, unchanged statement and proof. |
| Sheaf.AlgebraicGeometry.ProperCurveBundlePullbackDegree | unclaimed | Transitive importer; no occurrence of the repaired declaration, unchanged statement and proof. |
| Sheaf.AlgebraicGeometry.ProperIntegralCurveAmpleDegree | unclaimed | Transitive importer; no occurrence of the repaired declaration, unchanged statement and proof. |
| Sheaf.TraceFormula.PointedGenusZeroProjectiveLine | unclaimed | Transitive importer; no occurrence of the repaired declaration, unchanged statement and proof. |
| Sheaf.TraceFormula.ValuationNodalPolarSection | unclaimed | Transitive importer; no occurrence of the repaired declaration, unchanged statement and proof. |

## Status

landed 20261023T123606-L-1218033 2026-10-23 (merge of deliver/J2/Sheaf.AlgebraicGeometry.CoherentPropertyDevissage)
