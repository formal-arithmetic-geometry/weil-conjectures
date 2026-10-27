# finitePerfectAdic_actual_level_objects

## Reason

The actual-level-descent proof needs the comparison isomorphism to the actual
finite quotient, not only an etale object with bounded lisse cohomology. A new
proved retained-origin theorem constructs these data, including the Isom stalk
markings. Its weaker object-existence consequence closes the existing auxiliary
hole instead of duplicating that obligation. The auxiliary module was unclaimed
when checked against the current server claims and queue on 2026-10-28.

## Old

```lean
theorem finitePerfectAdic_actual_level_objects (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶ completedAdicFiniteCommRing X d n) (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ) (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale) (T : FinitePerfectAdicAlgebraTower d) (hperfect : ∀ n : ℕ, DerivedCategory.IsPerfect (T.level n)) (hmark : FinitePerfectAdicLevelMarkings X d φ M V T) : ∃ K : ∀ n : ℕ, DerivedCategory (Sheaf V.left.smallEtaleTopology (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))), (∀ n : ℕ, ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))) i).obj (K n))) ∧ (∀ (n : ℕ) (i : ℤ), IsFiniteLocallyConstantSheaf ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))) i).obj (K n)))
```

The body was `by sorry`; its private proof import was
`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`.

## New

```lean
theorem finitePerfectAdic_actual_level_objects (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶ completedAdicFiniteCommRing X d n) (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ) (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale) (T : FinitePerfectAdicAlgebraTower d) (hperfect : ∀ n : ℕ, DerivedCategory.IsPerfect (T.level n)) (hmark : FinitePerfectAdicLevelMarkings X d φ M V T) : ∃ K : ∀ n : ℕ, DerivedCategory (Sheaf V.left.smallEtaleTopology (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))), (∀ n : ℕ, ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))) i).obj (K n))) ∧ (∀ (n : ℕ) (i : ℤ), IsFiniteLocallyConstantSheaf ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))) i).obj (K n)))
```

The signature, attributes, universe and public imports are identical. The proof
chooses the K_n supplied by `finitePerfectAdic_marked_origin` and forgets the
additional comparison and stalk fields. The sole private proof import is now
`Sheaf.Paper.FinitePerfectAdicMarkedOrigin`.

New public declarations are confined to the two new Sheaf modules:
`finitePerfectAdicQuotientCoordinates` is the actual composite of exact
restriction functors; `finitePerfectAdic_marked_origin` is proved; and
`finitePerfectAdic_descend_coordinate_transitions` is the one named remaining
proof step. No existing definition or target statement changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FinitePerfectAdicActualLevelObjects | unclaimed | Its existing theorem is proved without changing its signature. |
| Sheaf.Paper.FinitePerfectAdicActualLevels | unclaimed in snapshot | Sole direct importer and sole external textual user; its original proof and statement are unchanged and checked against the replacement. |
| Sheaf.Paper.FinitePerfectAdicActualLevelDescent | K3 | Uses the stronger new construction and the remaining transition step; existing signature unchanged. |
| Sheaf.Paper.FinitePerfectAdicMarkedOrigin | new, K3 | Real quotient-coordinate definition and proved object/stalk construction. |
| Sheaf.Paper.FinitePerfectAdicCoordinateTransitions | new, K3 | Arrow descent between supplied actual origins; one named sorry. |

`tools/downstream.py ... --direct --uses finitePerfectAdic_actual_level_objects`
reports exactly the first two modules for textual uses. The auxiliary is not an
adaptation of another group's held work. No forced adaptations are needed.

## Status

landed 20261027T234033-L-4168553 2026-10-27 (merge of deliver/K3/Sheaf.Paper.FinitePerfectAdicActualLevelDescent)
