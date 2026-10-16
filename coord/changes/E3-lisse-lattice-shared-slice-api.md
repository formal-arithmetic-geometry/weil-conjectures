# Reuse of the concrete pro-etale slice API

## Reason

The broader version of the landing duplicate-statement check found that both new lattice
transport modules copied the slice-site lemmas from the unclaimed existing localization
module. Expose its seven existing concrete declarations, then privately import and reuse them
from both transport modules. Their bodies and types are retained verbatim; only visibility
and documentation are added. No other group's module is edited, and no target or existing
public statement changes. The concrete functors continue to use the same schemes and arrows,
so the displayed coefficient identifications remain definitionally the identity.

## Old

In `lean/Sheaf/AlgebraicGeometry/ProEtaleWeaklyEtaleLocalization.lean`:

```lean
private theorem weaklyEtale_slice (X : Scheme.{u}) (W : X.ProEt) (T : Over W) :
    WeaklyEtale T.hom.left := by
  have hcomp : T.hom.left ≫ W.hom = T.left.hom := by simp
  have : WeaklyEtale (T.hom.left ≫ W.hom) := hcomp ▸ inferInstance
  exact WeaklyEtale.of_comp T.hom.left W.hom

private def sliceTo (X : Scheme.{u}) (W : X.ProEt) : Over W ⥤ W.left.ProEt where
  obj T := by
    have := weaklyEtale_slice X W T
    exact ProEt.mk T.hom.left
  map f := MorphismProperty.Over.homMk f.left.left (by
    have h := congrArg (fun f ↦ f.left) (Over.w f)
    exact h)

private def sliceFrom (X : Scheme.{u}) (W : X.ProEt) : W.left.ProEt ⥤ Over W where
  obj V := Over.mk (Y := ProEt.mk (V.hom ≫ W.hom))
    (MorphismProperty.Over.homMk V.hom rfl)
  map {V V'} f := Over.homMk (MorphismProperty.Over.homMk f.left (by
    change f.left ≫ (V'.hom ≫ W.hom) = V.hom ≫ W.hom
    simpa only [Category.assoc] using congrArg (fun g ↦ g ≫ W.hom)
      (MorphismProperty.Over.w f))) (by
        apply MorphismProperty.Over.Hom.ext
        exact MorphismProperty.Over.w f)

private def sliceEquiv (X : Scheme.{u}) (W : X.ProEt) : Over W ≌ W.left.ProEt where
  functor := sliceTo X W
  inverse := sliceFrom X W
  unitIso := NatIso.ofComponents (fun T ↦ Over.isoMk
    (MorphismProperty.Over.isoMk (Iso.refl _) (by simp [sliceTo, sliceFrom])) (by
      apply MorphismProperty.Over.Hom.ext
      change 𝟙 _ ≫ T.hom.left = T.hom.left
      exact Category.id_comp _))
  counitIso := NatIso.ofComponents (fun V ↦
    MorphismProperty.Over.isoMk (Iso.refl _) (by simp [sliceTo, sliceFrom]))

private theorem sliceFrom_cover (X : Scheme.{u}) (W : X.ProEt) :
    CoverPreserving (topology W.left) ((topology X).over W) (sliceFrom X W) where
  cover_preserve {V S} hS := by
    rw [GrothendieckTopology.mem_over_iff]
    change (S.functorPushforward (sliceFrom X W)).functorPushforward (Over.forget W) ∈ _
    rw [← Sieve.functorPushforward_comp]
    exact (coverPreserving_overMap (inferInstance : WeaklyEtale W.hom)).cover_preserve hS

private theorem sliceFrom_cocont (X : Scheme.{u}) (W : X.ProEt) :
    (sliceFrom X W).IsCocontinuous (topology W.left) ((topology X).over W) where
  cover_lift {V S} hS := by
    rw [GrothendieckTopology.mem_over_iff, mem_topology_iff] at hS
    obtain ⟨R, hR, hle⟩ := hS
    obtain ⟨ι, Z, φ, rfl⟩ := R.exists_eq_ofArrows
    let Z' (i : ι) : W.left.ProEt :=
      MorphismProperty.Over.mk ⊤ ((φ i).left ≫ V.hom)
        (weaklyEtale_left_comp (inferInstance : WeaklyEtale W.hom) (φ i))
    let φ' (i : ι) : Z' i ⟶ V := MorphismProperty.Over.homMk (φ i).left rfl
    apply mem_topology_iff.mpr
    refine ⟨Presieve.ofArrows Z' φ', ?_, ?_⟩
    · rw [mem_precoverage_iff] at hR ⊢
      rw [Presieve.map_ofArrows] at hR ⊢
      exact hR
    · rintro T _ ⟨i⟩
      have hY : 𝟙 (Z i).left ≫ (Z i).hom = ((φ i).left ≫ V.hom) ≫ W.hom := by
        simp only [Category.id_comp, Category.assoc]
        exact (MorphismProperty.Over.w (φ i)).symm
      let a : (sliceFrom X W).obj (Z' i) ⟶
          Over.mk ((φ i) ≫ ((sliceFrom X W).obj V).hom) :=
        Over.homMk (MorphismProperty.Over.homMk (𝟙 (Z i).left) hY) (by
          apply MorphismProperty.Over.Hom.ext
          change 𝟙 _ ≫ ((φ i).left ≫ V.hom) = (φ i).left ≫ V.hom
          exact Category.id_comp _)
      have ha : (sliceFrom X W).map (φ' i) = a ≫ Over.homMk (φ i) := by
        apply Over.OverMorphism.ext
        apply MorphismProperty.Over.Hom.ext
        exact (Category.id_comp _).symm
      change S ((sliceFrom X W).map (φ' i))
      rw [ha]
      exact S.downward_closed ((Sieve.overEquiv_iff _ _).mp (hle _ _ ⟨i⟩)) a

private theorem sliceDense (X : Scheme.{u}) (W : X.ProEt) :
    (sliceEquiv X W).inverse.IsDenseSubsite (topology W.left) ((topology X).over W) where
  functorPushforward_mem_iff {V S} := by
    constructor
    · intro hS
      have := sliceFrom_cocont X W
      have h := (sliceFrom X W).cover_lift (topology W.left) ((topology X).over W) hS
      have : (sliceFrom X W).Full := inferInstanceAs (sliceEquiv X W).inverse.Full
      have : (sliceFrom X W).Faithful := inferInstanceAs (sliceEquiv X W).inverse.Faithful
      change (S.functorPushforward (sliceFrom X W)).functorPullback (sliceFrom X W) ∈ _ at h
      simpa only [Sieve.functorPullback_functorPushforward_eq] using h
    · exact (sliceFrom_cover X W).cover_preserve
```

The two new lattice-transport modules contained private copies of these constructions.

## New

In the same existing module:

```lean
/-- A morphism in a pro-etale slice is weakly etale by cancellation.
Source: Stacks Project, Tags 094T, 0951 and 00XZ.
(blueprint: lem-weil-proetale-weakly-etale-localization) -/
theorem weaklyEtale_slice (X : Scheme.{u}) (W : X.ProEt) (T : Over W) :
    WeaklyEtale T.hom.left := by
  have hcomp : T.hom.left ≫ W.hom = T.left.hom := by simp
  have : WeaklyEtale (T.hom.left ≫ W.hom) := hcomp ▸ inferInstance
  exact WeaklyEtale.of_comp T.hom.left W.hom

/-- The functor from the slice at W to the small pro-etale site of its scheme.
Source: Stacks Project, Tags 094T, 0951 and 00XZ.
(blueprint: lem-weil-proetale-weakly-etale-localization) -/
def sliceTo (X : Scheme.{u}) (W : X.ProEt) : Over W ⥤ W.left.ProEt where
  obj T := by
    have := weaklyEtale_slice X W T
    exact ProEt.mk T.hom.left
  map f := MorphismProperty.Over.homMk f.left.left (by
    have h := congrArg (fun f ↦ f.left) (Over.w f)
    exact h)

/-- The functor to the slice defined by composition with W.hom.
Source: Stacks Project, Tags 094T, 0951 and 00XZ.
(blueprint: lem-weil-proetale-weakly-etale-localization) -/
def sliceFrom (X : Scheme.{u}) (W : X.ProEt) : W.left.ProEt ⥤ Over W where
  obj V := Over.mk (Y := ProEt.mk (V.hom ≫ W.hom))
    (MorphismProperty.Over.homMk V.hom rfl)
  map {V V'} f := Over.homMk (MorphismProperty.Over.homMk f.left (by
    change f.left ≫ (V'.hom ≫ W.hom) = V.hom ≫ W.hom
    simpa only [Category.assoc] using congrArg (fun g ↦ g ≫ W.hom)
      (MorphismProperty.Over.w f))) (by
        apply MorphismProperty.Over.Hom.ext
        exact MorphismProperty.Over.w f)

/-- The concrete equivalence from the slice to the small pro-etale site.
Source: Stacks Project, Tags 094T, 0951 and 00XZ.
(blueprint: lem-weil-proetale-weakly-etale-localization) -/
def sliceEquiv (X : Scheme.{u}) (W : X.ProEt) : Over W ≌ W.left.ProEt where
  functor := sliceTo X W
  inverse := sliceFrom X W
  unitIso := NatIso.ofComponents (fun T ↦ Over.isoMk
    (MorphismProperty.Over.isoMk (Iso.refl _) (by simp [sliceTo, sliceFrom])) (by
      apply MorphismProperty.Over.Hom.ext
      change 𝟙 _ ≫ T.hom.left = T.hom.left
      exact Category.id_comp _))
  counitIso := NatIso.ofComponents (fun V ↦
    MorphismProperty.Over.isoMk (Iso.refl _) (by simp [sliceTo, sliceFrom]))

/-- Composition into the slice preserves the pro-etale coverings.
Source: Stacks Project, Tags 094T, 0951 and 00XZ.
(blueprint: lem-weil-proetale-weakly-etale-localization) -/
theorem sliceFrom_cover (X : Scheme.{u}) (W : X.ProEt) :
    CoverPreserving (topology W.left) ((topology X).over W) (sliceFrom X W) where
  cover_preserve {V S} hS := by
    rw [GrothendieckTopology.mem_over_iff]
    change (S.functorPushforward (sliceFrom X W)).functorPushforward (Over.forget W) ∈ _
    rw [← Sieve.functorPushforward_comp]
    exact (coverPreserving_overMap (inferInstance : WeaklyEtale W.hom)).cover_preserve hS

/-- Composition into the slice is cocontinuous for the pro-etale topologies.
Source: Stacks Project, Tags 094T, 0951 and 00XZ.
(blueprint: lem-weil-proetale-weakly-etale-localization) -/
theorem sliceFrom_cocont (X : Scheme.{u}) (W : X.ProEt) :
    (sliceFrom X W).IsCocontinuous (topology W.left) ((topology X).over W) where
  cover_lift {V S} hS := by
    rw [GrothendieckTopology.mem_over_iff, mem_topology_iff] at hS
    obtain ⟨R, hR, hle⟩ := hS
    obtain ⟨ι, Z, φ, rfl⟩ := R.exists_eq_ofArrows
    let Z' (i : ι) : W.left.ProEt :=
      MorphismProperty.Over.mk ⊤ ((φ i).left ≫ V.hom)
        (weaklyEtale_left_comp (inferInstance : WeaklyEtale W.hom) (φ i))
    let φ' (i : ι) : Z' i ⟶ V := MorphismProperty.Over.homMk (φ i).left rfl
    apply mem_topology_iff.mpr
    refine ⟨Presieve.ofArrows Z' φ', ?_, ?_⟩
    · rw [mem_precoverage_iff] at hR ⊢
      rw [Presieve.map_ofArrows] at hR ⊢
      exact hR
    · rintro T _ ⟨i⟩
      have hY : 𝟙 (Z i).left ≫ (Z i).hom = ((φ i).left ≫ V.hom) ≫ W.hom := by
        simp only [Category.id_comp, Category.assoc]
        exact (MorphismProperty.Over.w (φ i)).symm
      let a : (sliceFrom X W).obj (Z' i) ⟶
          Over.mk ((φ i) ≫ ((sliceFrom X W).obj V).hom) :=
        Over.homMk (MorphismProperty.Over.homMk (𝟙 (Z i).left) hY) (by
          apply MorphismProperty.Over.Hom.ext
          change 𝟙 _ ≫ ((φ i).left ≫ V.hom) = (φ i).left ≫ V.hom
          exact Category.id_comp _)
      have ha : (sliceFrom X W).map (φ' i) = a ≫ Over.homMk (φ i) := by
        apply Over.OverMorphism.ext
        apply MorphismProperty.Over.Hom.ext
        exact (Category.id_comp _).symm
      change S ((sliceFrom X W).map (φ' i))
      rw [ha]
      exact S.downward_closed ((Sieve.overEquiv_iff _ _).mp (hle _ _ ⟨i⟩)) a

/-- The inverse slice equivalence is a dense subsite for the pro-etale topologies.
Source: Stacks Project, Tags 094T, 0951 and 00XZ.
(blueprint: lem-weil-proetale-weakly-etale-localization) -/
theorem sliceDense (X : Scheme.{u}) (W : X.ProEt) :
    (sliceEquiv X W).inverse.IsDenseSubsite (topology W.left) ((topology X).over W) where
  functorPushforward_mem_iff {V S} := by
    constructor
    · intro hS
      have := sliceFrom_cocont X W
      have h := (sliceFrom X W).cover_lift (topology W.left) ((topology X).over W) hS
      have : (sliceFrom X W).Full := inferInstanceAs (sliceEquiv X W).inverse.Full
      have : (sliceFrom X W).Faithful := inferInstanceAs (sliceEquiv X W).inverse.Faithful
      change (S.functorPushforward (sliceFrom X W)).functorPullback (sliceFrom X W) ∈ _ at h
      simpa only [Sieve.functorPullback_functorPushforward_eq] using h
    · exact (sliceFrom_cover X W).cover_preserve
```

Both lattice-transport modules remove these copies and use the exposed declarations through
`open Scheme.ProEt`. The imports are proof-only. The existing localization node gains only
`lean.declarations`; both transport nodes record localization as a proof dependency.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization --uses
weaklyEtale_slice sliceTo sliceFrom sliceEquiv sliceFrom_cover sliceFrom_cocont sliceDense`
listed these 31 downstream modules. The sole downstream textual helper-name hit is the
ringed-open comparison's own private slice helpers, so it does not need an adaptation.
The localization module is unclaimed when this record is written.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization` | unclaimed | Expose existing concrete slice API; all proof and definition bodies retained. |
| `Sheaf.AlgebraicGeometry.NoetherianStratumDetection` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleExtensionByZero` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleExtensionByZeroAdjunction` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. Textual helper-name hits refer to its own private helpers. |
| `Sheaf.Paper.CondensedCoefficientComparisons` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.Paper.CondensedLfpCoefficientModel` | A4 | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.Paper.CondensedQbarComparisons` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | A3 | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.Paper.CondensedStratumModelAssembly` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.Paper.CondensedStratumModelInductionStep` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.Paper.CondensedStratumModelInductionStepNonempty` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing` | G1 | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCtfTriangulated` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.Paper.FiniteRingConstructibleSheafOrigin` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.Paper.FiniteTensorConstructibleCohomology` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.Paper.FiniteTorsionConstructibility` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.Paper.ProEtaleLisseOrigin` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.Paper.ProEtaleResidueTorTest` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `TargetsCheck` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | unclaimed | Existing signature, definitions and proof unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.LisseLatticePresentationTransport` | E3 (new) | Removes copied slice API; imports and uses the existing API. |
| `Sheaf.AlgebraicGeometry.LisseLatticeSliceTransport` | E3 (new) | Removes copied slice API; imports and uses the existing API. |

## Status

landed 20261016T070240-L-770593 2026-10-16 (merge of deliver/E3/Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal)
