# AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek

## Reason

Repair the returned landing conflict using the current source. Prove the general
reduction theorem from existing library declarations and avoid expansion of concrete
derived-functor implementations. The static preflight conservatively flags local
attribute commands; this record documents their scope.

## Old

The current namespace begins:

```lean
namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
```

The current general reduction theorem is:

```lean
theorem nonempty_iso_reductionModIdeal_rightDerivedLowerShriek (J : Ideal Λ) :
    Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ⋙ reductionModIdeal Λ Y J ≅
      reductionModIdeal Λ X J ⋙ R(f)_![ModuleCat.{u + 1} Λ]) :=
  sorry
```

## New

The namespace-local command controls elaboration only inside this file:

```lean
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
```

The following command disables two search registrations for the general theorem
alone. It does not remove their exported instance attributes:

```lean
attribute [-instance]
  CompactificationUpperShriek.isLeftAdjoint_rightDerivedLowerStar_of_isProper
  CompactificationUpperShriek.isLeftAdjoint_rightDerivedLowerShriek in
```

The complete general reduction proof is:

```lean
theorem nonempty_iso_reductionModIdeal_rightDerivedLowerShriek (J : Ideal Λ) :
    Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ⋙ reductionModIdeal Λ Y J ≅
      reductionModIdeal Λ X J ⋙ R(f)_![ModuleCat.{u + 1} Λ]) := by
  let c := HasCompactification.compactification f
  have : (R((c.g)_*[ModuleCat.{u + 1} Λ])).IsLeftAdjoint :=
    CompactificationUpperShriek.isLeftAdjoint_rightDerivedLowerStar_of_isProper
      (ModuleCat.{u + 1} Λ) c.g
  have (I : Type (u + 1)) :
      PreservesColimitsOfShape (Discrete I) (R((c.g)_*[ModuleCat.{u + 1} Λ])) :=
    (Adjunction.ofIsLeftAdjoint _).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have (I : Type (u + 1)) :
      PreservesColimitsOfShape (Discrete I) (L((c.g)^*[ModuleCat.{u + 1} Λ])) :=
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) c.g).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have h (K : _root_.DerivedCategory (Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (N : ModuleCat.{u + 1} Λ) : IsIso ((rightDerivedLowerStarProjectionMapApp Λ c.g K).app
        (constantSingle (ModuleCat.{u + 1} Λ) Y N)) := by
    let τ := Functor.whiskerLeft (constantFunctor Λ Y)
      (rightDerivedLowerStarProjectionMapApp Λ c.g K)
    have e (M : ModuleCat.{u + 1} Λ) :
        (constantFunctor Λ Y).obj
            ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} Λ) 0).obj M) ≅
          constantSingle (ModuleCat.{u + 1} Λ) Y M :=
      (Functor.mapDerivedCategorySingleFunctor _ 0).app M
    have key := _root_.DerivedCategory.isIso_app_singleFunctor_obj τ (by
      change IsIso ((rightDerivedLowerStarProjectionMapApp Λ c.g K).app _)
      exact isIso_rightDerivedLowerStarProjectionMapApp_of_iso (e _).symm
        (isIso_rightDerivedLowerStarProjectionMapApp_constantSingle_self Λ c.g K)) N
    exact isIso_rightDerivedLowerStarProjectionMapApp_of_iso (e N) key
  have : IsIso (rightDerivedLowerShriekReductionModIdealMap Λ J c) := by
    refine isIso_rightDerivedLowerShriekDerivedTensorRightMap (ModuleCat.{u + 1} Λ) c _ fun K ↦ ?_
    change IsIso (((projectionMapOfCompactification (ModuleCat.{u + 1} Λ) c).app K).app
      (constantSingle (ModuleCat.{u + 1} Λ) Y (ModuleCat.of Λ (Λ ⧸ J))))
    rw [projectionMapOfCompactification_app_app]
    infer_instance
  exact ⟨Functor.isoWhiskerLeft _
      (eqToIso (reductionModIdeal_eq_derivedTensorRight Λ J Y)) ≪≫
    asIso (rightDerivedLowerShriekReductionModIdealMap Λ J c) ≪≫
    Functor.isoWhiskerRight
      (eqToIso (reductionModIdeal_eq_derivedTensorRight Λ J X).symm) _⟩
```

The finite lower-shriek corollary keeps its specialized comparison theorem. The
principal lower-star theorem uses its dualizable-quotient comparison results and
the fully proved private `principalIdeal_property` lemma. This helper handles the
zero/nonzero generator split for an arbitrary predicate on ideals. The principal
lower-shriek corollary preserves the source open/proper factorization, using the
principal lower-star theorem and the existing open tensor comparison. The latter is
first typed using tensor functors, then explicitly transported to reduction.
The comparison proofs use whiskered `eqToIso` of
`reductionModIdeal_eq_derivedTensorRight` instead of whole-goal simplification.
No public declaration or module is added.
All existing signatures, public imports, exported attributes, docstrings and
non-theorem bodies stay unchanged. The two added imports are private proof imports.
No target semantic review is reopened. The proper-adjoint premise remains admitted
in its original module. A complete version compiled cleanly in 28.7 seconds in this elaboration form. No diagnostic settings or raised compilation,
heartbeat or kernel-checking limits are included in the final file.

## Users

The downstream scan with `--uses
AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek` found
only the assigned module as an executable textual user. The local attributes do not
export to consumers. No signature or definition changes, so no consumer adaptation
is necessary.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | H2 | Prove reduction; local proof elaboration only. |

## Status

landed 20261021T101116-L-10637 2026-10-21 (merge of deliver/H2/WeilConjectures.SixFunctors.Etale.Derived.Exchange)
