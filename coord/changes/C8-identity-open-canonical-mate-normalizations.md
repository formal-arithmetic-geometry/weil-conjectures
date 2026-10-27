# AlgebraicGeometry.ProEtale.CondensedRing.identity_open_derived_restriction

## Reason

The item defines its comparisons by the specified canonical mates. The underived
section theorems provide existential normalized isomorphisms, but their original public
interfaces omit the equality between those witnesses and the canonical mate. That
equality is already established in their private proofs. Similarly, the general derived
square-mate cochain normalization is private. Expose proved companion theorems for these
three existing nodes, then assemble the restriction and identity proofs from them. The original composition
hole is retained with its unchanged proof plan.

The original existential theorems retain their exact signatures and are recovered by
forgetting the additional canonical equation. All definition bodies and existing public
imports are unchanged. No target statement or definition used by a target changes meaning.

## Old

The original public theorem interfaces are:

```lean
theorem moduleDirectImageOpenPasting :
    ∃ β : Comparisons Λ, Sectionwise Λ β ∧ Composition Λ ∧ SuccessiveOpens Λ β ∧
      MixedPasting Λ β ∧ Units Λ β ∧ Degreewise Λ β

theorem identityOpenModuleSections :
    ProjectionGeometry.{u} ∧ OpenRestriction Λ ∧
      ∃ c : Comparisons Λ, UniqueNormalized Λ c ∧ Composition Λ c ∧ Identity Λ c

```

The proof of `localized_mate_cochain` is private. The item has three theorem bodies
`:= by sorry` and only `set_option autoImplicit false` at file scope.

## New

The original signatures above remain verbatim. New proved theorem APIs:

- `ModuleOpenPasting.moduleDirectImageOpenPasting_canonical` adds the equation identifying
  each witness with the canonical mate of the module pullback square.
- `IdentityOpenModuleSections.identityOpenModuleSections_canonical` adds the equation
  identifying each witness with that mate followed by the identity direct image.
- `UnboundedExactTower.localized_mate_cochain_normalization` is a public wrapper around
  the existing private general cochain normalization of derived square mates.

The principal added signatures are:

```lean
theorem moduleDirectImageOpenPasting_canonical :
    ∃ β : Comparisons Λ, Sectionwise Λ β ∧ Composition Λ ∧ SuccessiveOpens Λ β ∧
      MixedPasting Λ β ∧ Units Λ β ∧ Degreewise Λ β ∧
      ∀ {X Y U P : Scheme.{u}} (f : X ⟶ Y) (j : U ⟶ Y) [IsOpenImmersion j]
        (fU : P ⟶ U) (i : P ⟶ X) [IsOpenImmersion i] (sq : IsPullback i fU f j),
        (β f j fU i sq).hom =
          (mateEquiv (upperStarLowerStarAdjunction Λ f)
            (upperStarLowerStarAdjunction Λ fU)
            (TwoSquare.mk _ _ _ _
              (((upperStarComp Λ i f).symm ≪≫ upperStarCongr Λ sq.w ≪≫
                upperStarComp Λ fU j).inv))).natTrans

theorem identityOpenModuleSections_canonical :
    ProjectionGeometry.{u} ∧ OpenRestriction Λ ∧
      ∃ c : Comparisons Λ, UniqueNormalized Λ c ∧ Composition Λ c ∧ Identity Λ c ∧
        ∀ {U Z Z' : Scheme.{u}} (j : U ⟶ Z) (j' : U ⟶ Z')
          [IsOpenImmersion j] [IsOpenImmersion j'] (h : Z' ⟶ Z)
          (w : j' ≫ h = j) (hw : h ⁻¹' Set.range j = Set.range j'),
          (c j j' h w hw).hom =
            (mateEquiv (upperStarLowerStarAdjunction Λ h)
              (upperStarLowerStarAdjunction Λ (𝟙 U))
              (TwoSquare.mk _ _ _ _
                (((upperStarComp Λ (𝟙 U) j).symm ≪≫
                  upperStarCongr Λ (w.trans (Category.id_comp j).symm).symm ≪≫
                  upperStarComp Λ j' h).hom))).natTrans ≫
              Functor.whiskerLeft (upperStar Λ j') (lowerStarId Λ U).hom ≫
              (Functor.rightUnitor (upperStar Λ j')).hom

theorem localized_mate_cochain_normalization (a : F ⊣ G) (a' : F' ⊣ G')
    (θ : g ⋙ F' ≅ F ⋙ h) (I : CochainComplex A ℤ) :
    g.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
        g.mapDerivedCategory.map (cochainUnit G I) ≫
        (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
          a'.mapDerivedCategoryRightDerivedAdjunction
          (TwoSquare.mk _ _ _ _ (localizedSquare F F' g h θ).hom)).app
            (DerivedCategory.Q.obj I) ≫
        G'.rightDerivedFunctor.map (h.mapDerivedCategoryFactors.hom.app I) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (mateEquiv a a' (TwoSquare.mk _ _ _ _ θ.hom)).natTrans (.up ℤ)).app I) ≫
        cochainUnit G' ((h.mapHomologicalComplex (.up ℤ)).obj I)
```

Each theorem has its source, proof explanation and existing blueprint node in its
docstring; the corresponding existing node lists it as a companion declaration.
The item uses three elaboration options to recognize the canonical mapped-complex
identifications:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward false
```

These affect elaboration of this file only. A local instance priority selects
`CategoryTheory.Abelian.toPreadditive` before statement elaboration, avoiding a costly
conversion between the definitionally identical direct module preadditive instance and
the abelian projection. Public definitions and instances are unchanged. Local
irreducibility attributes prevent derived categories, adjunctions and compositors from
being expanded during rewriting. Proved private helpers carry out the canonical mate
calculation, K-injective representative extensionality and underived identification.
The three public theorem statements and all three data definitions retain their exact text.

## Users

The source inventory from `tools/downstream.py` gives the five live downstream modules
of the three API modules, including the changed IdentityOpenModuleSections. The current
item was quarantined and is restored by this assignment. Its recorded consumers are
also included below, even where quarantined. No held consumer is modified.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.IdentityOpenModuleSections | unclaimed | Adds a proved canonical normalization API; existing signatures and data unchanged. |
| Sheaf.SixFunctors.OpenStarShriekScalarMateSquare | unclaimed | Existing public signatures and definitions unchanged; no consumer adaptation. |
| Sheaf.CategoryTheory.TowerLimitTransposeNormalization | unclaimed | Existing public signatures and definitions unchanged; no consumer adaptation. |
| Sheaf.Paper.RingedRestrictionStrictLimitCoherence | E2 | Existing public signatures and definitions unchanged; no consumer adaptation. |
| Sheaf.Paper.SfExactPullbackQuotientAugmentationSquare | unclaimed | Existing public signatures and definitions unchanged; no consumer adaptation. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | C8 | Adds a proved canonical normalization API; existing signatures and data unchanged. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | unclaimed | Existing public signatures and definitions unchanged; no consumer adaptation. |
| Sheaf.Paper.IdentityOpenUnderivedSquareNormalization | unclaimed | Existing public signatures and definitions unchanged; no consumer adaptation. |
| Sheaf.Paper.NormalizedOpenRefinementCoherence | unclaimed | Existing public signatures and definitions unchanged; no consumer adaptation. |

## Status

landed 20261025T122654-L-1794778 2026-10-25 (merge of deliver/C8/Sheaf.Paper.IdentityOpenDerivedRestriction)
