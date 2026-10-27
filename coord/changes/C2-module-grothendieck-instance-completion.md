# CategoryTheory.Mod.monoidalClosed and CategoryTheory.Mod.hasFunctorialFlatResolution

## Reason

Fill the two existing sorry bodies, without changing either elaborated public type.
The stage-3 interface check conservatively treats instance bodies and local context
commands as interface changes, so this record includes every textual downstream user.

The closed structure is obtained from the actual relative monoidal tensor, by its
pointwise ambient coequalizer and the special adjoint functor theorem. Right adjoints
are determined up to natural isomorphism by this universal property. Free modules on
flat objects are flat by the split action coequalizer, and the augmentation is the
explicit free image of the given ambient augmentation followed by the counit.
No new assumption, axiom, hollow definition, or arbitrary witness is introduced.

Both original elaborated instance types omit the section's MonoidalPreadditive
hypothesis. The proofs derive it instead from colimit-preservation of the ambient
tensor, and explicitly discard the section instance to avoid accidentally adding a
binder. Separate #check probes of the original source and delivered source agree.
Their original attributes and public imports remain unchanged. MonObj notation is
opened only as local elaboration context; the new proof imports are private.

All other existing non-theorem bodies, including the Grothendieck instance, remain
unchanged. The additional helper constructions are private and fully proved.
No consumer is edited, and there are no forced adaptations. Filling the formerly
unknown internal-hom structure with a genuine right adjoint preserves the specified
closed-category meaning. Target signatures are unchanged; the reader can check
this choice against the existing equalizer-adjunction specification, which remains
proved in Sheaf.CategoryTheory.Monoidal.ModuleEqualizerInternalHom.

## Old

The exact two original instance declarations (the surrounding section and their
docstrings are retained in the delivered module):

```lean
noncomputable instance monoidalClosed : MonoidalClosed (Mod C R) :=
  sorry

instance hasFunctorialFlatResolution [Abelian.HasFunctorialFlatResolution C] :
    Abelian.HasFunctorialFlatResolution (Mod C R) :=
  sorry
```

## New

The exact completed instance declarations are:

```lean
noncomputable instance monoidalClosed : MonoidalClosed (Mod C R) where
  closed M := by
    -- Keep the original signature: closedness already makes the ambient tensor additive.
    rename_i hpre _ _ _ _
    clear hpre
    have hleft (X : C) : (MonoidalCategory.tensorLeft X).Additive := by
      have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
        (MonoidalCategory.tensorLeft X)
      exact Functor.additive_of_preservesBinaryBiproducts _
    have hright (X : C) : (MonoidalCategory.tensorRight X).Additive := by
      have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
        (MonoidalCategory.tensorRight X)
      exact Functor.additive_of_preservesBinaryBiproducts _
    have : MonoidalPreadditive C :=
      { whiskerLeft_zero := fun {X Y Z} ↦ (MonoidalCategory.tensorLeft X).map_zero Y Z
        zero_whiskerRight := fun {X Y Z} ↦ (MonoidalCategory.tensorRight X).map_zero Y Z
        whiskerLeft_add := fun {X Y Z} f g ↦ (MonoidalCategory.tensorLeft X).map_add
        add_whiskerRight := fun {X Y Z} f g ↦ (MonoidalCategory.tensorRight X).map_add }
    have : IsGrothendieckAbelian.{v} (Mod C R) := isGrothendieckAbelian R
    let F₀ := forget R ⋙ MonoidalCategory.tensorRight R ⋙
      MonoidalCategory.tensorRight M.X
    let F₁ := forget R ⋙ MonoidalCategory.tensorRight M.X
    let f : F₀ ⟶ F₁ :=
      { app := fun N ↦ ((β_ N.X R).hom ≫ γ[R,N.X]) ▷ M.X
        naturality := by
          intro N N' φ
          change (φ.hom ▷ R) ▷ M.X ≫
              ((β_ N'.X R).hom ≫ γ[R,N'.X]) ▷ M.X =
            ((β_ N.X R).hom ≫ γ[R,N.X]) ▷ M.X ≫ φ.hom ▷ M.X
          rw [← comp_whiskerRight, ← comp_whiskerRight]
          congr 1
          rw [BraidedCategory.braiding_naturality_left_assoc, ← act_hom]
          simp only [Category.assoc] }
    let g : F₀ ⟶ F₁ :=
      { app := fun N ↦ (α_ N.X R M.X).hom ≫ N.X ◁ γ[R,M.X]
        naturality := by
          intro N N' φ
          change (φ.hom ▷ R) ▷ M.X ≫ (α_ N'.X R M.X).hom ≫
              N'.X ◁ γ[R,M.X] =
            ((α_ N.X R M.X).hom ≫ N.X ◁ γ[R,M.X]) ≫ φ.hom ▷ M.X
          rw [associator_naturality_left_assoc, ← whisker_exchange]
          simp only [Category.assoc] }
    let D := parallelPair f g
    have : PreservesColimitsOfSize.{v, v} D.flip :=
      ⟨fun {J} _ ↦ preservesColimitsOfShape_of_evaluation _ _ fun j ↦ by
        cases j
        · exact inferInstanceAs (PreservesColimitsOfShape J F₀)
        · exact inferInstanceAs (PreservesColimitsOfShape J F₁)⟩
    let e : D.flip ⋙ colim ≅ MonoidalCategory.tensorRight M ⋙ forget R :=
      NatIso.ofComponents
        (fun N ↦ HasColimit.isoOfNatIso (diagramIsoParallelPair (D.flip.obj N)) ≪≫
          IsColimit.coconePointUniqueUpToIso
            (t := Cofork.ofπ (tensorObjπ N M) (tensorObjπ_condition N M))
            (colimit.isColimit _) (isColimitTensorπ N M)) (by
        intro N N' φ
        apply colimit.hom_ext
        intro j
        simp only [Functor.comp_map, colim_map, Iso.trans_hom, Category.assoc,
          ι_colimMap_assoc, HasColimit.isoOfNatIso_ι_hom_assoc]
        cases j
        · simp [D, F₀, F₁, f, g, tensorObjπ_whiskerRight]
          have h := congrArg (fun k ↦ k ≫ tensorObjπ N' M) (f.naturality φ)
          simp only [Category.assoc] at h
          change (φ.hom ▷ R) ▷ M.X ≫
              ((β_ N'.X R).hom ≫ γ[R,N'.X]) ▷ M.X ≫ tensorObjπ N' M =
            ((β_ N.X R).hom ≫ γ[R,N.X]) ▷ M.X ≫
              φ.hom ▷ M.X ≫ tensorObjπ N' M at h
          simpa only [comp_whiskerRight, Category.assoc] using h
        · simp [D, F₀, F₁, f, g, tensorObjπ_whiskerRight])
    have : PreservesColimitsOfSize.{v, v}
        (MonoidalCategory.tensorRight M ⋙ forget R) := preservesColimits_of_natIso e
    have : PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight M) :=
      preservesColimits_of_reflects_of_preserves _ (forget R)
    have : PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft M) :=
      preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M).symm
    have : (MonoidalCategory.tensorLeft M).IsLeftAdjoint :=
      isLeftAdjoint_of_preservesColimits_of_isSeparating
        (isSeparator_separator (Mod C R)) _
    exact
      { rightAdj := (MonoidalCategory.tensorLeft M).rightAdjoint
        adj := Adjunction.ofIsLeftAdjoint _ }

instance hasFunctorialFlatResolution [Abelian.HasFunctorialFlatResolution C] :
    Abelian.HasFunctorialFlatResolution (Mod C R) := by
  -- Derive additivity without capturing the unused section instance in the signature.
  rename_i hpre _ _ _ _ _
  clear hpre
  have hleft (X : C) : (MonoidalCategory.tensorLeft X).Additive := by
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
      (MonoidalCategory.tensorLeft X)
    exact Functor.additive_of_preservesBinaryBiproducts _
  have hright (X : C) : (MonoidalCategory.tensorRight X).Additive := by
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
      (MonoidalCategory.tensorRight X)
    exact Functor.additive_of_preservesBinaryBiproducts _
  have : MonoidalPreadditive C :=
    { whiskerLeft_zero := fun {X Y Z} ↦ (MonoidalCategory.tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (MonoidalCategory.tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (MonoidalCategory.tensorLeft X).map_add
      add_whiskerRight := fun {X Y Z} f g ↦ (MonoidalCategory.tensorRight X).map_add }
  obtain ⟨Λ⟩ := ‹Abelian.HasFunctorialFlatResolution C›
  have : (free R).IsLeftAdjoint := (freeForgetAdjunction R).isLeftAdjoint
  let F := forget R ⋙ Λ.F ⋙ ObjectProperty.flat.ι ⋙ free R
  let π : F ⟶ 𝟭 (Mod C R) :=
    Functor.whiskerRight (Functor.whiskerLeft (forget R) Λ.π) (free R) ≫
      (freeForgetAdjunction R).counit
  refine ⟨{ F := ObjectProperty.lift _ F ?_, π := π, epi_π_app := ?_ }⟩
  · intro M
    exact flat_free (Λ.F.obj ((forget R).obj M)).property
  · intro M
    change Epi ((free R).map (Λ.π.app ((forget R).obj M)) ≫
      (freeForgetAdjunction R).counit.app M)
    have : Epi (Λ.π.app ((forget R).obj M)) := inferInstance
    have : PreservesColimits (free R) :=
      (freeForgetAdjunction R).leftAdjoint_preservesColimits
    have : Epi ((free R).map (Λ.π.app ((forget R).obj M))) :=
      (free R).map_epi _
    exact epi_comp _ _
```

The helper source is in the same delivered Lean module. In addition, `omit
[MonoidalPreadditive C] in` precedes each of the two original docstrings; this
preserves the original elaborated parameter lists rather than changing them.

## Users

The following are all name matches reported by tools/downstream.py --uses, plus
the item itself. Claims are as in this machine's current shared snapshot. The
common effect is identical signatures and mathematical assumptions, completed
instances, and no required source adaptation. Most named matches only mark the
instance locally irreducible, and remain valid unchanged. The matches in
InternalSliceDerivedHomComparison refer to DerivedCategory.monoidalClosed and are
conservative short-name matches, not uses of the changed instance.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtalePullbackInternalHom | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.Paper.ClosedSupportBoundedContinuity | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.Paper.CoefficientProjectionSquare | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | Same local irreducibility and flat-resolution instance attributes; no adaptation. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.Paper.CondensedCompactSupportProjection | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.Paper.CondensedERealization | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.Paper.CondensedOpenExceptionalProjectionFormula | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.Paper.CondensedOpenExtensionProducts | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.Paper.IntegralConstantModelLocalResolution | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.Paper.IntegralExtensionByZero | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.Paper.IntegralOpenExtensionReduction | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.Paper.IntegralQuotientProjectionComparison | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorRouteModel | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.Paper.IntegralTensorShriek | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.Paper.InternalScalarTensorComparison | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.Paper.InternalSliceDerivedHomComparison | unclaimed | Textual over-approximation: different monoidalClosed declaration; no change. |
| Sheaf.Paper.LatticeSupportedHomFiniteComparison | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.Paper.LocalModelTorBoundDescent | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.Paper.RationalLocalizedHom | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| Sheaf.SixFunctors.LocallyClosedGeneratorTensorIntersection | E1 | Same explicit closed-structure and flat-resolution instance signatures; no adaptation. |
| WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian | C2 (this assignment) | Fill both existing holes and retain original elaborated public types. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Local irreducibility attribute on CategoryTheory.Mod.monoidalClosed remains valid; no source adaptation. Compile attempted, but the server returned no answer. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Existing use or local irreducibility attribute remains valid; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | N3 | Existing use or local irreducibility attribute remains valid; no adaptation. |

| WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory | unclaimed | Compiles unchanged against the completed module; verification only. |
| Sheaf.CategoryTheory.Monoidal.ModuleEqualizerInternalHom | unclaimed | Compiles unchanged against the completed module; verification only. |

Two direct consumers compile against this packet's actual module output:
WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory and
Sheaf.CategoryTheory.Monoidal.ModuleEqualizerInternalHom. Poincare was also submitted
unchanged for verification, but the batch and individual attempts returned no answer
from the busy compile server (exit 124), without a Lean diagnostic. These copies are
only for verification, and are not adapted or delivered.

## Status

landed 20261022T113839-L-302719 2026-10-22 (merge of deliver/C2/WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian)
