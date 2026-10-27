# CategoryTheory.Mod.monoidalClosed and CategoryTheory.Mod.hasFunctorialFlatResolution

## Reason

Restore the closedness proof on the current upstream source and complete the flat-resolution
proof. The original instance signatures, attributes, docstrings and public imports remain
verbatim. Both original elaborated types omit MonoidalPreadditive; each proof explicitly
discards that unused section assumption and derives additivity from ambient closedness.
The unchanged Grothendieck instance body remains verbatim.

The closed structure uses the actual relative tensor coequalizer, preservation of colimits,
and the special adjoint functor theorem. Its right adjoint is determined up to natural
isomorphism by the proved adjunction. The flat resolution is explicitly constructed by
forgetting, applying the supplied ambient resolution, and taking free modules, with
augmentation free(pi) followed by the counit. Private proved split-coequalizer helpers
identify tensoring with a free module after forgetting, and reflect finite limits.
These helper proofs reuse the extracted UpstreamExtra module's argument without importing
that module, which would make a cycle. No arbitrary witness of an unproved existence theorem
is used. No public helper, new axiom or new hole is introduced.

The only added imports are private proof imports of TensorRegular and FreePresentation.
MonObj notation is opened only in a closed section of private helpers. No other module is
adapted. The completed structure has exactly the existing closed-category meaning;
the five target statements and their mathematical interpretation remain unchanged.

## Old

```lean
noncomputable instance monoidalClosed : MonoidalClosed (Mod C R) :=
  sorry


instance hasFunctorialFlatResolution [Abelian.HasFunctorialFlatResolution C] :
    Abelian.HasFunctorialFlatResolution (Mod C R) :=
  sorry

```

## New

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
      { app := fun N ↦ ((β_ N.X R).hom ≫ ModObj.smul (M := R) (X := N.X)) ▷ M.X
        naturality := by
          intro N N' φ
          change (φ.hom ▷ R) ▷ M.X ≫
              ((β_ N'.X R).hom ≫ ModObj.smul (M := R) (X := N'.X)) ▷ M.X =
            ((β_ N.X R).hom ≫ ModObj.smul (M := R) (X := N.X)) ▷ M.X ≫ φ.hom ▷ M.X
          rw [← comp_whiskerRight, ← comp_whiskerRight]
          congr 1
          rw [BraidedCategory.braiding_naturality_left_assoc, ← act_hom]
          simp only [Category.assoc] }
    let g : F₀ ⟶ F₁ :=
      { app := fun N ↦ (α_ N.X R M.X).hom ≫ N.X ◁ ModObj.smul (M := R) (X := M.X)
        naturality := by
          intro N N' φ
          change (φ.hom ▷ R) ▷ M.X ≫ (α_ N'.X R M.X).hom ≫
              N'.X ◁ ModObj.smul (M := R) (X := M.X) =
            ((α_ N.X R M.X).hom ≫ N.X ◁ ModObj.smul (M := R) (X := M.X)) ≫ φ.hom ▷ M.X
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
              ((β_ N'.X R).hom ≫ ModObj.smul (M := R) (X := N'.X)) ▷ M.X ≫ tensorObjπ N' M =
            ((β_ N.X R).hom ≫ ModObj.smul (M := R) (X := N.X)) ▷ M.X ≫
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

## Users

The source-only downstream scan finds 354 transitive importers. The table lists every
textual name match from downstream.py --uses and the representative consumers checked against
the changed output. All other importers receive the same public signatures and public imports,
so their statements require no adaptation. InternalSliceDerivedHomComparison is an
over-approximate name match referring to DerivedCategory.monoidalClosed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtalePullbackInternalHom | unclaimed | Existing public interface unchanged; no adaptation. |
| Sheaf.CategoryTheory.Monoidal.ModuleEqualizerInternalHom | unclaimed | Existing public interface unchanged; no adaptation. |
| Sheaf.Paper.CondensedOpenExtensionProducts | unclaimed | Existing public interface unchanged; no adaptation. |
| Sheaf.Paper.InternalScalarTensorComparison | unclaimed | Existing public interface unchanged; no adaptation. |
| Sheaf.Paper.InternalSliceDerivedHomComparison | unclaimed | Existing public interface unchanged; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian | unclaimed | Existing public interface unchanged; no adaptation. |
| WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory | unclaimed | Existing public interface unchanged; no adaptation. |
| WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian | M4 | Two existing instance bodies completed; public types preserved. |

The item and the three representative consumers above compile together in import order
against the changed item output (9.3, 5.0, 8.0, 5.1 seconds), without warnings. Original
and completed source probes show identical elaborated types for both instances. The completed
instances use exactly propext, Classical.choice and Quot.sound. Consumer verification copies
are not delivered.

## Status

landed 20261023T103107-L-3050696 2026-10-23 (merge of deliver/M4/WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian)
