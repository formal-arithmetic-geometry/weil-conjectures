# AlgebraicGeometry.ProEtale.continuousSetSheaf and continuous-set constructions

## Reason

The three stated proof dependencies import TotallyDisconnectedCoefficientRealization for
its definitions. The item must import their theorems, creating cycles. Extract the existing
15 prerequisite declarations into ContinuousSetConstructions and publicly import it from
the item and the three dependency modules. Names, universes, signatures, visibility and all
non-theorem bodies remain identical. The two prerequisite theorem proofs are completed. The proved prerequisite descent
theorem has its own new node, lem-sfb-continuous-set-proetale-descent; it is not a new
Lean statement or another construction.
No mathematical statement or target meaning changes; this is a relocation of concrete data,
not a new coefficient construction. No source-library file is changed.

## Old

Defined in Sheaf.Paper.TotallyDisconnectedCoefficientRealization:

```lean
abbrev continuousSetPresheaf (X : Scheme.{u}) (D : Type (u + 1)) [TopologicalSpace D] :=
  (Scheme.ProEt.forget X ⋙ Over.forget X).op ⋙ continuousMapPresheaf D

theorem continuousSetPresheaf_isSheaf (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] :
    Presheaf.IsSheaf (Scheme.ProEt.topology X) (continuousSetPresheaf X D) := by
  sorry

noncomputable def continuousSetSheaf (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)) :=
  ⟨continuousSetPresheaf X D, continuousSetPresheaf_isSheaf X D⟩

def continuousSetSheafMap (X : Scheme.{u}) {D E : Type (u + 1)}
    [TopologicalSpace D] [TopologicalSpace E] (h : C(D, E)) :
    continuousSetSheaf X D ⟶ continuousSetSheaf X E :=
  ⟨{ app := fun _ ↦ ↾fun s ↦ h.comp s, naturality := fun _ _ _ ↦ rfl }⟩

noncomputable abbrev continuousSetProfiniteFunctor :
    TopCat.{u + 1} ⥤ Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)) :=
  topCatToSheafCompHausLike.{u + 1, u} (fun T ↦ TotallyDisconnectedSpace T)
    (fun _ _ f hf ↦ ((Profinite.effectiveEpi_tfae f).out 0 2).mp hf)

noncomputable abbrev continuousSetProfiniteSheaf (D : Type (u + 1)) [TopologicalSpace D] :=
  continuousSetProfiniteFunctor.obj (TopCat.of D)

noncomputable def continuousSetTestProjection (S : Profinite.{u}) :
    C((profiniteToProEt.obj S).left, S) :=
  ContinuousMap.fst.comp
    ⟨(LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm,
      (LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm.continuous⟩

noncomputable def continuousSetRelativeTestProjection (X : Scheme.{u}) (S : Profinite.{u}) :
    C(((Scheme.proEtaleBaseChange (toSpecZ X)).obj (profiniteToProEt.obj S)).left, S) :=
  (continuousSetTestProjection S).comp
    (pullback.fst (profiniteToProEt.obj S).hom (toSpecZ X)).base.hom

noncomputable abbrev continuousSetPointAdjunction (X : Scheme.{u}) :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous profiniteToProEt
    (Type (u + 1)) (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)).comp
    (Scheme.proEtaleSheafAdjunction (toSpecZ X) (Type (u + 1)))

def IsContinuousSetRealization (X : Scheme.{u}) (D : Type (u + 1)) [TopologicalSpace D]
    (σ : (profinitePointSetSchemeInverseImage X).obj (continuousSetProfiniteSheaf D) ⟶
      continuousSetSheaf X D) : Prop :=
  ∀ (S : Profinite.{u}) (b : C(S, D)),
    (((continuousSetPointAdjunction X).homEquiv _ _ σ).hom.app (op S)) b =
      b.comp (continuousSetRelativeTestProjection X S)

theorem continuousSetDirectImage_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type (u + 1)) [TopologicalSpace D] {U V : Y.ProEtᵒᵖ} (g : U ⟶ V) :
    (continuousSetPresheaf Y D).map g ≫
        (↾fun s ↦ s.comp (pullback.fst V.unop.hom f).base.hom) =
      (↾fun s ↦ s.comp (pullback.fst U.unop.hom f).base.hom) ≫
        ((Scheme.proEtaleSheafDirectImage f (Type (u + 1))).obj
          (continuousSetSheaf X D)).obj.map g := by
  sorry

noncomputable def continuousSetDirectImageMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type (u + 1)) [TopologicalSpace D] :
    continuousSetSheaf Y D ⟶
      (Scheme.proEtaleSheafDirectImage f (Type (u + 1))).obj (continuousSetSheaf X D) :=
  ⟨{ app := fun V ↦ ↾fun s ↦ s.comp (pullback.fst V.unop.hom f).base.hom
     naturality := fun _ _ g ↦ continuousSetDirectImage_naturality f D g }⟩

noncomputable def continuousSetPullbackMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type (u + 1)) [TopologicalSpace D] :
    (Scheme.proEtaleSheafInverseImage f (Type (u + 1))).obj (continuousSetSheaf Y D) ⟶
      continuousSetSheaf X D :=
  ((Scheme.proEtaleSheafAdjunction f (Type (u + 1))).homEquiv _ _).symm
    (continuousSetDirectImageMap f D)

def continuousSetConstantPresheafMap (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] :
    (Functor.const X.ProEtᵒᵖ).obj D ⟶ continuousSetPresheaf X D where
  app U := ↾fun d ↦ ContinuousMap.const U.unop.left d
  naturality _ _ _ := rfl

noncomputable def continuousSetConstantMap (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] :
    (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj D ⟶
      continuousSetSheaf X D :=
  ((sheafificationAdjunction (Scheme.ProEt.topology X) (Type (u + 1))).homEquiv _ _).symm
    (continuousSetConstantPresheafMap X D)
```

## New

Defined in Sheaf.Paper.ContinuousSetConstructions, publicly re-exported by the old module:

```lean
abbrev continuousSetPresheaf (X : Scheme.{u}) (D : Type (u + 1)) [TopologicalSpace D] :=
  (Scheme.ProEt.forget X ⋙ Over.forget X).op ⋙ continuousMapPresheaf D

/-- Continuous functions satisfy descent on the small pro-etale site.
Source: Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-sfb-totally-disconnected-coefficient-realization).
Proof: continuous functions form an fpqc sheaf by quotient-map descent. Restrict this
sheaf along the forgetful functor from the small pro-etale site, whose covering families
are fpqc covering families. This is step 1 of the node's proof. -/
theorem continuousSetPresheaf_isSheaf (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] :
    Presheaf.IsSheaf (Scheme.ProEt.topology X) (continuousSetPresheaf X D) := by
  exact (Scheme.ProEt.forget X ⋙ Over.forget X).op_comp_isSheaf_of_isSheaf _
    Scheme.proetaleTopology (continuousMapPresheaf D)
    (.of_le Scheme.proetaleTopology_le_fpqcTopology
      (isSheaf_fpqcTopology_continuousMapPresheaf D))

/-- The actual sheaf of continuous functions, with no sheafification of its sections.
Source: Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable def continuousSetSheaf (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)) :=
  ⟨continuousSetPresheaf X D, continuousSetPresheaf_isSheaf X D⟩

/-- Postcomposition of continuous sections with a continuous coefficient map.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
def continuousSetSheafMap (X : Scheme.{u}) {D E : Type (u + 1)}
    [TopologicalSpace D] [TopologicalSpace E] (h : C(D, E)) :
    continuousSetSheaf X D ⟶ continuousSetSheaf X E :=
  ⟨{ app := fun _ ↦ ↾fun s ↦ h.comp s, naturality := fun _ _ _ ↦ rfl }⟩

/-- The existing Mathlib continuous-function sheaf functor on profinite sets.
Source: Hemo--Richarz--Scholbach, Example 3.1; Mathlib `topCatToSheafCompHausLike`
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable abbrev continuousSetProfiniteFunctor :
    TopCat.{u + 1} ⥤ Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)) :=
  topCatToSheafCompHausLike.{u + 1, u} (fun T ↦ TotallyDisconnectedSpace T)
    (fun _ _ f hf ↦ ((Profinite.effectiveEpi_tfae f).out 0 2).mp hf)

/-- The profinite coefficient sheaf `S ↦ C(S,D)`, using Mathlib's construction.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable abbrev continuousSetProfiniteSheaf (D : Type (u + 1)) [TopologicalSpace D] :=
  continuousSetProfiniteFunctor.obj (TopCat.of D)

/-- The canonical label map from the spectrum of locally constant integer functions to S.
Source: Hemo--Richarz--Scholbach, Example 3.1, test-object construction; the spectrum
homeomorphism in `lem-weil-pbc-locally-constant-prime-spectrum`
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable def continuousSetTestProjection (S : Profinite.{u}) :
    C((profiniteToProEt.obj S).left, S) :=
  ContinuousMap.fst.comp
    ⟨(LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm,
      (LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm.continuous⟩

/-- The projection of a relative test object to its profinite label space.
Source: Hemo--Richarz--Scholbach, Example 3.1, relative test objects
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable def continuousSetRelativeTestProjection (X : Scheme.{u}) (S : Profinite.{u}) :
    C(((Scheme.proEtaleBaseChange (toSpecZ X)).obj (profiniteToProEt.obj S)).left, S) :=
  (continuousSetTestProjection S).comp
    (pullback.fst (profiniteToProEt.obj S).hom (toSpecZ X)).base.hom

/-- The composite adjunction defining the specified set inverse image from the point.
Source: Hemo--Richarz--Scholbach, Example 3.1; the point-pullback theorem
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable abbrev continuousSetPointAdjunction (X : Scheme.{u}) :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous profiniteToProEt
    (Type (u + 1)) (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)).comp
    (Scheme.proEtaleSheafAdjunction (toSpecZ X) (Type (u + 1)))

/-- Test-function normalization of the realization map: the adjoint sends b to b ∘ r.
Source: Hemo--Richarz--Scholbach, Example 3.1, explicit adjunction calculation
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
def IsContinuousSetRealization (X : Scheme.{u}) (D : Type (u + 1)) [TopologicalSpace D]
    (σ : (profinitePointSetSchemeInverseImage X).obj (continuousSetProfiniteSheaf D) ⟶
      continuousSetSheaf X D) : Prop :=
  ∀ (S : Profinite.{u}) (b : C(S, D)),
    (((continuousSetPointAdjunction X).homEquiv _ _ σ).hom.app (op S)) b =
      b.comp (continuousSetRelativeTestProjection X S)

/-- Naturality of the sectionwise direct-image comparison.
Source: Hemo--Richarz--Scholbach, Example 3.1, scheme pullback
(blueprint: lem-sfb-totally-disconnected-coefficient-realization).
Proof: for a morphism of test schemes the two maps to its pullback followed by the
first projection agree by the defining equation of the pullback map. Precomposing a
continuous function with these equal scheme maps gives the claimed equality (step 8). -/
theorem continuousSetDirectImage_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type (u + 1)) [TopologicalSpace D] {U V : Y.ProEtᵒᵖ} (g : U ⟶ V) :
    (continuousSetPresheaf Y D).map g ≫
        (↾fun s ↦ s.comp (pullback.fst V.unop.hom f).base.hom) =
      (↾fun s ↦ s.comp (pullback.fst U.unop.hom f).base.hom) ≫
        ((Scheme.proEtaleSheafDirectImage f (Type (u + 1))).obj
          (continuousSetSheaf X D)).obj.map g := by
  ext s x
  change C(U.unop.left, D) at s
  change s (g.unop.left (pullback.fst V.unop.hom f x)) =
    s (pullback.fst U.unop.hom f
      (((Scheme.proEtaleBaseChange f).map g.unop).left x))
  have hmap : ((Scheme.proEtaleBaseChange f).map g.unop).left ≫
      pullback.fst U.unop.hom f = pullback.fst V.unop.hom f ≫ g.unop.left := by
    simp [Scheme.proEtaleBaseChange, MorphismProperty.Over.pullback]
  exact congrArg s (congrArg (fun k : _ ⟶ U.unop.left ↦ k x) hmap.symm)

/-- Precomposition on the base-changed test object, as an actual sheaf morphism.
Source: Hemo--Richarz--Scholbach, Example 3.1, scheme pullback
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable def continuousSetDirectImageMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type (u + 1)) [TopologicalSpace D] :
    continuousSetSheaf Y D ⟶
      (Scheme.proEtaleSheafDirectImage f (Type (u + 1))).obj (continuousSetSheaf X D) :=
  ⟨{ app := fun V ↦ ↾fun s ↦ s.comp (pullback.fst V.unop.hom f).base.hom
     naturality := fun _ _ g ↦ continuousSetDirectImage_naturality f D g }⟩

/-- The canonical scheme-pullback comparison is the adjunct of precomposition.
Source: Hemo--Richarz--Scholbach, Example 3.1 and the following paragraph
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable def continuousSetPullbackMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type (u + 1)) [TopologicalSpace D] :
    (Scheme.proEtaleSheafInverseImage f (Type (u + 1))).obj (continuousSetSheaf Y D) ⟶
      continuousSetSheaf X D :=
  ((Scheme.proEtaleSheafAdjunction f (Type (u + 1))).homEquiv _ _).symm
    (continuousSetDirectImageMap f D)

/-- The map from the constant presheaf sends an element to the constant function.
Source: Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
def continuousSetConstantPresheafMap (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] :
    (Functor.const X.ProEtᵒᵖ).obj D ⟶ continuousSetPresheaf X D where
  app U := ↾fun d ↦ ContinuousMap.const U.unop.left d
  naturality _ _ _ := rfl

/-- The canonical constant-sheaf comparison is the sheafification adjunct of constants.
Source: Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-sfb-totally-disconnected-coefficient-realization). -/
noncomputable def continuousSetConstantMap (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] :
    (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj D ⟶
      continuousSetSheaf X D :=
  ((sheafificationAdjunction (Scheme.ProEt.topology X) (Type (u + 1))).homEquiv _ _).symm
    (continuousSetConstantPresheafMap X D)
```

## Users

Read-only tools/downstream.py checks covered every moved name. The full downstream import
closure is listed as well, so consumers using other re-exported declarations are accounted for.
Each unchanged consumer keeps the same mathematical type because every name remains public
through the old module. The move adds no hypotheses and changes no definitional data.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.TotallyDisconnectedCoefficientRealization | J1 | Imports shared constructions and the stated proof dependencies; closes all its holes. |
| Sheaf.Paper.CompleteGroupTorsorMonodromy | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.CompleteIntegralResidueFunctor | J4 | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.CompleteNormOpenTest | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.ConstructibleNormedGeometricFibres | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.ContinuousRightTorsor | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.ContinuousSetDescentComponents | unclaimed | Only line 8 public import changes to ContinuousSetConstructions; theorem unchanged. |
| Sheaf.Paper.KummerChartGeometryMaps | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.KummerCoefficientModels | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.KummerCoherentRoof | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.KummerConstantNerveTerm | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.KummerGeometricColumns | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.KummerGlobalChart | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.KummerInvariantScalarMap | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.KummerLocalSource | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.KummerNerveCoordinates | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.KummerNerveGeometricMap | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.KummerNerveTransport | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.KummerNormalizedChart | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.KummerParameterizedTerm | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.KummerRefinement | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.KummerResolvedDescent | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.KummerScalarInvariantSquare | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.KummerStratumChart | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.KummerStratumGeometry | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.LisseLatticePotentialKummerTameness | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.NativeDerivedWeilTensorConstructible | A9 | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.NormAlgClInternalHomBaseChange | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.NormalizedContinuousSetComparisonCoherence | R6 | Only line 8 public import changes to ContinuousSetConstructions; theorem unchanged. |
| Sheaf.Paper.NormalizedContinuousSetKanEvaluation | R7 | Only line 12 public import changes to ContinuousSetConstructions; theorem unchanged. |
| Sheaf.Paper.SupportedLatticeNormProjection | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.TamePairProperGenerators | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.TameRootTowerExtension | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |
| Sheaf.Paper.TameStratumKummerDescent | unclaimed | No adaptation: original import still publicly exposes the identical declarations and data. |

R6 and R7 hold the coherence and Kan modules respectively. The original versions were tested
one at a time against the changed item with lcompile.py --all. The former reports:
`the modules import one another in a cycle: Sheaf.Paper.NormalizedContinuousSetComparisonCoherence, Sheaf.Paper.TotallyDisconnectedCoefficientRealization`.
The latter reports the same diagnostic with NormalizedContinuousSetKanEvaluation instead.
Changing the single import line repairs each cycle, and all five adapted/new modules compile.
ContinuousSetDescentComponents is unclaimed and needs the same import change.

## Status

landed 20261023T102928-L-3007894 2026-10-23 (merge of deliver/J1/Sheaf.Paper.TotallyDisconnectedCoefficientRealization)
