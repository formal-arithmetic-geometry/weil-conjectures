# RankOne section data and explicit comparison signatures

## Reason

The ordinary finite-coefficient calculation and the generic support localization are independent
parts of the source argument. Both need the original canonical section/Kummer constructions;
extracting those constructions into a public data module avoids an import cycle between the
ordinary calculation and its finite-module cohomology lemma. The original module publicly
reexports them, retaining every fully qualified declaration name and meaning.

The inferred types of evaluationExt and comparisonCohomology are now written explicitly, and
those two definitions and kummerClass are marked irreducible. This prevents backward unification
from expanding whole derived functor constructions. With respectTransparency enabled the data
module compiles in about 19 seconds. The facade also enables respectTransparency after a
delivery dry-run timeout; its profiled compilation then completed in 25.5 seconds. The constructions are unchanged, and their bodies remain
exposed; proof helpers unfold kummerClass explicitly. No arbitrary data are chosen from a mere
existence statement. evaluationExt still chooses the comparison uniquely determined on every
injective cocycle by its existing source theorem.

The current shared source already imports the upstream WeilConjectures owners of the two
retired Sheaf comparison modules. This packet retains those upstream owners. All original
public imports remain available from the original facade, directly or through the public
data module. Mathlib's RatFunc import stays on the facade,
where the theorem statement uses it.

This is a relocation and elaboration repair, not a change to the mathematical definitions used
by any target. Target statements and the rankOne_local_calculation signature are unchanged.
No consumer requires a forced adaptation.

## Old

The following public definitions and instance were in
lean/Sheaf/Paper/PurityRankOneLocalCalculation.lean:

```lean
/-- Evaluation on a site object, the section functor used in the support definition.
Source: blueprint proof Step 4 (blueprint: thm-pur-rank-one-local-calculation). -/
abbrev sections {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] (W : C) :=
  sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙ (evaluation _ _).obj (op W)

/-- The recorded open immersion is the inclusion of its basic open.
Source: blueprint affine-line datum (blueprint: thm-pur-rank-one-local-calculation). -/
instance openImmersion_isOpenImmersion (Y : Scheme.{u}) :
    IsOpenImmersion (openImmersion Y) :=
  inferInstanceAs (IsOpenImmersion (((Line Y).basicOpen (coordinate Y)).ι))

/-- The standard punctured-line object of the small etale site.
Source: blueprint proof Step 1 (blueprint: thm-pur-rank-one-local-calculation). -/
def openObject (Y : Scheme.{u}) : (Line Y).Etale :=
  Scheme.Etale.mk (openImmersion Y)

/-- Restriction from the affine line to its punctured open, whose complement is the origin.
Source: blueprint proof Step 4 (blueprint: thm-pur-rank-one-local-calculation). -/
def restriction (Y : Scheme.{u}) : openObject Y ⟶ Scheme.Etale.mk (𝟙 (Line Y)) :=
  MorphismProperty.Over.homMk (openImmersion Y)
    (by change openImmersion Y ≫ 𝟙 (Line Y) = openImmersion Y; simp)

/-- The genuine inverse-image coefficient sheaf on the pro-etale site.
Source: blueprint proof Step 7 (blueprint: thm-pur-rank-one-local-calculation). -/
abbrev proCoefficient (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).obj F

/-- The three complexes in the support sequence, with the actual kernel inclusion and
restriction. Source: Milne, Section 9, Theorem 9.4; blueprint proof Step 4
(blueprint: thm-pur-rank-one-local-calculation). -/
def sectionComplex {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] {V W : C} (j : W ⟶ V)
    (I : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℕ) :
    ShortComplex (CochainComplex (ModuleCat.{u + 1} A) ℕ) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex
      (Sheaf.supportedSectionsInclusion J (ModuleCat.{u + 1} A) j) (.up ℕ)).app I)
    ((NatTrans.mapHomologicalComplex
      ((sheafSections J (ModuleCat.{u + 1} A)).map j.op) (.up ℕ)).app I)
    (by ext n : 1; exact kernel.condition ((I.X n).obj.map j.op))

/-- A support boundary is exactly the snake boundary on injective section complexes,
transported by the canonical resolution comparisons. This characterization rules out
both an arbitrary isomorphism and an arbitrary choice of sign.
Source: Milne, Section 9, Theorem 9.4; blueprint proof Step 4
(blueprint: thm-pur-rank-one-local-calculation). -/
def IsBoundary {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] [HasSheafify J (ModuleCat.{u + 1} A)]
    [EnoughInjectives (Sheaf J (ModuleCat.{u + 1} A))]
    {V W : C} (j : W ⟶ V) (F : Sheaf J (ModuleCat.{u + 1} A))
    (δ : ((sections J A W).rightDerived 1).obj F ⟶
      ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).rightDerived 2).obj F) :
    Prop :=
  ∀ I : InjectiveResolution F, ∃ hI : (sectionComplex J A j I.cocomplex).ShortExact,
    δ = (I.isoRightDerivedObj (sections J A W) 1).hom ≫
      hI.δ 1 2 rfl ≫
      (I.isoRightDerivedObj
        (Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j) 2).inv

/-- Free abelian sheafification represents sections, with its canonical Yoneda map.
Source: Stacks 03F3; blueprint proof Step 2
(blueprint: thm-pur-rank-one-local-calculation). -/
def evaluationRepresented (X : Scheme.{u}) (W : X.Etale) :
    preadditiveCoyoneda.obj (op ((presheafToSheaf X.smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj (uliftYoneda.{u + 1}.obj W ⋙ AddCommGrpCat.free))) ≅
      sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op W) :=
  NatIso.ofComponents
    (fun F ↦ (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology W F).toAddCommGrpIso)
    (by
      intro F G f
      ext a
      exact (EtaleOpenComparison.sectionsEquiv_naturality X.smallEtaleTopology W f a).symm)

/-- The Ext/derived-evaluation comparison normalized on every injective cocycle.
The theorem used here determines the comparison uniquely, since every Ext class has
an injective cocycle representative. No coefficient object is chosen from mere existence.
Source: Stacks 06XR; blueprint proof Step 2
(blueprint: thm-pur-rank-one-local-calculation). -/
def evaluationExt (X : Scheme.{u}) (W : X.Etale) (q : ℕ) :=
  Classical.choose (CategoryTheory.exists_ext_rightDerived_cocycle_comparison
    ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (uliftYoneda.{u + 1}.obj W ⋙ AddCommGrpCat.free))
    (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (evaluation _ _).obj (op W)) (evaluationRepresented X W)) q

/-- The actual Kummer class over an etale object: precompose the Kummer extension
with the section represented by the unit, then apply the specified coefficient map.
The final inverse is the canonical module/abelian evaluation comparison.
Source: Kummer sequence; blueprint proof Steps 2 and 4
(blueprint: thm-pur-rank-one-local-calculation). -/
def kummerClass (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (m : ℕ)
    (hm : IsUnit (m : Γ(X, ⊤)))
    (f : X.rootsOfUnitySheaf m ⟶ (Etale.moduleAbelianForget A X).obj F)
    (v : Γ(W.left, ⊤)ˣ) : ((sections X.smallEtaleTopology A W).rightDerived 1).obj F := by
  letI := (Etale.module_cohomology_conventions A X).2.1 F W 1
  exact (asIso ((Etale.moduleEvaluationForgetComparison A X W 1).app F)).inv
    ((evaluationExt X W 1).inv.app ((Etale.moduleAbelianForget A X).obj F)
      (((Abelian.Ext.mk₀
        ((EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology W X.gmSheaf).symm
          (ULift.up (Additive.ofMul v)))).comp
            (X.kummerSequence_shortExact m hm).extClass (zero_add 1)).comp
              (Abelian.Ext.mk₀ f) (add_zero 1)))

/-- The section comparison is the actual unit of etale/pro-etale inverse image,
evaluated at the same etale object. Source: blueprint proof Step 7
(blueprint: thm-pur-rank-one-local-calculation). -/
def comparisonSections (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) (W : X.Etale) :
    sections X.smallEtaleTopology A W ⋙ 𝟭 (ModuleCat.{u + 1} A) ⟶
      ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X ⋙
        sections (Scheme.ProEt.topology X) A ((Scheme.toProEt X).obj W) where
  app F := ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app F).hom.app
    (op W)
  naturality F G f := by
    exact congrArg (fun t ↦ t.hom.app (op W))
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X).unit.naturality f)

/-- The canonical higher section comparison, derived from the adjunction unit.
Source: Stacks 099W; blueprint proof Step 7
(blueprint: thm-pur-rank-one-local-calculation). -/
def comparisonCohomology (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (W : X.Etale) (q : ℕ) :=
  Functor.rightDerivedBaseChange
    (G := sections X.smallEtaleTopology A W)
    (G' := sections (Scheme.ProEt.topology X) A ((Scheme.toProEt X).obj W))
    (β := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X)
    (γ := 𝟭 (ModuleCat.{u + 1} A)) (comparisonSections A X W) q

/-- Pullback of a constant unit to the punctured affine line.
Source: blueprint proof Step 5 (blueprint: thm-pur-rank-one-local-calculation). -/
def constantUnit (Ω : Type u) [Field Ω] (c : Ωˣ) :
    Γ(Punctured (Spec (CommRingCat.of Ω)), ⊤)ˣ :=
  Units.map
    (((puncturedProjection (Spec (CommRingCat.of Ω))).appTop.hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom).toMonoidHom c
```

## New

The original module has `public import Sheaf.Paper.PurityRankOneSectionData`. The same names
are now declared there as follows:

```lean
/-- Evaluation on a site object, the section functor used in the support definition.
Source: blueprint proof Step 4 (blueprint: thm-pur-rank-one-local-calculation). -/
abbrev sections {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] (W : C) :=
  sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙ (evaluation _ _).obj (op W)

/-- The recorded open immersion is the inclusion of its basic open.
Source: blueprint affine-line datum (blueprint: thm-pur-rank-one-local-calculation). -/
instance openImmersion_isOpenImmersion (Y : Scheme.{u}) :
    IsOpenImmersion (openImmersion Y) :=
  inferInstanceAs (IsOpenImmersion (((Line Y).basicOpen (coordinate Y)).ι))

/-- The standard punctured-line object of the small etale site.
Source: blueprint proof Step 1 (blueprint: thm-pur-rank-one-local-calculation). -/
def openObject (Y : Scheme.{u}) : (Line Y).Etale :=
  Scheme.Etale.mk (openImmersion Y)

/-- Restriction from the affine line to its punctured open, whose complement is the origin.
Source: blueprint proof Step 4 (blueprint: thm-pur-rank-one-local-calculation). -/
def restriction (Y : Scheme.{u}) : openObject Y ⟶ Scheme.Etale.mk (𝟙 (Line Y)) :=
  MorphismProperty.Over.homMk (openImmersion Y)
    (by change openImmersion Y ≫ 𝟙 (Line Y) = openImmersion Y; simp)

/-- The genuine inverse-image coefficient sheaf on the pro-etale site.
Source: blueprint proof Step 7 (blueprint: thm-pur-rank-one-local-calculation). -/
abbrev proCoefficient (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).obj F

/-- The three complexes in the support sequence, with the actual kernel inclusion and
restriction. Source: Milne, Section 9, Theorem 9.4; blueprint proof Step 4
(blueprint: thm-pur-rank-one-local-calculation). -/
def sectionComplex {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] {V W : C} (j : W ⟶ V)
    (I : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℕ) :
    ShortComplex (CochainComplex (ModuleCat.{u + 1} A) ℕ) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex
      (Sheaf.supportedSectionsInclusion J (ModuleCat.{u + 1} A) j) (.up ℕ)).app I)
    ((NatTrans.mapHomologicalComplex
      ((sheafSections J (ModuleCat.{u + 1} A)).map j.op) (.up ℕ)).app I)
    (by ext n : 1; exact kernel.condition ((I.X n).obj.map j.op))

/-- A support boundary is exactly the snake boundary on injective section complexes,
transported by the canonical resolution comparisons. This characterization rules out
both an arbitrary isomorphism and an arbitrary choice of sign.
Source: Milne, Section 9, Theorem 9.4; blueprint proof Step 4
(blueprint: thm-pur-rank-one-local-calculation). -/
def IsBoundary {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] [HasSheafify J (ModuleCat.{u + 1} A)]
    [EnoughInjectives (Sheaf J (ModuleCat.{u + 1} A))]
    {V W : C} (j : W ⟶ V) (F : Sheaf J (ModuleCat.{u + 1} A))
    (δ : ((sections J A W).rightDerived 1).obj F ⟶
      ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).rightDerived 2).obj F) :
    Prop :=
  ∀ I : InjectiveResolution F, ∃ hI : (sectionComplex J A j I.cocomplex).ShortExact,
    δ = (I.isoRightDerivedObj (sections J A W) 1).hom ≫
      hI.δ 1 2 rfl ≫
      (I.isoRightDerivedObj
        (Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j) 2).inv

/-- Free abelian sheafification represents sections, with its canonical Yoneda map.
Source: Stacks 03F3; blueprint proof Step 2
(blueprint: thm-pur-rank-one-local-calculation). -/
def evaluationRepresented (X : Scheme.{u}) (W : X.Etale) :
    preadditiveCoyoneda.obj (op ((presheafToSheaf X.smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj (uliftYoneda.{u + 1}.obj W ⋙ AddCommGrpCat.free))) ≅
      sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op W) :=
  NatIso.ofComponents
    (fun F ↦ (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology W F).toAddCommGrpIso)
    (by
      intro F G f
      ext a
      exact (EtaleOpenComparison.sectionsEquiv_naturality X.smallEtaleTopology W f a).symm)

/-- The Ext/derived-evaluation comparison normalized on every injective cocycle.
The theorem used here determines the comparison uniquely, since every Ext class has
an injective cocycle representative. No coefficient object is chosen from mere existence.
Source: Stacks 06XR; blueprint proof Step 2
(blueprint: thm-pur-rank-one-local-calculation). -/
@[irreducible]
def evaluationExt (X : Scheme.{u}) (W : X.Etale) (q : ℕ) :
    (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (evaluation _ _).obj (op W)).rightDerived q ≅
        (Abelian.extFunctor q).obj (op ((presheafToSheaf X.smallEtaleTopology
          AddCommGrpCat.{u + 1}).obj (uliftYoneda.{u + 1}.obj W ⋙ AddCommGrpCat.free))) :=
  Classical.choose (CategoryTheory.exists_ext_rightDerived_cocycle_comparison
    ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (uliftYoneda.{u + 1}.obj W ⋙ AddCommGrpCat.free))
    (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (evaluation _ _).obj (op W)) (evaluationRepresented X W)) q

/-- The actual Kummer class over an etale object: precompose the Kummer extension
with the section represented by the unit, then apply the specified coefficient map.
The final inverse is the canonical module/abelian evaluation comparison.
Source: Kummer sequence; blueprint proof Steps 2 and 4
(blueprint: thm-pur-rank-one-local-calculation). -/
@[irreducible]
def kummerClass (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (m : ℕ)
    (hm : IsUnit (m : Γ(X, ⊤)))
    (f : X.rootsOfUnitySheaf m ⟶ (Etale.moduleAbelianForget A X).obj F)
    (v : Γ(W.left, ⊤)ˣ) : ((sections X.smallEtaleTopology A W).rightDerived 1).obj F := by
  letI := (Etale.module_cohomology_conventions A X).2.1 F W 1
  exact (asIso ((Etale.moduleEvaluationForgetComparison A X W 1).app F)).inv
    ((evaluationExt X W 1).inv.app ((Etale.moduleAbelianForget A X).obj F)
      (((Abelian.Ext.mk₀
        ((EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology W X.gmSheaf).symm
          (ULift.up (Additive.ofMul v)))).comp
            (X.kummerSequence_shortExact m hm).extClass (zero_add 1)).comp
              (Abelian.Ext.mk₀ f) (add_zero 1)))

/-- The section comparison is the actual unit of etale/pro-etale inverse image,
evaluated at the same etale object. Source: blueprint proof Step 7
(blueprint: thm-pur-rank-one-local-calculation). -/
def comparisonSections (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) (W : X.Etale) :
    sections X.smallEtaleTopology A W ⋙ 𝟭 (ModuleCat.{u + 1} A) ⟶
      ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X ⋙
        sections (Scheme.ProEt.topology X) A ((Scheme.toProEt X).obj W) where
  app F := ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app F).hom.app
    (op W)
  naturality F G f := by
    exact congrArg (fun t ↦ t.hom.app (op W))
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X).unit.naturality f)

/-- The canonical higher section comparison, derived from the adjunction unit.
Source: Stacks 099W; blueprint proof Step 7
(blueprint: thm-pur-rank-one-local-calculation). -/
@[irreducible]
def comparisonCohomology (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (W : X.Etale) (q : ℕ) :
    (sections X.smallEtaleTopology A W).rightDerived q ⋙ 𝟭 (ModuleCat.{u + 1} A) ⟶
      ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X ⋙
        (sections (Scheme.ProEt.topology X) A ((Scheme.toProEt X).obj W)).rightDerived q :=
  Functor.rightDerivedBaseChange
    (G := sections X.smallEtaleTopology A W)
    (G' := sections (Scheme.ProEt.topology X) A ((Scheme.toProEt X).obj W))
    (β := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X)
    (γ := 𝟭 (ModuleCat.{u + 1} A)) (comparisonSections A X W) q

/-- Pullback of a constant unit to the punctured affine line.
Source: blueprint proof Step 5 (blueprint: thm-pur-rank-one-local-calculation). -/
def constantUnit (Ω : Type u) [Field Ω] (c : Ωˣ) :
    Γ(Punctured (Spec (CommRingCat.of Ω)), ⊤)ˣ :=
  Units.map
    (((puncturedProjection (Spec (CommRingCat.of Ω))).appTop.hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom).toMonoidHom c
```

## Users

`tools/downstream.py Sheaf.Paper.PurityRankOneLocalCalculation --uses sections openObject
restriction proCoefficient sectionComplex IsBoundary evaluationRepresented evaluationExt
kummerClass comparisonSections comparisonCohomology constantUnit` reports 185 downstream
modules. Textual name matches outside this item are only unrelated module sections and prose
in LocalizedTopChern, LocalizedFlagProduct and VectorBundleThomClass, inspected individually.
No downstream code uses the three newly irreducible bodies. The full transitive consumer list
and current claim holders are recorded below; none of these modules is adapted.

| module | group holding it | effect |
|---|---|---|
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | W8 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | X5 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | X6 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | X8 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.CartierClassAgreement | U5 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | G4 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | P2 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | T6 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | S7 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | T7 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | D8 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | E5 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | H8 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | J6 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | E2 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | R3 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | G3 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.PurityDivisorClass | J7 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.PurityDncComparisons | G3 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.PurityFrameIndependence | A4 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.PurityRankOneLocalCalculation | F2 | F2 item: reexports moved definitions and proves the unchanged theorem. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | K6 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.RelativeSupportBottomDescent | A3 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | R2 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | K9 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| TargetsCheck | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.Statement | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Unchanged public signatures and meanings; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Unchanged public signatures and meanings; no adaptation. |

The unchanged direct consumers RelativeSupportBottomDescent, PurityAffineLineOrientation,
and PurityAffineLineOrientationUniqueness compile against the new facade. The fourth direct
consumer, ProjectiveBundleFormula, encounters a stale published import of the retired Sheaf
EtaleOpenCohomologyComparison twin, conflicting with the upstream owner already used by the
current original item source. Its diagnostic is reported in report.md; no consumer adaptation
is made for this published-build mismatch.

## Status

landed 20261019T231138-L-553771 2026-10-19 (merge of deliver/F2/Sheaf.Paper.PurityRankOneLocalCalculation)
