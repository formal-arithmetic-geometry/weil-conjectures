/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SupportLongExact
public import Sheaf.Paper.PurityAffineLineDatum
public import Sheaf.AlgebraicGeometry.ModuleCohomologyConventions
public import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyComparison
public import WeilConjectures.CategoryTheory.Abelian.ExtRightDerivedCocycleComparison
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

import WeilConjectures.AlgebraicGeometry.Sites.Kummer

/-!
# The finite rank-one Kummer residue

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
`thm-pur-rank-one-local-calculation` (blueprint: thm-pur-rank-one-local-calculation).

The boundary below is specified by the snake boundary of the actual section complexes
of every injective resolution. In particular its sign is fixed. Module-valued derived
sections retain the coefficient action, so the normalization and its uniqueness are linear.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting.RankOne

/-- Evaluation on a site object, the section functor used in the support definition.
Source: blueprint proof Step 4 (blueprint: thm-pur-rank-one-local-calculation). -/
abbrev sections {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] (W : C) :=
  sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙ (evaluation _ _).obj (op W)

/-- Curried evaluation has the same additive structure as the explicit section functor.
Source: functor composition and pointwise addition
(blueprint: def-pur-rank-one-local-data). -/
instance sheafSections_obj_additive
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] (W : C) :
    ((sheafSections J (ModuleCat.{u + 1} A)).obj (op W)).Additive :=
  inferInstanceAs ((sections J A W).Additive)

/-- Curried evaluation preserves finite limits, as explicit evaluation does.
Source: limits of sheaves and pointwise evaluation
(blueprint: def-pur-rank-one-local-data). -/
instance sheafSections_obj_preservesFiniteLimits
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] (W : C) :
    PreservesFiniteLimits ((sheafSections J (ModuleCat.{u + 1} A)).obj (op W)) :=
  inferInstanceAs (PreservesFiniteLimits (sections J A W))

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
@[reducible] def sectionComplex {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] {V W : C} (j : W ⟶ V)
    (I : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℕ) :
    ShortComplex (CochainComplex (ModuleCat.{u + 1} A) ℕ) :=
  { X₁ := ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).mapHomologicalComplex
      (.up ℕ)).obj I
    X₂ := ((sections J A V).mapHomologicalComplex (.up ℕ)).obj I
    X₃ := ((sections J A W).mapHomologicalComplex (.up ℕ)).obj I
    f := ((NatTrans.mapHomologicalComplex
      (Sheaf.supportedSectionsInclusion J (ModuleCat.{u + 1} A) j) (.up ℕ)).app I)
    g := ((NatTrans.mapHomologicalComplex
      ((sheafSections J (ModuleCat.{u + 1} A)).map j.op) (.up ℕ)).app I)
    zero := by ext n : 1; exact kernel.condition ((I.X n).obj.map j.op) }

/-- The adjacent nonnegative support degrees, used to keep the snake-boundary
index proof stable under rewriting. Source: the support sequence, Step 4
(blueprint: thm-pur-rank-one-local-calculation). -/
theorem support_degree_relation : (ComplexShape.up ℕ).Rel 1 2 := rfl

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
      hI.δ 1 2 support_degree_relation ≫
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

end WeilConjectures.PurityFiniteSetting.RankOne
