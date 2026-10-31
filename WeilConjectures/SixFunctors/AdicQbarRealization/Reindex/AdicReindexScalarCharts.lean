/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexScalarModels
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexScalarChartVertices
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexScalarChartEquations

/-! # Computation charts for scalar associators and reindexing

Source: Stacks 06YY and 07A4; Bhatt--Scholze, Proposition 6.8.14.
(blueprint: lem-sf-adic-reindex-scalar-charts).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.AdicQbarRealization.completedScalarSheafReindex
  WeilConjectures.AdicQbarRealization.nativeScalarSheafAssociator
  WeilConjectures.AdicQbarRealization.completedScalarReindex
  WeilConjectures.AdicQbarRealization.scalarExactModel
  WeilConjectures.AdicQbarRealization.completedReindexModel

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

/-- Five individual computation squares, over a chosen representative.
Source: the localization argument in steps 1 and 3 of
lem-sf-adic-reindex-balanced-scalar.
(blueprint: lem-sf-adic-reindex-scalar-charts). -/
structure ScalarComputationCharts {D : Type*} [Category D] {ι : Type*}
    (Good : ι → Prop) (V₀ V₁ V₂ V₃ V₄ : D)
    (f₀ : V₀ ⟶ V₁) (f₁ : V₁ ⟶ V₂) (f₂ : V₂ ⟶ V₃)
    (d : V₃ ⟶ V₄) (u : V₀ ⟶ V₄)
    (W₀ W₁ W₂ W₃ W₄ : ι → D)
    (c₀ : ∀ P, W₀ P ⟶ W₁ P) (c₁ : ∀ P, W₁ P ⟶ W₂ P)
    (c₂ : ∀ P, W₂ P ⟶ W₃ P) (c₃ : ∀ P, W₃ P ⟶ W₄ P)
    (c : ∀ P, W₀ P ⟶ W₄ P) where
  P : ι
  good : Good P
  v₀ : V₀ ≅ W₀ P
  v₁ : V₁ ≅ W₁ P
  v₂ : V₂ ≅ W₂ P
  v₃ : V₃ ≅ W₃ P
  v₄ : V₄ ≅ W₄ P
  h₀ : f₀ ≫ v₁.hom = v₀.hom ≫ c₀ P
  h₁ : f₁ ≫ v₂.hom = v₁.hom ≫ c₁ P
  h₂ : f₂ ≫ v₃.hom = v₂.hom ≫ c₂ P
  h₃ : d ≫ v₄.hom = v₃.hom ≫ c₃ P
  h₄ : u ≫ v₄.hom = v₀.hom ≫ c P

/-- Paste the five computation squares and an ordinary rectangle identity.
Source: categorical cancellation in step 3 of lem-sf-adic-reindex-balanced-scalar.
(blueprint: lem-sf-adic-reindex-scalar-charts). -/
theorem ScalarComputationCharts.paste {D : Type*} [Category D] {ι : Type*}
    {Good : ι → Prop} {V₀ V₁ V₂ V₃ V₄ : D}
    {f₀ : V₀ ⟶ V₁} {f₁ : V₁ ⟶ V₂} {f₂ : V₂ ⟶ V₃}
    {d : V₃ ⟶ V₄} {u : V₀ ⟶ V₄}
    {W₀ W₁ W₂ W₃ W₄ : ι → D}
    {c₀ : ∀ P, W₀ P ⟶ W₁ P} {c₁ : ∀ P, W₁ P ⟶ W₂ P}
    {c₂ : ∀ P, W₂ P ⟶ W₃ P} {c₃ : ∀ P, W₃ P ⟶ W₄ P}
    {c : ∀ P, W₀ P ⟶ W₄ P}
    (t : ScalarComputationCharts Good V₀ V₁ V₂ V₃ V₄ f₀ f₁ f₂ d u
      W₀ W₁ W₂ W₃ W₄ c₀ c₁ c₂ c₃ c)
    (d' : V₄ ⟶ V₃) (hd : d ≫ d' = 𝟙 _)
    (hc : c₀ t.P ≫ c₁ t.P ≫ c₂ t.P ≫ c₃ t.P = c t.P) :
    f₀ ≫ f₁ ≫ f₂ = u ≫ d' := by
  have he : (f₀ ≫ f₁ ≫ f₂) ≫ d = u := by
    apply (cancel_mono t.v₄.hom).mp
    simp only [Category.assoc]
    rw [t.h₃, reassoc_of% t.h₂, reassoc_of% t.h₁, reassoc_of% t.h₀, hc, t.h₄]
  have hh := congrArg (fun z ↦ z ≫ d') he
  simpa only [Category.assoc, hd, Category.comp_id] using hh

/-- Paste localized ordinary computation squares using a single functor.
Source: functoriality and categorical cancellation in the scalar rectangle.
(blueprint: lem-sf-adic-reindex-scalar-charts). -/
theorem ScalarComputationCharts.paste_complex {C D : Type*} [Category C]
    [Limits.HasZeroMorphisms C] [Category D] {κ : Type*} (shape : ComplexShape κ)
    {ι : Type*} {Good : ι → Prop} {V₀ V₁ V₂ V₃ V₄ : D}
    {f₀ : V₀ ⟶ V₁} {f₁ : V₁ ⟶ V₂} {f₂ : V₂ ⟶ V₃}
    {d : V₃ ⟶ V₄} {u : V₀ ⟶ V₄}
    {W₀ W₁ W₂ W₃ W₄ : ι → HomologicalComplex C shape}
    {c₀ : ∀ P, W₀ P ⟶ W₁ P} {c₁ : ∀ P, W₁ P ⟶ W₂ P}
    {c₂ : ∀ P, W₂ P ⟶ W₃ P} {c₃ : ∀ P, W₃ P ⟶ W₄ P}
    {c : ∀ P, W₀ P ⟶ W₄ P} (F : HomologicalComplex C shape ⥤ D)
    (t : ScalarComputationCharts Good V₀ V₁ V₂ V₃ V₄ f₀ f₁ f₂ d u
      (fun P ↦ F.obj (W₀ P)) (fun P ↦ F.obj (W₁ P))
      (fun P ↦ F.obj (W₂ P)) (fun P ↦ F.obj (W₃ P)) (fun P ↦ F.obj (W₄ P))
      (fun P ↦ F.map (c₀ P)) (fun P ↦ F.map (c₁ P))
      (fun P ↦ F.map (c₂ P)) (fun P ↦ F.map (c₃ P)) (fun P ↦ F.map (c P)))
    (d' : V₄ ⟶ V₃) (hd : d ≫ d' = 𝟙 _)
    (hc : ∀ n, (c₀ t.P ≫ c₁ t.P ≫ c₂ t.P ≫ c₃ t.P).f n = (c t.P).f n) :
    f₀ ≫ f₁ ≫ f₂ = u ≫ d' := by
  apply t.paste d' hd
  have he := HomologicalComplex.hom_ext _ _ hc
  simpa only [Functor.map_comp] using congrArg F.map he

/-- The ordinary cochain words and the prescribed derived words of the scalar square.
Source: Stacks 06YY and 07A4; BS 6.8.14--6.8.15.
(blueprint: lem-sf-adic-reindex-scalar-charts). -/
abbrev IntegralScalarCharts (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    (B : RingReindex l X g R S)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (be : pbcExtend (coefficientMap l Y S E) ⋙ modulePull l X g B ≅
      podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g ⋙
        pbcExtend (coefficientMap l X R E))
    (bl : pbcExtend (coefficientMap l Y S L) ⋙ modulePull l X g B ≅
      podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) L) g ⋙
        pbcExtend (coefficientMap l X R L))
    (de : pbcDerivedExtend (coefficientMap l Y S E) ⋙ derivedPull l X g B ≅
      podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g ⋙
        pbcDerivedExtend (coefficientMap l X R E))
    (dl : pbcDerivedExtend (coefficientMap l Y S L) ⋙ derivedPull l X g B ≅
      podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) L) g ⋙
        pbcDerivedExtend (coefficientMap l X R L))
    (K : DerivedCategory (integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) E) Y)) :=
    ScalarComputationCharts
      (fun P : CochainComplex (integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) E) Y) ℤ ↦
        Nonempty (DerivedCategory.Q.obj P ≅ K))
      ((pbcDerivedExtend (coefficientMap l X R E)).obj ((podCompletedDerivedInverseImage l
      (Coefficient.{u} l (PadicAlgCl l) E) g).obj K))
      ((pbcDerivedExtend (coefficientMap l X R L)).obj
        ((completedDerivedScalarExtension l (Coefficient.{u} l (PadicAlgCl l) E) (Coefficient.{u}
      l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) X).obj
      ((podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g).obj K)))
      ((pbcDerivedExtend (coefficientMap l X R L)).obj
        ((podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) L) g).obj
      ((completedDerivedScalarExtension l (Coefficient.{u} l (PadicAlgCl l) E) (Coefficient.{u} l
      (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) Y).obj K)))
      ((derivedPull l X g B).obj ((pbcDerivedExtend (coefficientMap l Y S L)).obj
      ((completedDerivedScalarExtension l (Coefficient.{u} l (PadicAlgCl l) E) (Coefficient.{u} l
      (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) Y).obj K)))
      ((derivedPull l X g B).obj ((pbcDerivedExtend (coefficientMap l Y S E)).obj K))
      ((pbcReductionNormalization (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
      (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) X)
      (coefficientMap l X R L) (coefficientMap l X R E) (R.coefficient_scalar E L h))
      ((podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g).obj K)).inv
      ((pbcDerivedExtend (coefficientMap l X R L)).map
        ((completedScalarReindex l (Coefficient.{u} l (PadicAlgCl l) E) (Coefficient.{u} l
      (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) g).hom.app K))
      (dl.inv.app ((completedDerivedScalarExtension l (Coefficient.{u} l (PadicAlgCl l) E)
      (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) Y).obj
      K)) ((derivedPull l X g B).map ((pbcReductionNormalization (completedCoefficientMap l
      (Coefficient.{u} l (PadicAlgCl l) E) (Coefficient.{u} l (PadicAlgCl l) L)
      (coefficientInclusion l (PadicAlgCl l) E L h) Y) (coefficientMap l Y S L) (coefficientMap l
      Y S E) (S.coefficient_scalar E L h)) K).hom) (de.inv.app K)
      (fun P ↦ DerivedCategory.Q.obj
        (((pbcExtend (coefficientMap l X R E)).mapHomologicalComplex (.up ℤ)).obj
          (((podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) E)
      g).mapHomologicalComplex (.up ℤ)).obj P)))
      (fun P ↦ DerivedCategory.Q.obj
        (((pbcExtend (coefficientMap l X R L)).mapHomologicalComplex (.up ℤ)).obj
          (((completedOrdinaryScalarExtension l (Coefficient.{u} l (PadicAlgCl l) E)
      (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h)
      X).mapHomologicalComplex (.up ℤ)).obj
            (((podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) E)
      g).mapHomologicalComplex (.up ℤ)).obj P))))
      (fun P ↦ DerivedCategory.Q.obj
        (((pbcExtend (coefficientMap l X R L)).mapHomologicalComplex (.up ℤ)).obj
          (((podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) L)
      g).mapHomologicalComplex (.up ℤ)).obj
            (((completedOrdinaryScalarExtension l (Coefficient.{u} l (PadicAlgCl l) E)
      (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h)
      Y).mapHomologicalComplex (.up ℤ)).obj P))))
      (fun P ↦ DerivedCategory.Q.obj
        (((modulePull l X g B).mapHomologicalComplex (.up ℤ)).obj
          (((pbcExtend (coefficientMap l Y S L)).mapHomologicalComplex (.up ℤ)).obj
            (((completedOrdinaryScalarExtension l (Coefficient.{u} l (PadicAlgCl l) E)
      (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h)
      Y).mapHomologicalComplex (.up ℤ)).obj P))))
      (fun P ↦ DerivedCategory.Q.obj
        (((modulePull l X g B).mapHomologicalComplex (.up ℤ)).obj
          (((pbcExtend (coefficientMap l Y S E)).mapHomologicalComplex (.up ℤ)).obj P)))
      (fun P ↦ DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (nativeScalarSheafAssociator l X R E L h) (.up
      ℤ)).inv.app
          (((podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) E)
      g).mapHomologicalComplex (.up ℤ)).obj P)))
      (fun P ↦ DerivedCategory.Q.map
        (((pbcExtend (coefficientMap l X R L)).mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex (completedScalarSheafReindex l (Coefficient.{u} l
      (PadicAlgCl l) E) (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl
      l) E L h) g) (.up ℤ)).hom.app P)))
      (fun P ↦ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex bl (.up ℤ)).inv.app
          (((completedOrdinaryScalarExtension l (Coefficient.{u} l (PadicAlgCl l) E)
      (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h)
      Y).mapHomologicalComplex (.up ℤ)).obj P)))
      (fun P ↦ DerivedCategory.Q.map
        (((modulePull l X g B).mapHomologicalComplex (.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso (nativeScalarSheafAssociator l Y S E L h) (.up
      ℤ)).hom.app P)))
      (fun P ↦ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex be (.up ℤ)).inv.app P))

/-- The individual comparison maps are computed by their ordinary cochain models.
No section normalization or commutativity of the ordinary rectangle is assumed:
the balance isomorphisms here are arbitrary, subject only to their representative
normalizations. Thus this is a comparison-of-models assertion, independent of the
pure-tensor rectangle equation.
Source: Stacks 06YY, 07A4; BS 6.8.14--6.8.15; steps 1 and 3 of
lem-sf-adic-reindex-balanced-scalar.
(blueprint: lem-sf-adic-reindex-scalar-charts).

Proof in words: take a flat-term K-flat representative P of K. Exact reindexing
preserves this class, and finite coefficient extension takes it to flat-term
K-flat complexes. At each of the five vertices, use the universal scalar
computation counits, exact inverse-image factorization, and the chosen
representative isomorphism to identify the derived word with the localization
of the ordinary word. For the two vertical balance edges the equations are
precisely hE and hL, inverted and whiskered. For scalar reindexing, expand its
five defining isomorphisms; the scalarExactModel counit normalization and the
exact-derived square factors identify its edge with the ordinary scalar sheaf
reindexing. The remaining two edges are the representative equations for the
unit-normalized derived tensor associators. These follow by deriving the ordinary
unit-normalized adjunctions on the same resolving complexes. Naturality transports
all five individual equations along Q(P) isomorphic to K. This proves the charts
without using or asserting any relation among the five ordinary edges. -/
theorem integralReindex_scalar_charts (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    (B : RingReindex l X g R S)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (be : pbcExtend (coefficientMap l Y S E) ⋙ modulePull l X g B ≅
      podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g ⋙
        pbcExtend (coefficientMap l X R E))
    (bl : pbcExtend (coefficientMap l Y S L) ⋙ modulePull l X g B ≅
      podCompletedModuleInverseImage l (Coefficient.{u} l (PadicAlgCl l) L) g ⋙
        pbcExtend (coefficientMap l X R L))
    (de : pbcDerivedExtend (coefficientMap l Y S E) ⋙ derivedPull l X g B ≅
      podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g ⋙
        pbcDerivedExtend (coefficientMap l X R E))
    (dl : pbcDerivedExtend (coefficientMap l Y S L) ⋙ derivedPull l X g B ≅
      podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) L) g ⋙
        pbcDerivedExtend (coefficientMap l X R L))
    (hE : integralReindexRepresentative l X g B E be de)
    (hL : integralReindexRepresentative l X g B L bl dl)
    (K : DerivedCategory (integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) E) Y)) :
    Nonempty (IntegralScalarCharts l g R S B E L h be bl de dl K) := by
  classical
  let A := DerivedCategory.Q.objPreimage K
  obtain ⟨P, f, hp, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients A
  have := hq
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := completedIntegralCommRingSheafUnrestricted l
        (Coefficient.{u} l (PadicAlgCl l) E) Y) (P.X n) := fun n ↦
    (CategoryTheory.exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso _ (P.X n)).symm (hf n)
  let t := adicScalarChartVertices l g R S B E L h be bl de dl K P e hp hflat
  obtain ⟨a⟩ := adic_scalar_chart_equations l g R S B E L h be bl de dl hE hL
    K P e hp hflat
  refine ⟨?_⟩
  exact {
    P := t.P
    good := t.good
    v₀ := t.v₀
    v₁ := t.v₁
    v₂ := t.v₂
    v₃ := t.v₃
    v₄ := t.v₄
    h₀ := a.h₀
    h₁ := a.h₁
    h₂ := a.h₂
    h₃ := a.h₃
    h₄ := a.h₄ }

end WeilConjectures.AdicQbarRealization
