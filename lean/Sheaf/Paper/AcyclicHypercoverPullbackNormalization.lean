/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleHypercoverAugmentation
public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleOrdinaryPullbackComparison
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.SiteHypercoverDisjointUnion
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory

import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Sheaf.CategoryTheory.RingedHypercoverInjectiveAugmentationRing
import Sheaf.Algebra.Homology.BoundedBelowAugmentation
import Sheaf.Algebra.Homology.BoundedBelowTotalComparison
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.CategoryTheory.KInjectiveDerivedMapComputation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition

/-!
# Augmentation-normalized acyclic hypercover pullback

Source: Stacks Project, proetale.tex, Tag 09A2, lemma-compute-cohomology;
its injective-resolution proof and the functorial restriction augmentations.

## Main statements

* `descent`: the four resolution and augmentation quasi-isomorphisms (on each site)
  and the unique natural comparison normalized by every injective resolution.
* `pullback_normalization`: the actual derived-unit square.
* `comparison_refinement`, `restriction_refinement`, `restriction_comp`: the
  refinement and composition clauses of the same comparison statement.
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.AcyclicHypercover

/-- Evaluation with scalars forgotten. Source: Stacks, Tag 09A2
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization). -/
def sections (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (W : X.ProEt) : proEtaleRingModules X R ⥤ AddCommGrpCat.{u + 1} :=
  SheafOfModules.evaluation _ (op W) ⋙ forget₂ (ModuleCat _) AddCommGrpCat

/-- Evaluation is additive. Source: Stacks, Tag 09A2
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization). -/
instance sections_additive (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (W : X.ProEt) :
    (sections X R W).Additive where
  map_add := by intros; rfl

/-- Alternating coface sections with scalars forgotten, extended by zero to integers.
Source: Stacks, Tag 09A2
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization). -/
def rows (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (W : X.ProEt) (U : SimplicialObject (Over W)) :=
  ProEt.hypercoverSectionRows X R W U ⋙
    (forget₂ (ModuleCat _) AddCommGrpCat).mapHomologicalComplex (.up ℤ)

/-- The signed total from the recorded total functor, followed by forgetting scalars.
Source: Stacks, Tag 09A2
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization). -/
def total (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (W : X.ProEt) (U : SimplicialObject (Over W)) :=
  ProEt.hypercoverTotal X R W U ⋙
    (forget₂ (ModuleCat _) AddCommGrpCat).mapHomologicalComplex (.up ℤ)

/-- The specified restriction augmentation, with scalars forgotten.
Source: Stacks, Tag 09A2
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization). -/
def augmentation (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (W : X.ProEt) (U : SimplicialObject (Over W)) :
    (sections X R W).mapHomologicalComplex (.up ℤ) ⟶ total X R W U :=
  Functor.whiskerRight (ProEt.hypercoverAugmentation X R W U)
    ((forget₂ (ModuleCat _) AddCommGrpCat).mapHomologicalComplex (.up ℤ))

/-- The coefficient-resolution map from a section row into the signed total, degreewise.
It uses the coefficient-degree-zero map and the (n,0) total injection.
Source: Stacks, Tag 09A2
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization). -/
def rowResolutionComponent (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (W : X.ProEt)
    (U : SimplicialObject (Over W)) (M : proEtaleRingModules X R)
    (I : CochainComplex (proEtaleRingModules X R) ℤ)
    (i : (HomologicalComplex.single _ (.up ℤ) 0).obj M ⟶ I) (n : ℤ) :
    ((rows X R W U).obj M).X n ⟶ ((total X R W U).obj I).X n :=
  (forget₂ (ModuleCat _) AddCommGrpCat).map
    ((((ProEt.hypercoverSectionRows X R W U).map
      ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv ≫ i.f 0)).f n) ≫
      (HomologicalComplex₂.flip
        (((ProEt.hypercoverSectionRows X R W U).mapHomologicalComplex (.up ℤ)).obj I)).ιTotal
          (.up ℤ) n 0 n (by simp))

/-- The resolution map commutes with the total differential.
Source: Stacks, Tag 09A2
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization).
Proof: the horizontal identity is naturality of the alternating section-row functor.
The vertical differential kills i^0 since i is a chain map from M[0]. The remaining
signed differential therefore agrees with the row differential on every total injection. -/
theorem rowResolutionComponent_comm (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (W : X.ProEt)
    (U : SimplicialObject (Over W)) (M : proEtaleRingModules X R)
    (I : CochainComplex (proEtaleRingModules X R) ℤ)
    (i : (HomologicalComplex.single _ (.up ℤ) 0).obj M ⟶ I) (n m : ℤ) :
    rowResolutionComponent X R W U M I i n ≫ ((total X R W U).obj I).d n m =
      ((rows X R W U).obj M).d n m ≫ rowResolutionComponent X R W U M I i m := by
  sorry

/-- The coefficient-resolution map C_U(M) to T_U(I), using the actual section maps.
Source: Stacks, Tag 09A2
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization). -/
def rowResolution (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (W : X.ProEt)
    (U : SimplicialObject (Over W)) (M : proEtaleRingModules X R)
    (I : CochainComplex (proEtaleRingModules X R) ℤ)
    (i : (HomologicalComplex.single _ (.up ℤ) 0).obj M ⟶ I) :
    (rows X R W U).obj M ⟶ (total X R W U).obj I where
  f := rowResolutionComponent X R W U M I i
  comm' n m _ := rowResolutionComponent_comm X R W U M I i n m

/-- The row is the total of the coefficient sheaf placed in degree zero.
Source: Stacks, Tag 09A2, the displayed section complex and its double complex
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization).
Proof: in total degree n the single coefficient complex has only the (n,0) summand.
The total injection is therefore an isomorphism with inverse its projection. The
single-object identification identifies its row differential with the alternating
coface differential; negative-degree source and target are zero. -/
theorem rowResolution_single_isIso (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (W : X.ProEt)
    (U : SimplicialObject (Over W)) (M : proEtaleRingModules X R) :
    IsIso (rowResolution X R W U M
      ((HomologicalComplex.single _ (.up ℤ) 0).obj M) (𝟙 _)) := by
  sorry

/-- The canonical row-to-single-total identification, with its specified total injection.
Source: Stacks, Tag 09A2
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization). -/
def rowSingleTotalIso (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (W : X.ProEt)
    (U : SimplicialObject (Over W)) (M : proEtaleRingModules X R) :
    (rows X R W U).obj M ≅
      (total X R W U).obj ((HomologicalComplex.single _ (.up ℤ) 0).obj M) :=
  letI := rowResolution_single_isIso X R W U M
  asIso (rowResolution X R W U M
    ((HomologicalComplex.single _ (.up ℤ) 0).obj M) (𝟙 _))

/-- The resolution arrow is precisely the total of i after the single-total identification.
Source: Stacks, Tag 09A2, the coefficient-resolution double complex
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization).
Proof: naturality of the total injection in coefficient complexes identifies both
maps on the unique nonzero coefficient summand. The two degree-zero single-object
identifications cancel, leaving the specified map i in every row degree. -/
theorem rowResolution_eq_total_map (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (W : X.ProEt)
    (U : SimplicialObject (Over W)) (M : proEtaleRingModules X R)
    (I : CochainComplex (proEtaleRingModules X R) ℤ)
    (i : (HomologicalComplex.single _ (.up ℤ) 0).obj M ⟶ I) :
    (rowSingleTotalIso X R W U M).hom ≫ (total X R W U).map i =
      rowResolution X R W U M I i := by
  sorry

/-- Derived sections of a sheaf placed in degree zero.
Source: Stacks, Tag 09A2
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization). -/
def derivedSectionsZero (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  HomologicalComplex.single (proEtaleRingModules X R) (.up ℤ) 0 ⋙ DerivedCategory.Q ⋙
    (sections X R (⊤_ X.ProEt)).rightDerivedFunctor

/-- Computation on any of the specified bounded-below injective resolutions.
Source: Stacks, Tag 09A2, and Derived Categories, Tag 070I
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization). -/
def resolutionSectionsIso (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (M : proEtaleRingModules X R)
    (N : ℤ) (I : CochainComplex (proEtaleRingModules X R) ℤ)
    [I.IsStrictlyGE N] [∀ n : ℤ, Injective (I.X n)]
    (i : (HomologicalComplex.single _ (.up ℤ) 0).obj M ⟶ I) [QuasiIso i] :
    (derivedSectionsZero X R).obj M ≅
      DerivedCategory.Q.obj (((sections X R (⊤_ X.ProEt)).mapHomologicalComplex (.up ℤ)).obj I) :=
  letI := CochainComplex.isKInjective_of_injective I N
  (sections X R (⊤_ X.ProEt)).rightDerivedFunctor.mapIso (asIso (DerivedCategory.Q.map i)) ≪≫
    (sections X R (⊤_ X.ProEt)).rightDerivedFunctorObjQIso I

/-- The augmentation-normalization equation for every bounded-below injective resolution.
It characterizes a comparison uniquely and records resolution independence.
Source: Stacks, Tag 09A2
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization). -/
def IsNormalized (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (U : SimplicialObject (Over (⊤_ X.ProEt)))
    (A : derivedSectionsZero X R ≅ rows X R (⊤_ X.ProEt) U ⋙ DerivedCategory.Q) : Prop :=
  ∀ (M : proEtaleRingModules X R) (N : ℤ)
    (I : CochainComplex (proEtaleRingModules X R) ℤ)
    [I.IsStrictlyGE N] [∀ n : ℤ, Injective (I.X n)]
    (i : (HomologicalComplex.single _ (.up ℤ) 0).obj M ⟶ I) [QuasiIso i],
    A.hom.app M ≫ DerivedCategory.Q.map (rowResolution X R (⊤_ X.ProEt) U M I i) =
      (resolutionSectionsIso X R M N I i).hom ≫
        DerivedCategory.Q.map ((augmentation X R (⊤_ X.ProEt) U).app I)

/-- Acyclic hypercover descent with the specified augmentations and every injective resolution.
Source: Stacks, Tag 09A2, lemma-compute-cohomology, injective-resolution proof
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization).

Proof: (1) The section rows and signed totals use delta+(-1)^p d. The resolution
maps and augmentations are the actual restrictions into the indicated total summands.
(2) The module forgetful functor is exact (lem-weil-pbc-module-sheaves-colimits-forgetful).
Module epimorphisms are locally surjective as abelian sheaves, hence epimorphisms of set
sheaves (lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective and
lem-weil-pbc-site-sheaf-sets-epi-locally-surjective). Weak contractibility makes evaluation
exact. This applies to nonaffine terms as well.
(3) Pull matching covers back along test matching families. The site axioms and
subcanonicity hold by det-pe-topos-functoriality-site. Apply
lem-sc-ringed-hypercover-injective-augmentation-ring to each injective coefficient term.
Bounded-below row augmentation (lem-weil-pbc-bounded-below-row-augmentation) makes alpha_I
a quasi-isomorphism. (4) Exact evaluation and bounded-below column comparison
(lem-weil-pbc-bounded-below-total-column-comparison) make the resolution map a
quasi-isomorphism; only finite effective diagonals occur.
(5) Bounded-below injective complexes are K-injective
(lem-weil-pbc-bounded-below-injectives-kinjective). Compare any two resolutions by the
K-injective Hom bijection (lem-weil-pbc-kinjective-hom-derived). Applying total sections
to a coefficient homotopy uses (-1)^p times that homotopy on bidegree (p,q); the mixed
terms cancel. The augmentation square commutes. Cancelling the two quasi-isomorphisms
therefore identifies the zigzags for every resolution. The canonical resolution
computation is lem-sf-kinjective-derived-map-computation, using
def-sfb-right-derived-functor and prop-pur-kinjective-resolutions-exist. The same
calculation for coefficient maps gives naturality and uniqueness of the natural iso. -/
theorem descent (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (U : SimplicialObject (Over (⊤_ X.ProEt)))
    (hcover : ∀ (n : ℕ) (T : Over (⊤_ X.ProEt)) (μ : U _⦋n⦌ ⟶ T),
      SimplicialObject.IsProperFaceMatchingArrow U n T μ →
        Sieve.generate (Presieve.singleton μ.left) ∈ ProEt.topology X T.left)
    (hweak : ∀ n : ℕ, (ProEt.topology X).IsWeaklyContractible.{u + 1} (U _⦋n⦌).left) :
    (∀ (M : proEtaleRingModules X R) (N : ℤ)
      (I : CochainComplex (proEtaleRingModules X R) ℤ)
      [I.IsStrictlyGE N] [∀ n : ℤ, Injective (I.X n)]
      (i : (HomologicalComplex.single _ (.up ℤ) 0).obj M ⟶ I) [QuasiIso i],
      QuasiIso (rowResolution X R (⊤_ X.ProEt) U M I i) ∧
        QuasiIso ((augmentation X R (⊤_ X.ProEt) U).app I)) ∧
    ∃! A : derivedSectionsZero X R ≅ rows X R (⊤_ X.ProEt) U ⋙ DerivedCategory.Q,
      IsNormalized X R U A := by
  sorry

/-- The unique augmentation-normalized comparison, natural in coefficients.
The universal normalization equation determines this object; no arbitrary map is chosen.
Source: Stacks, Tag 09A2
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization). -/
def comparison (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (U : SimplicialObject (Over (⊤_ X.ProEt)))
    (hcover : ∀ (n : ℕ) (T : Over (⊤_ X.ProEt)) (μ : U _⦋n⦌ ⟶ T),
      SimplicialObject.IsProperFaceMatchingArrow U n T μ →
        Sieve.generate (Presieve.singleton μ.left) ∈ ProEt.topology X T.left)
    (hweak : ∀ n : ℕ, (ProEt.topology X).IsWeaklyContractible.{u + 1} (U _⦋n⦌).left) :
    derivedSectionsZero X R ≅ rows X R (⊤_ X.ProEt) U ⋙ DerivedCategory.Q :=
  Classical.choose (descent X R U hcover hweak).2.exists

/-- Refinement is ordinary restriction on the slice, then alternating cofaces,
extension by zero, and forgetting scalars. Source: Stacks, Tag 09A2
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization). -/
def refinement (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (W : X.ProEt) (U U' : SimplicialObject (Over W)) (r : U' ⟶ U)
    (M : proEtaleRingModules X R) : (rows X R W U).obj M ⟶ (rows X R W U').obj M :=
  ((forget₂ (ModuleCat _) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
    ((ComplexShape.embeddingUpNat.extendFunctor _).map
      ((AlgebraicTopology.alternatingCofaceMapComplex _).map
        (Functor.whiskerRight r.rightOp
          ((PresheafOfModules.forgetToPresheafModuleCat (op (Over.mk (𝟙 W)))
            Over.mkIdTerminal.op).obj
              ((PresheafOfModules.pushforward₀ (Over.forget W) _).obj M.val)))))

variable {X Y : Scheme.{u}} (h : Y ⟶ X)
  (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S)

/-- Restriction over h is the actual normalized module unit followed by restriction
along V to the base change of U. Source: Stacks, Tag 09A2, functoriality refinement
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization). -/
def sectionRestriction (M : proEtaleRingModules X R) (U : X.ProEt) (V : Y.ProEt)
    (g : V ⟶ (proEtaleBaseChange h).obj U) :
    (sections X R U).obj M ⟶
      (sections Y S V).obj ((proEtaleRingModulePullback h R S c).obj M) :=
  (forget₂ (ModuleCat _) AddCommGrpCat).map
      (((proEtaleRingModuleAdjunction h R S c).unit.app M).val.app (op U)) ≫
    ((proEtaleRingModulePullback h R S c).obj M).val.presheaf.map g.op

/-- The degreewise section restriction, using the canonical extension-by-zero
identifications. Source: Stacks, Tag 09A2, functoriality refinement
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization). -/
def restrictionComponent (W : X.ProEt) (Z : Y.ProEt)
    (U : SimplicialObject (Over W)) (V : SimplicialObject (Over Z))
    (g : V ⋙ Over.forget Z ⟶ U ⋙ Over.forget W ⋙ proEtaleBaseChange h)
    (M : proEtaleRingModules X R) :
    ∀ n : ℤ, ((rows X R W U).obj M).X n ⟶
      ((rows Y S Z V).obj ((proEtaleRingModulePullback h R S c).obj M)).X n
  | .ofNat n =>
    (forget₂ (ModuleCat _) AddCommGrpCat).map
        ((((AlgebraicTopology.alternatingCofaceMapComplex _).obj
          ((ProEt.hypercoverSections X R W U).obj M)).extendXIso
            ComplexShape.embeddingUpNat (i := n) rfl).hom) ≫
      sectionRestriction h R S c M (U _⦋n⦌).left (V _⦋n⦌).left (g.app (op ⦋n⦌)) ≫
      (forget₂ (ModuleCat _) AddCommGrpCat).map
        ((((AlgebraicTopology.alternatingCofaceMapComplex _).obj
          ((ProEt.hypercoverSections Y S Z V).obj
            ((proEtaleRingModulePullback h R S c).obj M))).extendXIso
              ComplexShape.embeddingUpNat (i := n) rfl).inv)
  | .negSucc _ => 0

/-- The actual section restrictions commute with the alternating differential.
Source: Stacks, Tag 09A2, functoriality refinement
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization).
Proof: naturality of the ordinary module unit and of g gives commutation with
individual face restrictions. Sum with coefficients (-1)^i. Extension by zero
has zero differentials at negative degrees, including the transition -1 to 0. -/
theorem restrictionComponent_comm (W : X.ProEt) (Z : Y.ProEt)
    (U : SimplicialObject (Over W)) (V : SimplicialObject (Over Z))
    (g : V ⋙ Over.forget Z ⟶ U ⋙ Over.forget W ⋙ proEtaleBaseChange h)
    (M : proEtaleRingModules X R) (i j : ℤ) :
    restrictionComponent h R S c W Z U V g M i ≫
        ((rows Y S Z V).obj ((proEtaleRingModulePullback h R S c).obj M)).d i j =
      ((rows X R W U).obj M).d i j ≫ restrictionComponent h R S c W Z U V g M j := by
  sorry

/-- The actual alternating section cochain map c_g, extended by zero in negative degrees.
Source: Stacks, Tag 09A2, restriction functoriality refinement
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization). -/
def restriction (W : X.ProEt) (Z : Y.ProEt)
    (U : SimplicialObject (Over W)) (V : SimplicialObject (Over Z))
    (g : V ⋙ Over.forget Z ⟶ U ⋙ Over.forget W ⋙ proEtaleBaseChange h)
    (M : proEtaleRingModules X R) :
    (rows X R W U).obj M ⟶
      (rows Y S Z V).obj ((proEtaleRingModulePullback h R S c).obj M) where
  f := restrictionComponent h R S c W Z U V g M
  comm' i j _ := restrictionComponent_comm h R S c W Z U V g M i j

/-- The sectionwise direct image has the canonical terminal-object section comparison.
Source: Stacks, Tags 09A2 and 0D6E
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization). -/
def directSectionsIso :
    proEtaleRingModuleDirectImage h R S c ⋙ sections X R (⊤_ X.ProEt) ≅
      sections Y S (⊤_ Y.ProEt) :=
  NatIso.ofComponents (fun N ↦ N.val.presheaf.mapIso
    (terminalIsTerminal.uniqueUpToIso
      ((terminalIsTerminal (C := X.ProEt)).isTerminalObj (proEtaleBaseChange h) _)).op)
    (by
      intro N N' f
      ext m
      exact (PresheafOfModules.naturality_apply f.val
        (terminalIsTerminal.uniqueUpToIso
          ((terminalIsTerminal (C := X.ProEt)).isTerminalObj
            (proEtaleBaseChange h) _)).hom.op m).symm)

/-- The actual right adjoint preserves K-injectives because its left adjoint is exact.
Source: Stacks, Tag 08BJ
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization). -/
instance directImage_preservesKInjective :
    (proEtaleRingModuleDirectImage h R S c).PreservesKInjectiveComplexes :=
  (proEtaleRingModuleAdjunction h R S c).preservesKInjectiveComplexes

/-- The actual derived-unit pullback followed by the canonical composition comparison.
The last factor identifies termwise pullback of M[0] with (h*M)[0].
Source: Stacks, Tags 0DVC and 0D6E
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization). -/
def derivedSectionPullback (M : proEtaleRingModules X R) :
    (sections X R (⊤_ X.ProEt)).rightDerivedFunctor.obj
        (DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) ⟶
      (sections Y S (⊤_ Y.ProEt)).rightDerivedFunctor.obj
        (DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj
          ((proEtaleRingModulePullback h R S c).obj M))) :=
  (sections X R (⊤_ X.ProEt)).rightDerivedFunctor.map
      ((proEtaleRingDerivedAdjunction h R S c).unit.app
        (DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj M))) ≫
    (Functor.rightDerivedFunctorCompIso' (proEtaleRingModuleDirectImage h R S c)
      (sections X R (⊤_ X.ProEt)) (directSectionsIso h R S c)).hom.app
        ((proEtaleRingDerivedPullback h R S c).obj
          (DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj M))) ≫
    (sections Y S (⊤_ Y.ProEt)).rightDerivedFunctor.map
      ((proEtaleRingDerivedPullbackFactors h R S c).hom.app
        ((HomologicalComplex.single _ (.up ℤ) 0).obj M) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex
            (proEtaleRingModulePullback h R S c) (.up ℤ) 0).hom.app M))

/-- The hypercover map is the actual unit-induced derived-section pullback.
Source: Stacks Project, Tag 09A2, with the stated functoriality refinement
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization).

Proof: steps 1--5 of descent give the two normalized comparison zigzags. For step 6,
choose a chain map b:h*I to J lifting the resolution of h*M, by the K-injective Hom
bijection. Its adjoint a:I to h_*J is h_*b after the ordinary unit. Exactness of h*
and lem-weil-pbc-right-adjoint-preserves-kinjective make h_*J K-injective.
The representative formula of lem-pc-pre-derived-adjoint-functors-general, with
identity left resolution, identifies Q(a) after Q(i) inverse with the actual derived
unit. Naturality of the ordinary unit gives a i homotopic to h_*j after that unit.
For step 7, restriction along g followed by b defines G:T_U(I) to T_V(J).
The signed total homotopy from step 5 gives G T_U(i)=T_V(j)c_g in the derived category.
The augmentation square G alpha_I=alpha_J Gamma(a) commutes strictly, because both
maps restrict a section along V_0 to X and apply b; the other columns vanish.
Apply lem-weil-pbc-ringed-topoi-derived-pushforward-composition to h followed by
global sections. On the K-injective h_*J its composition comparison is precisely
the terminal-object section identification (take the identity resolution).
lem-sf-kinjective-derived-map-computation identifies Gamma(a) with the specified
unit-induced map. Cancel the four quasi-isomorphisms from descent. This gives the
displayed square, without assuming g is cartesian or inverting its restriction map. -/
theorem pullback_normalization
    (U : SimplicialObject (Over (⊤_ X.ProEt)))
    (V : SimplicialObject (Over (⊤_ Y.ProEt)))
    (hU : ∀ (n : ℕ) (T : Over (⊤_ X.ProEt)) (μ : U _⦋n⦌ ⟶ T),
      SimplicialObject.IsProperFaceMatchingArrow U n T μ →
        Sieve.generate (Presieve.singleton μ.left) ∈ ProEt.topology X T.left)
    (wU : ∀ n : ℕ, (ProEt.topology X).IsWeaklyContractible.{u + 1} (U _⦋n⦌).left)
    (hV : ∀ (n : ℕ) (T : Over (⊤_ Y.ProEt)) (μ : V _⦋n⦌ ⟶ T),
      SimplicialObject.IsProperFaceMatchingArrow V n T μ →
        Sieve.generate (Presieve.singleton μ.left) ∈ ProEt.topology Y T.left)
    (wV : ∀ n : ℕ, (ProEt.topology Y).IsWeaklyContractible.{u + 1} (V _⦋n⦌).left)
    (g : V ⋙ Over.forget (⊤_ Y.ProEt) ⟶
      U ⋙ Over.forget (⊤_ X.ProEt) ⋙ proEtaleBaseChange h)
    (M : proEtaleRingModules X R) :
    (comparison X R U hU wU).hom.app M ≫
        DerivedCategory.Q.map (restriction h R S c _ _ U V g M) =
      derivedSectionPullback h R S c M ≫
        (comparison Y S V hV wV).hom.app ((proEtaleRingModulePullback h R S c).obj M) := by
  sorry

/-- The restriction maps form a natural transformation in the coefficient sheaf.
Source: Stacks, Tag 09A2, functoriality refinement
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization).
Proof: the ordinary unit is natural in M and restrictions commute with coefficient maps
on each simplex. The extension identifications are natural too. Thus the chain maps
commute in each degree, including negative degrees where the source and target vanish. -/
theorem restriction_naturality (W : X.ProEt) (Z : Y.ProEt)
    (U : SimplicialObject (Over W)) (V : SimplicialObject (Over Z))
    (g : V ⋙ Over.forget Z ⟶ U ⋙ Over.forget W ⋙ proEtaleBaseChange h)
    {M L : proEtaleRingModules X R} (f : M ⟶ L) :
    (rows X R W U).map f ≫ restriction h R S c W Z U V g L =
      restriction h R S c W Z U V g M ≫
        (rows Y S Z V).map ((proEtaleRingModulePullback h R S c).map f) := by
  sorry

/-- Normalized comparisons commute with refinements on either site.
Source: Stacks, Tag 09A2, functoriality refinement
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization).
Proof: for each coefficient complex, refinement commutes strictly with its coefficient
map and its restriction augmentation. Cancel the resolution and augmentation
quasi-isomorphisms in the two normalized zigzags. This is proof step 8; applying it
to either X or X' gives refinement compatibility on both sides of the pullback square. -/
theorem comparison_refinement (T : Scheme.{u})
    (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (U U' : SimplicialObject (Over (⊤_ T.ProEt)))
    (hU : ∀ (n : ℕ) (Z : Over (⊤_ T.ProEt)) (μ : U _⦋n⦌ ⟶ Z),
      SimplicialObject.IsProperFaceMatchingArrow U n Z μ →
        Sieve.generate (Presieve.singleton μ.left) ∈ ProEt.topology T Z.left)
    (wU : ∀ n : ℕ, (ProEt.topology T).IsWeaklyContractible.{u + 1} (U _⦋n⦌).left)
    (hU' : ∀ (n : ℕ) (Z : Over (⊤_ T.ProEt)) (μ : U' _⦋n⦌ ⟶ Z),
      SimplicialObject.IsProperFaceMatchingArrow U' n Z μ →
        Sieve.generate (Presieve.singleton μ.left) ∈ ProEt.topology T Z.left)
    (wU' : ∀ n : ℕ, (ProEt.topology T).IsWeaklyContractible.{u + 1} (U' _⦋n⦌).left)
    (r : U' ⟶ U) (M : proEtaleRingModules T A) :
    (comparison T A U hU wU).hom.app M ≫
        DerivedCategory.Q.map (refinement T A _ U U' r M) =
      (comparison T A U' hU' wU').hom.app M := by
  sorry

/-- Refinements of both hypercovers commute with the actual coefficient restriction map.
Source: Stacks, Tag 09A2, functoriality refinement
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization).
Proof: the assumed equality of augmented simplicial diagrams says the two composite
maps to every base-changed simplex agree. Apply the module unit and sheaf restriction;
functoriality gives the equality on each section. Alternating cofaces and extension
preserve that equality, proving the strict cochain square. -/
theorem restriction_refinement
    (U U' : SimplicialObject (Over (⊤_ X.ProEt)))
    (V V' : SimplicialObject (Over (⊤_ Y.ProEt))) (r : U' ⟶ U) (s : V' ⟶ V)
    (g : V ⋙ Over.forget (⊤_ Y.ProEt) ⟶
      U ⋙ Over.forget (⊤_ X.ProEt) ⋙ proEtaleBaseChange h)
    (g' : V' ⋙ Over.forget (⊤_ Y.ProEt) ⟶
      U' ⋙ Over.forget (⊤_ X.ProEt) ⋙ proEtaleBaseChange h)
    (comm : Functor.whiskerRight s (Over.forget _) ≫ g =
      g' ≫ Functor.whiskerRight r (Over.forget _ ⋙ proEtaleBaseChange h))
    (M : proEtaleRingModules X R) :
    restriction h R S c _ _ U V g M ≫
        refinement Y S _ V V' s ((proEtaleRingModulePullback h R S c).obj M) =
      refinement X R _ U U' r M ≫ restriction h R S c _ _ U' V' g' M := by
  sorry

/-- Section-complex pullbacks commute with composition, using the canonical coefficient
identification and the composite augmented simplicial diagram.
Source: Stacks, Tag 09A2, functoriality refinement
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization).
Proof: step 8. The defining section equation for compositionIso is the mate of
fibre-product pasting under the actual module adjunctions. Thus applying the unit and
restricting successively along g and g' equals restricting along their composite, after
the displayed coefficient comparison. This is an equality on each section, hence on
the alternating cochain complexes, including negative degrees. Combine this equality
with pullback_normalization twice, cancelling the common middle comparison, to obtain
the same compatibility for the actual derived-unit maps. No cartesian assumption enters. -/
theorem restriction_comp {Z : Scheme.{u}} (k : Z ⟶ Y)
    (T : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (d : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj S ≅ T)
    (U : SimplicialObject (Over (⊤_ X.ProEt)))
    (V : SimplicialObject (Over (⊤_ Y.ProEt)))
    (W : SimplicialObject (Over (⊤_ Z.ProEt)))
    (g : V ⋙ Over.forget (⊤_ Y.ProEt) ⟶
      U ⋙ Over.forget (⊤_ X.ProEt) ⋙ proEtaleBaseChange h)
    (g' : W ⋙ Over.forget (⊤_ Z.ProEt) ⟶
      V ⋙ Over.forget (⊤_ Y.ProEt) ⋙ proEtaleBaseChange k)
    (M : proEtaleRingModules X R) :
    restriction (k ≫ h) R T (proEtaleRingCompositeCoefficients k h R S T c d) _ _ U W
        (g' ≫ Functor.whiskerRight g (proEtaleBaseChange k) ≫
          Functor.whiskerLeft (U ⋙ Over.forget _)
            (MorphismProperty.Over.pullbackComp k h).inv) M ≫
        (rows Z T _ W).map ((compositionIso h R S c k T d).hom.app M) =
      restriction h R S c _ _ U V g M ≫
        restriction k S T d _ _ V W g' ((proEtaleRingModulePullback h R S c).obj M) := by
  sorry

/-- The actual unit-induced derived-section maps compose under the same coefficient
identification used by the section complexes.
Source: Stacks, Tags 09A2, 0DVC and 0D6E, composition refinement
(blueprint: lem-sfb-acyclic-hypercover-pullback-normalization).
Proof: the unit of the composite ordinary adjunction is the successive pair of units.
The conjugation characterization of compositionIso identifies it with the unit of
the composite scheme map. The derived adjunction representative formula with identity
left resolution gives the same equation on K-injective right resolutions. Canonical
derived-section composition is normalized on those resolutions by identity maps, so
its two pastings agree. Applying derived sections gives the displayed equation. Together
with restriction_comp and pullback_normalization this is the composition compatibility
of the normalized hypercover identification (proof step 8). -/
theorem derivedSectionPullback_comp {Z : Scheme.{u}} (k : Z ⟶ Y)
    (T : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (d : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj S ≅ T)
    (M : proEtaleRingModules X R) :
    derivedSectionPullback (k ≫ h) R T
        (proEtaleRingCompositeCoefficients k h R S T c d) M ≫
        (derivedSectionsZero Z T).map ((compositionIso h R S c k T d).hom.app M) =
      derivedSectionPullback h R S c M ≫
        derivedSectionPullback k S T d ((proEtaleRingModulePullback h R S c).obj M) := by
  sorry

end AlgebraicGeometry.Scheme.AcyclicHypercover
