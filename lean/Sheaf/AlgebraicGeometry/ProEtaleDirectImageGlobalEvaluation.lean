/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.Paper.FiniteDirectImageComposition
public import Sheaf.AlgebraicGeometry.ProEtaleUnitLerayChainFormula
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackIdentity
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.AlgebraicGeometry.ProEtaleOpenUnitEvaluation
import Sheaf.CategoryTheory.KInjectiveDerivedMapComputation
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.Paper.SfDerivedDirectImage

/-!
# Normalized derived global sections after ordinary pro-etale direct image

Source: Stacks Project, sites-cohomology.tex, Tags 0D6H and 0D6E;
K-injective normalization and open-unit calculation in derived.tex, Tags 070Y and 0DVC
(blueprint: lem-pur-proetale-direct-image-global-evaluation).

The section functor and its terminal-object comparison are the published ordinary
constant-ring constructions. All derived images below are the actual finite-level
sectionwise direct image, without completion or a constructibility restriction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
section
attribute [-instance]
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme

/-- The recorded tensor-unit-normalized adjunction, with the right functor written
as the sectionwise constant-module direct image used at finite level.
Source: Stacks, modules on sites, lemma-adjoint-push-pull-modules
(blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
def proEtaleOrdinaryModuleAdjunction (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantRingPullback A f ⊣ proEtaleConstantModuleDirectImage f A :=
  (proEtaleConstantRingAdjunction A f).ofNatIsoRight (proEtaleUnitLerayDirectImageIso A f)

/-- The actual finite direct image preserves K-injectives, since the recorded
inverse image is exact. Source: Stacks Tag 08BJ
(blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
instance proEtaleOrdinaryDirectImage_preservesKInjective (A : Type u)
    [CommRing A] [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (proEtaleConstantModuleDirectImage f A).PreservesKInjectiveComplexes :=
  (proEtaleOrdinaryModuleAdjunction A f).preservesKInjectiveComplexes

/-- The ordinary derived adjunction on the exact finite-coefficient presentation.
Source: Stacks Tag 0DVC (blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
def proEtaleOrdinaryDerivedAdjunction (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantRingDerivedPullback A f ⊣ proEtaleConstantDerivedDirectImage f A :=
  (proEtaleOrdinaryModuleAdjunction A f).mapDerivedCategoryRightDerivedAdjunction

/-- The canonical finite composition comparison in ordinary constant-ring modules.
It is the conjugate of the published inverse-image composition isomorphism, through
exactly the derived adjunctions of the finite direct image; thus it is the canonical
ringed-topos comparison of Tag 0D6E, with orientation R(gf)_* -> Rg_* Rf_*.
Source: Stacks Tag 0D6E (blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
def proEtaleOrdinaryDirectImageComposition (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    proEtaleConstantDerivedDirectImage (f ≫ g) A ≅
      proEtaleConstantDerivedDirectImage f A ⋙ proEtaleConstantDerivedDirectImage g A :=
  conjugateIsoEquiv (proEtaleOrdinaryDerivedAdjunction A (f ≫ g))
    ((proEtaleOrdinaryDerivedAdjunction A g).comp (proEtaleOrdinaryDerivedAdjunction A f))
    (proEtaleConstantRingPullbackComposition f g A)

/-- Fix abelian-group sheafification at the published coefficient universe.
Source: Stacks Tag 07A5 (blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
private noncomputable local instance (priority := 5000) globalEvaluation_sheafify
    (X : Scheme.{u}) : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} X

/-- Use the published locally-bijective characterization at that same universe.
Source: Stacks Tag 07A5 (blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
private noncomputable local instance (priority := 5000) globalEvaluation_locallyBijective
    (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X

/-- Finiteness of the conventions' coefficient ring, supplied by its published quotient
construction. Source: blueprint def-pur-conventions, A = O_E/(varpi^n)
(blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
instance purityGlobalEvaluation_finiteRing (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite P.Ring :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos

/-- Derived final-object evaluation in the same localization universes as the published
unit--Leray construction. Source: Stacks Tag 0D6H
(blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
abbrev proEtaleGlobalEvaluationSections (A : Type u) [CommRing A] [Finite A]
    (X : Scheme.{u}) :=
  @Functor.rightDerivedFunctor.{u+2,u+2,u+1,u+1,u+2,u+1} _ _ _ _ _ _
    (proEtaleRingModules_hasDerivedCategory X (proEtaleConstantRing X A))
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _)
    (proEtaleUnitLeraySections A X) inferInstance
    (proEtaleRingModules_hasKInjectiveResolutions X (proEtaleConstantRing X A))

/-- The canonical K-injective evaluation isomorphism in those fixed localization universes.
Source: Stacks Tag 070Y (blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
abbrev proEtaleGlobalEvaluationSectionsObj (A : Type u) [CommRing A] [Finite A]
    (X : Scheme.{u})
    (J : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
    [J.IsKInjective] :=
  @Functor.rightDerivedFunctorObjQIso.{u+2,u+2,u+1,u+1,u+2,u+1} _ _ _ _ _ _
    (proEtaleRingModules_hasDerivedCategory X (proEtaleConstantRing X A))
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _)
    (proEtaleRingModules_hasKInjectiveResolutions X (proEtaleConstantRing X A))
    (proEtaleUnitLeraySections A X) inferInstance J inferInstance

/-- The finite direct image on K-injectives, using its published standard localization.
Source: Stacks Tag 070Y (blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
abbrev proEtaleGlobalEvaluationImageObj (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
    [J.IsKInjective] :=
  @Functor.rightDerivedFunctorObjQIso.{u+2,u+2,u+1,u+1,u+2,u+2} _ _ _ _ _ _
    (proEtaleRingModules_hasDerivedCategory X (proEtaleConstantRing X A))
    (proEtaleRingModules_hasDerivedCategory Y (proEtaleConstantRing Y A))
    (proEtaleRingModules_hasKInjectiveResolutions X (proEtaleConstantRing X A))
    (proEtaleConstantModuleDirectImage f A) inferInstance J inferInstance

/-- The published terminal-object comparison, written for the actual finite direct image.
Source: Stacks Tag 0D6H (blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
def proEtaleGlobalEvaluationTerminal (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantModuleDirectImage f A ⋙ proEtaleUnitLeraySections A Y ≅
      proEtaleUnitLeraySections A X :=
  isoWhiskerRight (proEtaleUnitLerayDirectImageIso A f).symm
    (proEtaleUnitLeraySections A Y) ≪≫ proEtaleUnitLerayTerminalIso A f

/-- The canonical comparison, derived from evaluation at the final object. The universal
right-derived compositor fixes the comparison on K-injectives and all derived morphisms.
Source: Stacks Tags 0D6H and 0D6E
(blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
def proEtaleGlobalEvaluation (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantDerivedDirectImage f A ⋙
        (proEtaleGlobalEvaluationSections A Y) ≅
      (proEtaleGlobalEvaluationSections A X) :=
  letI := proEtaleRingModules_hasKInjectiveResolutions X (proEtaleConstantRing X A)
  letI := proEtaleRingModules_hasKInjectiveResolutions Y (proEtaleConstantRing Y A)
  Functor.rightDerivedFunctorCompIso' (proEtaleConstantModuleDirectImage f A)
    (proEtaleUnitLeraySections A Y) (proEtaleGlobalEvaluationTerminal A f)

/-- The natural isomorphism on precisely D^+(X_proet,A), with every derived morphism.
Source: Stacks Tag 0D6H (blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
def proEtaleGlobalEvaluationPlus (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  isoWhiskerLeft (@DerivedCategory.Plus.ι
    (proEtaleRingModules X (proEtaleConstantRing X P.Ring)) _ _
    (proEtaleRingModules_hasDerivedCategory X (proEtaleConstantRing X P.Ring)))
    (proEtaleGlobalEvaluation P.Ring f)

/-- The normalized identity inverse image. The source theorem specifies every section
of its module comparison, its termwise extension, and its localization, so the extracted
isomorphism is determined by that normalization rather than by bare existence.
Source: blueprint lem-pur-proetale-derived-pullback-identity
(blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
def proEtaleGlobalEvaluationPullbackId (A : Type u) [CommRing A] [Finite A]
    (X : Scheme.{u}) : proEtaleConstantRingDerivedPullback A (𝟙 X) ≅ 𝟭 _ :=
  (proEtaleDerivedPullback_identity X A).choose_spec.2.2.choose_spec.2.choose_spec.2.2
    |>.choose_spec.2.choose

/-- The canonical identity direct-image comparison is the mate of the section-normalized
identity inverse image, for the same ordinary adjunction as the composition comparison.
Source: Stacks Tag 0D6E (blueprint: lem-pur-proetale-direct-image-global-evaluation). -/
def proEtaleGlobalEvaluationDirectImageId (A : Type u) [CommRing A] [Finite A]
    (X : Scheme.{u}) : proEtaleConstantDerivedDirectImage (𝟙 X) A ≅ 𝟭 _ :=
  conjugateIsoEquiv (proEtaleOrdinaryDerivedAdjunction A (𝟙 X)) (Adjunction.id)
    (proEtaleGlobalEvaluationPullbackId A X).symm

variable (P : WeilConjectures.PurityFiniteSetting.{u})
  {T Y W : Scheme.{u}}
  [T.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [W.Over (Spec (.of P.field.k))]

/-- The comparison is the identity of final-object section complexes, through the
canonical K-injective resolution identifications.
Source: Stacks Tags 0D6H and 070Y
(blueprint: lem-pur-proetale-direct-image-global-evaluation).

Proof: (1) Good truncation supplies a bounded-below complex representing every D^+
object, and lem-sc-bounded-below-injective-resolution supplies its K-injective model.
(2) The exact left adjoint makes f_* preserve K-injectives by Tag 08BJ.
(3) On this model, evaluate the sectionwise direct image at the final object: its
base change is canonically T. The coefficient action and differentials agree.
(4) The universal right-derived comparison on this model is therefore the displayed
map, with the three canonical resolution identifications. The unique homotopy-class
calculation of lem-sf-kinjective-derived-map-computation gives the same comparison
for arbitrary derived morphisms and for changes of resolutions, including roofs. -/
theorem proEtaleDirectImageGlobalEvaluation (f : T ⟶ Y)
    [f.IsOver (Spec (.of P.field.k))]
    (J : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T P.Ring)) ℤ)
    [J.IsKInjective] (_hJ : ∃ a : ℤ, J.IsStrictlyGE a) :
    (proEtaleGlobalEvaluation P.Ring f).hom.app (DerivedCategory.Q.obj J) =
      (proEtaleGlobalEvaluationSections P.Ring Y).map
          (proEtaleGlobalEvaluationImageObj P.Ring f J).hom ≫
        ((proEtaleGlobalEvaluationSectionsObj P.Ring Y)
          (((proEtaleConstantModuleDirectImage f P.Ring).mapHomologicalComplex
            (.up ℤ)).obj J)).hom ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
            (proEtaleGlobalEvaluationTerminal P.Ring f).hom (.up ℤ)).app J) ≫
        ((proEtaleGlobalEvaluationSectionsObj P.Ring T) J).inv := by
  sorry

/-- Compatibility with the specified derived shift comparisons, on D^+.
Source: Stacks Tag 05SU (blueprint: lem-pur-proetale-direct-image-global-evaluation).
Proof: shift a bounded-below K-injective representative J by n. Shifts preserve
K-injectivity since Hom(M,J[n]) = Hom(M[-n],J) for acyclic M. Evaluation and direct
image act termwise, so both differentials acquire exactly the same factor (-1)^n.
The preceding resolution normalization and its transition naturality identify this
calculation with the already specified derived-functor shift comparisons. -/
theorem proEtaleDirectImageGlobalEvaluation_shift (f : T ⟶ Y)
    [f.IsOver (Spec (.of P.field.k))]
    (L : @DerivedCategory.Plus (proEtaleRingModules T (proEtaleConstantRing T P.Ring))
      _ _ (proEtaleRingModules_hasDerivedCategory T (proEtaleConstantRing T P.Ring)))
    (n : ℤ) :
    ((proEtaleConstantDerivedDirectImage f P.Ring ⋙
        (proEtaleGlobalEvaluationSections P.Ring Y)).commShiftIso n).hom.app
          L.obj ≫ (shiftFunctor _ n).map ((proEtaleGlobalEvaluation P.Ring f).hom.app L.obj) =
      (proEtaleGlobalEvaluation P.Ring f).hom.app (L.obj⟦n⟧) ≫
        ((proEtaleGlobalEvaluationSections P.Ring T).commShiftIso n).hom.app
          L.obj := by
  sorry

/-- The final-object comparison agrees with the canonical direct-image compositor.
Source: Stacks Tag 0D6E (blueprint: lem-pur-proetale-direct-image-global-evaluation).
Proof: on a bounded-below K-injective J, f_*J remains K-injective. Thus the resolution
used in the canonical compositor may be the identity of f_*J. Tag 0D6E then gives
(gf)_*J = g_*f_*J. Evaluating at W and then Y gives exactly evaluation at T. The
canonical isomorphism from the iterated pullback of the final object to T is unique,
so both parenthesizations agree. Derived-map and resolution naturality transport
this equality to L. -/
theorem proEtaleDirectImageGlobalEvaluation_comp (f : T ⟶ Y) (g : Y ⟶ W)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    (L : @DerivedCategory.Plus (proEtaleRingModules T (proEtaleConstantRing T P.Ring))
      _ _ (proEtaleRingModules_hasDerivedCategory T (proEtaleConstantRing T P.Ring))) :
    (proEtaleGlobalEvaluation P.Ring (f ≫ g)).hom.app L.obj =
      (proEtaleGlobalEvaluationSections P.Ring W).map
          ((proEtaleOrdinaryDirectImageComposition P.Ring f g).hom.app L.obj) ≫
        (proEtaleGlobalEvaluation P.Ring g).hom.app
          ((proEtaleConstantDerivedDirectImage f P.Ring).obj L.obj) ≫
        (proEtaleGlobalEvaluation P.Ring f).hom.app L.obj := by
  sorry

/-- Identity normalization, after the canonical identity direct-image identification.
Source: Stacks Tag 0D6E (blueprint: lem-pur-proetale-direct-image-global-evaluation).
Proof: the representative-level final-object identification for the identity is the
identity of section complexes. The specified identity inverse image and its adjoint
mate have exactly that normalization. Passing through the same K-injective resolution
identifications gives the formula on every bounded-below derived object. -/
theorem proEtaleDirectImageGlobalEvaluation_id
    (L : @DerivedCategory.Plus (proEtaleRingModules T (proEtaleConstantRing T P.Ring))
      _ _ (proEtaleRingModules_hasDerivedCategory T (proEtaleConstantRing T P.Ring))) :
    (proEtaleGlobalEvaluation P.Ring (𝟙 T)).hom.app L.obj =
      (proEtaleGlobalEvaluationSections P.Ring T).map
        ((proEtaleGlobalEvaluationDirectImageId P.Ring T).hom.app L.obj) := by
  sorry

/-- The open-unit composite is restriction, including its resolution map. This equation
uses an arbitrary K-injective resolution of j^*I, so it characterizes the actual derived
restriction without assuming inverse image preserves K-injectives.
Source: Stacks Tags 0DVC and 09BN
(blueprint: lem-pur-proetale-direct-image-global-evaluation).
Proof: resolve the bounded-below termwise j^*I by v:j^*I -> H. The derived adjunction
unit is represented by eta_I followed by j_*v, by the pre-derived-adjunction
characterization with v adjoint to the identity of j^*L. Evaluate eta_I at T: the
open-unit evaluation theorem identifies it with restriction to U. Evaluation of
j_*v, followed by the final-object comparison, is Gamma(U,v). The displayed right
side is therefore restriction followed by this resolution map. Naturality of the
K-injective derived-map formula proves independence of I,H,v. This works for every
open immersion, with no quasi-compactness assumption. -/
theorem proEtaleDirectImageGlobalEvaluation_open
    {U : Scheme.{u}} [U.Over (Spec (.of P.field.k))] (j : U ⟶ T)
    [j.IsOver (Spec (.of P.field.k))] [IsOpenImmersion j]
    (I : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T P.Ring)) ℤ)
    (H : CochainComplex (proEtaleRingModules U (proEtaleConstantRing U P.Ring)) ℤ)
    [I.IsKInjective] [H.IsKInjective]
    (_hI : ∃ a : ℤ, I.IsStrictlyGE a) (_hH : ∃ a : ℤ, H.IsStrictlyGE a)
    (v : ((proEtaleConstantRingPullback P.Ring j).mapHomologicalComplex (.up ℤ)).obj I ⟶ H)
    [QuasiIso v] :
    (proEtaleGlobalEvaluationSections P.Ring T).map
        ((proEtaleOrdinaryDerivedAdjunction P.Ring j).unit.app (DerivedCategory.Q.obj I)) ≫
      (proEtaleGlobalEvaluation P.Ring j).hom.app
        ((proEtaleConstantRingDerivedPullback P.Ring j).obj (DerivedCategory.Q.obj I)) ≫
      (proEtaleGlobalEvaluationSections P.Ring U).map
        ((proEtaleConstantRingPullback P.Ring j).mapDerivedCategoryFactors.hom.app I ≫
          DerivedCategory.Q.map v) =
    ((proEtaleGlobalEvaluationSectionsObj P.Ring T) I).hom ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (proEtaleUnitLeraySectionUnit P.Ring j)
          (.up ℤ)).app I ≫
          ((proEtaleUnitLeraySections P.Ring U).mapHomologicalComplex (.up ℤ)).map v) ≫
      ((proEtaleGlobalEvaluationSectionsObj P.Ring U) H).inv := by
  sorry

/-- The third arrow is identified with its given sign and the given shift comparison.
Together with naturality at the first two arrows, this identifies the global-sections
triangles, in particular for a support-localization triangle.
Source: Stacks Tags 0D6H and 05SU
(blueprint: lem-pur-proetale-direct-image-global-evaluation).
Proof: use naturality of ell at the triangle's actual third morphism d. Apply the shift
compatibility above to its first vertex B. Substitution gives the displayed square,
whose shifted comparison is ell_B[1]. The first two squares are ordinary naturality.
The derived functors are triangulated, so this compares the distinguished triangles
with their existing third arrows, rather than choosing new connecting morphisms. -/
theorem proEtaleDirectImageGlobalEvaluation_third (f : T ⟶ Y)
    [f.IsOver (Spec (.of P.field.k))]
    (B D : @DerivedCategory.Plus (proEtaleRingModules T (proEtaleConstantRing T P.Ring))
      _ _ (proEtaleRingModules_hasDerivedCategory T (proEtaleConstantRing T P.Ring)))
    (d : D.obj ⟶ B.obj⟦(1 : ℤ)⟧) :
    (proEtaleGlobalEvaluationSections P.Ring Y).map
        ((proEtaleConstantDerivedDirectImage f P.Ring).map d) ≫
      ((proEtaleConstantDerivedDirectImage f P.Ring ⋙
        (proEtaleGlobalEvaluationSections P.Ring Y)).commShiftIso (1 : ℤ)).hom.app
          B.obj ≫
      (shiftFunctor _ (1 : ℤ)).map ((proEtaleGlobalEvaluation P.Ring f).hom.app B.obj) =
    (proEtaleGlobalEvaluation P.Ring f).hom.app D.obj ≫
      (proEtaleGlobalEvaluationSections P.Ring T).map d ≫
      ((proEtaleGlobalEvaluationSections P.Ring T).commShiftIso (1 : ℤ)).hom.app
        B.obj := by
  sorry

end AlgebraicGeometry.Scheme

end
