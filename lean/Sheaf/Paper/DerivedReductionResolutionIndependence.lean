/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
public import Sheaf.Algebra.Homology.MixedTensorPointwiseLeftDerived
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.Algebra.Homology.DiagramKFlatReplacements

import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
/-!
# Resolution independence of exact-sections derived reduction

Source: Stacks Project, sites-cohomology.tex, Tag 06YY, and more-algebra.tex, Tag 06Y6.
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence).

The ordinary tensor models below are the quotient complexes: scalar extension to R/(t)
represents C/tC, and sheaf change of rings represents P/tP. Their comparisons are fixed
on pure tensors by the module-sheafification unit. No comparison is assumed invertible.
Site object, site morphism, coefficient and derived morphism universes remain separate.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v r wO wS wR wA

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open CategoryTheory.Functor
open scoped ChangeOfRings

namespace SheafOfModules
namespace PrincipalReduction

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r} ⋙
    forget₂ RingCat.{r} AddCommGrpCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]

/-- Underlying additive sheaf. Source: Stacks 03DA
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev additiveSheaf (O : Sheaf J CommRingCat.{r}) :=
  (sheafCompose J ((forget₂ CommRingCat.{r} RingCat.{r} ⋙
    forget₂ RingCat.{r} AddCommGrpCat.{r}))).obj O

/-- Multiplication by a final-object section is uniquely specified on every section.
Source: Stacks 03CV (blueprint: lem-pod-derived-reduction-sheaf-resolution-independence).
Proof: at V multiply by the restriction of a. Restrictions preserve products, so these
additive maps form a sheaf morphism. Equality of all components gives uniqueness. -/
theorem existsUnique_sectionMultiplication (O : Sheaf J CommRingCat.{r})
    (U : C) (hU : IsTerminal U) (a : O.obj.obj (op U)) :
    ∃! μ : additiveSheaf O ⟶ additiveSheaf O,
      ∀ (V : C) (x : O.obj.obj (op V)),
        μ.hom.app (op V) x = O.obj.map (hU.from V).op a * x := by
  sorry

/-- Multiplication by the specified section, determined uniquely sectionwise.
Source: Stacks 03CV (blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable def sectionMultiplication (O : Sheaf J CommRingCat.{r})
    (U : C) (hU : IsTerminal U) (a : O.obj.obj (op U)) :
    additiveSheaf O ⟶ additiveSheaf O :=
  (existsUnique_sectionMultiplication O U hU a).exists.choose

/-- The hypotheses of the exact-sections principal quotient comparison. The short exact
sequence is in abelian sheaves, so its epimorphism is not required to be sectionwise
surjective. Source: Stacks 06YY and the extracted exact-sections coherence argument
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
structure Setup (R : Type r) [CommRing R] where
  /-- The final object at which sections are taken. -/
  U : C
  /-- Finality. -/
  terminal : IsTerminal U
  /-- The original coefficient sheaf. -/
  O : Sheaf J CommRingCat.{r}
  /-- Its principal quotient sheaf. -/
  S : Sheaf J CommRingCat.{r}
  /-- The original coefficient map. -/
  ρ : R →+* O.obj.obj (op U)
  /-- The element defining the quotient. -/
  t : R
  /-- The sheaf quotient map. -/
  φ : O ⟶ S
  /-- The coefficient sequence is a complex. -/
  zero : sectionMultiplication O U terminal (ρ t) ≫
    (sheafCompose J ((forget₂ CommRingCat.{r} RingCat.{r} ⋙
    forget₂ RingCat.{r} AddCommGrpCat.{r}))).map φ = 0
  /-- Exactness including injectivity and epimorphy. -/
  shortExact : (ShortComplex.mk (sectionMultiplication O U terminal (ρ t))
    ((sheafCompose J ((forget₂ CommRingCat.{r} RingCat.{r} ⋙
    forget₂ RingCat.{r} AddCommGrpCat.{r}))).map φ) zero).ShortExact
  /-- Exactness of abelian sections, with no boundedness hypothesis. -/
  sectionsExact : exactFunctor _ _ ((sheafSections J AddCommGrpCat.{r}).obj (op U))

namespace Setup

variable {R : Type r} [CommRing R] (D : Setup (C := C) (J := J) R)

/-- The actual quotient R/(t). Source: Stacks 06Y6
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
abbrev A := R ⧸ Ideal.span {D.t}

/-- The quotient coefficient homomorphism. Source: Stacks 06Y6
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
abbrev quotientMap : R →+* D.A := Ideal.Quotient.mk _

/-- The composite coefficient map kills the principal ideal.
Source: the coefficient short exact sequence, Stacks 06YY
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence).
Proof: evaluate D.zero at U and 1 and use the section multiplication formula. This
says phi(rho(t))=0. Multiples and sums are killed because phi composed with rho is a ring map. -/
theorem ideal_le_ker : Ideal.span {D.t} ≤
    RingHom.ker ((D.φ.hom.app (op D.U)).hom.comp D.ρ) := by
  sorry

/-- The induced map R/(t) to the quotient section ring, by the quotient universal property.
Source: Stacks 06YY (blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable def quotientSectionsMap : D.A →+* D.S.obj.obj (op D.U) :=
  Ideal.Quotient.lift _ ((D.φ.hom.app (op D.U)).hom.comp D.ρ) (ideal_le_ker D)

/-- Integral sections with restriction along rho. Source: Stacks 03CW
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev sections :
    ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O) ⥤
      ModuleCat.{r} R :=
  evaluation (derivedChangeRingIndependentCoefficients J D.O) (op D.U) ⋙
    ModuleCat.restrictScalars D.ρ

/-- Quotient sections with their actual R/(t) action. Source: Stacks 03CW
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev quotientSections :
    ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.S) ⥤
      ModuleCat.{r} D.A :=
  evaluation (derivedChangeRingIndependentCoefficients J D.S) (op D.U) ⋙
    ModuleCat.restrictScalars D.quotientSectionsMap

/-- Exact abelian sections induce exact module sections, for either coefficient map.
Source: Stacks 03DA, 05RU
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence).
Proof: kernels, images and cokernels of module sheaves have the same underlying
abelian sheaves. Apply D.sectionsExact and note that restriction of scalars changes
none of these groups. The argument applies to both coefficient rings. -/
theorem sections_exact :
    (PreservesFiniteLimits D.sections ∧ PreservesFiniteColimits D.sections) ∧
    (PreservesFiniteLimits D.quotientSections ∧
      PreservesFiniteColimits D.quotientSections) := by
  sorry

/-- Exact integral sections preserve finite limits. Source: Stacks 03DA
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable instance sectionsLimits : PreservesFiniteLimits D.sections :=
  (sections_exact D).1.1

/-- Exact integral sections preserve finite colimits. Source: Stacks 03DA
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable instance sectionsColimits : PreservesFiniteColimits D.sections :=
  (sections_exact D).1.2

/-- Exact quotient sections preserve finite limits. Source: Stacks 03DA
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable instance quotientSectionsLimits : PreservesFiniteLimits D.quotientSections :=
  (sections_exact D).2.1

/-- Exact quotient sections preserve finite colimits. Source: Stacks 03DA
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable instance quotientSectionsColimits : PreservesFiniteColimits D.quotientSections :=
  (sections_exact D).2.2

/-- Additivity of exact integral sections, inherited from preservation of products.
Source: Stacks 03DA (blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable instance sectionsAdditive : D.sections.Additive :=
  Functor.additive_of_preserves_binary_products D.sections

/-- Additivity of exact quotient sections, inherited from preservation of products.
Source: Stacks 03DA (blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable instance quotientSectionsAdditive : D.quotientSections.Additive :=
  Functor.additive_of_preserves_binary_products D.quotientSections

variable [HasDerivedCategory.{wO}
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O))]
  [HasDerivedCategory.{wS}
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.S))]
  [HasDerivedCategory.{wR} (ModuleCat.{r} R)]
  [HasDerivedCategory.{wA} (ModuleCat.{r} D.A)]

/-- G, obtained from exact sections by localization. Source: Stacks 05RU
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev G := D.sections.mapDerivedCategory

/-- G', obtained from exact quotient sections by localization. Source: Stacks 05RU
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev G' := D.quotientSections.mapDerivedCategory

/-- The canonical universal derived-extension pair, including its counit. Its ordinary
objects and maps are prescribed and its derived pair is determined up to the unique
counit-compatible isomorphism. Source: Stacks 06YY
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable def extension :=
  (nonempty_derivedChangeOfRingsCochainModel.{u, v, r, wO, wS} D.φ).some

/-- Termwise sheaf quotient P/tP, using the recorded change-of-rings functor.
Source: Stacks 03EK, 06YY
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev quotientComplex := D.extension.E.mapHomologicalComplex (.up ℤ)

/-- Derived sheaf quotient T. Source: Stacks 06YY
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev T := D.extension.T

/-- A[0], with the regular quotient-module action. Source: Stacks 06Y6
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev quotientSingle :=
  (HomologicalComplex.single (ModuleCat.{r} D.A) (.up ℤ) 0).obj
    (𝟙_ (ModuleCat.{r} D.A))

/-- The second-factor derived-tensor functor supplied by its recorded dependency.
Source: Stacks 06Y6 (blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev tensorFamily :=
  (DerivedCategory.exists_derivedTensor_second_factor_functor D.quotientMap).2.choose

/-- The universal family of ordinary-module tensor counits. Source: Stacks 06Y6
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev tensorFamilyCounit :=
  (DerivedCategory.exists_derivedTensor_second_factor_functor D.quotientMap).2.choose_spec.choose

/-- L = - tensor_R^L A, without any flatness assumption on A. Source: Stacks 06Y6
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev L := D.tensorFamily.obj D.quotientSingle

/-- The universal property for the specified second-factor functor at A[0].
Source: Stacks 06Y6 (blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable instance tensorFamilyUniversal :
    D.L.IsLeftDerivedFunctor (D.tensorFamilyCounit D.quotientSingle)
      (HomologicalComplex.quasiIso (ModuleCat.{r} R) (.up ℤ)) :=
  (DerivedCategory.exists_derivedTensor_second_factor_functor
    D.quotientMap).2.choose_spec.choose_spec.1 D.quotientSingle

/-- The pointwise universal tensor pair of the recorded mixed-tensor dependency.
Source: Stacks 064L, 06Y6
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev pointwiseTensor :=
  (DerivedCategory.exists_mixedTensor_pointwise_leftDerived
    D.quotientMap D.quotientSingle).choose

/-- Its actual natural counit, before specialization to the quotient complex.
Source: Stacks 064L, 06Y6
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev pointwiseCounit :=
  (DerivedCategory.exists_mixedTensor_pointwise_leftDerived
    D.quotientMap D.quotientSingle).choose_spec.choose

/-- The pointwise mixed-tensor counit has the universal derived property.
Source: Stacks 064L, 06Y6
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable instance pointwiseUniversal :
    D.pointwiseTensor.IsLeftDerivedFunctor D.pointwiseCounit
      (HomologicalComplex.quasiIso (ModuleCat.{r} R) (.up ℤ)) :=
  (DerivedCategory.exists_mixedTensor_pointwise_leftDerived
    D.quotientMap D.quotientSingle).choose_spec.choose_spec.1

/-- Tensor with A[0] is termwise scalar extension: the single-factor totalization
comparison followed by the ordinary tensor unitor. This is the quotient model C/tC.
Source: Stacks 06Y6 (blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable def tensorSingleIso (K : CochainComplex (ModuleCat.{r} R) ℤ) :
    (((ModuleCat.mixedTensor D.quotientMap).flip.map₂CochainComplex).obj K).obj
      D.quotientSingle ≅
      ((ModuleCat.extendScalars D.quotientMap).mapHomologicalComplex (.up ℤ)).obj K :=
  CochainComplex.mapBifunctorSingle₂Iso (ModuleCat.mixedTensor D.quotientMap).flip
      (𝟙_ (ModuleCat.{r} D.A)) K ≪≫
    (NatIso.mapHomologicalComplex
      (isoWhiskerLeft (ModuleCat.extendScalars D.quotientMap)
        (leftUnitorNatIso (ModuleCat.{r} D.A)) ≪≫ Functor.rightUnitor _) (.up ℤ)).app K

/-- c_C is the mixed-tensor universal counit, transported to L by the unique universal
comparison, then identified with C/tC. In particular C is not assumed K-flat.
Source: Stacks 06Y6 (blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable def c (K : CochainComplex (ModuleCat.{r} R) ℤ) :
    D.L.obj (DerivedCategory.Q.obj K) ⟶ DerivedCategory.Q.obj
      (((ModuleCat.extendScalars D.quotientMap).mapHomologicalComplex (.up ℤ)).obj K) :=
  (Functor.leftDerivedUnique D.pointwiseTensor D.L
    (D.tensorFamilyCounit D.quotientSingle) D.pointwiseCounit
    (HomologicalComplex.quasiIso (ModuleCat.{r} R) (.up ℤ))).hom.app
      (DerivedCategory.Q.obj K) ≫
    D.pointwiseCounit.app K ≫ DerivedCategory.Q.map (D.tensorSingleIso K).hom

/-- The quotient image of a section, constructed by the module-sheafification unit.
Source: Stacks 03EK (blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable def quotientSection
    (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O))
    (x : M.val.obj (op D.U)) : (D.extension.E.obj M).val.obj (op D.U) :=
  ((eqToHom (D.extension.obj_eq M).symm).val.app (op D.U))
    ((((PresheafOfModules.sheafificationAdjunction
      (R := derivedChangeRingIndependentCoefficients J D.S) (𝟙 _)).unit.app
        (changeOfRingsPresheaf D.φ M)).app (op D.U))
          ((1 : D.S.obj.obj (op D.U)) ⊗ₜ[D.O.obj.obj (op D.U),
            (D.φ.hom.app (op D.U)).hom] x))

/-- The exact-sections quotient identification is uniquely fixed by its section formula.
Source: Stacks 03EK, 03ER, 06YY
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence).
Proof: tensor the coefficient short exact sequence with each flat term of P.
Its cokernel is both P^i/tP^i and P^i tensor_O S, via x tensor b-bar to bx modulo t
and x-bar to x tensor 1. Exact sections identify its section cokernel with
Gamma(P^i)/tGamma(P^i). This gives the displayed bijective A-linear map on tensors.
The formula commutes with differentials, hence gives a complex isomorphism. Tensors
1 tensor x generate over A in every degree; the formula determines the chain map
uniquely, hence also its inverse and the entire isomorphism. -/
theorem existsUnique_theta
    (P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
    (hflat : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i)) :
    ∃! e : ((ModuleCat.extendScalars D.quotientMap).mapHomologicalComplex (.up ℤ)).obj
        ((D.sections.mapHomologicalComplex (.up ℤ)).obj P) ≅
      (D.quotientSections.mapHomologicalComplex (.up ℤ)).obj (D.quotientComplex.obj P),
      ∀ (i : ℤ) (a : D.A) (x : (P.X i).val.obj (op D.U)),
        e.hom.f i (a ⊗ₜ[R, D.quotientMap] x) =
          D.quotientSectionsMap a • D.quotientSection (P.X i) x := by
  sorry

/-- theta_P, chosen from a property that determines the whole isomorphism uniquely.
Source: Stacks 03EK, 06YY
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable def theta
    (P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
    (hflat : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i)) :=
  (existsUnique_theta D P hflat).exists.choose

/-- The canonical K-flat computation e_P is precisely the derived-extension counit.
Source: Stacks 06YY (blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable def modelIso
    (P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P) :
    D.T.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj (D.quotientComplex.obj P) :=
  letI := D.extension.computes P hP
  asIso (D.extension.ε.app P)

/-- alpha_P is theta_P after c_Gamma(P), with the localization factors and the inverse
of the canonical K-flat computation written explicitly. Source: Stacks 06YY, 06Y6
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable def alpha
    (P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P)
    (hflat : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i)) :
    D.L.obj (D.G.obj (DerivedCategory.Q.obj P)) ⟶
      D.G'.obj (D.T.obj (DerivedCategory.Q.obj P)) :=
  D.L.map (D.sections.mapDerivedCategoryFactors.hom.app P) ≫
    D.c ((D.sections.mapHomologicalComplex (.up ℤ)).obj P) ≫
    DerivedCategory.Q.map (D.theta P hflat).hom ≫
    D.quotientSections.mapDerivedCategoryFactors.inv.app (D.quotientComplex.obj P) ≫
    D.G'.map (D.modelIso P hP).inv

/-- The comparison transported along a supplied resolution p, taking no inverse of alpha.
Source: Stacks 06YY (blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable def resolvedComparison
    {M P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ}
    (p : P ⟶ M) [QuasiIso p]
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P)
    (hflat : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i)) :
    D.L.obj (D.G.obj (DerivedCategory.Q.obj M)) ⟶
      D.G'.obj (D.T.obj (DerivedCategory.Q.obj M)) :=
  (D.G ⋙ D.L).map (inv (DerivedCategory.Q.map p)) ≫
    D.alpha P hP hflat ≫ (D.T ⋙ D.G').map (DerivedCategory.Q.map p)

/-- Naturality for every map between flat-term K-flat models, and independence of two
such resolutions of an arbitrary unbounded complex. Neither clause asserts invertibility
of alpha. Source: Stacks 06YY and the extracted strict-cospan argument
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence).

Proof (the six steps of the node):
1. Exact abelian sections preserve kernels and cokernels, hence cohomology. Restricting
scalars changes no underlying group, so G and G' descend through quasi-isomorphisms.
2. Flat terms and the coefficient sequence identify P tensor S with P/tP. Exact sections
give theta_P. On the class of x, both maps in its naturality square give the class of h(x).
3. Specialize the mixed-tensor counit to A[0]. Its naturality and the natural ordinary
quotient identification give Q_A(u-bar) c_C = c_C' L(Q_R u), for arbitrary section C.
4. The K-flat computation e_P is the sheaf extension counit, so it too is natural in h.
Combine its square with steps 2 and 3 and conjugate by G'(e_P) to get the first clause.
5. Apply lem-weil-pbc-diagram-kflat-replacements to the strict cospan P -> M <- P'.
It gives flat-term K-flat S0,S1,S2 and quasi-isomorphisms r:S0->P, r':S1->P', q:S2->M
with qa=pr and qb=p'r'. Two-out-of-three makes a and b quasi-isomorphisms as well.
6. Write F=LG, H=G'T and beta(p)=F(p)^(-1) alpha_P H(p), in Lean composition order.
Naturality for r and a and cancellation of their invertible F-images yield
beta(p)=beta(pr)=beta(qa)=beta(q). The same calculation with r' and b yields
beta(p')=beta(q). All inverses are images of resolution maps or K-flat counits;
no inverse of alpha is used. Thus the equality uses exactly the canonical model
identifications specified by the supplied resolutions. -/
theorem resolution_independence :
    (∀ (P P' : CochainComplex
        (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P)
      (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P')
      (hf : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i))
      (hf' : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P'.X i)) (h : P ⟶ P'),
      D.alpha P hP hf ≫ (D.T ⋙ D.G').map (DerivedCategory.Q.map h) =
        (D.G ⋙ D.L).map (DerivedCategory.Q.map h) ≫ D.alpha P' hP' hf') ∧
    (∀ (M P P' : CochainComplex
        (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
      (p : P ⟶ M) (p' : P' ⟶ M) [QuasiIso p] [QuasiIso p']
      (hP : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P)
      (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P')
      (hf : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i))
      (hf' : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P'.X i)),
      D.resolvedComparison p hP hf = D.resolvedComparison p' hP' hf') := by
  sorry

end Setup
end PrincipalReduction
end SheafOfModules
