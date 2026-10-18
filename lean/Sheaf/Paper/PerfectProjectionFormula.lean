/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import Sheaf.Paper.ProjectionFormulaBaseChangeNaturality
public import Sheaf.Paper.ProjectionFormulaIdentityCompactification
public import Sheaf.Paper.StrictPerfectPackageOnSite
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.ProjectionFormulaTotalization
import Sheaf.Paper.RingedProjectionRestriction
public import Sheaf.Paper.CompletedConstantSheafReduction
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-!
# Perfect projection formula for completed coefficient reductions

Source: Weil conjectures blueprint, proper base change, order 1275; Stacks Project,
Cohomology on Sites, Tags 0B56 and 0944, and More on Algebra, Tag 0657
(blueprint: lemma-weil-pbc-perfect-projection-formula).

The completed ring is presented as the limit of constant finite quotient sheaves.
The recorded finite-coefficient comparisons identify this presentation with the
continuous-functions presentation, including its quotient maps. Tensors and derived
categories are ordinary and uncompleted. Natural numbers index positive exponents n+1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.PerfectProjection

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The recorded completed ring, in its constant finite-quotient presentation.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
abbrev ring (T : Scheme.{u}) := adicLisseCompletedRing T d.ideal

/-- The existing module category over this completed ring, at the mandated coefficient size.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
abbrev modules (T : Scheme.{u}) := proEtaleRingModules T (ring d T)

/-- The ordinary localization of module complexes, with no completion condition.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
abbrev derived (T : Scheme.{u}) := DerivedCategory (modules d T)

/-- The residue as an object of the ordinary derived category over the completed ring.
Source: blueprint order 1275, displayed formula
(blueprint: lemma-weil-pbc-perfect-projection-formula). -/
abbrev quotient (T : Scheme.{u}) (n : ℕ) : derived d T :=
  (DerivedCategory.singleFunctor (modules d T) 0).obj
    (CompletedConstantReduction.residue T d.ideal n)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The projectionwise constant-ring comparison is a cone, including all tower arrows.
Source: Stacks 098T and blueprint order 1275, proof step 1
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: commute the quotient projection past the inverse-image functor, use the
constant-comparison naturality of the profinite inverse-image lemma, and then use
the limit cone equation for the quotient system on Y. -/
theorem coefficientCone_naturality {n m : ℕᵒᵖ} (a : n ⟶ m) :
    𝟙 ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (ring d Y)) ≫
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (limit.π (adicLisseRingSystem Y d.ideal) m) ≫
      (proEtaleConstantComparison f).app (CommRingCat.of (A ⧸ d.ideal ^ (m.unop + 1))) =
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (limit.π (adicLisseRingSystem Y d.ideal) n) ≫
      (proEtaleConstantComparison f).app (CommRingCat.of (A ⧸ d.ideal ^ (n.unop + 1)))) ≫
      (adicLisseRingSystem X d.ideal).map a := sorry

/-- The actual inverse-limit comparison, characterized by its quotient projections.
Source: blueprint order 1275, coefficient identification
(blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def coefficientMap :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (ring d Y) ⟶
      ring d X :=
  limit.lift (adicLisseRingSystem X d.ideal)
    { pt := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (ring d Y)
      π := { app := fun n ↦ (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
                (limit.π (adicLisseRingSystem Y d.ideal) n) ≫
              (proEtaleConstantComparison f).app
                (CommRingCat.of (A ⧸ d.ideal ^ (n.unop + 1)))
             naturality := fun _ _ a ↦ coefficientCone_naturality d f a } }

/-- The specified comparison is invertible for the finite quotient tower.
Source: blueprint order 1275, proof step 1; Stacks 098T
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: apply profinite-coefficient inverse image to the quotient ring system.
The cone projection equations identify its canonical map with coefficientMap.
The function-sheaf and constant-sheaf presentations agree by the recorded finite
coefficient comparisons, naturally in every quotient transition. -/
theorem coefficientMap_isIso : IsIso (coefficientMap d f) := sorry

/-- The canonical coefficient identification; only its invertibility is postponed.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def coefficients :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (ring d Y) ≅
      ring d X :=
  @asIso _ _ _ _ (coefficientMap d f) (coefficientMap_isIso d f)

/-- The ordinary derived pullback with this specific completed coefficient identification.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
abbrev pullback :=
  proEtaleRingDerivedPullback f (ring d Y) (ring d X) (coefficients d f)

/-- The ordinary derived direct image with the same coefficient action.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
abbrev directImage :=
  proEtaleRingDerivedDirectImage f (ring d Y) (ring d X) (coefficients d f)

variable (aY : ProEtaleTensorModel Y (ring d Y))
  (aX : ProEtaleTensorModel X (ring d X))
  (K : derived d X)

/-- The existing canonical projection mate, with the completed coefficients specialized.
Source: Stacks 0B56 and blueprint order 1275
(blueprint: lemma-weil-pbc-perfect-projection-formula). -/
abbrev projection (P : derived d Y) :=
  proEtaleProjectionFormulaMate f (ring d Y) (ring d X)
    (coefficients d f) aY aX K P

/-- The full isomorphism locus of the specified projection morphism.
Source: blueprint order 1275, Detailed form
(blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def locus : ObjectProperty (derived d Y) :=
  fun P ↦ IsIso (projection d f aY aX K P)

/-- Thick closure, the finite-free base case (including rank zero), and site-perfectness.
Source: Stacks 0944 and blueprint order 1275, Detailed form
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: (1) The profinite coefficient comparison gives the ordinary ringed-topos
operations. (2) The unit normalization of ringed-projection-mate-exact gives the
identity on the coefficient ring; additivity gives finite free sheaves, also rank zero.
(3) Its two functors are exact and its natural transformation respects shifts.
The triangle morphism isomorphism lemma gives two-out-of-three; naturality gives
inverse F(r) pi_P^{-1} G(i) on any retract. Thus the locus is thick triangulated.
(4) Restrict using ringed-projection-restriction. On each covering object use its
own bounded finite-projective representative. The terms are finite-free retracts;
stupid truncations give degreewise-split distinguished triangles, so finite induction
proves invertibility there. Local detection proves it globally. No uniform bound
or global thick-generation claim about all site-perfect objects is used. -/
theorem perfect_projection_formula :
    (locus d f aY aX K).IsTriangulated ∧
    (locus d f aY aX K).IsStableUnderRetracts ∧
    (∀ m : ℕ, locus d f aY aX K
      ((DerivedCategory.singleFunctor (modules d Y) 0).obj
        (∏ᶜ fun _ : Fin m ↦ SheafOfModules.unit ((adicLisseForget Y).obj
          (ring d Y))))) ∧
    (∀ P : derived d Y,
      SheafOfModules.IsPerfectOnSmallRingedSite (ring d Y) P →
        locus d f aY aX K P) := sorry

/-- The canonical module pullback comparison is fixed by the constant-section adjunct.
Source: blueprint order 1275, proof step 5
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: the level comparison of profinite-coefficient inverse image commutes with the
completed-ring projection, so its adjunct is linear for the completed coefficient
action. Restrict the module adjunction to this linear map. The inverse coefficient
comparison gives its inverse. Uniqueness of adjuncts and sheaf maps gives uniqueness. -/
theorem quotientPullback_existsUnique (n : ℕ) :
    ∃! e : (proEtaleRingModulePullback f (ring d Y) (ring d X)
        (coefficients d f)).obj (CompletedConstantReduction.residue Y d.ideal n) ≅
          CompletedConstantReduction.residue X d.ideal n,
      ∀ (U : Y.ProEtᵒᵖ)
        (x : (adicLisseConstantRing Y (A ⧸ d.ideal ^ (n + 1))).obj.obj U),
        ((proEtaleRingModuleAdjunction f (ring d Y) (ring d X)
          (coefficients d f)).homEquiv _ _ e.hom).val.app U x =
        (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app
          (adicLisseConstantRing Y (A ⧸ d.ideal ^ (n + 1))) ≫
          (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
            ((proEtaleConstantComparison f).app
              (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))))).hom.app U) x := sorry

/-- Pull back the quotient module by its uniquely normalized module comparison.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def quotientPullback (n : ℕ) :=
  (quotientPullback_existsUnique d f n).exists.choose

/-- The derived comparison is the exact termwise pullback comparison in degree zero.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def quotientDerivedPullback (n : ℕ) :
    (pullback d f).obj (quotient d Y n) ≅ quotient d X n :=
  ((proEtaleRingModulePullback f (ring d Y) (ring d X)
    (coefficients d f)).mapDerivedCategorySingleFunctor 0).app
      (CompletedConstantReduction.residue Y d.ideal n) ≪≫
    (DerivedCategory.singleFunctor (modules d X) 0).mapIso (quotientPullback d f n)

/-- K_n as an A_X-object: derived tensor with the restricted quotient sheaf.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
abbrev reduction (n : ℕ) := aX.tensor.obj (K, quotient d X n)

/-- The reduction projection map uses the canonical quotient pullback identification.
Source: blueprint order 1275, displayed pi_n
(blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def reductionMap (n : ℕ) :
    aY.tensor.obj ((directImage d f).obj K, quotient d Y n) ⟶
      (directImage d f).obj (reduction d aX K n) :=
  projection d f aY aX K (quotient d Y n) ≫
    (directImage d f).map
      (aX.tensor.map (Prod.mkHom (𝟙 K) (quotientDerivedPullback d f n).hom))

/-- Every positive quotient is site-perfect and its canonical projection map is invertible.
Source: Stacks 0944 and 093M; blueprint order 1275, proof step 5
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: choose a bounded finite-projective A-resolution of A/I^(n+1), using the datum's
perfectness hypothesis. Completed-constant-sheaf-reduction realizes it as a bounded
complex of finite-free retracts representing the quotient. Thus the quotient is
site-perfect. Apply perfect_projection_formula and compose with the direct image
of the canonical quotient pullback isomorphism. This is exactly the displayed map. -/
theorem reductionMap_isIso (n : ℕ) :
    SheafOfModules.IsPerfectOnSmallRingedSite (ring d Y) (quotient d Y n) ∧
      IsIso (reductionMap d f aY aX K n) := sorry

/-- The specified pi_n as an isomorphism, with the original projection map as its hom.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def reductionIso (n : ℕ) :
    aY.tensor.obj ((directImage d f).obj K, quotient d Y n) ≅
      (directImage d f).obj (reduction d aX K n) :=
  @asIso _ _ _ _ (reductionMap d f aY aX K n)
    (reductionMap_isIso d f aY aX K n).2

/-- rho_n is the unique inverse of the canonical, resolution-independent projection map.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
abbrev inverse (n : ℕ) := (reductionIso d f aY aX K n).inv

/-- The actual quotient homomorphism is linear for the completed coefficient action.
Source: blueprint order 1275, tower clause
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: define the map by the quotient ring map on sections. The limit cone equation
makes it linear. Ring-map naturality makes it commute with restrictions. The underlying
section functions determine a module-sheaf morphism uniquely. -/
theorem quotientModuleMap_existsUnique (T : Scheme.{u}) (n m : ℕ) (h : n ≤ m) :
    ∃! q : CompletedConstantReduction.residue T d.ideal m ⟶
      CompletedConstantReduction.residue T d.ideal n,
      ∀ (U : T.ProEtᵒᵖ)
        (x : (adicLisseConstantRing T (A ⧸ d.ideal ^ (m + 1))).obj.obj U),
        q.val.app U x =
          ((adicLisseRingSystem T d.ideal).map (homOfLE h).op).hom.app U x := sorry

/-- The quotient tower map retains its uniquely specified sectionwise quotient formula.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def quotientModuleMap (T : Scheme.{u}) (n m : ℕ) (h : n ≤ m) :=
  (quotientModuleMap_existsUnique d T n m h).exists.choose

/-- The positive quotient tower map in the ordinary completed-coefficient derived category.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def quotientMap (T : Scheme.{u}) (n m : ℕ) (h : n ≤ m) :
    quotient d T m ⟶ quotient d T n :=
  (DerivedCategory.singleFunctor (modules d T) 0).map (quotientModuleMap d T n m h)

/-- Quotient pullback comparisons commute with every quotient tower map.
Source: blueprint order 1275, proof steps 5 and 6
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: the two adjuncts are the same map on each constant quotient section, by
profinite-coefficient inverse-image naturality. The unique module comparisons and
exact termwise pullback preserve this equality in the derived category. -/
theorem quotientDerivedPullback_naturality (n m : ℕ) (h : n ≤ m) :
    (pullback d f).map (quotientMap d Y n m h) ≫ (quotientDerivedPullback d f n).hom =
      (quotientDerivedPullback d f m).hom ≫ quotientMap d X n m h := sorry

/-- Both the forward maps and their unique inverses commute with the whole quotient tower.
Source: blueprint order 1275, proof step 6
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: naturality of the canonical projection mate in its coefficient variable gives
the first equation, after quotientDerivedPullback_naturality identifies the target
maps. Multiply this square by the two inverse maps to get the second equation.
The argument applies to every n≤m, including equality, rather than only adjacent levels. -/
theorem tower_compatibility (n m : ℕ) (h : n ≤ m) :
    reductionMap d f aY aX K m ≫
      (directImage d f).map (aX.tensor.map (Prod.mkHom (𝟙 K) (quotientMap d X n m h))) =
    aY.tensor.map (Prod.mkHom (𝟙 ((directImage d f).obj K)) (quotientMap d Y n m h)) ≫
      reductionMap d f aY aX K n ∧
    inverse d f aY aX K m ≫
      aY.tensor.map (Prod.mkHom (𝟙 ((directImage d f).obj K)) (quotientMap d Y n m h)) =
    (directImage d f).map (aX.tensor.map (Prod.mkHom (𝟙 K) (quotientMap d X n m h))) ≫
      inverse d f aY aX K n := sorry

/-- The maps and inverses commute with coefficient-linear operators, also between objects.
Source: blueprint order 1275, proof step 6 and order 1274, paragraph 1
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: the counit mate is natural in K. Tensor this naturality with the fixed quotient
and use functoriality of direct image. Its quotient pullback identification is fixed,
so it does not change the square. Multiply by the two inverses for the reverse square.
Taking K'=K gives endomorphisms; families of these squares give compatible operators
on the reduction tower by tower_compatibility. -/
theorem operator_compatibility (K' : derived d X) (q : K ⟶ K') (n : ℕ) :
    reductionMap d f aY aX K n ≫
      (directImage d f).map (aX.tensor.map (Prod.mkHom q (𝟙 (quotient d X n)))) =
    aY.tensor.map (Prod.mkHom ((directImage d f).map q) (𝟙 (quotient d Y n))) ≫
      reductionMap d f aY aX K' n ∧
    inverse d f aY aX K n ≫
      aY.tensor.map (Prod.mkHom ((directImage d f).map q) (𝟙 (quotient d Y n))) =
    (directImage d f).map (aX.tensor.map (Prod.mkHom q (𝟙 (quotient d X n)))) ≫
      inverse d f aY aX K' n := sorry

/-- The canonical mixed representative square, for any flat K-flat second factor.
Source: Stacks 07A4 and blueprint order 1275, proof step 6
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: resolve the first complex by flat K-flat complexes. Tensor with the K-flat
second factor preserves the resolution quasi-isomorphism. Compose the tensor model's
representative comparison with its localization. Common refinements give the displayed
square for every resolution. Its left factor is invertible, which proves uniqueness. -/
theorem mixed_existsUnique (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (a : ProEtaleTensorModel T R) (I F : CochainComplex (proEtaleRingModules T R) ℤ)
    (hF : proEtaleFlatRepresentatives T R F) :
    ∃! e : a.tensor.obj (DerivedCategory.Q.obj I, DerivedCategory.Q.obj F) ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor I F (proEtaleOrdinaryTensor T R)),
      ∀ (P : CochainComplex (proEtaleRingModules T R) ℤ)
        (hP : proEtaleFlatRepresentatives T R P) (p : P ⟶ I), QuasiIso p →
        a.tensor.map (Prod.mkHom (DerivedCategory.Q.map p) (𝟙 (DerivedCategory.Q.obj F))) ≫
          e.hom = a.representative.inv.app (⟨P, hP⟩, ⟨F, hF⟩) ≫
            DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap p (𝟙 F)
              (proEtaleOrdinaryTensor T R) (ComplexShape.up ℤ)) := sorry

/-- The mixed comparison is determined by every resolution square, with no arbitrary choice.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def mixed (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (a : ProEtaleTensorModel T R) (I F : CochainComplex (proEtaleRingModules T R) ℤ)
    (hF : proEtaleFlatRepresentatives T R F) :=
  (mixed_existsUnique T R a I F hF).exists.choose

/-- The ordinary unit comparison is fixed by the ring map adjoint to the coefficients.
Source: blueprint order 1275, proof step 2; Stacks 03EL
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: on local generators of scalar extension multiply the coefficient scalar with
the inverse-image ring section, using c. Its inverse inserts the unit. Balancing gives
both inverse identities. The adjunction normalization gives the displayed equation;
these generating sections and sheafification give uniqueness. -/
theorem ordinaryUnit_existsUnique :
    ∃! j : (proEtaleRingModulePullback f (ring d Y) (ring d X) (coefficients d f)).obj
        (SheafOfModules.unit ((adicLisseForget Y).obj (ring d Y))) ≅
          SheafOfModules.unit ((adicLisseForget X).obj (ring d X)),
      ∀ (U : Y.ProEtᵒᵖ) (r : (ring d Y).obj.obj U),
        ((proEtaleRingModuleAdjunction f (ring d Y) (ring d X) (coefficients d f)).homEquiv
          _ _ j.hom).val.app U r =
        (proEtaleRingDirectImageMap f (ring d Y) (ring d X) (coefficients d f)).hom.app U r :=
  sorry

/-- The canonically normalized ordinary unit comparison.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def ordinaryUnit := (ordinaryUnit_existsUnique d f).exists.choose

/-- The ordinary right unit constraint of the existing sheaf tensor structure.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def ordinaryRightUnit (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (M : proEtaleRingModules T R) :=
  letI := SheafOfModules.monoidalCategory R
  ρ_ M

/-- The tensor of two module maps in the existing ordinary sheaf tensor structure.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def ordinaryTensorHom (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    {M N P Q : proEtaleRingModules T R} (v : M ⟶ N) (w : P ⟶ Q) :=
  letI := SheafOfModules.monoidalCategory R
  v ⊗ₘ w

/-- Compatibility of the ordinary tensor comparison with the actual tensor unit.
Source: blueprint order 1275, proof step 2; Stacks 03EL
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: both maps send s tensor (m tensor r) to s*c(r) times m. The pure-tensor
characterizations of both comparisons imply equality on all generators and hence
on their sheafifications. -/
theorem ordinaryUnit_coherence (M : modules d Y) :
    (proEtaleOrdinaryTensorPullback f (ring d Y) (ring d X) (coefficients d f) M
      (SheafOfModules.unit ((adicLisseForget Y).obj (ring d Y)))).hom ≫
      ordinaryTensorHom X (ring d X)
        (𝟙 ((proEtaleRingModulePullback f (ring d Y) (ring d X) (coefficients d f)).obj M))
        (ordinaryUnit d f).hom ≫
      (ordinaryRightUnit X (ring d X)
        ((proEtaleRingModulePullback f (ring d Y) (ring d X) (coefficients d f)).obj M)).hom =
    (proEtaleRingModulePullback f (ring d Y) (ring d X) (coefficients d f)).map
      (ordinaryRightUnit Y (ring d Y) M).hom := sorry

/-- Chosen representatives for evaluating the signed-totalization inverse at a quotient.
The maps represent the fixed K and the fixed quotient, rather than new derived objects.
Source: blueprint order 1275, proof steps 5--6
(blueprint: lemma-weil-pbc-perfect-projection-formula). -/
structure Resolution (n : ℕ) where
  injective : CochainComplex (modules d X) ℤ
  isKInjective : injective.IsKInjective
  representsK : K ≅ DerivedCategory.Q.obj injective
  coefficient : CochainComplex (modules d Y) ℤ
  bounded : ∃ l r : ℤ, ∀ i : ℤ, i < l ∨ r < i → IsZero (coefficient.X i)
  package : SheafOfModules.StrictPerfectCoefficientPackageOnSite
    ((adicLisseForget Y).obj (ring d Y)) coefficient
  representsQuotient : DerivedCategory.Q.obj coefficient ≅ quotient d Y n

/-- Every quotient admits the representatives used in the totalization comparison.
Source: blueprint order 1275, proof steps 5--6
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: take a K-injective representative of K in all module sheaves. Perfectness of
the quotient over A gives a bounded finite-projective A-resolution. Termwise constant
sheafification followed by completed scalar extension gives the coefficient complex;
completed-constant-sheaf-reduction supplies its augmentation quasi-isomorphism and
finite-free retracts. Localize the augmentation to obtain representsQuotient. -/
theorem resolution_exists (n : ℕ) : Nonempty (Resolution d (X := X) (Y := Y) K n) := sorry

variable {n : ℕ} (r : Resolution d (X := X) (Y := Y) K n)

/-- The ordinary module pullback used by every total complex below.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
abbrev ordinaryPull := proEtaleRingModulePullback f (ring d Y) (ring d X) (coefficients d f)

/-- The ordinary module direct image, before K-injective localization.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
abbrev ordinaryPush := proEtaleRingModuleDirectImage f (ring d Y) (ring d X) (coefficients d f)

/-- The signed total chain mate, with differential d_I tensor 1 + (-1)^a 1 tensor d_F.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def Resolution.total :=
  letI := SheafOfModules.monoidalCategory (ring d Y)
  letI := SheafOfModules.monoidalCategory (ring d X)
  tensorAdjunctionTotal (ordinaryPull d f) (ordinaryPush d f)
    (proEtaleRingModuleAdjunction f (ring d Y) (ring d X) (coefficients d f))
    (proEtaleOrdinaryTensorPullback f (ring d Y) (ring d X) (coefficients d f))
    (fun {_ _ _ _} v z ↦ proEtaleOrdinaryTensorPullback_naturality
      f (ring d Y) (ring d X) (coefficients d f) _ _ _ _ v z) r.injective r.coefficient

/-- The specified finite-total inverse, using the degreewise finite-free retract package.
The existing tensorAdjunctionTotalInverse_summand gives the required summand formula
(1 tensor p_r) q_(I^a,N_r) push(1 tensor pull(i_r)); its total is finite in each degree.
Source: blueprint order 1275 and definition 1264
(blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def Resolution.totalInverse :=
  letI := SheafOfModules.monoidalCategory (ring d Y)
  letI := SheafOfModules.monoidalCategory (ring d X)
  tensorAdjunctionTotalInverse (ordinaryPull d f) (ordinaryPush d f)
    (proEtaleRingModuleAdjunction f (ring d Y) (ring d X) (coefficients d f))
    (proEtaleOrdinaryTensorPullback f (ring d Y) (ring d X) (coefficients d f))
    (fun {_ _ _ _} v z ↦ proEtaleOrdinaryTensorPullback_naturality
      f (ring d Y) (ring d X) (coefficients d f) _ _ _ _ v z)
    (ordinaryUnit d f) (ordinaryUnit_coherence d f)
    r.injective r.coefficient r.bounded r.package.N r.package.i r.package.p r.package.splitting

/-- The coefficient model and its ordinary pullback are flat K-flat representatives.
Source: blueprint order 1275, proof steps 4--6
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: each degreewise term is a finite-free retract, hence flat. Bounded-above
flat complexes are K-flat. Apply canonical tensor pullback's preservation theorem
for the pullback representative. Both statements include zero terms and rank zero. -/
theorem Resolution.flat : proEtaleFlatRepresentatives Y (ring d Y) r.coefficient ∧
    proEtaleFlatRepresentatives X (ring d X)
      (((ordinaryPull d f).mapHomologicalComplex (.up ℤ)).obj r.coefficient) := sorry

/-- The actual total tensor complex on X used in the finite-total calculation.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def Resolution.targetComplex :=
  CochainComplex.mapBifunctor r.injective
    (((ordinaryPull d f).mapHomologicalComplex (.up ℤ)).obj r.coefficient)
    (proEtaleOrdinaryTensor X (ring d X))

/-- Tensoring the K-injective model with the pulled-back bounded finite-projective model
is K-injective. Source: blueprint order 1275, definition 1264
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: dualize the bounded finite-free retract package. Tensor with it identifies
with Hom from its bounded dual. The dual is K-flat, so Hom into a K-injective is
K-injective. This is the split-perfect-tensor-K-injective lemma. -/
theorem Resolution.targetComplex_isKInjective : (r.targetComplex d f K).IsKInjective := sorry

/-- The normalized K-injective model of the actual derived direct image of K.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def Resolution.pushModel :
    (directImage d f).obj K ≅ DerivedCategory.Q.obj
      (((ordinaryPush d f).mapHomologicalComplex (.up ℤ)).obj r.injective) :=
  letI := r.isKInjective
  (directImage d f).mapIso r.representsK ≪≫
    (@asIso _ _ _ _ ((ordinaryPush d f).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj r.injective))
      (proEtaleRingDerivedDirectImage_kInjective f (ring d Y) (ring d X)
        (coefficients d f) r.injective)).symm

/-- The normalized source comparison, specified by the mixed representative squares.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def Resolution.sourceModel :
    aY.tensor.obj ((directImage d f).obj K, quotient d Y n) ≅
      DerivedCategory.Q.obj
        (CochainComplex.mapBifunctor
          (((ordinaryPush d f).mapHomologicalComplex (.up ℤ)).obj r.injective)
          r.coefficient (proEtaleOrdinaryTensor Y (ring d Y))) :=
  aY.tensor.mapIso (Iso.prod (r.pushModel d f K) r.representsQuotient.symm) ≪≫
    mixed Y (ring d Y) aY _ r.coefficient (r.flat d f K).1

/-- The normalized target comparison, using exact pullback, mixed tensor and the
K-injective right-derived unit. Source: blueprint order 1275
(blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def Resolution.targetModel :
    (directImage d f).obj (reduction d aX K n) ≅ DerivedCategory.Q.obj
      (((ordinaryPush d f).mapHomologicalComplex (.up ℤ)).obj (r.targetComplex d f K)) :=
  letI := r.targetComplex_isKInjective d f K
  (directImage d f).mapIso
    (aX.tensor.mapIso (Iso.prod r.representsK
      ((quotientDerivedPullback d f n).symm ≪≫
        (pullback d f).mapIso r.representsQuotient.symm ≪≫
          (proEtaleRingDerivedPullbackFactors f (ring d Y) (ring d X)
            (coefficients d f)).app r.coefficient)) ≪≫
      mixed X (ring d X) aX _ _ (r.flat d f K).2) ≪≫
    (@asIso _ _ _ _ ((ordinaryPush d f).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj (r.targetComplex d f K)))
      (proEtaleRingDerivedDirectImage_kInjective f (ring d Y) (ring d X)
        (coefficients d f) (r.targetComplex d f K))).symm

/-- Agreement with signed totalization, for every chosen resolution, fixes both arrows
and proves resolution independence of the inverse.
Source: blueprint order 1275, first proof and proof step 6; Stacks 0944
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: use exact termwise pullback and the canonical tensor comparison on flat K-flat
representatives to compute the counit mate on the chosen models. The resulting forward
map is the localization of the ordinary signed total mate. Its finite-total inverse
has the prescribed degreewise retract formula and commutes with both differentials,
including the sign (-1)^a. Localizing gives the displayed reverse map. Totalization
proves both composite identities, so uniqueness of inverse identifies it with rho_n.
The statement quantifies over every model; thus changing either resolution or any
splitting package gives the same derived forward map and the same inverse. -/
theorem totalization_compatibility :
    reductionMap d f aY aX K n =
      (r.sourceModel d f aY K).hom ≫ DerivedCategory.Q.map (r.total d f K) ≫
        (r.targetModel d f aX K).inv ∧
    inverse d f aY aX K n =
      (r.targetModel d f aX K).hom ≫ DerivedCategory.Q.map (r.totalInverse d f K) ≫
        (r.sourceModel d f aY K).inv := sorry


section BaseChange

variable {X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {g : Y' ⟶ Y}
  (sq : ChosenCartesianSquare g' f' f g)
  (aY' : ProEtaleTensorModel Y' (ring d Y'))
  (aX' : ProEtaleTensorModel X' (ring d X'))

/-- The canonical completed coefficient identifications agree around the square.
Source: blueprint order 1275, proof step 6
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: use identity/composition coherence of profinite coefficient inverse image.
At every quotient the two composites preserve the same constant sections and agree
by square commutativity. The completed projections determine the comparison uniquely,
so the resulting composite coefficient isomorphisms agree, with the required transport. -/
theorem coefficients_square (sq : ChosenCartesianSquare g' f' f g) : HEq
    (proEtaleRingCompositeCoefficients g' f (ring d Y) (ring d X) (ring d X')
      (coefficients d f) (coefficients d g'))
    (proEtaleRingCompositeCoefficients f' g (ring d Y) (ring d Y') (ring d X')
      (coefficients d g) (coefficients d f')) := sorry

/-- The actual base-change morphism, with the canonical completed coefficient coherence.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def exchange :=
  proEtaleAmbientRingedExchange sq (ring d X) (ring d Y) (ring d X') (ring d Y')
    (coefficients d f) (coefficients d g) (coefficients d g') (coefficients d f')
    (coefficients_square d f sq)

/-- Source comparison in the reduction projection-formula square: tensor pullback,
then base change of K and the canonical quotient comparison.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def baseChangeSource (n : ℕ) :
    (pullback d g).obj (aY.tensor.obj ((directImage d f).obj K, quotient d Y n)) ⟶
      aY'.tensor.obj ((directImage d f').obj ((pullback d g').obj K), quotient d Y' n) :=
  (proEtaleCanonicalTensorComparison g (ring d Y) (ring d Y') (coefficients d g)
    aY aY').hom.app ((directImage d f).obj K, quotient d Y n) ≫
      aY'.tensor.map (Prod.mkHom ((exchange d f sq).app K)
        (quotientDerivedPullback d g n).hom)

/-- Target comparison in that square: ordinary ambient exchange and tensor pullback,
followed by the canonical quotient comparison. Exchange is not assumed invertible.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def baseChangeTarget (n : ℕ) :
    (pullback d g).obj ((directImage d f).obj (reduction d aX K n)) ⟶
      (directImage d f').obj (reduction d aX' ((pullback d g').obj K) n) :=
  (exchange d f sq).app (reduction d aX K n) ≫
    (directImage d f').map
      ((proEtaleCanonicalTensorComparison g' (ring d X) (ring d X') (coefficients d g')
        aX aX').hom.app (K, quotient d X n) ≫
          aX'.tensor.map (Prod.mkHom (𝟙 ((pullback d g').obj K))
            (quotientDerivedPullback d g' n).hom))

/-- Both directions of the reduction projection formula commute with base change.
Source: blueprint order 1275, proof step 6 and order 1274, base-change paragraph
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: apply projection-formula-base-change-naturality to Q=(P_(n+1))_Y and the
canonical completed coefficients. Coherence of the quotient pullback comparisons
identifies its source and target arrows with baseChangeSource and baseChangeTarget.
This gives the forward square. Multiply by the two projection inverses to obtain
the reverse square. No base-change-isomorphism hypothesis is used. -/
theorem baseChange_compatibility (n : ℕ) :
    (pullback d g).map (reductionMap d f aY aX K n) ≫
      baseChangeTarget d f aX K sq aX' n =
    baseChangeSource d f aY K sq aY' n ≫
      reductionMap d f' aY' aX' ((pullback d g').obj K) n ∧
    baseChangeTarget d f aX K sq aX' n ≫
      inverse d f' aY' aX' ((pullback d g').obj K) n =
    (pullback d g).map (inverse d f aY aX K n) ≫
      baseChangeSource d f aY K sq aY' n := sorry

end BaseChange

/-- Proper morphisms give precisely the identity-compactification formula and inverse,
after the displayed quotient pullback identification.
Source: blueprint order 1275, first proof; identity-compactification lemma, order 1272
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: identity-compactification identifies j_!, Lj^*, theta_1 and their constraints
with identities, so the ordered formula is the same projection mate. Compose with
the canonical quotient pullback identification for the forward equation and with
its inverse for the reverse equation. Uniqueness of inverse identifies rho_n. -/
theorem identityCompactification_compatibility [IsProper f] (n : ℕ) :
    reductionMap d f aY aX K n =
      IdentityProjectionCompactification.forward f (ring d Y) (ring d X)
        (coefficients d f) aY aX K (quotient d Y n) ≫
      (directImage d f).map
        (aX.tensor.map (Prod.mkHom (𝟙 K) (quotientDerivedPullback d f n).hom)) ∧
    inverse d f aY aX K n =
      (directImage d f).map
        (aX.tensor.map (Prod.mkHom (𝟙 K) (quotientDerivedPullback d f n).inv)) ≫
      IdentityProjectionCompactification.backward f (ring d Y) (ring d X)
        (coefficients d f) aY aX K (quotient d Y n)
        (reductionMap_isIso d f aY aX K n).1 := sorry

end AlgebraicGeometry.Scheme.PerfectProjection
