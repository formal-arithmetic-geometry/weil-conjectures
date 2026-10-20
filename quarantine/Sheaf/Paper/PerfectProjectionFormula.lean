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
import all Sheaf.Algebra.Homology.KFlatResolutionGeneral
import Sheaf.Paper.ProjectionMateExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.Paper.ProEtaleProjectionFormulaArrows
import Sheaf.Algebra.Homology.SplitPerfectTensorKInjective
import Sheaf.Paper.ProjectionFormulaTotalization
import Sheaf.Paper.RingedProjectionRestriction
public import Sheaf.Paper.CompletedConstantSheafReduction
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import WeilConjectures.Algebra.Homology.DerivedCategory.ProjectiveHom
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations

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
      (adicLisseRingSystem X d.ideal).map a := by
  let c : adicLisseRingSystem Y d.ideal ⋙
      proEtaleSheafInverseImage f CommRingCat.{u + 1} ⟶
        adicLisseRingSystem X d.ideal :=
    NatTrans.ofOpSequence
      (fun n ↦ (proEtaleConstantComparison f).app
        (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))))
      (fun n ↦ by
        simpa only [Functor.comp_map, adicLisseRingSystem,
          Functor.ofOpSequence_map_homOfLE_succ] using
          (proEtaleConstantComparison f).naturality
            (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1))))
  change 𝟙 _ ≫ _ ≫ c.app m = (_ ≫ c.app n) ≫ _
  rw [Category.id_comp, Category.assoc, ← c.naturality]
  rw [Functor.comp_map, ← Category.assoc, ← Functor.map_comp, limit.w]

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
theorem coefficientMap_isIso : IsIso (coefficientMap d f) := by
  let Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1} :=
    Functor.ofOpSequence (X := fun n ↦ CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))
      (fun n ↦ CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
  let c (T : Scheme.{u}) : proEtaleCoefficientTower T Q ⟶ adicLisseRingSystem T d.ideal :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
      intro n
      simp only [proEtaleCoefficientTower, Functor.comp_map, Q, adicLisseRingSystem,
        Functor.ofOpSequence_map_homOfLE_succ, Category.comp_id, Category.id_comp])
  have hc (T : Scheme.{u}) : IsIso (c T) := by
    have : ∀ n, IsIso ((c T).app n) := fun _ ↦ inferInstanceAs (IsIso (𝟙 _))
    exact NatIso.isIso_of_isIso_app _
  have : ∀ n : ℕᵒᵖ, Finite (Q.obj n) := fun n ↦ d.quotientFinite n.unop
  have hp := proEtale_profinite_coefficient_inverse_image Q
  have := hp.2.1 X Y f
  have := hc X
  have := hc Y
  have he : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (limMap (c Y)) ≫
      coefficientMap d f = proEtaleProfiniteComparison f Q ≫ limMap (c X) := by
    apply limit.hom_ext
    intro n
    simp only [Category.assoc, coefficientMap, limit.lift_π,
      limMap_π]
    change _ ≫ _ ≫ _ = _
    rw [← Category.assoc, ← Functor.map_comp, limMap_π]
    simp only [c, NatTrans.ofOpSequence_app, Category.comp_id]
    exact (hp.2.2.1 X Y f n).symm
  have : IsIso ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (limMap (c Y)) ≫
      coefficientMap d f) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (limMap (c Y)))
    (coefficientMap d f)

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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem moduleUnit_existsUnique
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    ∃! j : (proEtaleRingModulePullback f R S c).obj
        (SheafOfModules.unit ((adicLisseForget Y).obj R)) ≅
          SheafOfModules.unit ((adicLisseForget X).obj S),
      ∀ (U : Y.ProEtᵒᵖ) (r : R.obj.obj U),
        ((proEtaleRingModuleAdjunction f R S c).homEquiv
          _ _ j.hom).val.app U r =
        (proEtaleRingDirectImageMap f R S c).hom.app U r := by
  let adj := proEtaleRingModuleAdjunction f R S c
  let φ : (adicLisseForget Y).obj R ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj
          ((adicLisseForget X).obj S) :=
    ⟨Functor.whiskerRight
      (proEtaleRingDirectImageMap f R S c).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have : (SheafOfModules.pushforward.{u + 1} φ).IsRightAdjoint := adj.isRightAdjoint
  let adj' := SheafOfModules.pullbackPushforwardAdjunction.{u + 1} φ
  let e := adj.leftAdjointUniq adj'
  let j := e.app (SheafOfModules.unit ((adicLisseForget Y).obj R)) ≪≫
    asIso (SheafOfModules.pullbackObjUnitToUnit φ)
  have hj : adj.homEquiv _ _ j.hom = SheafOfModules.unitToPushforwardObjUnit φ := by
    change adj.homEquiv _ _ (e.hom.app _ ≫ _) = _
    rw [adj.homEquiv_naturality_right]
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    change adj'.homEquiv _ _ (SheafOfModules.pullbackObjUnitToUnit φ) = _
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit φ
  refine ⟨j, ?_, ?_⟩
  · intro U r
    exact congrArg (fun z ↦ z.val.app U r) hj
  · intro j' hj'
    apply Iso.ext
    apply (adj.homEquiv _ _).injective
    rw [hj]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    exact hj' U r

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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
              (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))))).hom.app U) x := by
  let RY := adicLisseConstantRing Y (A ⧸ d.ideal ^ (n + 1))
  let RX := adicLisseConstantRing X (A ⧸ d.ideal ^ (n + 1))
  have : IsIso ((proEtaleConstantComparison f).app
      (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))) := by
    let Q := (Functor.const ℕᵒᵖ).obj (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))
    have : ∀ i : ℕᵒᵖ, Finite (Q.obj i) := fun _ ↦ d.quotientFinite n
    exact (proEtale_profinite_coefficient_inverse_image Q).1 X Y f (op n)
  let c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX :=
    asIso ((proEtaleConstantComparison f).app
      (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))))
  let aY : ring d Y ⟶ RY := limit.π (adicLisseRingSystem Y d.ideal) (op n)
  let aX : ring d X ⟶ RX := limit.π (adicLisseRingSystem X d.ideal) (op n)
  have hc : (coefficients d f).hom ≫ aX =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aY ≫ c.hom :=
    limit.lift_π _ (op n)
  let resY := proEtaleRingRestrictScalars aY
  let resX := proEtaleRingRestrictScalars aX
  let adj := proEtaleRingModuleAdjunction f (ring d Y) (ring d X) (coefficients d f)
  let adj' := proEtaleRingModuleAdjunction f RY RX c
  let cmp := proEtaleRingRestrictionDirectImage f (ring d Y) RY (ring d X) RX
    aY aX (coefficients d f) c hc
  let t := proEtaleRingRestrictionPullbackInv f (ring d Y) RY (ring d X) RX
    aY aX (coefficients d f) c hc
  have : IsIso t := proEtaleRingRestrictionPullbackInv_isIso
    f (ring d Y) RY (ring d X) RX aY aX (coefficients d f) c hc
  obtain ⟨j, hj, _⟩ := moduleUnit_existsUnique f RY RX c
  let M := SheafOfModules.unit ((adicLisseForget Y).obj RY)
  let e : (proEtaleRingModulePullback f (ring d Y) (ring d X)
      (coefficients d f)).obj (CompletedConstantReduction.residue Y d.ideal n) ≅
        CompletedConstantReduction.residue X d.ideal n :=
    (asIso t).app M ≪≫ resX.mapIso j
  have he : adj.homEquiv _ _ e.hom =
      resY.map (adj'.homEquiv _ _ j.hom) ≫
        cmp.hom.app (SheafOfModules.unit ((adicLisseForget X).obj RX)) := by
    have ht : t.app M = (adj.homEquiv _ _).symm
        (resY.map (adj'.unit.app M) ≫
          cmp.hom.app ((proEtaleRingModulePullback f RY RX c).obj M)) := by
      change _ = (proEtaleRingModulePullback f (ring d Y) (ring d X)
        (coefficients d f)).map (_ ≫ _) ≫ _
      simp only [Functor.map_comp, Category.assoc]
      rfl
    change adj.homEquiv _ _ (t.app M ≫ resX.map j.hom) = _
    rw [adj.homEquiv_naturality_right, ht]
    erw [Equiv.apply_symm_apply]
    have hn := cmp.hom.naturality j.hom
    dsimp only [Functor.comp_map] at hn
    rw [Category.assoc, ← hn]
    simp only [← Category.assoc, Adjunction.homEquiv_unit]
    rw [resY.map_comp]
  have he' : ∀ (U : Y.ProEtᵒᵖ)
      (x : (adicLisseConstantRing Y (A ⧸ d.ideal ^ (n + 1))).obj.obj U),
      (adj.homEquiv _ _ e.hom).val.app U x =
        (proEtaleRingDirectImageMap f RY RX c).hom.app U x := by
    intro U x
    rw [he]
    change (cmp.hom.app (SheafOfModules.unit ((adicLisseForget X).obj RX))).val.app U
      ((adj'.homEquiv _ _ j.hom).val.app U x) = _
    erw [(Classical.choose_spec
      (proEtaleRingRestrictionDirectImage_existsUnique f (ring d Y) RY (ring d X) RX
        aY aX (coefficients d f) c hc)).1]
    exact hj U x
  refine ⟨e, he', ?_⟩
  intro e' he''
  apply Iso.ext
  apply (adj.homEquiv _ _).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (he'' U x).trans (he' U x).symm


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
theorem resolution_exists (n : ℕ) : Nonempty (Resolution d (X := X) (Y := Y) K n) := by
  classical
  have : IsNoetherianRing A := d.noetherian
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  obtain ⟨I, hI, ⟨eI⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  obtain ⟨F, a, b, ha, hb, hF, ⟨eF⟩⟩ := d.quotientPerfect (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  have := ha
  have := hb
  have (i : ℤ) : Module.Projective A (F.X i) := (hF i).1
  have (i : ℤ) : Projective (F.X i) := inferInstance
  let Q := (CochainComplex.singleFunctor (ModuleCat.{u + 1} A) 0).obj
    (ModuleCat.of A (A ⧸ d.ideal ^ (n + 1)))
  obtain ⟨q, hq⟩ := DerivedCategory.Q_map_surjective_of_projective F Q b eF.inv
  have : IsIso (DerivedCategory.Q.map q) := by rw [hq]; infer_instance
  have hq' : QuasiIso q :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u + 1} A) q).mp inferInstance
  have hbound : ∀ i : ℤ, i < a ∨ b < i → IsZero (F.X i) := by
    intro i hi
    rcases hi with hi | hi
    · exact F.isZero_of_isStrictlyGE a i hi
    · exact F.isZero_of_isStrictlyLE b i hi
  obtain ⟨hred, hret, hbounded⟩ :=
    (CompletedConstantReduction.completed_constant_sheaf_reduction Y d.ideal).2.2.2
      n F q a b hq' (fun i ↦ ⟨(hF i).2, (hF i).1⟩) hbound
  let C := ((completedAdicChange Y
    (CompletedConstantReduction.base Y d.ideal)).mapHomologicalComplex
    (.up ℤ)).obj ((CompletedConstantReduction.constantComplex Y A).obj F)
  have : HasFiniteBiproducts (modules d Y) := HasFiniteBiproducts.of_hasFiniteProducts
  choose N i p hip using hret
  let e (j : ℤ) := biproductIso (fun _ : Fin (N j) ↦
    SheafOfModules.unit ((adicLisseForget Y).obj (ring d Y)))
  let pkg : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget Y).obj (ring d Y)) C :=
    { N := N
      i := fun j ↦ i j ≫ (e j).inv
      p := fun j ↦ (e j).hom ≫ p j
      splitting := fun j ↦ by
        simp only [Category.assoc, Iso.inv_hom_id_assoc, hip]
        rfl }
  let q' := CompletedConstantReduction.reductionComplex Y d.ideal n
    ((CompletedConstantReduction.constantComplex Y A).obj F)
    (CompletedConstantReduction.constantAugmentation Y d.ideal n F q)
  have : QuasiIso q' := hred
  let eq : DerivedCategory.Q.obj C ≅ quotient d Y n :=
    asIso (DerivedCategory.Q.map q')
  exact ⟨⟨I, hI, eI, C, ⟨a, b, hbounded⟩, pkg, eq⟩⟩


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
      IsIso (reductionMap d f aY aX K n) := by
  obtain ⟨r⟩ := resolution_exists d (X := X) (Y := Y) K n
  have hperfect : SheafOfModules.IsPerfectOnSmallRingedSite (ring d Y) (quotient d Y n) := by
    refine ⟨r.coefficient, ?_, ⟨r.representsQuotient.symm⟩⟩
    intro V
    refine ⟨⊤, (ProEt.topology Y).top_mem V, ?_⟩
    intro U g _
    let L := SheafOfModules.overFunctor ((adicLisseForget Y).obj (ring d Y)) U
    have : PreservesFiniteLimits L := by
      let T := SheafOfModules.forget.{u + 1}
        (((adicLisseForget Y).obj (ring d Y)).over U) ⋙
          PresheafOfModules.toPresheaf (((adicLisseForget Y).obj (ring d Y)).over U).obj
      have : PreservesFiniteLimits (L ⋙ T) := by
        change PreservesFiniteLimits
          ((SheafOfModules.forget.{u + 1} ((adicLisseForget Y).obj (ring d Y)) ⋙
            PresheafOfModules.toPresheaf ((adicLisseForget Y).obj (ring d Y)).obj) ⋙
              (Functor.whiskeringLeft _ _ _).obj (Over.forget U).op)
        infer_instance
      exact preservesFiniteLimits_of_reflects_of_preserves L T
    let e (m : ℕ) :
        L.obj (∏ᶜ fun _ : Fin m ↦ SheafOfModules.unit ((adicLisseForget Y).obj (ring d Y))) ≅
          ∏ᶜ fun _ : Fin m ↦
            SheafOfModules.unit (((adicLisseForget Y).obj (ring d Y)).over U) :=
      PreservesProduct.iso L _
    let pkg : SheafOfModules.StrictPerfectCoefficientPackageOnSite
        (((adicLisseForget Y).obj (ring d Y)).over U)
        ((L.mapHomologicalComplex (.up ℤ)).obj r.coefficient) :=
      { N := r.package.N
        i := fun i ↦ L.map (r.package.i i) ≫ (e (r.package.N i)).hom
        p := fun i ↦ (e (r.package.N i)).inv ≫ L.map (r.package.p i)
        splitting := fun i ↦ by
          simp only [Category.assoc, Iso.hom_inv_id_assoc, ← L.map_comp,
            r.package.splitting, L.map_id]
          rfl }
    refine ⟨(L.mapHomologicalComplex (.up ℤ)).obj r.coefficient, ?_, ⟨pkg⟩, 𝟙 _, ?_⟩
    · obtain ⟨a, b, hab⟩ := r.bounded
      exact ⟨a, b, fun i hi ↦ L.map_isZero (hab i hi)⟩
    · infer_instance
  refine ⟨hperfect, ?_⟩
  have : IsIso (projection d f aY aX K (quotient d Y n)) :=
    (perfect_projection_formula d f aY aX K).2.2.2 _ hperfect
  change IsIso (projection d f aY aX K (quotient d Y n) ≫
    (directImage d f).map
      (aX.tensor.mapIso (Iso.prod (Iso.refl K) (quotientDerivedPullback d f n))).hom)
  infer_instance

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
        ((adicLisseRingSystem T d.ideal).map (homOfLE h).op).hom.app U x := by
  let q := (adicLisseRingSystem T d.ideal).map (homOfLE h).op
  let φ : (CompletedConstantReduction.residue T d.ideal m).val.presheaf ⟶
      (CompletedConstantReduction.residue T d.ideal n).val.presheaf :=
    Functor.whiskerRight q.hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})
  let qm : CompletedConstantReduction.residue T d.ideal m ⟶
      CompletedConstantReduction.residue T d.ideal n :=
    ⟨PresheafOfModules.homMk φ (by
      intro U r x
      change (adicLisseConstantRing T (A ⧸ d.ideal ^ (m + 1))).obj.obj U at x
      change q.hom.app U
          ((show (adicLisseConstantRing T (A ⧸ d.ideal ^ (m + 1))).obj.obj U from
            (limit.π (adicLisseRingSystem T d.ideal) (op m)).hom.app U r) * x) =
        (show (adicLisseConstantRing T (A ⧸ d.ideal ^ (n + 1))).obj.obj U from
          (limit.π (adicLisseRingSystem T d.ideal) (op n)).hom.app U r) *
            (show (adicLisseConstantRing T (A ⧸ d.ideal ^ (n + 1))).obj.obj U from
              q.hom.app U x)
      rw [map_mul]
      congr 1
      exact congrArg (fun z ↦ z.hom.app U r)
        (limit.w (adicLisseRingSystem T d.ideal) (homOfLE h).op))⟩
  refine ⟨qm, fun _ _ ↦ rfl, ?_⟩
  intro qm' hqm'
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact hqm' U x

/-- The quotient tower map retains its uniquely specified sectionwise quotient formula.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def quotientModuleMap (T : Scheme.{u}) (n m : ℕ) (h : n ≤ m) :=
  (quotientModuleMap_existsUnique d T n m h).exists.choose

/-- The positive quotient tower map in the ordinary completed-coefficient derived category.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def quotientMap (T : Scheme.{u}) (n m : ℕ) (h : n ≤ m) :
    quotient d T m ⟶ quotient d T n :=
  (DerivedCategory.singleFunctor (modules d T) 0).map (quotientModuleMap d T n m h)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Quotient pullback comparisons commute with every quotient tower map.
Source: blueprint order 1275, proof steps 5 and 6
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: the two adjuncts are the same map on each constant quotient section, by
profinite-coefficient inverse-image naturality. The unique module comparisons and
exact termwise pullback preserve this equality in the derived category. -/
theorem quotientDerivedPullback_naturality (n m : ℕ) (h : n ≤ m) :
    (pullback d f).map (quotientMap d Y n m h) ≫ (quotientDerivedPullback d f n).hom =
      (quotientDerivedPullback d f m).hom ≫ quotientMap d X n m h := by
  let L := proEtaleRingModulePullback f (ring d Y) (ring d X) (coefficients d f)
  let adj := proEtaleRingModuleAdjunction f (ring d Y) (ring d X) (coefficients d f)
  let adjR := proEtaleSheafAdjunction f CommRingCat.{u + 1}
  let c : adicLisseRingSystem Y d.ideal ⋙
      proEtaleSheafInverseImage f CommRingCat.{u + 1} ⟶
        adicLisseRingSystem X d.ideal :=
    NatTrans.ofOpSequence
      (fun n ↦ (proEtaleConstantComparison f).app
        (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))))
      (fun n ↦ by
        simpa only [Functor.comp_map, adicLisseRingSystem,
          Functor.ofOpSequence_map_homOfLE_succ] using
          (proEtaleConstantComparison f).naturality
            (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1))))
  have hr := congrArg (adjR.homEquiv _ _) (c.naturality (homOfLE h).op)
  simp only [Functor.comp_map, adjR.homEquiv_naturality_left,
    adjR.homEquiv_naturality_right] at hr
  have hm : L.map (quotientModuleMap d Y n m h) ≫ (quotientPullback d f n).hom =
      (quotientPullback d f m).hom ≫ quotientModuleMap d X n m h := by
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (adj.homEquiv _ _ (quotientPullback d f n).hom).val.app U
        ((quotientModuleMap d Y n m h).val.app U x) =
      (quotientModuleMap d X n m h).val.app ((proEtaleBaseChange f).op.obj U)
        ((adj.homEquiv _ _ (quotientPullback d f m).hom).val.app U x)
    dsimp only [quotientModuleMap, quotientPullback, adj]
    rw [(quotientModuleMap_existsUnique d Y n m h).exists.choose_spec,
      (quotientPullback_existsUnique d f n).exists.choose_spec,
      (quotientPullback_existsUnique d f m).exists.choose_spec,
      (quotientModuleMap_existsUnique d X n m h).exists.choose_spec]
    exact congrArg (fun z ↦ z.hom.app U x) hr
  have hn := (L.mapDerivedCategorySingleFunctor 0).hom.naturality
    (quotientModuleMap d Y n m h)
  change (pullback d f).map (quotientMap d Y n m h) ≫
      (L.mapDerivedCategorySingleFunctor 0).hom.app _ ≫
        (DerivedCategory.singleFunctor (modules d X) 0).map (quotientPullback d f n).hom =
    ((L.mapDerivedCategorySingleFunctor 0).hom.app _ ≫
      (DerivedCategory.singleFunctor (modules d X) 0).map (quotientPullback d f m).hom) ≫ _
  dsimp only [Functor.comp_map] at hn
  dsimp only [pullback, proEtaleRingDerivedPullback, quotientMap]
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← Functor.map_comp, hm]


private theorem inverse_square {C : Type*} [Category C]
    {S S' T T' : C} (p : S ⟶ T) (p' : S' ⟶ T')
    [IsIso p] [IsIso p'] (a : S ⟶ S') (b : T ⟶ T')
    (h : p ≫ b = a ≫ p') : inv p ≫ a = b ≫ inv p' := by
  apply (cancel_mono p').1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← h, IsIso.inv_hom_id_assoc]

private theorem projection_naturality {P Q : derived d Y} (q : P ⟶ Q) :
    aY.tensor.map (Prod.mkHom (𝟙 ((directImage d f).obj K)) q) ≫
        projection d f aY aX K Q =
      projection d f aY aX K P ≫
        (directImage d f).map
          (aX.tensor.map (Prod.mkHom (𝟙 K) ((pullback d f).map q))) := by
  exact (((proEtaleRingDerivedAdjunction f (ring d Y) (ring d X)
    (coefficients d f)).rightAdjointProjectionMap
    (T_C := Functor.curry.obj aX.tensor) (T_D := Functor.curry.obj aY.tensor)
    (Functor.curry.map (proEtaleCanonicalTensorComparison f (ring d Y) (ring d X)
      (coefficients d f) aY aX).hom ≫
        (Functor.curryObjProdComp (pullback d f) (pullback d f) aX.tensor).hom)).app K).naturality q

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
      inverse d f aY aX K n := by
  have hnat := projection_naturality d f aY aX K (quotientMap d Y n m h)
  have hs := congrArg (fun z ↦ z ≫ (directImage d f).map
    (aX.tensor.map (Prod.mkHom (𝟙 K) (quotientDerivedPullback d f n).hom))) hnat
  simp only [Category.assoc, ← Functor.map_comp, prod_comp,
    Category.comp_id] at hs
  rw [quotientDerivedPullback_naturality d f n m h] at hs
  have hf : reductionMap d f aY aX K m ≫
      (directImage d f).map (aX.tensor.map (Prod.mkHom (𝟙 K) (quotientMap d X n m h))) =
    aY.tensor.map (Prod.mkHom (𝟙 ((directImage d f).obj K)) (quotientMap d Y n m h)) ≫
      reductionMap d f aY aX K n := by
    simpa only [reductionMap, Category.assoc, ← Functor.map_comp, prod_comp,
      Category.id_comp, Category.comp_id] using hs.symm
  refine ⟨hf, ?_⟩
  have := (reductionMap_isIso d f aY aX K m).2
  have := (reductionMap_isIso d f aY aX K n).2
  exact inverse_square _ _ _ _ hf

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
      inverse d f aY aX K' n := by
  have h : reductionMap d f aY aX K n ≫
      (directImage d f).map (aX.tensor.map (Prod.mkHom q (𝟙 (quotient d X n)))) =
    aY.tensor.map (Prod.mkHom ((directImage d f).map q) (𝟙 (quotient d Y n))) ≫
      reductionMap d f aY aX K' n := by
    have hnat := derivedProjectionFormulaMate_naturality (pullback d f) (directImage d f)
      (proEtaleRingDerivedAdjunction f (ring d Y) (ring d X) (coefficients d f))
      aY.tensor aX.tensor
      (proEtaleCanonicalTensorComparison f (ring d Y) (ring d X) (coefficients d f) aY aX)
      K K' (quotient d Y n) q
    change projection d f aY aX K (quotient d Y n) ≫ _ =
      _ ≫ projection d f aY aX K' (quotient d Y n) at hnat
    simpa only [reductionMap, Category.assoc, ← Functor.map_comp, prod_comp,
      Category.id_comp, Category.comp_id] using
      congrArg (fun z ↦ z ≫ (directImage d f).map
        (aX.tensor.map (Prod.mkHom (𝟙 K') (quotientDerivedPullback d f n).hom))) hnat
  refine ⟨h, ?_⟩
  have := (reductionMap_isIso d f aY aX K n).2
  have := (reductionMap_isIso d f aY aX K' n).2
  exact inverse_square _ _ _ _ h

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
              (proEtaleOrdinaryTensor T R) (ComplexShape.up ℤ)) := by
  exact proEtaleMixedTensor_existsUnique R a I F hF

/-- The mixed comparison is determined by every resolution square, with no arbitrary choice.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def mixed (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (a : ProEtaleTensorModel T R) (I F : CochainComplex (proEtaleRingModules T R) ℤ)
    (hF : proEtaleFlatRepresentatives T R F) :=
  (mixed_existsUnique T R a I F hF).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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
        (proEtaleRingDirectImageMap f (ring d Y) (ring d X) (coefficients d f)).hom.app U r := by
  exact moduleUnit_existsUnique f (ring d Y) (ring d X) (coefficients d f)

/-- The canonically normalized ordinary unit comparison.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def ordinaryUnit := (ordinaryUnit_existsUnique d f).exists.choose

/-- The ordinary right unit constraint of the existing sheaf tensor structure.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def ordinaryRightUnit (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (M : proEtaleRingModules T R) :
    ((proEtaleOrdinaryTensor T R).obj M).obj
      (SheafOfModules.unit ((adicLisseForget T).obj R)) ≅ M :=
  letI := SheafOfModules.monoidalCategory R
  let S := PresheafOfModules.sheafification.{u + 1}
    (𝟙 ((adicLisseForget T).obj R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((adicLisseForget T).obj R).obj)
  SheafOfModules.tensorObjIsoSheafification M
      (SheafOfModules.unit ((adicLisseForget T).obj R)) ≪≫
    S.mapIso (ρ_ M.val) ≪≫ (asIso adj.counit).app M

/-- The tensor of two module maps in the existing ordinary sheaf tensor structure.
Source: blueprint order 1275 (blueprint: lemma-weil-pbc-perfect-projection-formula). -/
def ordinaryTensorHom (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    {M N P Q : proEtaleRingModules T R} (v : M ⟶ N) (w : P ⟶ Q) :
    ((proEtaleOrdinaryTensor T R).obj M).obj P ⟶
      ((proEtaleOrdinaryTensor T R).obj N).obj Q :=
  letI := SheafOfModules.monoidalCategory R
  v ⊗ₘ w

section UnitHelpers

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction

variable (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})

set_option backward.isDefEq.respectTransparency false in
private theorem unit_test (M : proEtaleRingModules T R) :
    let := SheafOfModules.monoidalCategory R
    (SheafOfModules.tensorObjIsoSheafification M
      (SheafOfModules.unit ((adicLisseForget T).obj R))).inv ≫ (ordinaryRightUnit T R M).hom =
    (PresheafOfModules.sheafification.{u + 1}
      (𝟙 ((adicLisseForget T).obj R).obj)).map (ρ_ M.val).hom ≫
      (PresheafOfModules.sheafificationAdjunction.{u + 1}
        (𝟙 ((adicLisseForget T).obj R).obj)).counit.app M := by
  simp only [ordinaryRightUnit, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, asIso_hom, Iso.inv_hom_id_assoc]

private theorem oplax_unit_map
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.OplaxMonoidal] (M : C) (N : D) (v : F.obj M ⟶ N) :
    Functor.OplaxMonoidal.δ F M (𝟙_ C) ≫
        (v ⊗ₘ Functor.OplaxMonoidal.η F) ≫ (ρ_ N).hom = F.map (ρ_ M).hom ≫ v := by
  rw [tensorHom_def', Category.assoc, rightUnitor_naturality]
  simp only [Functor.OplaxMonoidal.right_unitality_hom_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem canonicalRightUnit_sheafification (M : proEtaleRingModules T R) :
    let := SheafOfModules.monoidalCategory R
    (SheafOfModules.tensorObjIsoSheafification M
      (SheafOfModules.unit ((adicLisseForget T).obj R))).inv ≫ (ρ_ M).hom =
    (PresheafOfModules.sheafification.{u + 1}
      (𝟙 ((adicLisseForget T).obj R).obj)).map (ρ_ M.val).hom ≫
      (PresheafOfModules.sheafificationAdjunction.{u + 1}
        (𝟙 ((adicLisseForget T).obj R).obj)).counit.app M := by
  let := SheafOfModules.monoidalCategory R
  let S := PresheafOfModules.sheafification.{u + 1}
    (𝟙 ((adicLisseForget T).obj R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((adicLisseForget T).obj R).obj)
  simp only [SheafOfModules.tensorObjIsoSheafification, Iso.trans_inv, Iso.symm_inv,
    tensorIso_hom, Iso.app_hom, Functor.Monoidal.μIso_inv, asIso_hom]
  have hη : adj.counit.app
      (SheafOfModules.unit ((adicLisseForget T).obj R)) = Functor.OplaxMonoidal.η S := rfl
  rw [hη]
  exact oplax_unit_map S M.val M (adj.counit.app M)

set_option backward.isDefEq.respectTransparency false in
/-- The explicit sheafification construction is the existing monoidal right unitor.
Source: Stacks 03EL (blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: precompose with the tensor/sheafification isomorphism. Both maps become
sheafification of the presheaf unitor followed by the sheafification counit,
by oplax monoidal unitality. -/
theorem ordinaryRightUnit_eq (M : proEtaleRingModules T R) :
    let := SheafOfModules.monoidalCategory R
    ordinaryRightUnit T R M = ρ_ M := by
  let := SheafOfModules.monoidalCategory R
  apply Iso.ext
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M
    (SheafOfModules.unit ((adicLisseForget T).obj R))).inv).mp
  rw [unit_test, canonicalRightUnit_sheafification]

set_option backward.isDefEq.respectTransparency false in
private theorem rightUnit_pair (M : proEtaleRingModules T R) (U : T.ProEtᵒᵖ)
    (m : M.val.obj U) (r : R.obj.obj U) :
    let := SheafOfModules.monoidalCategory R
    (ordinaryRightUnit T R M).hom.val.app U
      (proEtaleTensorPair T R M (SheafOfModules.unit ((adicLisseForget T).obj R)) U m r) =
        r • m := by
  let := SheafOfModules.monoidalCategory R
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((adicLisseForget T).obj R).obj)
  have he : adj.homEquiv _ M
      ((SheafOfModules.tensorObjIsoSheafification M
        (SheafOfModules.unit ((adicLisseForget T).obj R))).inv ≫ (ordinaryRightUnit T R M).hom) =
      (ρ_ M.val).hom := by
    rw [unit_test]
    have h := (adj.homEquiv (M.val ⊗ (SheafOfModules.unit
      ((adicLisseForget T).obj R)).val) M).apply_symm_apply ((ρ_ M.val).hom)
    rw [Adjunction.homEquiv_counit] at h
    exact h
  exact congrArg (fun z ↦ z.app U (m ⊗ₜ[R.obj.obj U] r)) he

private theorem tensor_hom_ext (M N P : proEtaleRingModules T R)
    (v w : ((proEtaleOrdinaryTensor T R).obj M).obj N ⟶ P)
    (h : ∀ U m n, v.val.app U (proEtaleTensorPair T R M N U m n) =
      w.val.app U (proEtaleTensorPair T R M N U m n)) : v = w := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((adicLisseForget T).obj R).obj)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply (adj.homEquiv (M.val ⊗ N.val) P).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  exact h U m n

private theorem pair_natural {M N N' : proEtaleRingModules T R}
    (w : N ⟶ N') (U : T.ProEtᵒᵖ) (m : M.val.obj U) (n : N.val.obj U) :
    let := SheafOfModules.monoidalCategory R
    (M ◁ w).val.app U (proEtaleTensorPair T R M N U m n) =
      proEtaleTensorPair T R M N' U m (w.val.app U n) := by
  let := SheafOfModules.monoidalCategory R
  let S := PresheafOfModules.sheafification.{u + 1}
    (𝟙 ((adicLisseForget T).obj R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((adicLisseForget T).obj R).obj)
  have hn := SheafOfModules.whiskerLeft_tensorObjIsoSheafification_hom_kfg
    (R := R) M w
  have hi : (SheafOfModules.tensorObjIsoSheafification (R := R) M N).inv ≫ (M ◁ w) =
      S.map (M.val ◁ w.val) ≫
        (SheafOfModules.tensorObjIsoSheafification (R := R) M N').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hn, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have he := congrArg (fun z ↦ adj.homEquiv _ _ z) hi
  rw [Adjunction.homEquiv_naturality_left] at he
  exact congrArg (fun z ↦ z.app U (m ⊗ₜ[R.obj.obj U] n)) he

attribute [local irreducible] SheafOfModules.monoidalCategory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem moduleUnit_tensor_coherence
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (j : (proEtaleRingModulePullback f R S c).obj
      (SheafOfModules.unit ((adicLisseForget Y).obj R)) ≅
        SheafOfModules.unit ((adicLisseForget X).obj S))
    (hj : ∀ (U : Y.ProEtᵒᵖ) (r : R.obj.obj U),
      ((proEtaleRingModuleAdjunction f R S c).homEquiv _ _ j.hom).val.app U r =
        (proEtaleRingDirectImageMap f R S c).hom.app U r)
    (M : proEtaleRingModules Y R) :
    (proEtaleOrdinaryTensorPullback f R S c M
      (SheafOfModules.unit ((adicLisseForget Y).obj R))).hom ≫
      ordinaryTensorHom X S
        (𝟙 ((proEtaleRingModulePullback f R S c).obj M))
        j.hom ≫
      (ordinaryRightUnit X S
        ((proEtaleRingModulePullback f R S c).obj M)).hom =
    (proEtaleRingModulePullback f R S c).map
      (ordinaryRightUnit Y R M).hom := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let adj := proEtaleRingModuleAdjunction f R S c
  let L := proEtaleRingModulePullback f R S c
  have hr : adj.homEquiv
      (((proEtaleOrdinaryTensor Y R).obj M).obj
        (SheafOfModules.unit ((adicLisseForget Y).obj R)))
      (L.obj M) (L.map (ordinaryRightUnit Y R M).hom) =
      (ordinaryRightUnit Y R M).hom ≫ adj.unit.app M := by
    rw [← Category.comp_id (L.map _), adj.homEquiv_naturality_left, adj.homEquiv_id]
  apply (adj.homEquiv _ _).injective
  rw [hr, adj.homEquiv_naturality_right, Functor.map_comp]
  apply tensor_hom_ext Y R
  intro U m r
  change (ordinaryRightUnit X S _).hom.val.app
      (op ((proEtaleBaseChange f).obj U.unop))
      ((ordinaryTensorHom X S (𝟙 _) j.hom).val.app _
        ((adj.homEquiv _ _ (proEtaleOrdinaryTensorPullback f R S c M
          (SheafOfModules.unit ((adicLisseForget Y).obj R))).hom).val.app U
            (proEtaleTensorPair Y R _ _ U m r))) =
    (adj.unit.app M).val.app U
      ((ordinaryRightUnit Y R M).hom.val.app U
        (proEtaleTensorPair Y R _ _ U m r))
  erw [((proEtaleOrdinaryTensorPullback_existsUnique f R S
    c).exists.choose_spec).2 M _ U.unop m r]
  let W := op ((proEtaleBaseChange f).obj U.unop)
  let x : (L.obj M).val.obj W := (adj.unit.app M).val.app U m
  let y : (L.obj (SheafOfModules.unit ((adicLisseForget Y).obj R))).val.obj W :=
    (adj.unit.app (SheafOfModules.unit ((adicLisseForget Y).obj R))).val.app U r
  have hp := pair_natural X S j.hom W x y
  have hs := congrArg (fun z ↦ (ordinaryRightUnit X S (L.obj M)).hom.val.app W z) hp
  simp only [ordinaryTensorHom, id_tensorHom]
  refine hs.trans ?_
  have hu := rightUnit_pair X S (L.obj M) W x (j.hom.val.app W y)
  have hv := rightUnit_pair Y R M U m r
  have hj' := hj U r
  rw [Adjunction.homEquiv_unit] at hj'
  change j.hom.val.app W y = _ at hj'
  calc
    _ = (show S.obj.obj W from j.hom.val.app W y) • x := hu
    _ = (show S.obj.obj W from (proEtaleRingDirectImageMap f R S c).hom.app U r) • x :=
      congrArg (fun z ↦ z • x) hj'
    _ = (adj.unit.app M).val.app U (r • m) := by
      rw [map_smul]
      rfl
    _ = _ := congrArg ((adj.unit.app M).val.app U) hv.symm

end UnitHelpers

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
      (ordinaryRightUnit Y (ring d Y) M).hom := by
  exact moduleUnit_tensor_coherence f (ring d Y) (ring d X) (coefficients d f)
    (ordinaryUnit d f) (ordinaryUnit_existsUnique d f).exists.choose_spec M


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
    (ordinaryUnit d f) (fun M ↦ by
      have h := ordinaryUnit_coherence d f M
      rw [ordinaryRightUnit_eq, ordinaryRightUnit_eq] at h
      exact h)
    r.injective r.coefficient r.bounded r.package.N r.package.i r.package.p r.package.splitting

/-- The coefficient model and its ordinary pullback are flat K-flat representatives.
Source: blueprint order 1275, proof steps 4--6
(blueprint: lemma-weil-pbc-perfect-projection-formula).
Proof: each degreewise term is a finite-free retract, hence flat. Bounded-above
flat complexes are K-flat. Apply canonical tensor pullback's preservation theorem
for the pullback representative. Both statements include zero terms and rank zero. -/
theorem Resolution.flat : proEtaleFlatRepresentatives Y (ring d Y) r.coefficient ∧
    proEtaleFlatRepresentatives X (ring d X)
      (((ordinaryPull d f).mapHomologicalComplex (.up ℤ)).obj r.coefficient) := by
  refine ⟨proEtaleStrictPerfect_flat (ring d Y) r.coefficient r.package r.bounded, ?_⟩
  let L := ordinaryPull d f
  let e (m : ℕ) :
      L.obj (∏ᶜ fun _ : Fin m ↦ SheafOfModules.unit ((adicLisseForget Y).obj (ring d Y))) ≅
        ∏ᶜ fun _ : Fin m ↦ SheafOfModules.unit ((adicLisseForget X).obj (ring d X)) :=
    PreservesProduct.iso L _ ≪≫ Pi.mapIso (fun _ ↦ ordinaryUnit d f)
  let P : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget X).obj (ring d X))
      ((L.mapHomologicalComplex (.up ℤ)).obj r.coefficient) :=
    { N := r.package.N
      i := fun i ↦ L.map (r.package.i i) ≫ (e (r.package.N i)).hom
      p := fun i ↦ (e (r.package.N i)).inv ≫ L.map (r.package.p i)
      splitting := fun i ↦ by
        simp only [Category.assoc, Iso.hom_inv_id_assoc, ← L.map_comp, r.package.splitting,
          L.map_id]
        rfl }
  apply proEtaleStrictPerfect_flat (ring d X) _ P
  obtain ⟨l, h, hb⟩ := r.bounded
  exact ⟨l, h, fun i hi ↦ L.map_isZero (hb i hi)⟩

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
theorem Resolution.targetComplex_isKInjective : (r.targetComplex d f K).IsKInjective := by
  let := SheafOfModules.monoidalCategory (ring d Y)
  let := SheafOfModules.monoidalCategory (ring d X)
  exact tensorAdjunctionTotal_target_isKInjective (ordinaryPull d f) (ordinaryUnit d f)
    r.injective r.isKInjective r.coefficient r.bounded
    r.package.N r.package.i r.package.p r.package.splitting

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


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficientMap_comp {Z : Scheme.{u}} (g : Y ⟶ Z) :
    coefficientMap d (f ≫ g) =
      (proEtaleRingInverseImageComp f g).hom.app (ring d Z) ≫
        (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (coefficientMap d g) ≫
          coefficientMap d f := by
  apply limit.hom_ext
  intro n
  have hπ (V W : Scheme.{u}) (k : V ⟶ W) :
      coefficientMap d k ≫ limit.π (adicLisseRingSystem V d.ideal) n =
        (proEtaleSheafInverseImage k CommRingCat.{u + 1}).map
          (limit.π (adicLisseRingSystem W d.ideal) n) ≫
            (proEtaleConstantComparison k).app
              (CommRingCat.of (A ⧸ d.ideal ^ (n.unop + 1))) :=
    limit.lift_π _ n
  have : Finite (A ⧸ d.ideal ^ (n.unop + 1)) := d.quotientFinite n.unop
  let Q := (Functor.const ℕᵒᵖ).obj (CommRingCat.of (A ⧸ d.ideal ^ (n.unop + 1)))
  have : ∀ i : ℕᵒᵖ, Finite (Q.obj i) := fun _ ↦ d.quotientFinite n.unop
  obtain ⟨_, _, _, _, _, _, _, _, _, hc, _⟩ :=
    proEtale_profinite_coefficient_inverse_image Q
  have hc' := hc X Y Z f g n
  dsimp only [Q, proEtaleCoefficientTower, Functor.comp_obj,
    Functor.const_obj_obj] at hc'
  rw [hπ, hc']
  rw [← Category.assoc, ← Category.assoc]
  have hn := (proEtaleRingInverseImageComp f g).hom.naturality
    (limit.π (adicLisseRingSystem Z d.ideal) n)
  erw [hn]
  simp only [Functor.comp_map, Category.assoc]
  rw [hπ X Y f]
  conv_rhs => rw [← Functor.map_comp_assoc, hπ Y Z g, Functor.map_comp]
  simp only [Category.assoc]

private theorem coefficients_comp {Z : Scheme.{u}} (g : Y ⟶ Z) :
    proEtaleRingCompositeCoefficients f g (ring d Z) (ring d Y) (ring d X)
      (coefficients d g) (coefficients d f) = coefficients d (f ≫ g) := by
  apply Iso.ext
  exact (coefficientMap_comp d f g).symm


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
      (coefficients d g) (coefficients d f')) := by
  rw [coefficients_comp, coefficients_comp]
  have h := sq.w
  generalize g' ≫ f = k₁ at h ⊢
  generalize f' ≫ g = k₂ at h ⊢
  cases h
  rfl

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
        (reductionMap_isIso d f aY aX K n).1 := by
  have : IsIso (projection d f aY aX K (quotient d Y n)) :=
    (perfect_projection_formula d f aY aX K).2.2.2 _
      (reductionMap_isIso d f aY aX K n).1
  constructor
  · simp [reductionMap, IdentityProjectionCompactification.forward,
      IdentityProjectionCompactification.theta, projection]
  · simp [inverse, reductionIso, reductionMap, IdentityProjectionCompactification.backward,
      IdentityProjectionCompactification.rho, projection, ← Functor.map_comp, prod_comp]

end AlgebraicGeometry.Scheme.PerfectProjection
