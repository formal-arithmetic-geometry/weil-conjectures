/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.SixFunctors.ProEtale.IntegralPresentationEncoding
public import Sheaf.Paper.FiniteDiscreteOrdinaryEncoding
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.DerivedCompleteOnSlices
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import Sheaf.SixFunctors.ProEtale.IntegralNormalizedRestrictionSquares
import Sheaf.SixFunctors.ProEtale.IntegralReductionTransitionComparison
import Sheaf.Paper.SfDerivedCompleteLegacyComparison

/-! # Canonical completeness in the completed integral presentation

Source: blueprint main-20261015, integral-criterion-reductions, final sentence;
Stacks Project, Tags 06YY, 0941, 08TC and 0145
(blueprint: lem-pe-integral-completion-presentation).

The coefficient identification is normalized by every finite restriction square.
Finite comparisons retain their finite coefficient action.
Their restriction squares are normalized on underlying abelian sheaves, and their
units fix the derived comparisons uniquely. The index n denotes exponent n+1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u d

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.IntegralPresentation

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (A : Encoding l E X)

/-- The existing finite continuous-to-constant encoding, at exponent n+1.
Source: blueprint integral-limit and finite-coefficient conventions; Stacks 00YV
(blueprint: lem-pe-integral-completion-presentation). -/
abbrev FiniteEncoding (n : ℕ) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  FiniteDiscreteOrdinary.Encoding (Padic.coefficientExtensionRing l E (n + 1)) X

/-- The restriction square for the specified integral and finite coefficient encodings.
Source: blueprint integral-criterion comparison; Stacks 06YY
(blueprint: lem-pe-integral-completion-presentation). -/
abbrev RestrictionSquare (n : ℕ) (e : FiniteEncoding l E X n) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Mod.comap (AdicCompletion.quotient l E X n) ⋙ A.modules.functor ≅
    e.ordinary.functor ⋙ scalarReductionRestriction.{u, u} l E X n

/-- Normalization fixes the restriction square on every underlying abelian sheaf.
The right side is the identity section-action map, expressed using the encoding's
recorded equality with its concrete section functor.
Source: Stacks 06YY, identity on sections under scalar relabelling
(blueprint: lem-pe-integral-completion-presentation). -/
def SquareNormalized (n : ℕ) (e : FiniteEncoding l E X n)
    (a : RestrictionSquare l E X A n e) : Prop :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.finiteRing l E X n),
    (SheafOfModules.toSheaf (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)).map
        (a.hom.app M) =
      (SheafOfModules.toSheaf (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)).map
          (eqToIso (congrArg (fun F ↦ F.obj
            ((Mod.comap (AdicCompletion.quotient l E X n)).obj M)) A.functor_eq)).hom ≫
        (SheafOfModules.toSheaf (integralCoefficientSheaf.{u, u} l E X n)).map
        (eqToIso (congrArg (fun F ↦ F.obj M) e.ordinary_functor)).inv

/-- Localize the actual restriction square; both composition comparisons are Mathlib's
canonical localization comparisons.
Source: Stacks 05RU and 06YY
(blueprint: lem-pe-integral-completion-presentation). -/
def derivedSquare (n : ℕ) (e : FiniteEncoding l E X n)
    (a : RestrictionSquare l E X A n e) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    AdicCompletion.restrict l E X n ⋙ A.derived.functor ≅
      e.ordinaryDerived.functor ⋙ scalarReductionDerivedRestriction.{u, u} l E X n :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  letI := scalarReductionRestrictionLimits.{u, u} l E X n
  letI := scalarReductionRestrictionColimits.{u, u} l E X n
  (Functor.mapDerivedCategoryCompIso
    (Mod.comap (AdicCompletion.quotient l E X n)) (A.modules.functor)).symm ≪≫
    Functor.mapDerivedCategoryNatIso a ≪≫
      Functor.mapDerivedCategoryCompIso e.ordinary.functor
        (scalarReductionRestriction.{u, u} l E X n)

/-- A comparison in D(R_n), retaining the finite coefficient action.
Source: Stacks 06YY, derived tensor under an isomorphism of coefficients
(blueprint: lem-pe-integral-completion-presentation). -/
abbrev FiniteComparison (n : ℕ) (e : FiniteEncoding l E X n) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  A.derived.functor ⋙
      scalarReductionDerivedExtension.{u, u} l E X n ≅
    AdicCompletion.derivedReduction l E X n ⋙ e.ordinaryDerived.functor

/-- Restrict a finite comparison to the one completed integral derived category.
Source: Stacks 06YY; blueprint integral-criterion comparison
(blueprint: lem-pe-integral-completion-presentation). -/
def restrictedComparison (n : ℕ) (e : FiniteEncoding l E X n)
    (a : RestrictionSquare l E X A n e) (b : FiniteComparison l E X A n e)
    (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    (sfDerivedReductionRestricted l E X n).obj
        (A.derived.functor.obj K) ≅
      A.derived.functor.obj
        (AdicCompletion.integralLevel l E X K n) :=
  (scalarReductionDerivedRestriction.{u, u} l E X n).mapIso (b.app K) ≪≫
    ((derivedSquare l E X A n e a).app ((AdicCompletion.derivedReduction l E X n).obj K)).symm

/-- Unit normalization of a finite derived comparison. Since derived tensor is left
adjoint to restriction, this equation fixes the finite comparison uniquely.
Source: Stacks 06YY, canonical tensor unit
(blueprint: lem-pe-integral-completion-presentation). -/
def UnitCompatible (n : ℕ) (e : FiniteEncoding l E X n)
    (a : RestrictionSquare l E X A n e) (b : FiniteComparison l E X A n e) : Prop :=
  ∀ K : DerivedCategory (AdicCompletion.Modules l E X),
    (sfDerivedReductionUnit l E X n).app
        (A.derived.functor.obj K) ≫
      (restrictedComparison l E X A n e a b K).hom =
        A.derived.functor.map
          ((Mod.derivedExtendMapDerivedCategoryAdjunction
            (AdicCompletion.quotient l E X n)).unit.app K)

private theorem completedProducts :
    HasCountableProducts (DerivedCategory (scalarReductionSource.{u, u} l E X)) := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{u} _
  let : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} := sfAbSheafify X
  let : (Scheme.ProEt.topology X).WEqualsLocallyBijective Ab.{u + 1} := sfAbBijective X
  let R := completedIntegralCommRingSheafUnrestricted.{u, u} l E X
  let C := scalarReductionSource.{u, u} l E X
  let : HasCountableProducts C := (Scheme.ProEt.countableProducts_exact.{u, u, 0} X R).1
  have : CountableAB4Star C := by
    constructor
    intro I _
    have : (lim : (Discrete I ⥤ C) ⥤ C).PreservesEpimorphisms := by
      constructor
      intro B D f hf
      let eB := HasLimit.isoOfNatIso (Discrete.natIsoFunctor (F := B))
      let eD := HasLimit.isoOfNatIso (Discrete.natIsoFunctor (F := D))
      have h (i : I) : Epi (f.app ⟨i⟩) := inferInstance
      have : Epi (Limits.Pi.map (fun i : I ↦ f.app ⟨i⟩)) :=
        (Scheme.ProEt.countableProducts_exact.{u, u, 0} X R).2.2 I _ _ _ h
      have hh : lim.map f = eB.hom ≫ Limits.Pi.map (fun i : I ↦ f.app ⟨i⟩) ≫ eD.inv := by
        apply limit.hom_ext
        rintro ⟨i⟩
        dsimp only [eB, eD]
        simp only [Category.assoc, HasLimit.isoOfNatIso_inv_π,
          Discrete.natIsoFunctor_inv_app]
        change lim.map f ≫ limit.π D ⟨i⟩ =
          (HasLimit.isoOfNatIso (Discrete.natIsoFunctor (F := B))).hom ≫
            Limits.Pi.map (fun i : I ↦ f.app ⟨i⟩) ≫ Pi.π _ i
        rw [Pi.map_π, HasLimit.isoOfNatIso_hom_π_assoc]
        simp
      rw [hh]
      infer_instance
    exact hasExactLimitsOfShape_of_preservesEpi (C := C) (Discrete I)
  exact (derivedCategory_countableProducts_and_towerLimit.{0, u + 2, u + 1, u + 2} C).choose

private theorem internal_roos_complete
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hK : AlgebraicGeometry.ProEtale.IsDerivedComplete l E X K)
    [HasProduct (AdicCompletion.integralLevel l E X K)] :
    ∃ δ : (∏ᶜ (AdicCompletion.integralLevel l E X K)) ⟶ K⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle (AdicCompletion.integralStep l E X K) K
        (Pi.lift (fun n ↦ (Mod.derivedExtendMapDerivedCategoryAdjunction
          (AdicCompletion.quotient l E X n)).unit.app K)) δ := by
  obtain ⟨P, hP, ⟨e⟩, hη⟩ := hK
  obtain ⟨p, δ, hT, hp⟩ := AdicCompletion.roos_isDerivedLimit l E X K P hP e
  let : IsIso (DerivedCategory.Q.map (AdicCompletion.augmentation l E X P)) := hη
  let v : K ≅ DerivedCategory.Q.obj (AdicCompletion.roos l E X P) :=
    e.symm ≪≫ asIso (DerivedCategory.Q.map (AdicCompletion.augmentation l E X P))
  refine ⟨δ ≫ (shiftFunctor _ (1 : ℤ)).map v.inv, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hT _
  refine Pretriangulated.Triangle.isoMk _ _ v (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · change Pi.lift _ ≫ 𝟙 _ = v.hom ≫ p
    exact (Category.comp_id _).trans hp.symm
  · simp
  · simp [Category.assoc, ← Functor.map_comp]

private theorem map_roos_complete
    {C D : Type*} [Category C] [Category D] [HasZeroObject C] [HasZeroObject D]
    [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    {V : ℕ → C} {W : ℕ → D} [HasProduct V] [HasProduct W]
    [PreservesLimit (Discrete.functor V) F]
    [HasProduct (fun n ↦ F.obj (V n))]
    (t : ∀ n, V (n + 1) ⟶ V n) (s : ∀ n, W (n + 1) ⟶ W n)
    (a : ∀ n, F.obj (V n) ≅ W n)
    (K : C) (p : ∀ n, K ⟶ V n) (q : ∀ n, F.obj K ⟶ W n)
    (ht : ∀ n, F.map (t n) ≫ (a n).hom = (a (n + 1)).hom ≫ s n)
    (hp : ∀ n, F.map (p n) ≫ (a n).hom = q n)
    (δ : (∏ᶜ V) ⟶ K⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle t K (Pi.lift p) δ) :
    ∃ δ' : (∏ᶜ W) ⟶ (F.obj K)⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle s (F.obj K) (Pi.lift q) δ' := by
  let B : F.obj (∏ᶜ V) ≅ ∏ᶜ W := PreservesProduct.iso F V ≪≫
    { hom := Limits.Pi.map (fun n ↦ (a n).hom)
      inv := Limits.Pi.map (fun n ↦ (a n).inv)
      hom_inv_id := by apply Pi.hom_ext; intro n; simp [Category.assoc]
      inv_hom_id := by apply Pi.hom_ext; intro n; simp [Category.assoc] }
  have hB (n : ℕ) : B.hom ≫ Pi.π W n = F.map (Pi.π V n) ≫ (a n).hom := by
    simp [B]
  have hfirst : F.map (Pi.lift p) ≫ B.hom = Pi.lift q := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, hB, Pi.lift_π]
    rw [← Category.assoc, ← F.map_comp, Pi.lift_π, hp]
  have hmiddle : F.map (towerTransitionEndomorphism t) ≫ B.hom =
      B.hom ≫ towerTransitionEndomorphism s := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, hB, towerTransitionEndomorphism, towerProductShift,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
      Pi.lift_π, Functor.map_sub]
    simp only [reassoc_of% hB]
    erw [F.map_id, Category.id_comp]
    congr 1
    rw [← F.map_comp_assoc, Pi.lift_π, Functor.map_comp, Category.assoc, ht]
  refine ⟨B.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app K, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ (F.map_distinguished _ hT) _
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) B.symm B.symm ?_ ?_ ?_
  · change Pi.lift q ≫ B.inv = 𝟙 _ ≫ F.map (Pi.lift p)
    rw [← hfirst]
    simp
  · change towerTransitionEndomorphism s ≫ B.inv =
      B.inv ≫ F.map (towerTransitionEndomorphism t)
    apply (cancel_mono B.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using congrArg (fun f ↦ B.inv ≫ f) hmiddle.symm
  · change (B.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app K) ≫
        (shiftFunctor D (1 : ℤ)).map (𝟙 (F.obj K)) =
      B.inv ≫ (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app K)
    erw [(shiftFunctor D (1 : ℤ)).map_id]
    simpa only [Category.assoc, Functor.comp_obj] using
      Category.comp_id (B.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app K)

private theorem mateComparison_existsUnique
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (G : C ≌ C') (H : D ≌ D')
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (r : R ⋙ G.functor ≅ H.functor ⋙ R') :
    ∃! b : G.functor ⋙ L' ≅ L ⋙ H.functor,
      ∀ K, adj'.unit.app (G.functor.obj K) ≫
        (R'.map (b.hom.app K) ≫ r.inv.app (L.obj K)) = G.functor.map (adj.unit.app K) := by
  let m := ((mateEquiv adj adj').symm r.hom).natTrans
  have : IsIso m := isIso_inverseMate_of_equivalences adj adj' r
  let b : G.functor ⋙ L' ≅ L ⋙ H.functor := asIso m
  have hb (K : C) : adj'.unit.app (G.functor.obj K) ≫
      (R'.map (b.hom.app K) ≫ r.inv.app (L.obj K)) = G.functor.map (adj.unit.app K) := by
    have h := unit_mateEquiv_symm adj adj' r.hom K
    have hc := congrArg (fun f ↦ f ≫ r.inv.app (L.obj K)) h.symm
    simp only [Category.assoc, Iso.hom_inv_id_app] at hc
    exact hc.trans (Category.comp_id _)
  refine ⟨b, hb, ?_⟩
  intro b' hb'
  apply Iso.ext
  ext K
  apply (adj'.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply (cancel_mono (r.inv.app (L.obj K))).mp
  exact (Category.assoc _ _ _).trans ((hb' K).trans ((hb K).symm.trans
    (Category.assoc _ _ _).symm))

private theorem finiteComparison_existsUnique (n : ℕ) (e : FiniteEncoding l E X n)
    (a : RestrictionSquare l E X A n e) :
    ∃! b : FiniteComparison l E X A n e, UnitCompatible l E X A n e a b := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  simpa only [UnitCompatible, restrictedComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, sfDerivedReductionUnit] using
    mateComparison_existsUnique A.derived e.ordinaryDerived
      (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E X n))
      (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose
      (derivedSquare l E X A n e a)

/-- Canonical finite reductions agree, with their actual units and quotient transitions.
There is no completeness, constructibility, boundedness or Noetherian hypothesis here.
Source: blueprint integral-criterion-reductions, final sentence; Stacks 06YY
(blueprint: lem-pe-integral-completion-presentation).

Proof:
1. Use the finite-quotient theorem to identify continuous finite coefficients with
   constant coefficients. Choose their normalized section-action encodings.
2. The normalized integral-limit map alpha has b_n = pi_n alpha. Restricting the
   finite encoding and integral encoding therefore gives the same scalar action.
   Identity on the underlying sections gives the normalized restriction squares.
3. Localize these exact squares. Uniqueness of left adjoints gives the finite
   comparison in D(R_n), uniquely fixed by the tensor-unit equation. On a K-flat
   representative it sends p tensor r to p tensor r: the balancing relations are
   identical because b_n = pi_n alpha. Thus this is the canonical derived comparison.
4. The consecutive quotient sends p tensor r to p tensor rho_n(r) on either side.
   Hence the finite comparisons respect transitions; localization and restriction
   give exactly the displayed transition equation. These formulas work at every
   positive level, for unbounded K and for the zero complex as well. -/
theorem integral_completion_reduction_comparisons :
    ∃ (A : Encoding l E X) (e : ∀ n : ℕ, FiniteEncoding l E X n)
      (a : ∀ n : ℕ, RestrictionSquare l E X A n (e n)),
      (∀ n : ℕ, SquareNormalized l E X A n (e n) (a n)) ∧
      ∃ b : ∀ n : ℕ, FiniteComparison l E X A n (e n),
        (∀ n : ℕ, UnitCompatible l E X A n (e n) (a n) (b n)) ∧
        (∀ (n : ℕ) (b' : FiniteComparison l E X A n (e n)),
          UnitCompatible l E X A n (e n) (a n) b' → b' = b n) ∧
        ∀ (K : DerivedCategory (AdicCompletion.Modules l E X)) (n : ℕ),
          (sfDerivedReductionTransition l E X n).app
              (A.derived.functor.obj K) ≫
            (restrictedComparison l E X A n (e n) (a n) (b n) K).hom =
          (restrictedComparison l E X A (n + 1) (e (n + 1)) (a (n + 1)) (b (n + 1)) K).hom ≫
            A.derived.functor.map
              (AdicCompletion.integralStep l E X K n) := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  obtain ⟨B, e, a, ha⟩ := integral_completion_normalized_squares l E X
  have hb (n : ℕ) := finiteComparison_existsUnique l E X B n (e n) (a n)
  choose b hbu hbuniq using hb
  refine ⟨B, e, a, ha, b, hbu, hbuniq, ?_⟩
  exact integral_completion_transition_comparison l E X B e a ha b hbu


/-- A canonically complete complex gives the distinguished Roos triangle with first
map the product of its completed-coefficient reductions. In the global coefficient
setting it satisfies exactly the recorded completed integral completeness predicate.
Source: blueprint integral-criterion-reductions, final sentence; Stacks 0941, 08TC, 0145
(blueprint: lem-pe-integral-completion-presentation).

Proof:
1. Write alpha for A.ringIso. Its finite restriction squares give exactly the
   normalized integral-limit comparison. Relabelling scalars by alpha inverse and the
   internal-to-sectionwise
   equivalence preserve the underlying sheaves, kernels, cokernels and cone triangles.
2. Resolve K by a flat-term K-flat complex P. The internal/sectionwise tensor comparison
   identifies the two tensor products and preserves K-flatness. The preceding finite
   comparisons identify all reductions, units and transitions on these representatives.
3. Exact countable products identify the termwise product V of the reductions with
   their derived-category product. Cone(1-s)[-1] supplies the distinguished Roos triangle.
   The strict augmentation is (gamma,0), where gamma is the product of the tensor units.
4. The strict-augmentation clause of lem-weil-strict-roos-comparison identifies this
   augmentation with the specified canonical completion map, including its zero
   nullhomotopy. Thus canonical completeness makes the map u from K to this Roos model
   invertible, and its composite with the first Roos arrow is the product of the units.
5. Transport the Roos triangle by (u,id,id); TR1 makes the resulting triangle
   distinguished, with its fixed first map. Relabel coefficients by alpha. The unit
   and transition equations above identify precisely the tower in IsSfDerivedComplete.
6. In the global setting l != D.p, the legacy reduction tower uses these same maps,
   by its K-flat resolution comparisons. Equivalently use sfDerivedComplete_iff_legacy.
   No step requires a bound on K, constructibility, or Noetherianity of X. -/
theorem integral_completion_presentation
    (e : ∀ n : ℕ, FiniteEncoding l E X n)
    (a : ∀ n : ℕ, RestrictionSquare l E X A n (e n))
    (_ha : ∀ n : ℕ, SquareNormalized l E X A n (e n) (a n))
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (_hK : AlgebraicGeometry.ProEtale.IsDerivedComplete l E X K) :
    IsSfDerivedComplete l E X (A.derived.functor.obj K) ∧
      ∀ (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p),
        WeilConjectures.IsDerivedComplete l E X D hl
          (A.derived.functor.obj K) := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  have hb (n : ℕ) := finiteComparison_existsUnique l E X A n (e n) (a n)
  choose b hbu _ using hb
  have ht := integral_completion_transition_comparison l E X A e a _ha b hbu
  let : HasCountableProducts (DerivedCategory (scalarReductionSource.{u, u} l E X)) :=
    completedProducts l E X
  let : HasCountableProducts (DerivedCategory (AdicCompletion.Modules l E X)) :=
    { out := fun I _ ↦
      Adjunction.hasLimitsOfShape_of_equivalence A.derived.functor }
  let : A.derived.functor.Additive := by
    change A.modules.functor.mapDerivedCategory.Additive
    infer_instance
  let : A.derived.functor.CommShift ℤ := by
    change A.modules.functor.mapDerivedCategory.CommShift ℤ
    infer_instance
  let : A.derived.functor.IsTriangulated := by
    change A.modules.functor.mapDerivedCategory.IsTriangulated
    infer_instance
  obtain ⟨δ, hδ⟩ := internal_roos_complete l E X K _hK
  have ht' (n : ℕ) :
      (sfDerivedReductionTransition l E X n).app (A.derived.functor.obj K) ≫
        (restrictedComparison l E X A n (e n) (a n) (b n) K).hom =
      (restrictedComparison l E X A (n + 1) (e (n + 1)) (a (n + 1)) (b (n + 1)) K).hom ≫
        A.derived.functor.map (AdicCompletion.integralStep l E X K n) := ht K n
  have hs : IsSfDerivedComplete l E X (A.derived.functor.obj K) := by
    refine ⟨inferInstance, ?_⟩
    apply map_roos_complete A.derived.functor
      (AdicCompletion.integralStep l E X K)
      (fun n ↦ (sfDerivedReductionTransition l E X n).app (A.derived.functor.obj K))
      (fun n ↦ (restrictedComparison l E X A n (e n) (a n) (b n) K).symm)
      K (fun n ↦ (Mod.derivedExtendMapDerivedCategoryAdjunction
        (AdicCompletion.quotient l E X n)).unit.app K)
      (fun n ↦ (sfDerivedReductionUnit l E X n).app (A.derived.functor.obj K))
      ?_ ?_ δ hδ
    · intro n
      apply (cancel_epi
        (restrictedComparison l E X A (n + 1) (e (n + 1)) (a (n + 1)) (b (n + 1)) K).hom).1
      simpa only [Iso.symm_hom, ← Category.assoc, Iso.hom_inv_id, Category.id_comp,
        Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using
        congrArg (fun f ↦ f ≫
          (restrictedComparison l E X A n (e n) (a n) (b n) K).inv) (ht' n).symm
    · intro n
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.symm_hom,
        Functor.id_obj] using
        congrArg (fun f ↦ f ≫
          (restrictedComparison l E X A n (e n) (a n) (b n) K).inv) (hbu n K).symm
  refine ⟨hs, fun D hl ↦ (sfDerivedComplete_iff_legacy l E X D hl _).mp hs⟩


end AlgebraicGeometry.ProEtale.IntegralPresentation
