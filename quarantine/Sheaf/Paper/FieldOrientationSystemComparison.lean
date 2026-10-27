module

public import Sheaf.Paper.FieldOrientationSystemHeart
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.Paper.SmoothPurityCoefficientTowers
public import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.SmoothPurityTowerGluing
public import Sheaf.Paper.SmoothPurityTowerShriekLevels
public import Sheaf.Paper.FieldShriekSystemComparison
public import Sheaf.Paper.FieldExceptionalSystemComparison
public import Sheaf.Paper.SmoothPurityTowerGamma
public import Sheaf.Paper.SmoothPurityTowerGammaData
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.SecSmoothPurity.ReductionCompatibilities

public import Sheaf.Paper.FieldShriekSystemModels
public import Sheaf.Paper.FieldExceptionalSystemDomains
public import Sheaf.Paper.FieldExceptionalSystemAdjoints
public import Sheaf.Paper.FieldExceptionalSystemComponents
public import Sheaf.Paper.SmoothPurityTowerChartData
public import Sheaf.Paper.SmoothPurityCoordinateRightComparisons
public import Sheaf.Paper.TowerP1CoefficientCoordinates
public import Sheaf.Paper.TowerP1TensorCoordinates
public import Sheaf.Paper.TowerP1LevelWords
public import Sheaf.Paper.FiniteSmoothPurityMaps
public import Sheaf.Paper.FiniteSmoothCoefficientArrows
public import Sheaf.Paper.FiniteRingSectionDeformation
public import Sheaf.SecSmoothPurity.ReductionExceptionalObjects
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer

import Sheaf.Paper.FieldOrientationSystemComparisonData
import Sheaf.Paper.FieldOrientationSystemRigidity

/-! # Shifted-sheaf detection of the scalar orientation equation

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-field-extension/sk-lem-sp-field-extension-towers.proof.md (2),
rank-one tower orientation; returned step 6
(blueprint: lem-sp-field-orientation-system-comparison).

We use the dependency's actual strict-system derived category and its normalized
full subcategory. Positive coefficient exponent n+1 is indexed by n : ℕ.
All endpoint comparisons below retain their root, unit and counit normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.FieldOrientationSystem
open FieldShriekSystem FieldExceptionalSystem

variable (P : PurityFiniteSetting.{u}) (D : Models P)

variable {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
  (p : Z ⟶ Y) [IsProper p]
  (b : FieldShriekSystem.Laws P D (SpTowerGamma.factorization j p))
  (a : Domains P D (SpTowerGamma.factorization j p))
  (A : Adjoints P D (SpTowerGamma.factorization j p) b a)

/-- Componentwise detection is asserted only for maps of shifted degree-zero
sheaf systems. It does not assert faithfulness on arbitrary derived towers.
Source: blueprint (2), shifted-sheaf detection
(blueprint: lem-sp-field-orientation-system-comparison).

Proof: cancel the common shift and use faithfulness of the degree-zero single
embedding. A map of strict systems is its compatible family of component sheaf maps;
conversely equal component maps give the same strict-system map and hence the same
shifted single map. This is exactly step 4 of the node's proof. -/
theorem shifted_sheaf_map_ext (E : Index P) (T : Scheme.{u})
    (M N : SpTowerShriek.S P.coefficients.l E.val T) (f g : M ⟶ N) (s : ℤ) :
    ((DerivedCategory.singleFunctor _ 0).map f)⟦s⟧' =
        ((DerivedCategory.singleFunctor _ 0).map g)⟦s⟧' ↔
      ∀ n : ℕ, (SpTowerShriek.ev P.coefficients.l E.val T n).map f =
        (SpTowerShriek.ev P.coefficients.l E.val T n).map g := by
  constructor
  · intro h n
    have hsingle := (shiftFunctor _ s).map_injective h
    have hfg := (DerivedCategory.singleFunctor _ 0).map_injective hsingle
    exact congrArg (fun k ↦ (SpTowerShriek.ev P.coefficients.l E.val T n).map k) hfg
  · intro h
    have hfg : f = g := by
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      ext x
      exact congrArg (fun k ↦ (k.val.app (op U.unop.2)) x) (h U.unop.1)
    subst g
    rfl

section ExactFunctor

variable {C₁ C₂ : Type*} [Category C₁] [Category C₂] [Abelian C₁] [Abelian C₂]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

private def singleShiftComparison (M : C₁) (s : ℤ) :
    F.mapDerivedCategory.obj (((DerivedCategory.singleFunctor C₁ 0).obj M)⟦s⟧) ≅
      ((DerivedCategory.singleFunctor C₂ 0).obj (F.obj M))⟦s⟧ :=
  (F.mapDerivedCategory.commShiftIso s).app _ ≪≫
    (shiftFunctor _ s).mapIso ((F.mapDerivedCategorySingleFunctor 0).app M)

private theorem singleShiftComparison_naturality {M N : C₁} (f : M ⟶ N) (s : ℤ) :
    F.mapDerivedCategory.map (((DerivedCategory.singleFunctor C₁ 0).map f)⟦s⟧') ≫
        (singleShiftComparison F N s).hom =
      (singleShiftComparison F M s).hom ≫
        ((DerivedCategory.singleFunctor C₂ 0).map (F.map f))⟦s⟧' := by
  let V := F.mapDerivedCategory
  let v := F
  have hs := (V.commShiftIso s).hom.naturality ((DerivedCategory.singleFunctor _ 0).map f)
  have ht := (v.mapDerivedCategorySingleFunctor 0).hom.naturality f
  dsimp only [singleShiftComparison, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Iso.app_hom, Category.assoc]
  change V.map (((DerivedCategory.singleFunctor _ 0).map f)⟦s⟧') ≫
      (V.commShiftIso s).hom.app ((DerivedCategory.singleFunctor _ 0).obj N) =
    (V.commShiftIso s).hom.app ((DerivedCategory.singleFunctor _ 0).obj M) ≫
      (V.map ((DerivedCategory.singleFunctor _ 0).map f))⟦s⟧' at hs
  change V.map ((DerivedCategory.singleFunctor _ 0).map f) ≫
      (v.mapDerivedCategorySingleFunctor 0).hom.app N =
    (v.mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor _ 0).map (v.map f) at ht
  rw [← Category.assoc, hs, Category.assoc, ← Functor.map_comp, ht, Functor.map_comp]

end ExactFunctor

private theorem evaluation_single_shift_naturality (E : Index P) (T : Scheme.{u})
    {M N : SpTowerShriek.S P.coefficients.l E.val T} (f : M ⟶ N) (n : ℕ) (s : ℤ) :
    (SpTowerShriek.Ev P.coefficients.l E.val T n).map
        (((DerivedCategory.singleFunctor _ 0).map f)⟦s⟧') ≫
        (evaluationSingleShift P N n s).hom =
      (evaluationSingleShift P M n s).hom ≫
        ((DerivedCategory.singleFunctor _ 0).map
          ((SpTowerShriek.ev P.coefficients.l E.val T n).map f))⟦s⟧' := by
  exact singleShiftComparison_naturality (SpTowerShriek.ev P.coefficients.l E.val T n) f s

private theorem presented_map_ext (E : Index P) (T : Scheme.{u})
    (M N : SpTowerShriek.S P.coefficients.l E.val T) (s : ℤ)
    {V W : SpTowerShriek.D P.coefficients.l E.val T}
    (i : ((DerivedCategory.singleFunctor _ 0).obj M)⟦s⟧ ≅ V)
    (j : ((DerivedCategory.singleFunctor _ 0).obj N)⟦s⟧ ≅ W)
    (f g : V ⟶ W)
    (h : ∀ n : ℕ, (SpTowerShriek.Ev P.coefficients.l E.val T n).map f =
      (SpTowerShriek.Ev P.coefficients.l E.val T n).map g) : f = g := by
  let H := DerivedCategory.singleFunctor (SpTowerShriek.S P.coefficients.l E.val T) 0 ⋙
    shiftFunctor _ s
  let f' := H.preimage (i.hom ≫ f ≫ j.inv)
  let g' := H.preimage (i.hom ≫ g ≫ j.inv)
  have hf : ((DerivedCategory.singleFunctor _ 0).map f')⟦s⟧' =
      i.hom ≫ f ≫ j.inv := H.map_preimage _
  have hg : ((DerivedCategory.singleFunctor _ 0).map g')⟦s⟧' =
      i.hom ≫ g ≫ j.inv := H.map_preimage _
  have he : f' = g' := by
    apply (DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ s).map_injective
    apply (shifted_sheaf_map_ext P E T M N f' g' s).2
    intro n
    apply (DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ s).map_injective
    apply (cancel_epi (evaluationSingleShift P M n s).hom).1
    simp only [Functor.comp_map]
    rw [← evaluation_single_shift_naturality P E T f' n s,
      ← evaluation_single_shift_naturality P E T g' n s, hf, hg]
    simp only [Functor.map_comp, h n]
  have hc : i.hom ≫ f ≫ j.inv = i.hom ≫ g ≫ j.inv := by rw [← hf, ← hg, he]
  exact (cancel_epi i.hom).1 ((cancel_mono j.inv).1 (by
    simpa only [Category.assoc] using hc))

open MonoidalCategory in
private theorem coefficient_unit_tor (R : Type (u + 1)) [CommRing R]
    (T : Scheme.{u}) :
    Etale.DerivedCategory.hasTorAmplitudeIn R T 0 0 (Etale.ordinaryFiniteUnit R T) := by
  let := Sheaf.monoidalCategory T.smallEtaleTopology (ModuleCat.{u + 1} R)
  let C := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)
  let e : Etale.ordinaryFiniteUnit R T ≅ 𝟙_ (DerivedCategory C) :=
    PurityFiniteSetting.smoothPurityUnitIso R T
  intro M i hi
  let v : ((Etale.derivedTensor (ModuleCat.{u + 1} R) T).obj
      (Etale.ordinaryFiniteUnit R T)).obj ((DerivedCategory.singleFunctor C 0).obj M) ≅
      (DerivedCategory.singleFunctor C 0).obj M :=
    ((curriedTensor (DerivedCategory C)).mapIso e).app _ ≪≫
      (CategoryTheory.MonoidalCategory.leftUnitor _)
  have hz : IsZero ((DerivedCategory.homologyFunctor C i).obj
      ((DerivedCategory.singleFunctor C 0).obj M)) := by
    rcases hi with hi | hi
    · exact DerivedCategory.isZero_of_isGE _ 0 i hi
    · exact DerivedCategory.isZero_of_isLE _ 0 i hi
  exact hz.of_iso ((DerivedCategory.homologyFunctor C i).mapIso v)

attribute [local irreducible] FieldExceptionalSystem.component

/-- Whole-system orientation comparison, concentration and uniqueness restricted to
these shifted coefficient sheaves. The comparisons in the conclusion are normalized
by scalar units and root generators, not chosen from arbitrary endpoint isomorphisms.

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2),
rank-one tower orientation; returned step 6
(blueprint: lem-sp-field-orientation-system-comparison).

Proof:
1. The tower orientations of det-sp-tower-gamma evaluate to the finite diagonal
orientations. Both targets are concentrated in degree -2d. Exact whole-system scalar
extension (lem-sp-field-scalar-normalized-systems) commutes with the common shift;
lem-sf-exact-functor-derived-triangulated gives its standard single/shift comparison.
The coefficient/twist comparisons have the displayed unit and root normalizations.
2. The finite coefficient unit is free of rank one, constructible on one stratum,
and of Tor amplitude [0,0]. Apply det-sp-reduction-compatibilities (3), using
lem-sp-finite-orientation-reduction to identify its general-ring purity orientation
with the diagonal/DNC orientation. This includes ramification, since ell^(n+1) is
unit times the corresponding uniformizer power, without any flat quotient assumption.
3. lem-sp-field-exceptional-system-comparison evaluates the actual tower counit
transpose to the finite exceptional comparison. lem-coef-semilinear-derived-sections
identifies evaluation of the whole-system scalar extension. Thus the two already
constructed orientation arrows have identical evaluations at every positive level.
4. Conjugate by the second orientation and remove the common shift. Full faithfulness
of the degree-zero single embedding (lem-weil-pbc-derived-single-fully-faithful)
recovers an endomorphism of the abelian strict line system. Exact evaluation and
faithfulness of each finite single embedding show every component is identity.
The definition sk-def-sp-coefficient-towers makes this strict-system map the identity.
Shift back and compose with the second orientation to obtain the actual tower equation.
5. Apply the same argument to any other map with the same finite orientations.
lem-sp-strict-line-heart-assembly supplies the unique compatible sheaf-system maps
and their concentrated-complex identifications. Equality of sheaf-system maps is
componentwise. No faithfulness of evaluation on arbitrary derived objects is used.
-/
theorem field_orientation_system_comparison
    [IsNoetherian X]
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [(j ≫ p).IsOver (Spec (.of P.field.k))] [IsSeparated (j ≫ p)]
    [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
    (d : ℕ) [SmoothOfRelativeDimension d (j ≫ p)]
    {E F : Index P} (hEF : E ≤ F)
    (wE : Coordinates P D E X) (wF : Coordinates P D F X)
    (vE : Coordinates P D E Y) (vF : Coordinates P D F Y)
    (hE : normalized P D E Y (SpTowerGamma.unit P.coefficients.l E.val Y))
    (hF : normalized P D F Y (SpTowerGamma.unit P.coefficients.l F.val Y))
    (oE : line P D wE d ≅ omega P D j p b a A E hE)
    (oF : line P D wF d ≅ omega P D j p b a A F hF)
    (hoE : IsOrientation P D j p b a A E d wE vE hE oE.hom)
    (hoF : IsOrientation P D j p b a A F d wF vF hF oF.hom) :
    ∃ (q : (D.scalars E F hEF Y).T.obj
        (SpTowerGamma.unit P.coefficients.l E.val Y) ≅
          SpTowerGamma.unit P.coefficients.l F.val Y)
      (t : (D.scalars E F hEF X).T.obj (line P D wE d) ≅ line P D wF d),
      IsUnitComparison P D j p b hEF vE vF q.hom ∧
      IsLineComparison P D j p b hEF wE wF d t.hom ∧
      (D.scalars E F hEF X).T.map oE.hom ≫
          (component P D (SpTowerGamma.factorization j p) b a A hEF
            (coefficientUnit P D E Y hE)).hom ≫
          ((A.right F).map (ObjectProperty.homMk
            (Y := coefficientUnit P D F Y hF) q.hom)).hom = t.hom ≫ oF.hom ∧
      (∀ i : ℤ, i ≠ -2 * (d : ℤ) →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj
          (omega P D j p b a A E hE))) ∧
      (∀ i : ℤ, i ≠ -2 * (d : ℤ) →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj
          (omega P D j p b a A F hF))) ∧
      IsHeartInduced P D wE d (omega P D j p b a A E hE) oE.hom ∧
      IsHeartInduced P D wF d (omega P D j p b a A F hF) oF.hom ∧
      (∀ n : ℕ,
        letI : Finite (SpTowerShriek.R P.coefficients.l E.val n) := (D.base E).finite n
        Etale.DerivedCategory.hasTorAmplitudeIn
          (SpTowerP1.levelRing P.coefficients.l E.val n) Y 0 0
          (Etale.ordinaryFiniteUnit (SpTowerP1.levelRing P.coefficients.l E.val n) Y)) ∧
      (∀ n : ℕ,
        letI : Finite (SpTowerShriek.R P.coefficients.l F.val n) := (D.base F).finite n
        Etale.DerivedCategory.hasTorAmplitudeIn
          (SpTowerP1.levelRing P.coefficients.l F.val n) Y 0 0
          (Etale.ordinaryFiniteUnit (SpTowerP1.levelRing P.coefficients.l F.val n) Y)) ∧
      (∀ o : line P D wE d ⟶ omega P D j p b a A E hE,
        IsOrientation P D j p b a A E d wE vE hE o → o = oE.hom) ∧
      (∀ o : line P D wF d ⟶ omega P D j p b a A F hF,
        IsOrientation P D j p b a A F d wF vF hF o → o = oF.hom) := by
  obtain ⟨q, t, hq, ht, hfinite⟩ := field_orientation_comparison_data P D j p b a A
    d hEF wE wF vE vF hE hF oE oF hoE hoF
  obtain ⟨hce, hhe, hue⟩ :=
    field_orientation_system_rigidity P D j p b a A d E wE vE hE oE hoE
  obtain ⟨hcf, hhf, huf⟩ :=
    field_orientation_system_rigidity P D j p b a A d F wF vF hF oF hoF
  have heq : (D.scalars E F hEF X).T.map oE.hom ≫
      (component P D (SpTowerGamma.factorization j p) b a A hEF
        (coefficientUnit P D E Y hE)).hom ≫
      ((A.right F).map (ObjectProperty.homMk
        (Y := coefficientUnit P D F Y hF) q.hom)).hom = t.hom ≫ oF.hom := by
    unfold IsHeartInduced at hhf
    obtain ⟨i, _, _⟩ := hhf
    let L := heartIdentification P (line P D wF d) (2 * (d : ℤ)) i
    have he : t.inv ≫ (D.scalars E F hEF X).T.map oE.hom ≫
        (component P D (SpTowerGamma.factorization j p) b a A hEF
          (coefficientUnit P D E Y hE)).hom ≫
        ((A.right F).map (ObjectProperty.homMk
          (Y := coefficientUnit P D F Y hF) q.hom)).hom = oF.hom := by
      apply presented_map_ext P F X _ _ (2 * (d : ℤ)) L (L ≪≫ oF)
      intro n
      calc
        _ = (SpTowerShriek.Ev P.coefficients.l F.val X n).map t.inv ≫
            (SpTowerShriek.Ev P.coefficients.l F.val X n).map
              ((D.scalars E F hEF X).T.map oE.hom ≫
                (component P D (SpTowerGamma.factorization j p) b a A hEF
                  (coefficientUnit P D E Y hE)).hom ≫
                ((A.right F).map (ObjectProperty.homMk
                  (Y := coefficientUnit P D F Y hF) q.hom)).hom) :=
          Functor.map_comp _ _ _
        _ = (SpTowerShriek.Ev P.coefficients.l F.val X n).map t.inv ≫
            (SpTowerShriek.Ev P.coefficients.l F.val X n).map (t.hom ≫ oF.hom) := by
          rw [hfinite n]
        _ = _ := by rw [← Functor.map_comp, Iso.inv_hom_id_assoc]
    apply (cancel_epi t.inv).1
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using he
  refine ⟨q, t, hq, ht, heq, hce, hcf, hhe, hhf, ?_, ?_, hue, huf⟩
  · intro n
    let : Finite (SpTowerShriek.R P.coefficients.l E.val n) := (D.base E).finite n
    exact coefficient_unit_tor (SpTowerP1.levelRing P.coefficients.l E.val n) Y
  · intro n
    let : Finite (SpTowerShriek.R P.coefficients.l F.val n) := (D.base F).finite n
    exact coefficient_unit_tor (SpTowerP1.levelRing P.coefficients.l F.val n) Y

end AlgebraicGeometry.ProEtale.FieldOrientationSystem
