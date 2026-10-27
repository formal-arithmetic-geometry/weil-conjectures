module

public import Sheaf.Paper.FieldExceptionalSystemComparison
public import Sheaf.Paper.TowerClassSystems
public import Sheaf.Paper.ComparisonTorAmplitude
public import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.Paper.TowerUniformEtaleDomains
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-! # Etale origins of the two purity projection inputs

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension,
sk-lem-sp-field-extension-towers.proof.md (2), projection-formula domain
(blueprint: lem-sp-field-projection-origin-witnesses).

Natural index n denotes exponent n+1, so every positive coefficient level occurs.
The retained origins are independent at different levels. The coefficient rings
are the actual ell-power quotients, including ramified extensions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.FieldProjectionOrigin

open FieldShriekSystem FieldExceptionalSystem
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] FieldShriekSystem.coefficientMap normalized
variable (P : PurityFiniteSetting.{u})

/-- The existing degree-zero coefficient tower, with its actual quotient transitions.
Source: blueprint (2), J_(A,T) (blueprint: lem-sp-field-projection-origin-witnesses). -/
abbrev J (E : Index P) (T : Scheme.{u}) :=
  SpTowerClasses.unit T (spCoefficientCommRings P.coefficients.l E.val T)

/-- The ordinary coefficient map, characterized by the global section 1.
Source: blueprint (2), C_Y J_A = J_B
(blueprint: lem-sp-field-projection-origin-witnesses). -/
def coefficientUnitMap (D : Models P) {E F : Index P} (h : E ≤ F) (T : Scheme.{u}) :
    SpTowerClasses.coefficient T (spCoefficientCommRings P.coefficients.l E.val T) ⟶
      (res (FieldShriekSystem.coefficientMap P (D.coefficients E F h) T)).obj
        (SpTowerClasses.coefficient T (spCoefficientCommRings P.coefficients.l F.val T)) :=
  SheafOfModules.unitHomEquiv _ |>.symm
    { val := fun U ↦ (1 : (systemRing (Scheme.ProEt.topology T)
          (SpTowerShriek.B P.coefficients.l F.val T)
          (SpTowerShriek.tau P.coefficients.l F.val T)).obj.obj U)
      property := fun v ↦ map_one ((systemRing (Scheme.ProEt.topology T)
        (SpTowerShriek.B P.coefficients.l F.val T)
        (SpTowerShriek.tau P.coefficients.l F.val T)).obj.map v).hom }

/-- The derived tensor-unit comparison is the actual scalar-adjunction transpose
of the localized coefficient map. It is not an arbitrary identification of units.
Source: blueprint (2), C_Y J_A = J_B
(blueprint: lem-sp-field-projection-origin-witnesses). -/
def scalarUnitMap (D : Models P) {E F : Index P} (h : E ≤ F) (T : Scheme.{u}) :
    (D.scalars E F h T).T.obj (J P E T) ⟶ J P F T :=
  ((D.scalars E F h T).adjunction.homEquiv _ _).symm
    ((DerivedCategory.singleFunctor (SpTowerShriek.S P.coefficients.l E.val T) 0).map
        (coefficientUnitMap P D h T) ≫
      (Functor.mapDerivedCategorySingleFunctor
        (res (FieldShriekSystem.coefficientMap P (D.coefficients E F h) T)) 0).inv.app
        (SpTowerClasses.coefficient T (spCoefficientCommRings P.coefficients.l F.val T)))

attribute [local irreducible] scalarUnitMap

/-- A retained origin with precisely the displayed etale Tor interval. Its data
are the existing Origin, including the fixed-scalar pair and intrinsic realization.
Source: blueprint (2), the five etale representatives
(blueprint: lem-sp-field-projection-origin-witnesses). -/
def HasOriginIn (D : Models P) (E : Index P) (T : Scheme.{u}) (n : ℕ)
    (K : SpTowerShriek.D P.coefficients.l E.val T) (s t : ℤ) : Prop :=
  ∃ w : SpTowerShriek.Origin P.coefficients.l E.val (D.base E) T n K,
    Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1} (SpTowerShriek.R P.coefficients.l E.val n)) T w.witness.complex.obj ∧
      Etale.DerivedCategory.hasTorAmplitudeIn
        (ULift.{u + 1} (SpTowerShriek.R P.coefficients.l E.val n)) T s t w.witness.complex.obj

/-- Transport retains the entire etale antecedent and postcomposes exactly its
realization. It imposes no compatibility between different levels.
Source: blueprint (2), v_n = c_J inverse composed with w_n
(blueprint: lem-sp-field-projection-origin-witnesses). -/
def transportOrigin (D : Models P) (E : Index P) (T : Scheme.{u}) (n : ℕ)
    {K L : SpTowerShriek.D P.coefficients.l E.val T}
    (w : SpTowerShriek.Origin P.coefficients.l E.val (D.base E) T n K) (e : K ≅ L) :
    SpTowerShriek.Origin P.coefficients.l E.val (D.base E) T n L where
  level := w.level
  witness := w.witness
  realization := w.realization ≪≫ (SpTowerShriek.Ev P.coefficients.l E.val T n).mapIso e

/-- The actual exceptional comparison at the coefficient unit, followed by the
right adjoint applied to the canonical scalar-unit comparison.
Source: blueprint (2), c_(J_A) with C_Y J_A identified with J_B
(blueprint: lem-sp-field-projection-origin-witnesses). -/
def dualizingComparison (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    (A : Adjoints P D c b a) (l : FieldExceptionalSystem.Laws P D c b a A)
    (j : ∀ E : Index P, normalized P D E Y (J P E Y))
    {E F : Index P} (h : E ≤ F) (hu : IsIso (scalarUnitMap P D h Y)) :
    (scalar P D a h X).obj ((A.right E).obj ⟨J P E Y, j E⟩) ≅
      (A.right F).obj ⟨J P F Y, j F⟩ :=
  (FieldExceptionalSystem.iso P D c b a A l h).app ⟨J P E Y, j E⟩ ≪≫
    (A.right F).mapIso (ObjectProperty.isoMk _ (@asIso _ _ _ _ (scalarUnitMap P D h Y) hu))

attribute [local irreducible] dualizingComparison

/-- All five levelwise origin, exact Tor-interval, and bounded-below assertions.
The arbitrary-witness clause uses the inverse of the actual c_J comparison.
Source: blueprint (2), projection-formula domain
(blueprint: lem-sp-field-projection-origin-witnesses). -/
def WitnessLaws (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (d : ℕ) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    (A : Adjoints P D c b a) (l : FieldExceptionalSystem.Laws P D c b a A)
    (j : ∀ E : Index P, normalized P D E Y (J P E Y))
    (units : ∀ (E F : Index P) (h : E ≤ F), IsIso (scalarUnitMap P D h Y)) : Prop :=
  ∀ (E F : Index P) (h : E ≤ F) (K : N P D E Y) (s t : ℤ),
    (∀ n : ℕ, HasProEtaleTorAmplitude Y (SpTowerShriek.R P.coefficients.l E.val n)
      ((SpTowerShriek.Ev P.coefficients.l E.val Y n).obj K.obj) s t) →
    (∀ n : ℕ,
      HasOriginIn P D E Y n K.obj s t ∧
      HasOriginIn P D E X n ((A.right E).obj ⟨J P E Y, j E⟩).obj
        (-2 * (d : ℤ)) (-2 * (d : ℤ)) ∧
      HasOriginIn P D F Y n ((scalar P D a h Y).obj K).obj s t ∧
      HasOriginIn P D F X n ((A.right F).obj ⟨J P F Y, j F⟩).obj
        (-2 * (d : ℤ)) (-2 * (d : ℤ)) ∧
      HasOriginIn P D F X n
        ((scalar P D a h X).obj ((A.right E).obj ⟨J P E Y, j E⟩)).obj
        (-2 * (d : ℤ)) (-2 * (d : ℤ))) ∧
    (∃ m : ℤ, K.obj.IsGE m) ∧
    (∃ m : ℤ, ((A.right E).obj ⟨J P E Y, j E⟩).obj.IsGE m) ∧
    (∃ m : ℤ, ((scalar P D a h Y).obj K).obj.IsGE m) ∧
    (∃ m : ℤ, ((A.right F).obj ⟨J P F Y, j F⟩).obj.IsGE m) ∧
    (∃ m : ℤ,
      ((scalar P D a h X).obj ((A.right E).obj ⟨J P E Y, j E⟩)).obj.IsGE m) ∧
    (∀ n : ℕ,
      SpTowerShriek.GoodLevel P.coefficients.l E.val (D.base E) Y n K.obj ∧
      SpTowerShriek.GoodLevel P.coefficients.l E.val (D.base E) X n
        ((A.right E).obj ⟨J P E Y, j E⟩).obj ∧
      SpTowerShriek.GoodLevel P.coefficients.l F.val (D.base F) Y n
        ((scalar P D a h Y).obj K).obj ∧
      SpTowerShriek.GoodLevel P.coefficients.l F.val (D.base F) X n
        ((A.right F).obj ⟨J P F Y, j F⟩).obj ∧
      SpTowerShriek.GoodLevel P.coefficients.l F.val (D.base F) X n
        ((scalar P D a h X).obj ((A.right E).obj ⟨J P E Y, j E⟩)).obj) ∧
    (∀ (n : ℕ) (w : SpTowerShriek.Origin P.coefficients.l F.val (D.base F) X n
        ((A.right F).obj ⟨J P F Y, j F⟩).obj),
      Etale.DerivedCategory.isBoundedConstructible
          (ULift.{u + 1} (SpTowerShriek.R P.coefficients.l F.val n)) X
          (transportOrigin P D F X n w
            ((normalized P D F X).ι.mapIso
              (dualizingComparison P D c b a A l j h (units E F h))).symm).witness.complex.obj ∧
        Etale.DerivedCategory.hasTorAmplitudeIn
          (ULift.{u + 1} (SpTowerShriek.R P.coefficients.l F.val n)) X
          (-2 * (d : ℤ)) (-2 * (d : ℤ))
          (transportOrigin P D F X n w
            ((normalized P D F X).ι.mapIso
              (dualizingComparison P D c b a A l j h (units E F h))).symm).witness.complex.obj)


attribute [local irreducible] Functor.mapDerivedCategory

private theorem tor_of_iso (T : Scheme.{u}) (B : Type u) [CommRing B]
    {K L : proEtaleDerivedCategory T B} (e : K ≅ L) {s t : ℤ}
    (h : HasProEtaleTorAmplitude T B K s t) : HasProEtaleTorAmplitude T B L s t := by
  refine ⟨h.1, ?_⟩
  intro C Q hC f hf hQ M i hi
  exact h.2 C Q (hC.map (fun z ↦ z ≪≫ e.symm)) f hf hQ M i hi

private theorem normalized_tor (D : Models P) (E : Index P) (T : Scheme.{u})
    (K : N P D E T) :
    ∃ s t : ℤ, ∀ n : ℕ,
      HasProEtaleTorAmplitude T (SpTowerShriek.R P.coefficients.l E.val n)
        ((SpTowerShriek.Ev P.coefficients.l E.val T n).obj K.obj) s t := by
  have hn := K.property
  unfold normalized at hn
  obtain ⟨a, b, s, t, _, _, hb⟩ := hn.1.2
  let e := SpTowerCalculus.realization P.coefficients.l E.val (D.base E) T
    ((D.coordinates E).abelian T)
  refine ⟨s, t, fun n ↦ ?_⟩
  exact tor_of_iso T _
    (((SpTowerCalculus.levelComparison P.coefficients.l E.val (D.base E)
        (D.coordinates E) T n).app (e.inverse.obj K.obj)).symm ≪≫
      (SpTowerShriek.Ev P.coefficients.l E.val T n).mapIso (e.counitIso.app K.obj))
    (hb n).2

private theorem origin_properties (D : Models P) (E : Index P) (T : Scheme.{u})
    (n : ℕ) (K : SpTowerShriek.D P.coefficients.l E.val T) (s t : ℤ)
    (hK : HasOriginIn P D E T n K s t)
    (w : SpTowerShriek.Origin P.coefficients.l E.val (D.base E) T n K) :
    Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1} (SpTowerShriek.R P.coefficients.l E.val n)) T
        w.witness.complex.obj ∧
      Etale.DerivedCategory.hasTorAmplitudeIn
        (ULift.{u + 1} (SpTowerShriek.R P.coefficients.l E.val n)) T s t
        w.witness.complex.obj := by
  let v := hK.choose
  have hc := hK.choose_spec.1
  have ht := hK.choose_spec.2
  let B := SpTowerShriek.R P.coefficients.l E.val n
  let C := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) T
  let : (sfIntrinsicModuleEquivalence T B).functor.Additive :=
    inferInstanceAs (finiteCoefficientIntrinsicRealization T B).Additive
  let R := (sfIntrinsicModuleEquivalence T B).mapDerivedCategory
  let ec : C.mapDerivedCategory.obj w.witness.complex.obj ≅
      C.mapDerivedCategory.obj v.witness.complex.obj :=
    R.unitIso.app _ ≪≫
      R.inverse.mapIso
        (R.functor.mapIso w.witness.iso ≪≫ w.realization ≪≫ v.realization.symm ≪≫
          R.functor.mapIso v.witness.iso.symm) ≪≫
      (R.unitIso.app _).symm
  let G := (comparisonLowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) T).rightDerivedFunctor
  let adj : C.mapDerivedCategory ⊣ G :=
    derivedComparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} B)) T
  let : IsIso (adj.unit.app w.witness.complex.obj) :=
    isIso_derivedComparisonAdjunction_unit_app _ _ _ w.witness.complex.property
  let : IsIso (adj.unit.app v.witness.complex.obj) :=
    isIso_derivedComparisonAdjunction_unit_app _ _ _ v.witness.complex.property
  let e : w.witness.complex.obj ≅ v.witness.complex.obj :=
    asIso (adj.unit.app w.witness.complex.obj) ≪≫ G.mapIso ec ≪≫
      (asIso (adj.unit.app v.witness.complex.obj)).symm
  refine ⟨⟨fun i ↦ ?_, ?_⟩, ?_⟩
  · have := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc.1 i)
    exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      (IsConstructibleSheaf.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm)
  · let a := hc.2.choose
    let b := hc.2.choose_spec.choose
    have hab := hc.2.choose_spec.choose_spec.1
    have hv := hc.2.choose_spec.choose_spec.2
    exact ⟨a, b, hab, fun i hi ↦
      (hv i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e)⟩
  · intro M i hi
    exact (ht M i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
      (((Etale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} B)) T).mapIso e).app
        ((DerivedCategory.singleFunctor _ 0).obj M)))

private theorem quotient_finite_ctf
    (E : Index P) (T : Scheme.{u})
    (I J : Ideal (Padic.coefficientExtensionIntegers P.coefficients.l E.val))
    [Finite (Padic.coefficientExtensionIntegers P.coefficients.l E.val ⧸ I)]
    [Finite (Padic.coefficientExtensionIntegers P.coefficients.l E.val ⧸ J)]
    (h : I = J)
    (M : proEtaleDerivedCategory T
      (Padic.coefficientExtensionIntegers P.coefficients.l E.val ⧸ I))
    (hM : spFiniteConstructibleTor T _ M) :
    spFiniteConstructibleTor T _
      ((SpTowerShriek.quotientTransport P.coefficients.l E.val T I J h).obj M) := by
  subst J
  exact hM

private theorem good_level_of_finite (D : Models P) (E : Index P) (T : Scheme.{u})
    (n : ℕ) (K : SpTowerShriek.D P.coefficients.l E.val T)
    (hK : spFiniteConstructibleTor T (SpTowerShriek.R P.coefficients.l E.val n)
      ((SpTowerShriek.Ev P.coefficients.l E.val T n).obj K)) :
    SpTowerShriek.GoodLevel P.coefficients.l E.val (D.base E) T n K := by
  let := Padic.finite_coefficientExtensionRing P.coefficients.l E.val
    ((D.base E).ramification * (n + 1))
    (Nat.mul_pos (D.base E).ramification_positive (Nat.succ_pos n))
  have hh := quotient_finite_ctf P E T _ _ ((D.base E).ideals n) _ hK
  obtain ⟨⟨a, b, hab, hv⟩, hc, ht⟩ := hh
  refine ⟨⟨?_, hc⟩, ht⟩
  apply (Set.finite_Icc a b).subset
  intro i hi
  exact ⟨le_of_not_gt (fun h ↦ hi (hv i (.inl h))),
    le_of_not_gt (fun h ↦ hi (hv i (.inr h)))⟩

private theorem normalized_lower_bound (D : Models P) (E : Index P) (T : Scheme.{u})
    (K : N P D E T) : ∃ m : ℤ, K.obj.IsGE m := by
  let e := SpTowerCalculus.realization P.coefficients.l E.val (D.base E) T
    ((D.coordinates E).abelian T)
  have hn := K.property
  unfold normalized at hn
  have hK := hn.1
  obtain ⟨m, hm⟩ := (SpTowerP1Uniform.uniformTower_etale_domains
    P.coefficients.l E.val (D.base E) T ((D.coordinates E).abelian T)
      (e.inverse.obj K.obj) hK).1
  refine ⟨m, (DerivedCategory.isGE_iff K.obj m).2 ?_⟩
  intro i hi
  exact ((DerivedCategory.isGE_iff _ m).1 hm i hi).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso (e.counitIso.app K.obj)).symm

/-- The coefficient-unit construction is independent of the five origin clauses.
Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2),
projection-formula domain (blueprint: lem-sp-field-projection-origin-witnesses-data).

Proof: the coefficient system in degree zero has its actual quotient transitions.
Each level is the finite constant coefficient module, constructible and flat, with
cohomological and Tor intervals [0,0]. Under the section-preserving realization these
are the same finite modules. For each m ≤ n, the canonical reduction is multiplication
A_m tensor over A_n A_n → A_m; its inverse sends a to a tensor 1. The tensor-unitor
normalization in the coefficient-tower interface identifies this with the specified
reduction map. Thus the coefficient system is normalized, not merely levelwise finite.
For E ≤ F the source unit is flat, hence its derived scalar extension is computed by
ordinary scalar extension. Multiplication B tensor over A A → B is invertible with
inverse b ↦ b tensor 1. The ordinary scalar adjunction sends this multiplication to
the coefficient map determined by 1. The normalized derived adjunction and the
single-complex comparison therefore identify its localization with scalarUnitMap.
This proves that the particular displayed map is invertible for every inclusion.
The construction uses the actual ell-power quotients and makes no assumption on
ramification; the same multiplication identities hold on empty sites. -/
theorem field_projection_origin_data
    (X Y : Scheme.{u}) [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    (d : ℕ) [SmoothOfRelativeDimension d f] [IsSeparated f] (c : Compactification f)
    (D : Models P) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    (A : Adjoints P D c b a) (l : FieldExceptionalSystem.Laws P D c b a A) :
    ∃ (j : ∀ E : Index P, normalized P D E Y (J P E Y))
      (units : ∀ (E F : Index P) (h : E ≤ F), IsIso (scalarUnitMap P D h Y)), True := by
  sorry

/-- The five levelwise etale-origin clauses for supplied coefficient units.
Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2),
projection-formula domain (blueprint: lem-sp-field-projection-origin-witnesses-levels).

Proof: normalization gives bounded constructible levels of K. The assumed interval
[s,t] is unchanged by finite free field scalar extension, including ramified field
extensions, by field_scalar_normalized_systems. Smooth-coordinate tower gluing
identifies the dualizing object locally with the positive Tate line shifted by 2d:
apply its chart model to the coefficient unit, whose intervals are [0,0]. The chart
admissibility theorem gives Tor interval [-2d,-2d] on each chart. Choose a finite
admissible coordinate cover and use Tor-interval local detection to obtain this
same interval on X for both coefficient fields. The actual dualizingComparison,
which includes the prescribed scalar-unit map, identifies the scalar extension of
the first dualizing object with the second one, so the fifth object has that interval.
For each level and each of the first four objects, finiteRing_constructibleDerived_origin
supplies a bounded constructible etale antecedent and an intrinsic realization.
Factor this realization through fixed-scalar site comparison and package it as Origin.
The antecedent is bounded below by its bounded cohomology. Comparison Tor amplitude
reflects precisely the given interval, so these four origins have the required bounds.
For the fifth origin postcompose an origin of the second dualizing object with the
inverse evaluated dualizingComparison; its antecedent and both properties are unchanged.
All representatives are chosen separately at each level. Base.ideals identifies the
ell-power quotient at n with the uniformizer quotient at ramification*(n+1), so these
arguments include every positive level and every ramified extension. Empty schemes,
zero inputs, and d=0 require no change to the vanishing or isomorphism arguments. -/
theorem field_projection_origin_level_witnesses
    (X Y : Scheme.{u}) [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    (d : ℕ) [SmoothOfRelativeDimension d f] [IsSeparated f] (c : Compactification f)
    (D : Models P) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    (A : Adjoints P D c b a) (l : FieldExceptionalSystem.Laws P D c b a A)
    (j : ∀ E : Index P, normalized P D E Y (J P E Y))
    (units : ∀ (E F : Index P) (h : E ≤ F), IsIso (scalarUnitMap P D h Y))
    (E F : Index P) (h : E ≤ F) (K : N P D E Y) (s t : ℤ)
    (hK : ∀ n : ℕ, HasProEtaleTorAmplitude Y (SpTowerShriek.R P.coefficients.l E.val n)
      ((SpTowerShriek.Ev P.coefficients.l E.val Y n).obj K.obj) s t) :
    ∀ n : ℕ,
      HasOriginIn P D E Y n K.obj s t ∧
      HasOriginIn P D E X n ((A.right E).obj ⟨J P E Y, j E⟩).obj
        (-2 * (d : ℤ)) (-2 * (d : ℤ)) ∧
      HasOriginIn P D F Y n ((scalar P D a h Y).obj K).obj s t ∧
      HasOriginIn P D F X n ((A.right F).obj ⟨J P F Y, j F⟩).obj
        (-2 * (d : ℤ)) (-2 * (d : ℤ)) ∧
      HasOriginIn P D F X n
        ((scalar P D a h X).obj ((A.right E).obj ⟨J P E Y, j E⟩)).obj
        (-2 * (d : ℤ)) (-2 * (d : ℤ)) := by
  sorry

/-- Uniform lower bounds for the five projection inputs.
Source: blueprint (2), projection-formula domain
(blueprint: lem-sp-field-projection-origin-witnesses-lower-bounds).

Proof: each object belongs to the normalized full subcategory. Forget normalization,
apply uniformTower_etale_domains to its inverse realization, and transport the resulting
lower bound through the realization counit using homology isomorphisms. -/
theorem field_projection_origin_lower_bounds
    (X Y : Scheme.{u}) [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    (d : ℕ) [SmoothOfRelativeDimension d f] [IsSeparated f] (c : Compactification f)
    (D : Models P) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    (A : Adjoints P D c b a) (l : FieldExceptionalSystem.Laws P D c b a A)
    (j : ∀ E : Index P, normalized P D E Y (J P E Y))
    (E F : Index P) (h : E ≤ F) (K : N P D E Y) :
    (∃ m : ℤ, K.obj.IsGE m) ∧
    (∃ m : ℤ, ((A.right E).obj ⟨J P E Y, j E⟩).obj.IsGE m) ∧
    (∃ m : ℤ, ((scalar P D a h Y).obj K).obj.IsGE m) ∧
    (∃ m : ℤ, ((A.right F).obj ⟨J P F Y, j F⟩).obj.IsGE m) ∧
    (∃ m : ℤ,
      ((scalar P D a h X).obj ((A.right E).obj ⟨J P E Y, j E⟩)).obj.IsGE m) := by
  have _ := l
  exact ⟨normalized_lower_bound P D E Y K,
    normalized_lower_bound P D E X ((A.right E).obj ⟨J P E Y, j E⟩),
    normalized_lower_bound P D F Y ((scalar P D a h Y).obj K),
    normalized_lower_bound P D F X ((A.right F).obj ⟨J P F Y, j F⟩),
    normalized_lower_bound P D F X
      ((scalar P D a h X).obj ((A.right E).obj ⟨J P E Y, j E⟩))⟩

/-- GoodLevel hypotheses for the five projection inputs.
Source: blueprint (2), projection-formula domain
(blueprint: lem-sp-field-projection-origin-witnesses-good-levels).

Proof: Domains.finite gives bounded constructible cohomology and finite Tor amplitude
for every level of each normalized input. Transport these along Base.ideals. The support
is a subset of the finite integer interval bounding cohomology. This is exactly the
intrinsic constructibility and Tor predicate used by GoodLevel. -/
theorem field_projection_origin_good_levels
    (X Y : Scheme.{u}) [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    (d : ℕ) [SmoothOfRelativeDimension d f] [IsSeparated f] (c : Compactification f)
    (D : Models P) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    (A : Adjoints P D c b a) (l : FieldExceptionalSystem.Laws P D c b a A)
    (j : ∀ E : Index P, normalized P D E Y (J P E Y))
    (E F : Index P) (h : E ≤ F) (K : N P D E Y) :
    ∀ n : ℕ,
      SpTowerShriek.GoodLevel P.coefficients.l E.val (D.base E) Y n K.obj ∧
      SpTowerShriek.GoodLevel P.coefficients.l E.val (D.base E) X n
        ((A.right E).obj ⟨J P E Y, j E⟩).obj ∧
      SpTowerShriek.GoodLevel P.coefficients.l F.val (D.base F) Y n
        ((scalar P D a h Y).obj K).obj ∧
      SpTowerShriek.GoodLevel P.coefficients.l F.val (D.base F) X n
        ((A.right F).obj ⟨J P F Y, j F⟩).obj ∧
      SpTowerShriek.GoodLevel P.coefficients.l F.val (D.base F) X n
        ((scalar P D a h X).obj ((A.right E).obj ⟨J P E Y, j E⟩)).obj := by
  have _ := l
  intro n
  exact ⟨good_level_of_finite P D E Y n K.obj (a.finite E Y (.inr rfl) n K),
    good_level_of_finite P D E X n _
      (a.finite E X (.inl rfl) n ((A.right E).obj ⟨J P E Y, j E⟩)),
    good_level_of_finite P D F Y n _
      (a.finite F Y (.inr rfl) n ((scalar P D a h Y).obj K)),
    good_level_of_finite P D F X n _
      (a.finite F X (.inl rfl) n ((A.right F).obj ⟨J P F Y, j F⟩)),
    good_level_of_finite P D F X n _ (a.finite F X (.inl rfl) n
      ((scalar P D a h X).obj ((A.right E).obj ⟨J P E Y, j E⟩)))⟩

/-- Transport of arbitrary bounded-below origins along the inverse dualizing comparison.
Source: blueprint (2), projection-formula domain
(blueprint: lem-sp-field-projection-origin-witnesses-transport).

Proof: extract a uniform Tor interval for J_F from normalization and specialize the
level-witness theorem to F=F, K=J_F. It supplies one origin v of the dualizing object
with the required exact interval. Any retained origin w realizes the same object.
Full faithfulness of intrinsic realization identifies the fixed-scalar comparison
images of their etale antecedents. Both antecedents are bounded below, so the
comparison-adjunction units are invertible. Conjugating the derived right-comparison
image of the isomorphism by these units identifies the two etale antecedents.
Homology transports constructibility and the
same cohomological bounds from v to w. For each tensor test, derived tensor and
homology transport the required vanishing and hence the same exact Tor interval.
Finally transportOrigin changes only realization, so its antecedent is that of w. -/
theorem field_projection_origin_transport
    (X Y : Scheme.{u}) [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    (d : ℕ) [SmoothOfRelativeDimension d f] [IsSeparated f] (c : Compactification f)
    (D : Models P) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    (A : Adjoints P D c b a) (l : FieldExceptionalSystem.Laws P D c b a A)
    (j : ∀ E : Index P, normalized P D E Y (J P E Y))
    (units : ∀ (E F : Index P) (h : E ≤ F), IsIso (scalarUnitMap P D h Y))
    (E F : Index P) (h : E ≤ F) :
    ∀ (n : ℕ) (w : SpTowerShriek.Origin P.coefficients.l F.val (D.base F) X n
        ((A.right F).obj ⟨J P F Y, j F⟩).obj),
      Etale.DerivedCategory.isBoundedConstructible
          (ULift.{u + 1} (SpTowerShriek.R P.coefficients.l F.val n)) X
          (transportOrigin P D F X n w
            ((normalized P D F X).ι.mapIso
              (dualizingComparison P D c b a A l j h (units E F h))).symm).witness.complex.obj ∧
        Etale.DerivedCategory.hasTorAmplitudeIn
          (ULift.{u + 1} (SpTowerShriek.R P.coefficients.l F.val n)) X
          (-2 * (d : ℤ)) (-2 * (d : ℤ))
          (transportOrigin P D F X n w
            ((normalized P D F X).ι.mapIso
              (dualizingComparison P D c b a A l j h (units E F h))).symm).witness.complex.obj := by
  intro n w
  dsimp only [transportOrigin]
  let U : N P D F Y := ⟨J P F Y, j F⟩
  have hU := normalized_tor P D F Y U
  let s := hU.choose
  let t := hU.choose_spec.choose
  have ht := hU.choose_spec.choose_spec
  have hw := (field_projection_origin_level_witnesses P X Y f d c D b a A l j units
    F F le_rfl U s t ht n).2.1
  exact origin_properties P D F X n _ (-2 * (d : ℤ)) (-2 * (d : ℤ)) hw w

/-- The five purity projection inputs have bounded constructible etale origins
with their specified intervals, and meet both inputs of the tower projection domain.
Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2)
(blueprint: lem-sp-field-projection-origin-witnesses).

Proof: (1) Chart admissibility identifies the finite ell-power rings with the cofinal
uniformizer quotients. The coefficient units are normalized, with both intervals [0,0].
The given K has uniformly bounded constructible levels by normalized-towers.
(2) Tower gluing on a finite smooth-coordinate cover identifies the dualizing levels
with the pullback of the coefficient unit twisted by d and shifted by 2d. Chart
admissibility gives Tor interval [-2d,-2d]. Tor-interval local detection descends this
bound; the tensor unit test gives cohomological concentration in degree -2d.
(3) Field scalar normalized systems preserves the intervals of K. The exceptional
system comparison at J, followed by scalar multiplication C_Y J_A = J_B, identifies
C_X omega_A with omega_B, and transfers the same bounds to the fifth object.
(4) Finite-ring constructible derived origin supplies separate bounded constructible
etale representatives of the first four objects. Comparison Tor amplitude reflects
exactly [s,t], [-2d,-2d], [s,t], [-2d,-2d], also at ramified cofinal indices.
(5) Postcompose any given omega_B realization with the inverse evaluated c_J. This
retains its etale antecedent. Full faithfulness of site comparison identifies any
bounded-below antecedent with the bounded constructible one from (4), so it too is
bounded constructible and has Tor interval [-2d,-2d].
(6) The five uniform cohomological bounds imply boundedness below as ordinary strict
towers by chart admissibility. Their origins and GoodLevel predicates supply exactly
both inputs of shriek-levels (2a), for (K,omega_A), (C_Y K,omega_B), and
(C_Y K,C_X omega_A); X/Y input order is the one of that projection interface.
(7) No unramified hypothesis entered: Base.ideals identifies the exponent n+1 with
ramification*(n+1). For d=0 the interval is [0,0]; empty schemes and zero inputs
satisfy the same vanishing statements. No transition between origins is asserted. -/
theorem field_projection_origin_witnesses
    (X Y : Scheme.{u}) [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    (d : ℕ) [SmoothOfRelativeDimension d f] [IsSeparated f] (c : Compactification f)
    (D : Models P) (b : FieldShriekSystem.Laws P D c) (a : Domains P D c)
    (A : Adjoints P D c b a) (l : FieldExceptionalSystem.Laws P D c b a A) :
    ∃ (j : ∀ E : Index P, normalized P D E Y (J P E Y))
      (units : ∀ (E F : Index P) (h : E ≤ F), IsIso (scalarUnitMap P D h Y)),
      WitnessLaws P D c d b a A l j units := by
  obtain ⟨j, units, _⟩ := field_projection_origin_data P X Y f d c D b a A l
  refine ⟨j, units, ?_⟩
  intro E F h K s t hK
  have hl := field_projection_origin_lower_bounds P X Y f d c D b a A l j E F h K
  exact ⟨field_projection_origin_level_witnesses P X Y f d c D b a A l j units E F h K s t hK,
    hl.1, hl.2.1, hl.2.2.1, hl.2.2.2.1, hl.2.2.2.2,
    field_projection_origin_good_levels P X Y f d c D b a A l j E F h K,
    field_projection_origin_transport P X Y f d c D b a A l j units E F h⟩

end AlgebraicGeometry.ProEtale.FieldProjectionOrigin
