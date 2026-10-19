/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import Sheaf.Paper.CommonStageWeilShriek
public import Sheaf.Paper.IntegralPullbackCompletedComparison
public import Sheaf.Paper.FieldShriekLowerBound
public import Mathlib.CategoryTheory.Shift.Adjunction

/-! # Normalized shifts and finite-stage Weil compact support

Source: blueprint main-20261015, lem-zl-composition-weight-bound.proof.md,
first paragraph; lem-fix-weil-operations.proof.md, first two paragraphs;
Stacks Tags 014E, 0941 and 099N(5); SGA 4 XVII, sections 5--6
(blueprint: def-zl-field-weil-shriek-shift-data).

The common-stage proper/open functors and exchanges are reused. Their finite-stage
counterparts are adjoints of the recorded rational pullbacks. Shift comparisons
are fixed by signed Roos reindexing, localization, and adjunction mates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem map_heq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {K L K' L' : C} (hK : K = K') (hL : L = L')
    {a : K ⟶ L} {b : K' ⟶ L'} (h : HEq a b) : HEq (F.map a) (F.map b) := by
  cases hK
  cases hL
  cases h
  rfl

private def localizedIso {R : Type*} [CommRing R] (p : R)
    {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    (F G : C ⥤ D)
    (F' G' : ScalarLocalization R C p ⥤ ScalarLocalization R D p)
    [F'.Additive] [G'.Additive]
    (hF : ∀ K, F'.obj K = ⟨F.obj K.obj⟩)
    (hG : ∀ K, G'.obj K = ⟨G.obj K.obj⟩)
    (hFm : ∀ (K L : C) (a : K ⟶ L) (c : Localization.Away p),
      HEq (F'.map (c ⊗ₜ[R] a : ScalarLocalization.mk K ⟶ ScalarLocalization.mk L))
        (c ⊗ₜ[R] F.map a))
    (hGm : ∀ (K L : C) (a : K ⟶ L) (c : Localization.Away p),
      HEq (G'.map (c ⊗ₜ[R] a : ScalarLocalization.mk K ⟶ ScalarLocalization.mk L))
        (c ⊗ₜ[R] G.map a)) (e : F ≅ G) : F' ≅ G' :=
  NatIso.ofComponents (fun K ↦ eqToIso (hF K) ≪≫
    (ScalarLocalization.localization R D p).mapIso (e.app K.obj) ≪≫
      (eqToIso (hG K)).symm) (by
    intro K L a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul c a =>
      rw [(conj_eqToHom_iff_heq _ _ (hF K) (hF L)).2 (hFm K.obj L.obj a c),
        (conj_eqToHom_iff_heq _ _ (hG K) (hG L)).2 (hGm K.obj L.obj a c)]
      simp only [Iso.trans_hom, eqToIso.hom, Iso.symm_hom, eqToIso.inv,
        Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [cancel_epi]
      simp only [← Category.assoc, cancel_mono]
      change ScalarLocalization.composition R D p _ _ _ (1 ⊗ₜ[R] e.hom.app L.obj)
          (c ⊗ₜ[R] F.map a) =
        ScalarLocalization.composition R D p _ _ _ (c ⊗ₜ[R] G.map a)
          (1 ⊗ₜ[R] e.hom.app K.obj)
      simp only [ScalarLocalization.composition_tmul, one_mul, mul_one, e.hom.naturality]
    | add a b ha hb =>
      change F'.map (a + b) ≫ _ = _ ≫ G'.map (a + b)
      rw [F'.map_add, G'.map_add, Preadditive.add_comp, Preadditive.comp_add]
      exact congrArg₂ (· + ·) ha hb)

section PullbackShift
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The integral shift is uniquely fixed by the actual signed Roos coordinates and
its retained comparison on every good representative. Source: Stacks 014E, 0941,
099N(5) (blueprint: def-zl-field-weil-shriek-shift-data).
Proof: the product reindexing and diagonal mapping-cocone map (1,(-1)^r) give
natural coherent chain isomorphisms. Shifted flat-term K-flat complexes remain good.
Descend through the recorded good localization. Its resolving equivalence determines
the descended comparison uniquely from the displayed square. -/
theorem fieldIntegralPullShift_existsUnique :
    ∃! d : (integralDerivedPullback l E f).CommShift ℤ,
      ∃ c : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ,
        IntegralCompletedComparison.ShiftCoordinates l E f c ∧
          IntegralCompletedComparison.ShiftDescent l E f c d := by
  sorry

/-- The representative-normalized integral shift. Source: Stacks 0941, 099N(5)
(blueprint: def-zl-field-weil-shriek-shift-data). -/
instance fieldIntegralPullShift : (integralDerivedPullback l E f).CommShift ℤ :=
  (fieldIntegralPullShift_existsUnique l E f).exists.choose

variable [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Restrict the ambient shift through the fully faithful constructible inclusion.
Source: Stacks 099N(5) (blueprint: def-zl-field-weil-shriek-shift-data). -/
instance fieldConstructiblePullShift : (constructibleIntegralPullback l E f).CommShift ℤ :=
  letI : (integralDerivedPullback l E f).CommShift ℤ := fieldIntegralPullShift l E f
  letI : ((sfIntegralConstructible l E Y).ι).CommShift ℤ := inferInstance
  Functor.CommShift.ofComp
    (F := constructibleIntegralPullback l E f) (G := (sfIntegralConstructible l E X).ι)
    (Iso.refl ((sfIntegralConstructible l E Y).ι ⋙ integralDerivedPullback l E f)) ℤ

/-- Localize the fixed integral shift at one; the CommShift laws determine all integer
shifts. Source: blueprint coefficient passage; Stacks 014E, 099N(5)
(blueprint: def-zl-field-weil-shriek-shift-data).
Proof: tensor the integral comparison with one. The rational shift and localization
comparison at one have precisely these integral objects and identity components.
Naturality on integral arrows extends to tensor Homs. Zero and addition descend,
and every rational object is an integral object, proving uniqueness. -/
theorem fieldRationalPullShift_existsUnique :
    ∃! c : (rationalDerivedPullback l E f).CommShift ℤ,
      ∀ K : sfIntegralConstructibleCategory l E Y,
        HEq ((Functor.commShiftIso (rationalDerivedPullback l E f)
          (self := c) (1 : ℤ)).hom.app ((sfRationalConstructibleLocalization l E Y).obj K))
          ((sfRationalConstructibleLocalization l E X).map
            (((constructibleIntegralPullback l E f).commShiftIso (1 : ℤ)).hom.app K)) := by
  sorry

/-- The localized canonical pullback shift. Source: blueprint coefficient passage
(blueprint: def-zl-field-weil-shriek-shift-data). -/
instance fieldRationalPullShift : (rationalDerivedPullback l E f).CommShift ℤ :=
  (fieldRationalPullShift_existsUnique l E f).exists.choose
end PullbackShift

section CommonShift
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X Y : Scheme.{u}} (f : X ⟶ Y)
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- The common-stage shift is the class of the normalized rational shift at the
object's finite field. Source: blueprint common-stage coefficient passage
(blueprint: def-zl-field-weil-shriek-shift-data).
Proof: scalar comparison maps come from integral tensor maps and commute with signed
reindexing. Thus the rational comparisons agree upon enlargement and descend to every
representative. Every pair lies in its own finite stage, determining the components.
The finite zero and addition equations descend and give uniqueness. -/
theorem fieldCommonPullShift_existsUnique :
    ∃! c : (commonStageDerivedPullback l Ω f).CommShift ℤ,
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y L),
        HEq ((Functor.commShiftIso (commonStageDerivedPullback l Ω f)
          (self := c) (1 : ℤ)).hom.app
            ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K))
          ((GeneralAlgebraicallyClosedCoefficients.inclusion L).map
            (((rationalDerivedPullback l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).commShiftIso
                (1 : ℤ)).hom.app K)) := by
  sorry

/-- The representative-normalized common-stage shift. Source: blueprint coefficient passage
(blueprint: def-zl-field-weil-shriek-shift-data). -/
instance fieldCommonPullShift : (commonStageDerivedPullback l Ω f).CommShift ℤ :=
  (fieldCommonPullShift_existsUnique l Ω f).exists.choose
end CommonShift

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The rational inverse image along the geometric fibre map. Source: blueprint
lem-fix-weil-operations.proof, first paragraph
(blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldWeilPull {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :=
  @rationalDerivedPullback l _ E _ _ _ _ _ (zlFiberMap D f₀)
    (sfWeilPrimeInvertible D l hl X₀) (sfWeilPrimeInvertible D l hl Y₀)

/-- Rational composition is the localization of the already normalized integral
composition. Source: Stacks 099N(5), blueprint pullback composition
(blueprint: def-zl-field-weil-shriek-shift-data).
Proof: localize the integral component fixed by integralPullbackComposition.
Naturality extends from integral maps to fractions. The prescribed object action
identifies the endpoints; these components determine the natural isomorphism. -/
theorem fieldRationalPullComp_existsUnique {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃! c : rationalDerivedPullback l E (f ≫ g) ≅
        rationalDerivedPullback l E g ⋙ rationalDerivedPullback l E f,
      ∀ K : sfIntegralConstructibleCategory l E Z,
        HEq (c.hom.app ((sfRationalConstructibleLocalization l E Z).obj K))
          ((sfRationalConstructibleLocalization l E X).map
            (((integralPullbackComposition l E).choose f g).hom.app K)) := by
  let F := constructibleIntegralPullback l E (f ≫ g)
  let G := constructibleIntegralPullback l E g ⋙ constructibleIntegralPullback l E f
  let F' := rationalDerivedPullback l E (f ≫ g)
  let G' := rationalDerivedPullback l E g ⋙ rationalDerivedPullback l E f
  have hf := (rationalDerivedPullback_existsUnique l E f).exists.choose_spec
  have hg := (rationalDerivedPullback_existsUnique l E g).exists.choose_spec
  have hfg := (rationalDerivedPullback_existsUnique l E (f ≫ g)).exists.choose_spec
  let : F'.Additive := hfg.1
  let : (rationalDerivedPullback l E f).Additive := hf.1
  let : (rationalDerivedPullback l E g).Additive := hg.1
  have hG (K : sfRationalConstructibleCategory l E Z) : G'.obj K = ⟨G.obj K.obj⟩ :=
    (congrArg (rationalDerivedPullback l E f).obj (hg.2.1 K)).trans (hf.2.1 _)
  have hGm (K L : sfIntegralConstructibleCategory l E Z) (a : K ⟶ L)
      (c : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
      HEq (G'.map (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] a))
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] G.map a) := by
    exact (map_heq (rationalDerivedPullback l E f) (hg.2.1 ⟨K⟩) (hg.2.1 ⟨L⟩)
      (hg.2.2 K L a c)).trans (hf.2.2 _ _ _ c)
  let e := localizedIso (Padic.coefficientExtensionUniformizer l E)
    F G F' G' hfg.2.1 hG hfg.2.2 hGm ((integralPullbackComposition l E).choose f g)
  have he (K : sfIntegralConstructibleCategory l E Z) :
      HEq (e.hom.app ((sfRationalConstructibleLocalization l E Z).obj K))
        ((sfRationalConstructibleLocalization l E X).map
          (((integralPullbackComposition l E).choose f g).hom.app K)) := by
    apply (conj_eqToHom_iff_heq _ _ (hfg.2.1 ⟨K⟩) (hG ⟨K⟩)).1
    rfl
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq ((he' K.obj).trans (he K.obj).symm)


/-- The fixed rational pullback composition. Source: Stacks 099N(5)
(blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldRationalPullComp {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (fieldRationalPullComp_existsUnique l E f g).exists.choose

section Finite
variable {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The finite-stage Frobenius square uses the normalized composition and the actual
semilinear geometric-Frobenius naturality equality. Source: blueprint
lem-fix-weil-operations.proof, first paragraph
(blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldWeilPullSquare (f₀ : X₀ ⟶ Y₀) :
    fieldWeilPull D l hl E f₀ ⋙ sfWeilFrobeniusPullback D l hl X₀ E ≅
      sfWeilFrobeniusPullback D l hl Y₀ E ⋙ fieldWeilPull D l hl E f₀ :=
  letI := sfWeilPrimeInvertible D l hl X₀
  letI := sfWeilPrimeInvertible D l hl Y₀
  (fieldRationalPullComp l E (D.geometricFrobenius X₀).hom (zlFiberMap D f₀)).symm ≪≫
    eqToIso (congrArg (fun f ↦ rationalDerivedPullback l E f)
      (zlFrobenius_naturality D f₀)) ≪≫
    fieldRationalPullComp l E (zlFiberMap D f₀) (D.geometricFrobenius Y₀).hom

/-- Proper rational pullback has its constructible right adjoint, and open rational
pullback has its extension-by-zero left adjoint. Source: SGA 4 XVII, sections 5--6
(blueprint: def-zl-field-weil-shriek-shift-data).
Proof: the finite proper/open adjunctions preserve bounded constructibility. Their
coherent complete towers restrict the adjunctions to integral constructible objects.
Localizing the linear Hom bijections gives the asserted rational adjunctions. -/
theorem fieldWeilPull_adjoints (f₀ : X₀ ⟶ Y₀) :
    (IsProper f₀.left → (fieldWeilPull D l hl E f₀).IsLeftAdjoint) ∧
      (IsOpenImmersion f₀.left → (fieldWeilPull D l hl E f₀).IsRightAdjoint) := by
  sorry

/-- The adjunction-determined proper image. Source: SGA 4 XVII, section 5
(blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldWeilProper (p₀ : X₀ ⟶ Y₀) [IsProper p₀.left] :=
  letI := (fieldWeilPull_adjoints D l hl E p₀).1 inferInstance
  (fieldWeilPull D l hl E p₀).rightAdjoint

/-- The actual proper adjunction. Source: SGA 4 XVII, section 5
(blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldWeilProperAdj (p₀ : X₀ ⟶ Y₀) [IsProper p₀.left] :
    fieldWeilPull D l hl E p₀ ⊣ fieldWeilProper D l hl E p₀ :=
  letI := (fieldWeilPull_adjoints D l hl E p₀).1 inferInstance
  Adjunction.ofIsLeftAdjoint _

/-- The adjunction-determined open extension. Source: SGA 4 XVII, section 5
(blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldWeilOpen (j₀ : X₀ ⟶ Y₀) [IsOpenImmersion j₀.left] :=
  letI := (fieldWeilPull_adjoints D l hl E j₀).2 inferInstance
  (fieldWeilPull D l hl E j₀).leftAdjoint

/-- The actual open adjunction. Source: SGA 4 XVII, section 5
(blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldWeilOpenAdj (j₀ : X₀ ⟶ Y₀) [IsOpenImmersion j₀.left] :
    fieldWeilOpen D l hl E j₀ ⊣ fieldWeilPull D l hl E j₀ :=
  letI := (fieldWeilPull_adjoints D l hl E j₀).2 inferInstance
  Adjunction.ofIsRightAdjoint _

/-- The proper exchange is the right mate of inverse-image exchange.
Source: blueprint lem-fix-weil-operations.proof, first paragraph
(blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldWeilProperExchangeMap (p₀ : X₀ ⟶ Y₀) [IsProper p₀.left] :=
  (mateEquiv (fieldWeilProperAdj D l hl E p₀) (fieldWeilProperAdj D l hl E p₀)
    (TwoSquare.mk _ _ _ _ (fieldWeilPullSquare D l hl E p₀).inv)).natTrans

/-- The inverse open exchange is the left mate of inverse-image exchange.
Source: blueprint lem-fix-weil-operations.proof, first paragraph
(blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldWeilOpenExchangeInverseMap (j₀ : X₀ ⟶ Y₀) [IsOpenImmersion j₀.left] :=
  ((mateEquiv (fieldWeilOpenAdj D l hl E j₀) (fieldWeilOpenAdj D l hl E j₀)).symm
    (TwoSquare.mk _ _ _ _ (fieldWeilPullSquare D l hl E j₀).hom)).natTrans

/-- The specified proper and open mates are isomorphisms.
Source: blueprint lem-fix-weil-operations.proof, inverse automorphism square
(blueprint: def-zl-field-weil-shriek-shift-data).
Proof: form the same mates for the inverse geometric-Frobenius square. Pullback
composition coherence and mate pasting identify both composites with identities.
This proves invertibility of these particular maps. -/
theorem fieldWeilExchange_isIso :
    (∀ (p₀ : X₀ ⟶ Y₀) [IsProper p₀.left],
      IsIso (fieldWeilProperExchangeMap D l hl E p₀)) ∧
    (∀ (j₀ : X₀ ⟶ Y₀) [IsOpenImmersion j₀.left],
      IsIso (fieldWeilOpenExchangeInverseMap D l hl E j₀)) := by
  sorry

/-- Proper exchange, with its prescribed forward mate.
Source: blueprint lem-fix-weil-operations.proof
(blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldWeilProperExchange (p₀ : X₀ ⟶ Y₀) [IsProper p₀.left] :=
  @asIso _ _ _ _ (fieldWeilProperExchangeMap D l hl E p₀)
    ((fieldWeilExchange_isIso D l hl E).1 p₀)

/-- Open exchange, inverse to its prescribed left mate.
Source: blueprint lem-fix-weil-operations.proof
(blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldWeilOpenExchange (j₀ : X₀ ⟶ Y₀) [IsOpenImmersion j₀.left] :=
  (@asIso _ _ _ _ (fieldWeilOpenExchangeInverseMap D l hl E j₀)
    ((fieldWeilExchange_isIso D l hl E).2 j₀)).symm

/-- Finite-stage compact support, first open extension, then proper image.
Source: SGA 4 XVII, sections 5--6 (blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldWeilShriek (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left) :=
  letI : IsProper (zlCompactificationProper D f₀ c).left := inferInstanceAs (IsProper c.g)
  fieldWeilOpen D l hl E (zlCompactificationOpen D f₀ c) ⋙
    fieldWeilProper D l hl E (zlCompactificationProper D f₀ c)

/-- Compact-support exchange is the proper exchange followed by the open exchange.
Source: blueprint lem-fix-weil-operations.proof, compact-support paragraph
(blueprint: def-zl-field-weil-shriek-shift-data). -/
def fieldWeilShriekExchange (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left) :
    fieldWeilShriek D l hl E f₀ c ⋙ sfWeilFrobeniusPullback D l hl Y₀ E ≅
      sfWeilFrobeniusPullback D l hl X₀ E ⋙ fieldWeilShriek D l hl E f₀ c :=
  letI : IsProper (zlCompactificationProper D f₀ c).left := inferInstanceAs (IsProper c.g)
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (fieldWeilProperExchange D l hl E (zlCompactificationProper D f₀ c)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (fieldWeilOpenExchange D l hl E (zlCompactificationOpen D f₀ c)) _ ≪≫
    Functor.associator _ _ _

/-- The rational inverse-image shift, with the canonical residue-field inverses supplied.
Source: Stacks 099N(5) (blueprint: def-zl-field-weil-shriek-shift-data). -/
instance fieldWeilPullShift (f₀ : X₀ ⟶ Y₀) :
    (fieldWeilPull D l hl E f₀).CommShift ℤ :=
  @fieldRationalPullShift l _ E _ _ _ _ _ (zlFiberMap D f₀)
    (sfWeilPrimeInvertible D l hl X₀) (sfWeilPrimeInvertible D l hl Y₀)

/-- Proper shift is the unique shift compatible with the proper adjunction.
Source: SGA 4 XVII, section 5 (blueprint: def-zl-field-weil-shriek-shift-data). -/
instance fieldWeilProperShift (p₀ : X₀ ⟶ Y₀) [IsProper p₀.left] :
    (fieldWeilProper D l hl E p₀).CommShift ℤ :=
  (fieldWeilProperAdj D l hl E p₀).rightAdjointCommShift ℤ

/-- Open shift is the unique shift compatible with the open adjunction.
Source: SGA 4 XVII, section 5 (blueprint: def-zl-field-weil-shriek-shift-data). -/
instance fieldWeilOpenShift (j₀ : X₀ ⟶ Y₀) [IsOpenImmersion j₀.left] :
    (fieldWeilOpen D l hl E j₀).CommShift ℤ :=
  (fieldWeilOpenAdj D l hl E j₀).leftAdjointCommShift ℤ

/-- Compact support has the composite of its proper and open shifts.
Source: SGA 4 XVII, sections 5--6 (blueprint: def-zl-field-weil-shriek-shift-data). -/
instance fieldWeilShriekShift (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left) :
    (fieldWeilShriek D l hl E f₀ c).CommShift ℤ :=
  letI : IsProper (zlCompactificationProper D f₀ c).left := inferInstanceAs (IsProper c.g)
  inferInstanceAs ((fieldWeilOpen D l hl E (zlCompactificationOpen D f₀ c) ⋙
    fieldWeilProper D l hl E (zlCompactificationProper D f₀ c)).CommShift ℤ)

/-- The adjunction-defined finite operation agrees with the recorded normalized
compact-support action on every object and morphism. Source: SGA 4 XVII, sections
5--6; Bhatt--Scholze 6.7.6--6.7.7
(blueprint: def-zl-field-weil-shriek-shift-data).
Proof: the proper and open adjunctions restrict the completed proper/open adjunctions.
Uniqueness of adjoints identifies both chosen functors with those operations.
The projection-normalized realization of sfQcqsCompactSupportRealization then
identifies their composite with the recorded integral functor. Localize this
natural comparison on tensor Homs. Common proper refinements identify the chosen
base-changed compactification with any geometric compactification used by the action.
No separatedness of a structure morphism is used. -/
theorem fieldWeilShriek_recorded (f₀ : X₀ ⟶ Y₀)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (c : Compactification f₀.left) (cg : Compactification (zlFiberMap D f₀)) :
    Nonempty (fieldWeilShriek D l hl E f₀ c ≅
      sfCompactSupportFiniteFunctor
        (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
        (f := zlFiberMap D f₀) l D.k (zlClosurePrimeUnit D l hl) cg E) := by
  sorry

end Finite

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The common-stage inverse-image shift from the actual finite-stage representatives.
Source: blueprint common-stage coefficients (blueprint: def-zl-field-weil-shriek-shift-data). -/
instance fieldZlPullShift {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    (zlPull D l hl Ω f₀).CommShift ℤ :=
  @fieldCommonPullShift l _ Ω _ _ _ _ _ (zlFiberMap D f₀)
    (sfWeilPrimeInvertible D l hl X₀) (sfWeilPrimeInvertible D l hl Y₀)

/-- Common-stage compact-support shift, the composite of the open and proper adjunction
mates of normalized pullback shift. Source: SGA 4 XVII, sections 5--6
(blueprint: def-zl-field-weil-shriek-shift-data). -/
instance fieldZlShriekShift {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left) :
    (zlCommonStageShriek D l hl Ω f₀ c).CommShift ℤ :=
  letI : IsProper (zlCompactificationProper D f₀ c).left := inferInstanceAs (IsProper c.g)
  letI := (zlCommonStageOpenAdjunction D l hl Ω (zlCompactificationOpen D f₀ c))
    |>.leftAdjointCommShift ℤ
  letI := (zlCommonStageProperAdjunction D l hl Ω (zlCompactificationProper D f₀ c))
    |>.rightAdjointCommShift ℤ
  inferInstanceAs ((zlCommonStageOpenShriek D l hl Ω (zlCompactificationOpen D f₀ c) ⋙
    zlCommonStageProperPush D l hl Ω (zlCompactificationProper D f₀ c)).CommShift ℤ)

/-- The canonical finite-stage Frobenius shift. Source: Stacks 099N(5), blueprint
geometric Frobenius (blueprint: def-zl-field-weil-shriek-shift-data). -/
instance fieldWeilFrobeniusShift (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (sfWeilFrobeniusPullback D l hl X₀ E).CommShift ℤ :=
  @fieldRationalPullShift l _ E _ _ _ _ _ (D.geometricFrobenius X₀).hom
    (sfWeilPrimeInvertible D l hl X₀) (sfWeilPrimeInvertible D l hl X₀)

/-- The canonical common-stage Frobenius shift. Source: blueprint geometric Frobenius
(blueprint: def-zl-field-weil-shriek-shift-data). -/
instance fieldCommonWeilFrobeniusShift (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).CommShift ℤ :=
  @fieldCommonPullShift l _ Ω _ _ _ _ _ (D.geometricFrobenius X₀).hom
    (sfWeilPrimeInvertible D l hl X₀) (sfWeilPrimeInvertible D l hl X₀)

end WeilConjectures
