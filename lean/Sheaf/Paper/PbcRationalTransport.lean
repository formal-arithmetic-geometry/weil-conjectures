/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.CategoryTheory.ScalarLocalization
public import Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Sheaf.Paper.PbcUniformCompleteTriangulated
public import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # Functorial transport to finite rational coefficients

Source: Weil blueprint, proper base change, order 1306
(blueprint: prop-weil-pbc-rational-transport).
The scalar-first tensor convention is identified with the source's Hom-first convention
by TensorProduct.comm. All functors and comparisons below use actual tensor maps.

## Main definitions

- `CategoryTheory.ScalarLocalization.transport`: tensor extension of a linear functor.
- `CategoryTheory.ScalarLocalization.transportNat`: componentwise tensor extension.
- `WeilConjectures.pbcRationalExtension`: extension on the completed rational categories.

## Main statements

- `CategoryTheory.ScalarLocalization.transport_exact`: generic exact tensor transport.
- `WeilConjectures.pbcRationalTransport`: exactness, scalar formulas and uniqueness.
- `WeilConjectures.pbcRationalExchange`: transport of the four supplied operations and exchange.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe r u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace CategoryTheory.ScalarLocalization

variable (R : Type r) [CommRing R] (p : R)
variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D]
variable (F : C ⥤ D) [F.Additive] [F.Linear R]

/-- The Hom map is extension of scalars of the supplied linear map.
Source: blueprint order 1306, proof step 1
(blueprint: prop-weil-pbc-rational-transport). -/
def transportHom (K L : C) :
    (Localization.Away p ⊗[R] (K ⟶ L)) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[R] (F.obj K ⟶ F.obj L)) :=
  (F.mapLinearMap R).baseChange (Localization.Away p)

/-- The tensor Hom maps preserve identities and composition.
Source: blueprint order 1306, proof steps 1--2
(blueprint: prop-weil-pbc-rational-transport).
Proof: the pure-tensor formula for baseChange sends a tensor a ⊗ f to a ⊗ F(f).
The composition formula reduces preservation of composition on pure tensors to that
of F and multiplication of scalars. Bilinearity extends it to finite sums. Identities
are tensors of the integral identities with one. -/
theorem transport_laws :
    (∀ K : C, transportHom R p F K K ((1 : Localization.Away p) ⊗ₜ[R] 𝟙 K) =
      (1 : Localization.Away p) ⊗ₜ[R] 𝟙 (F.obj K)) ∧
    (∀ (K L M : C) (f : Localization.Away p ⊗[R] (K ⟶ L))
        (g : Localization.Away p ⊗[R] (L ⟶ M)),
      transportHom R p F K M (composition R C p K L M g f) =
        composition R D p (F.obj K) (F.obj L) (F.obj M)
          (transportHom R p F L M g) (transportHom R p F K L f)) := by
  constructor
  · intro K
    simp [transportHom]
  · intro K L M f g
    induction g using TensorProduct.induction_on with
    | zero => simp
    | tmul b g =>
      induction f using TensorProduct.induction_on with
      | zero => simp
      | tmul a f => simp [transportHom, composition_tmul]
      | add f f' hf hf' => simp [map_add, hf, hf']
    | add g g' hg hg' => simp [map_add, hg, hg']

/-- The extension agrees on objects and sends a ⊗ f to a ⊗ F(f).
Source: blueprint order 1306, proof steps 1--2
(blueprint: prop-weil-pbc-rational-transport). -/
def transport : ScalarLocalization R C p ⥤ ScalarLocalization R D p where
  obj K := ⟨F.obj K.obj⟩
  map {K L} f := transportHom R p F K.obj L.obj f
  map_id K := (transport_laws R p F).1 K.obj
  map_comp {K L M} f g := (transport_laws R p F).2 K.obj L.obj M.obj f g

/-- Additivity of the scalar extension. Source: blueprint order 1306
(blueprint: prop-weil-pbc-rational-transport). -/
instance transportAdditive : (transport R p F).Additive where
  map_add {K L} {f g} := (transportHom R p F K.obj L.obj).map_add f g

/-- Localized-ring linearity of the scalar extension. Source: blueprint order 1306
(blueprint: prop-weil-pbc-rational-transport). -/
instance transportLinear : (transport R p F).Linear (Localization.Away p) where
  map_smul {K L} f a := (transportHom R p F K.obj L.obj).map_smul a f

/-- Uniqueness among linear functors agreeing on integral objects and morphisms.
Source: blueprint order 1306, proof step 2
(blueprint: prop-weil-pbc-rational-transport).
Proof: a pure tensor is a times the integral tensor with one. Linearity forces its
image; additivity forces the image of every finite sum. The object equalities and
these Hom equalities give equality of functors by functor extensionality. -/
theorem transport_unique (H : ScalarLocalization R C p ⥤ ScalarLocalization R D p)
    [H.Additive] [H.Linear (Localization.Away p)]
    (hobj : ∀ K : C, H.obj ⟨K⟩ = ⟨F.obj K⟩)
    (hmap : ∀ (K L : C) (f : K ⟶ L),
      HEq (H.map ((1 : Localization.Away p) ⊗ₜ[R] f :
        ScalarLocalization.mk (R := R) (p := p) K ⟶ ⟨L⟩))
        ((1 : Localization.Away p) ⊗ₜ[R] F.map f)) :
    H = transport R p F := by
  refine Functor.ext (fun K ↦ hobj K.obj) ?_
  intro K L f
  change H.map f = eqToHom (hobj K.obj) ≫
    (transportHom R p F K.obj L.obj) f ≫ eqToHom (hobj L.obj).symm
  have hi (g : K.obj ⟶ L.obj) :
      H.map ((1 : Localization.Away p) ⊗ₜ[R] g : K ⟶ L) =
        eqToHom (hobj K.obj) ≫
          ((1 : Localization.Away p) ⊗ₜ[R] F.map g) ≫ eqToHom (hobj L.obj).symm := by
    exact (conj_eqToHom_iff_heq _ _ (hobj K.obj) (hobj L.obj)).mpr
      (hmap K.obj L.obj g)
  induction f using TensorProduct.induction_on with
  | zero =>
    change H.map (0 : K ⟶ L) = _
    simp only [Functor.map_zero, map_zero, Limits.zero_comp, Limits.comp_zero]
  | tmul a f =>
    calc
      H.map (a ⊗ₜ[R] f : K ⟶ L) =
          H.map (a • ((1 : Localization.Away p) ⊗ₜ[R] f) : K ⟶ L) := by
            congr 1
            simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      _ = a • H.map ((1 : Localization.Away p) ⊗ₜ[R] f : K ⟶ L) := H.map_smul a _
      _ = _ := by
        rw [hi, ← Linear.comp_smul, ← Linear.smul_comp]
        dsimp only [transportHom]
        rw [LinearMap.baseChange_tmul]
        congr 2
        change a • ((1 : Localization.Away p) ⊗ₜ[R] F.map f) = a ⊗ₜ[R] F.map f
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add f g hf hg =>
    change H.map (f + g : K ⟶ L) = _
    rw [H.map_add, map_add]
    erw [Preadditive.add_comp, Preadditive.comp_add]
    exact congrArg₂ (· + ·) hf hg


variable {F} {G : C ⥤ D} [G.Additive] [G.Linear R]

/-- Naturality after scalar extension, for the prescribed components.
Source: blueprint order 1306, proof step 3
(blueprint: prop-weil-pbc-rational-transport).
Proof: on a pure tensor, both sides are the integral naturality equation tensored
with its scalar. Additivity proves the equation for a sum of pure tensors. -/
theorem transportNat_naturality (η : F ⟶ G) (K L : ScalarLocalization R C p)
    (f : K ⟶ L) :
    (transport R p F).map f ≫ ((1 : Localization.Away p) ⊗ₜ[R] η.app L.obj) =
      ((1 : Localization.Away p) ⊗ₜ[R] η.app K.obj) ≫ (transport R p G).map f := by
  change composition R D p _ _ _ ((1 : Localization.Away p) ⊗ₜ[R] η.app L.obj)
      (transportHom R p F _ _ f) =
    composition R D p _ _ _ (transportHom R p G _ _ f)
      ((1 : Localization.Away p) ⊗ₜ[R] η.app K.obj)
  induction f using TensorProduct.induction_on with
  | zero => simp
  | tmul a f => simp [transportHom, composition_tmul, η.naturality]
  | add f g hf hg => simp [map_add, hf, hg]


/-- The unique extension of a natural transformation, with its integral components.
Source: blueprint order 1306, proof step 3
(blueprint: prop-weil-pbc-rational-transport). -/
def transportNat (η : F ⟶ G) : transport R p F ⟶ transport R p G where
  app K := (1 : Localization.Away p) ⊗ₜ[R] η.app K.obj
  naturality K L f := transportNat_naturality R p η K L f

/-- The prescribed components determine the extension uniquely, including zero objects.
Source: blueprint order 1306, proof step 3
(blueprint: prop-weil-pbc-rational-transport).
Proof: every localized object is an integral object. Equality of all prescribed
components therefore gives equality of natural transformations by extensionality. -/
theorem transportNat_unique (η : F ⟶ G) :
    ∃! e : transport R p F ⟶ transport R p G,
      ∀ K : C, e.app ⟨K⟩ = (1 : Localization.Away p) ⊗ₜ[R] η.app K := by
  refine ⟨transportNat R p η, fun K ↦ rfl, ?_⟩
  intro e he
  apply NatTrans.ext
  funext K
  exact he K.obj


/-- Exactness for the induced shift and isomorphic-image triangulation, with the
specified integral shift comparison tensored with one. The structures are the witnesses
of `exists_triangulated_scalarLocalization`, including its shift normalization and its
characterization of distinguished triangles, rather than arbitrary triangulations.
Source: blueprint order 1306, proof step 4; Stacks Project, Tag 05R6
(blueprint: prop-weil-pbc-rational-transport). -/
def HasExactTransport
    (R : Type r) [CommRing R]
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D]
    [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [IsTriangulated C] [(shiftFunctor C (1 : ℤ)).Linear R]
    [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [IsTriangulated D] [(shiftFunctor D (1 : ℤ)).Linear R]
    (p : R) (F : C ⥤ D) [F.Additive] [F.Linear R] [F.CommShift ℤ] : Prop := by
  let dataC := exists_triangulated_scalarLocalization R C p
  let dataD := exists_triangulated_scalarLocalization R D p
  letI : HasZeroObject (ScalarLocalization R C p) := dataC.choose
  letI : HasZeroObject (ScalarLocalization R D p) := dataD.choose
  letI : HasShift (ScalarLocalization R C p) ℤ := dataC.choose_spec.choose
  letI : HasShift (ScalarLocalization R D p) ℤ := dataD.choose_spec.choose
  letI : ∀ n : ℤ, (shiftFunctor (ScalarLocalization R C p) n).Additive :=
    dataC.choose_spec.choose_spec.2.choose
  letI : ∀ n : ℤ, (shiftFunctor (ScalarLocalization R D p) n).Additive :=
    dataD.choose_spec.choose_spec.2.choose
  letI : Pretriangulated (ScalarLocalization R C p) :=
    dataC.choose_spec.choose_spec.2.choose_spec.choose_spec.2.choose
  letI : Pretriangulated (ScalarLocalization R D p) :=
    dataD.choose_spec.choose_spec.2.choose_spec.choose_spec.2.choose
  exact ∃ s : (transport R p F).CommShift ℤ,
    (fun [_shiftComparison : (transport R p F).CommShift ℤ] ↦
      (transport R p F).IsTriangulated ∧
        ∀ K : C,
          HEq (((transport R p F).commShiftIso (1 : ℤ)).hom.app ⟨K⟩)
            ((1 : Localization.Away p) ⊗ₜ[R] (F.commShiftIso (1 : ℤ)).hom.app K))
      (_shiftComparison := s)

/-- Generic exact transport to the raw scalar localization.
Source: blueprint order 1306, proof steps 1--4
(blueprint: prop-weil-pbc-rational-transport).
Proof: `transport` is defined on objects and on localized Hom modules by
`LinearMap.baseChange`. The tensor formula gives preservation of identities and
composition, while additivity and localized linearity follow from the linear map.
The prescribed shift comparison is obtained by tensoring the integral comparison;
exactness follows because every distinguished localized triangle is isomorphic to
the localization of an integral distinguished triangle. The uniqueness clause is
`transport_unique`. For a second functor and natural transformation, tensor each
component with one; `transportNat_unique` gives existence and uniqueness. -/
theorem transport_exact
    (R : Type r) [CommRing R]
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D]
    [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [IsTriangulated C] [(shiftFunctor C (1 : ℤ)).Linear R]
    [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [IsTriangulated D] [(shiftFunctor D (1 : ℤ)).Linear R]
    (p : R) (F : C ⥤ D) [F.Additive] [F.Linear R]
    [F.CommShift ℤ] [F.IsTriangulated] :
    (transport R p F).Additive ∧
    (transport R p F).Linear (Localization.Away p) ∧
    (∀ (K L : C) (f : K ⟶ L) (a : Localization.Away p),
      (transport R p F).map (a ⊗ₜ[R] f :
        ScalarLocalization.mk (R := R) (p := p) K ⟶ ⟨L⟩) = a ⊗ₜ[R] F.map f) ∧
    HasExactTransport R p F ∧
    (∀ (H : ScalarLocalization R C p ⥤ ScalarLocalization R D p)
        [H.Additive] [H.Linear (Localization.Away p)],
      (∀ K : C, H.obj ⟨K⟩ = ⟨F.obj K⟩) →
      (∀ (K L : C) (f : K ⟶ L),
        HEq (H.map ((1 : Localization.Away p) ⊗ₜ[R] f :
          ScalarLocalization.mk (R := R) (p := p) K ⟶ ⟨L⟩))
          ((1 : Localization.Away p) ⊗ₜ[R] F.map f)) →
      H = transport R p F) ∧
    (∀ (G : C ⥤ D) [G.Additive] [G.Linear R]
        [G.CommShift ℤ] [G.IsTriangulated] (η : F ⟶ G),
      ∃! e : transport R p F ⟶ transport R p G,
        ∀ K : C, e.app ⟨K⟩ = (1 : Localization.Away p) ⊗ₜ[R] η.app K) := by
  sorry

end CategoryTheory.ScalarLocalization

namespace AlgebraicGeometry.Scheme

set_option linter.defProp false in
/-- Inherited integral triangulation. Source: blueprint order 1305
(blueprint: prop-weil-pbc-rational-transport). -/
abbrev pbcIntegralTriangulated (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) [IsNoetherian T]
    (hDim : ∃ d : ℕ, topologicalKrullDim T ≤ d)
    (hInv : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) :
    ObjectProperty.IsTriangulated
      (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) :=
  (pbcIntegralUniformComplete_isTriangulated l E T hDim hInv).2

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (T : Scheme.{u}) [IsNoetherian T]
  (hDim : ∃ d : ℕ, topologicalKrullDim T ≤ d)
  (hInv : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

/-- The inherited integral zero object. Source: blueprint order 1305
(blueprint: prop-weil-pbc-rational-transport). -/
instance pbcIntegralZero : HasZeroObject (PbcIntegralCategory l E T hDim hInv) :=
  letI := pbcIntegralTriangulated l E T hDim hInv
  inferInstance

/-- The inherited integral integer shifts. Source: blueprint order 1305
(blueprint: prop-weil-pbc-rational-transport). -/
instance pbcIntegralShift : HasShift (PbcIntegralCategory l E T hDim hInv) ℤ :=
  letI := pbcIntegralTriangulated l E T hDim hInv
  inferInstance

/-- Additivity of the inherited integral shifts. Source: blueprint order 1305
(blueprint: prop-weil-pbc-rational-transport). -/
instance pbcIntegralShiftAdditive (n : ℤ) :
    (shiftFunctor (PbcIntegralCategory l E T hDim hInv) n).Additive :=
  letI := pbcIntegralTriangulated l E T hDim hInv
  inferInstance

/-- The inherited integral distinguished triangles. Source: blueprint order 1305
(blueprint: prop-weil-pbc-rational-transport). -/
instance pbcIntegralPretriangulated :
    Pretriangulated (PbcIntegralCategory l E T hDim hInv) :=
  letI := pbcIntegralTriangulated l E T hDim hInv
  inferInstance

/-- Integral octahedra are inherited from the ambient derived category.
Source: blueprint order 1305 (blueprint: prop-weil-pbc-rational-transport). -/
instance pbcIntegralIsTriangulated :
    IsTriangulated (PbcIntegralCategory l E T hDim hInv) :=
  letI := pbcIntegralTriangulated l E T hDim hInv
  inferInstance

set_option linter.defProp false in
/-- The existing scalar-localization theorem, with its tensor-induced shift and precisely
its isomorphic image triangles. Source: blueprint order 1305
(blueprint: prop-weil-pbc-rational-transport). -/
abbrev pbcRationalTriangulationData :=
  letI := pbcIntegralTriangulated l E T hDim hInv
  ScalarLocalization.exists_triangulated_scalarLocalization
    (PbcIntegralRing l E)
    (PbcIntegralCategory l E T hDim hInv)
    (pbcUniformizer l E)

/-- The inherited zero object. Source: blueprint order 1305
(blueprint: prop-weil-pbc-rational-transport). -/
instance pbcRationalZero : HasZeroObject (PbcRationalDerivedCategory l E T hDim hInv) :=
  (pbcRationalTriangulationData l E T hDim hInv).choose

/-- The tensor-induced integer shift. Source: blueprint order 1305
(blueprint: prop-weil-pbc-rational-transport). -/
instance pbcRationalShift : HasShift (PbcRationalDerivedCategory l E T hDim hInv) ℤ :=
  (pbcRationalTriangulationData l E T hDim hInv).choose_spec.choose

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The lifted integer ring has the same uniformizer localization. This is the canonical
fraction map, transported through ULift.ringEquiv, followed by the recorded fraction map
for the original integer ring. Source: blueprint order 1306, proof step 1
(blueprint: prop-weil-pbc-rational-transport). -/
def pbcRationalCoefficientEquiv : Localization.Away (pbcUniformizer l E) ≃+* E :=
  (IsLocalization.ringEquivOfRingEquiv
    (R := PbcIntegralRing l E) (P := Padic.coefficientExtensionIntegers l E)
    (M := Submonoid.powers (pbcUniformizer l E))
    (T := Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
    (Localization.Away (pbcUniformizer l E))
    (Localization.Away (Padic.coefficientExtensionUniformizer l E))
    (ULift.ringEquiv : PbcIntegralRing l E ≃+* Padic.coefficientExtensionIntegers l E)
    (Submonoid.map_powers _ _)).trans
      (Padic.coefficientExtension_localization_uniformizer.{u, u} l E).2.choose.toRingEquiv

variable (T : Scheme.{u}) [IsNoetherian T]
variable (hDim : ∃ d : ℕ, topologicalKrullDim T ≤ d)
variable (hInv : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

/-- The rational Hom modules carry the actual E-action by the canonical fraction map.
Source: blueprint order 1306, proof step 1
(blueprint: prop-weil-pbc-rational-transport). -/
instance pbcRationalLinear : Linear E (PbcRationalDerivedCategory l E T hDim hInv) where
  homModule K L := Module.compHom (K ⟶ L) (pbcRationalCoefficientEquiv l E).symm.toRingHom
  smul_comp K L M a f g :=
    Linear.smul_comp K L M ((pbcRationalCoefficientEquiv l E).symm a) f g
  comp_smul K L M f a g :=
    Linear.comp_smul K L M f ((pbcRationalCoefficientEquiv l E).symm a) g

end AlgebraicGeometry.Scheme

namespace WeilConjectures

open AlgebraicGeometry AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (X Y : Scheme.{u}) [IsNoetherian X] [IsNoetherian Y]
variable (hX : ∃ d : ℕ, topologicalKrullDim X ≤ d)
variable (iX : ∀ t : X, IsUnit (l : X.presheaf.stalk t))
variable (hY : ∃ d : ℕ, topologicalKrullDim Y ≤ d)
variable (iY : ∀ t : Y, IsUnit (l : Y.presheaf.stalk t))
variable (F : PbcIntegralCategory l E X hX iX ⥤
  PbcIntegralCategory l E Y hY iY)
variable [F.Additive] [F.Linear (PbcIntegralRing l E)]

/-- Scalar extension of the supplied integral functor on the actual raw rational categories.
Source: blueprint order 1306, proof steps 1--2
(blueprint: prop-weil-pbc-rational-transport). -/
abbrev pbcRationalExtension : PbcRationalDerivedCategory l E X hX iX ⥤
    PbcRationalDerivedCategory l E Y hY iY :=
  ScalarLocalization.transport (PbcIntegralRing l E)
    (pbcUniformizer l E) F

/-- The prescribed localized shift comparison and preservation of distinguished triangles.
The HEq is needed only because the inherited shift has wrapped objects: its component is
literally the integral comparison tensored with one, under the induced shift identification.
Source: blueprint order 1306, proof step 4
(blueprint: prop-weil-pbc-rational-transport). -/
def HasExactPbcRationalTransport [F.CommShift ℤ] : Prop := by
  let dataX := (pbcRationalTriangulationData l E X hX iX).choose_spec.choose_spec.2
  let dataY := (pbcRationalTriangulationData l E Y hY iY).choose_spec.choose_spec.2
  letI : ∀ n : ℤ,
      (shiftFunctor (PbcRationalDerivedCategory l E X hX iX) n).Additive :=
    dataX.choose
  letI : ∀ n : ℤ,
      (shiftFunctor (PbcRationalDerivedCategory l E Y hY iY) n).Additive :=
    dataY.choose
  letI : Pretriangulated (PbcRationalDerivedCategory l E X hX iX) :=
    dataX.choose_spec.choose_spec.2.choose
  letI : Pretriangulated (PbcRationalDerivedCategory l E Y hY iY) :=
    dataY.choose_spec.choose_spec.2.choose
  exact ∃ s : (pbcRationalExtension l E X Y hX iX hY iY F).CommShift ℤ,
    (fun [_shiftComparison : (pbcRationalExtension l E X Y hX iX hY iY F).CommShift ℤ] ↦
      (pbcRationalExtension l E X Y hX iX hY iY F).IsTriangulated ∧
        ∀ K : PbcIntegralCategory l E X hX iX,
          HEq (((pbcRationalExtension l E X Y hX iX hY iY F).commShiftIso (1 : ℤ)).hom.app
            (ScalarLocalization.mk K))
            ((1 : Localization.Away (pbcUniformizer l E)) ⊗ₜ[
              PbcIntegralRing l E] (F.commShiftIso (1 : ℤ)).hom.app K))
      (_shiftComparison := s)

/-- Unique E-linear exact extension and extension of every integral natural transformation.
Source: blueprint proper base change, order 1306
(blueprint: prop-weil-pbc-rational-transport).

Proof, following all five steps of the node:
1. The extension has unchanged objects and its Hom map is baseChange of F.mapLinearMap.
The tensor balancing relation is respected by the supplied integral linearity.
2. On pure tensors functoriality follows from composition_tmul and F.map_comp, then from
bilinearity on finite sums. The identity is tensored with one. Every localized-ring-linear
extension agreeing on integral maps must send a ⊗ f to a ⊗ F(f); tensors generate Hom.
The canonical coefficient equivalence transfers this to E-linear uniqueness.
3. Tensor the components of the supplied natural transformation with one. Naturality
on a ⊗ f is its integral naturality equation tensored with a. All objects are integral,
so these components determine the transformation uniquely.
4. Localize the integral shift isomorphism and its inverse componentwise. The prescribed
comparison is their tensor with one. By lem-weil-linear-scalar-localization-triangulated,
every rational distinguished triangle is isomorphic to a localized integral triangle.
Its image is the localization of the distinguished F-image, hence distinguished.
5. Apply this result to each of the four supplied operations. Their composites send
pure tensors to the composite integral map tensored with the same scalar. Thus the
specified exchange has precisely the componentwise extension asserted separately below. -/
theorem pbcRationalTransport [F.CommShift ℤ] [F.IsTriangulated] :
    (pbcRationalExtension l E X Y hX iX hY iY F).Additive ∧
    (pbcRationalExtension l E X Y hX iX hY iY F).Linear E ∧
    (∀ (K L : PbcIntegralCategory l E X hX iX) (f : K ⟶ L)
        (a : Localization.Away (pbcUniformizer l E)),
      HEq ((pbcRationalExtension l E X Y hX iX hY iY F).map
        (a • (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map f))
        (a ⊗ₜ[PbcIntegralRing l E] F.map f)) ∧
    HasExactPbcRationalTransport l E X Y hX iX hY iY F ∧
    (∀ (H : PbcRationalDerivedCategory l E X hX iX ⥤ PbcRationalDerivedCategory l E Y hY iY)
        [H.Additive] [H.Linear E],
      (∀ K : PbcIntegralCategory l E X hX iX,
        H.obj ⟨K⟩ = ⟨F.obj K⟩) →
      (∀ (K L : PbcIntegralCategory l E X hX iX) (f : K ⟶ L),
        HEq (H.map
          ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map f))
          ((1 : Localization.Away (pbcUniformizer l E)) ⊗ₜ[
            PbcIntegralRing l E] F.map f)) →
      H = pbcRationalExtension l E X Y hX iX hY iY F) ∧
    (∀ (G : PbcIntegralCategory l E X hX iX ⥤
        PbcIntegralCategory l E Y hY iY)
        [G.Additive] [G.Linear (PbcIntegralRing l E)]
        [G.CommShift ℤ] [G.IsTriangulated] (η : F ⟶ G),
      ∃! e : pbcRationalExtension l E X Y hX iX hY iY F ⟶
          pbcRationalExtension l E X Y hX iX hY iY G,
        ∀ K : PbcIntegralCategory l E X hX iX,
          HEq (e.app ⟨K⟩) ((1 : Localization.Away (pbcUniformizer l E)) ⊗ₜ[
            PbcIntegralRing l E] η.app K)) := by
  sorry

variable (X' Y' : Scheme.{u}) [IsNoetherian X'] [IsNoetherian Y']
variable (hX' : ∃ d : ℕ, topologicalKrullDim X' ≤ d)
variable (iX' : ∀ t : X', IsUnit (l : X'.presheaf.stalk t))
variable (hY' : ∃ d : ℕ, topologicalKrullDim Y' ≤ d)
variable (iY' : ∀ t : Y', IsUnit (l : Y'.presheaf.stalk t))

/-- The four supplied exact integral operations and their specified exchange transport to
rational coefficients, with the actual integral exchange components tensored with one.
No preservation assertion for arbitrary scheme morphisms is made.
Source: blueprint proper base change, order 1306, final paragraph
(blueprint: prop-weil-pbc-rational-transport).
Proof: apply pbcRationalTransport to the four supplied operations. The two localized
composites agree on objects and pure tensors with the localization of each integral
composite. Tensor the given exchange components with one; its naturality equation on
pure tensors is the integral naturality equation tensored with their scalar, then
extend by additivity. Components determine the transformation uniquely since every
rational object is an integral object. These are proof steps 3--5 of the node. -/
theorem pbcRationalExchange
    (Rf : PbcIntegralCategory l E X hX iX ⥤
      PbcIntegralCategory l E Y hY iY)
    (Rf' : PbcIntegralCategory l E X' hX' iX' ⥤
      PbcIntegralCategory l E Y' hY' iY')
    (Lg : PbcIntegralCategory l E Y hY iY ⥤
      PbcIntegralCategory l E Y' hY' iY')
    (Lg' : PbcIntegralCategory l E X hX iX ⥤
      PbcIntegralCategory l E X' hX' iX')
    [Rf.Additive] [Rf.Linear (PbcIntegralRing l E)]
    [Rf.CommShift ℤ] [Rf.IsTriangulated]
    [Rf'.Additive] [Rf'.Linear (PbcIntegralRing l E)]
    [Rf'.CommShift ℤ] [Rf'.IsTriangulated]
    [Lg.Additive] [Lg.Linear (PbcIntegralRing l E)]
    [Lg.CommShift ℤ] [Lg.IsTriangulated]
    [Lg'.Additive] [Lg'.Linear (PbcIntegralRing l E)]
    [Lg'.CommShift ℤ] [Lg'.IsTriangulated]
    (Ex : Rf ⋙ Lg ⟶ Lg' ⋙ Rf') :
    HasExactPbcRationalTransport l E X Y hX iX hY iY Rf ∧
    HasExactPbcRationalTransport l E X' Y' hX' iX' hY' iY' Rf' ∧
    HasExactPbcRationalTransport l E Y Y' hY iY hY' iY' Lg ∧
    HasExactPbcRationalTransport l E X X' hX iX hX' iX' Lg' ∧
    ∃! e : (pbcRationalExtension l E X Y hX iX hY iY Rf) ⋙
          pbcRationalExtension l E Y Y' hY iY hY' iY' Lg ⟶
        (pbcRationalExtension l E X X' hX iX hX' iX' Lg') ⋙
          pbcRationalExtension l E X' Y' hX' iX' hY' iY' Rf',
      ∀ K : PbcIntegralCategory l E X hX iX,
        HEq (e.app ⟨K⟩) ((1 : Localization.Away (pbcUniformizer l E)) ⊗ₜ[
          PbcIntegralRing l E] Ex.app K) := by
  sorry

end WeilConjectures
