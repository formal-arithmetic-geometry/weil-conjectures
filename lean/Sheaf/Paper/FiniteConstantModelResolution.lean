/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.Paper.CompletedConstantSheafReduction
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Two-term resolutions of finite constant scalar models

Source: Bhatt--Scholze, Proposition 6.8.11(3), Lemma 6.8.2(1); Stacks Tags 093J,
093M (blueprint: lem-sfb-finite-constant-model-two-term-free-resolution).

The model functor first forms discrete constant modules, extends scalars by the map
sending a scalar to the constant continuous function, and applies the monoidal inverse
image from the point. Thus it is precisely B_T tensor over the discrete constant A,
not a tensor over the continuous coefficient ring on the point.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.FiniteConstantModel

variable (A : Type u) [CommRing A]

/-- The ordinary scalar action, as an integer-bilinear map on the lifted scalar ring.
Source: Stacks Tag 093J, constant modules
(blueprint: lem-sfb-finite-constant-model-two-term-free-resolution). -/
def scalarAction (P : ModuleCat.{u + 1} A) :
    AddCommGrpCat.of (ULift.{u + 1} A) ⊗ AddCommGrpCat.of P ⟶ AddCommGrpCat.of P :=
  AddCommGrpCat.ofHom (TensorProduct.lift (LinearMap.mk₂ ℤ
    (fun (a : ULift.{u + 1} A) (p : P) ↦ a.down • p)
    (fun _ _ _ ↦ add_smul _ _ _)
    (fun n a p ↦ by simp [mul_smul, Int.cast_smul_eq_zsmul])
    (fun _ _ _ ↦ smul_add _ _ _)
    (fun n a p ↦ by simp [smul_comm n a.down p]))).toAddMonoidHom

/-- The specified scalar action satisfies the internal module axioms.
Source: Stacks Tag 093J, constant modules
(blueprint: lem-sfb-finite-constant-model-two-term-free-resolution).
Proof: evaluate the unit equation on n tensor p and the associativity equation on
(a tensor b) tensor p. They become one_smul and mul_smul, respectively; integer
bilinearity extends these equalities to the whole tensor products. -/
theorem scalarAction_laws (P : ModuleCat.{u + 1} A) :
    MonObj.one (X := AddCommGrpCat.of (ULift.{u + 1} A)) ▷ AddCommGrpCat.of P ≫
        scalarAction A P = (λ_ (AddCommGrpCat.of P)).hom ∧
    MonObj.mul (X := AddCommGrpCat.of (ULift.{u + 1} A)) ▷ AddCommGrpCat.of P ≫
        scalarAction A P =
      (α_ _ _ _).hom ≫ AddCommGrpCat.of (ULift.{u + 1} A) ◁ scalarAction A P ≫
        scalarAction A P := by
  sorry

/-- The ordinary module, with its actual scalar action, as an internal abelian-group module.
Source: Stacks Tag 093J
(blueprint: lem-sfb-finite-constant-model-two-term-free-resolution). -/
instance scalarModule (P : ModuleCat.{u + 1} A) :
    ModObj (AddCommGrpCat.of (ULift.{u + 1} A)) (AddCommGrpCat.of P) :=
  ModObj.mk' _ (scalarAction A P) (scalarAction_laws A P).1 (scalarAction_laws A P).2

/-- Linearity is exactly compatibility with the specified internal action.
Source: Stacks Tag 093J
(blueprint: lem-sfb-finite-constant-model-two-term-free-resolution).
Proof: evaluate on a tensor p. Both sides are a times f(p), by f.map_smul;
the tensor universal property proves equality. -/
theorem scalarMap_linear {P Q : ModuleCat.{u + 1} A} (f : P ⟶ Q) :
    IsModHom (AddCommGrpCat.of (ULift.{u + 1} A))
      (AddCommGrpCat.ofHom f.hom.toAddMonoidHom) := by
  sorry

/-- The scalar module functor retains the underlying additive maps.
Source: Stacks Tag 093J
(blueprint: lem-sfb-finite-constant-model-two-term-free-resolution). -/
def scalarModules : ModuleCat.{u + 1} A ⥤ Mod Ab.{u + 1}
    (AddCommGrpCat.of (ULift.{u + 1} A)) where
  obj P := ⟨AddCommGrpCat.of P⟩
  map f :=
    { hom := AddCommGrpCat.ofHom f.hom.toAddMonoidHom
      isModHom := scalarMap_linear A f }

variable [TopologicalSpace A] [IsTopologicalRing A]

/-- Constant scalar functions, before sheafification.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-sfb-finite-constant-model-two-term-free-resolution). -/
def constantFunctions :
    (Functor.const Profinite.{u}ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶
      (Profinite.continuousCoefficientRingObj A).obj where
  app S := AddCommGrpCat.ofHom
    { toFun := fun a ↦ ULift.up (ContinuousMap.const S.unop a.down)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  naturality _ _ _ := rfl

/-- The canonical discrete-constant-to-continuous coefficient map, by sheafification.
Source: Bhatt--Scholze, Definition 6.8.1; Stacks Tag 093J
(blueprint: lem-sfb-finite-constant-model-two-term-free-resolution). -/
def scalarToContinuous :
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶ Profinite.continuousCoefficientRingObj A :=
  ((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv _ _).symm
    (constantFunctions A)

/-- The constant scalar map preserves the ring operations.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-sfb-finite-constant-model-two-term-free-resolution).
Proof: constant functions preserve one and multiplication sectionwise. The monoidal
sheafification adjunction transports these two equations to scalarToContinuous. -/
theorem scalarToContinuous_isMonHom : IsMonHom (scalarToContinuous A) := by
  sorry

attribute [instance] scalarToContinuous_isMonHom

/-- The constant scalar ring is commutative for the transported monoidal structure.
Source: Stacks Tag 093J
(blueprint: lem-sfb-finite-constant-model-two-term-free-resolution).
Proof: multiplication before sheafification is commutative, since A is commutative.
Sheafification is symmetric monoidal, so it transports that equality. -/
theorem constantScalars_commutative :
    IsCommMonObj ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A))) := by
  sorry

attribute [instance] constantScalars_commutative

/-- The canonical local model B_T tensor over discrete constant A with constant P.
The displayed composite also fixes its value on every scalar linear map.
Source: Bhatt--Scholze, Proposition 6.8.11(3), scalar extension construction
(blueprint: lem-sfb-finite-constant-model-two-term-free-resolution). -/
def modelFunctor (T : Scheme.{u}) : ModuleCat.{u + 1} A ⥤
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) T) :=
  scalarModules A ⋙
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod
      (AddCommGrpCat.of (ULift.{u + 1} A)) ⋙
    Mod.extendScalars (scalarToContinuous A) ⋙
    (upperStarFromPoint T).mapMod (Profinite.continuousCoefficientRingObj A)

/-- The finite scalar free module, with a harmless universe lift of its coordinates.
Source: Bhatt--Scholze, Proposition 6.8.11(3)
(blueprint: lem-sfb-finite-constant-model-two-term-free-resolution). -/
def freeScalars (n : ℕ) : ModuleCat.{u + 1} A :=
  ModuleCat.of A (Fin n → ULift.{u + 1} A)

end AlgebraicGeometry.ProEtale.FiniteConstantModel

namespace AlgebraicGeometry.ProEtale.FiniteConstantModel

universe uC vC

/-- A scalar short exact sequence, its specified scalar-extended short exact sequence,
and the augmented complex in degrees minus one and zero. The component equations
fix the differential and augmentation to the images of the original scalar maps.
Source: Bhatt--Scholze, Proposition 6.8.11(3)
(blueprint: lem-sfb-finite-constant-model-two-term-free-resolution). -/
def HasResolution {A : Type u} [CommRing A] {C : Type uC} [Category.{vC} C] [Abelian C]
    (F : ModuleCat.{u + 1} A ⥤ C) (free : ℕ → C) (P : ModuleCat.{u + 1} A)
    (rational : Bool) : Prop :=
  ∃ (a b : ℕ) (f : freeScalars A a ⟶ freeScalars A b)
      (g : freeScalars A b ⟶ P),
    (rational = true → a = 0) ∧ Function.Injective f.hom ∧
    Function.Exact f.hom g.hom ∧ Function.Surjective g.hom ∧
    Nonempty (F.obj (freeScalars A a) ≅ free a) ∧
    Nonempty (F.obj (freeScalars A b) ≅ free b) ∧
    (rational = true → Nonempty (F.obj P ≅ free b)) ∧
    ∃ h : F.map f ≫ F.map g = 0,
      (ShortComplex.mk (F.map f) (F.map g) h).ShortExact ∧
      ∃ (K : CochainComplex C ℤ)
        (e₁ : K.X (-1) ≅ F.obj (freeScalars A a))
        (e₀ : K.X 0 ≅ F.obj (freeScalars A b))
        (ε : K ⟶ (CochainComplex.singleFunctor C 0).obj (F.obj P)),
        (∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (K.X i)) ∧
        K.d (-1) 0 = e₁.hom ≫ F.map f ≫ e₀.inv ∧
        ε.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.obj P)).hom =
          e₀.hom ≫ F.map g ∧ QuasiIso ε

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]

/-- The continuous integral condensed ring with the specified extension absolute value.
Source: Bhatt--Scholze, Definition 6.8.1 and Lemma 6.8.2(1)
(blueprint: lem-sfb-finite-constant-model-two-term-free-resolution). -/
abbrev integralCoefficients :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Profinite.continuousCoefficientRingObj (Padic.coefficientExtensionIntegers l E)

/-- The continuous rational condensed ring with the specified extension absolute value.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-sfb-finite-constant-model-two-term-free-resolution). -/
abbrev rationalCoefficients :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Profinite.continuousCoefficientRingObj E

/-- Constant integral scalar modules extended to the actual pulled-back condensed ring.
Source: Bhatt--Scholze, Proposition 6.8.11(3)
(blueprint: lem-sfb-finite-constant-model-two-term-free-resolution). -/
def integralModel (T : Scheme.{u}) :
    ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E) ⥤
      Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (integralCoefficients l E) T) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  modelFunctor (Padic.coefficientExtensionIntegers l E) T

/-- Constant rational scalar modules extended to the actual pulled-back condensed ring.
Source: Bhatt--Scholze, Proposition 6.8.11(3), field case
(blueprint: lem-sfb-finite-constant-model-two-term-free-resolution). -/
def rationalModel (T : Scheme.{u}) :
    ModuleCat.{u + 1} E ⥤ Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (rationalCoefficients l E) T) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  modelFunctor E T

/-- Finite constant local models have length-one finite-free resolutions; over E the
negative-degree free term can be zero. No condition is placed on the scheme or on
scalar torsion, and all complexes are ordinary cochain complexes of module sheaves.

Source: Bhatt--Scholze, Proposition 6.8.11(3), with Lemma 6.8.2(1); Stacks 093J, 093M
(blueprint: lem-sfb-finite-constant-model-two-term-free-resolution).

Proof:
1. In the integral case take a finite presentation and its finitely generated kernel.
The kernel is torsion-free as a submodule of a finite free module over the domain O_E.
The DVR theorem lem-weil-l-adic-extension-integers-dvr and
lem-sc-dvr-fg-torsionfree-free make it finite free, giving the scalar short exact sequence.
2. In the field case a finite spanning set contains a basis; take a=0 and let the final
scalar map be that basis isomorphism, including the empty basis for the zero module.
3. By lem-weil-pbc-site-r-module-presheaf-sheafification-exact the constant sheaf
functor preserves this exact sequence, and also identifies finite scalar powers with
finite powers of the constant ring. The scalar map is constant continuous functions.
4. Relative tensor identifies B tensor A^n with B^n: send z tensor (x_i) to (zx_i),
and use (z_i) to sum z_i tensor e_i for its inverse. These maps identify the scalar
extended differentials with the given matrices, including n=0.
5. For integral coefficients, lem-weil-pbc-pid-noetherian-normal makes O_E Noetherian.
The canonical A-algebra comparison det-prop-sfb-qlbar-colimit-x-integral-limit identifies
B with the limit of the constant A/(pi^n). Its projections send constant scalars to
their residues, so lem-weil-pbc-completed-constant-sheaf-reduction (Stacks 093M)
preserves the constant short exact sequence under scalar extension. In the field case
the scalar basis isomorphism stays an isomorphism after both functors; no flatness
assertion for the discrete constant E is needed.
6. Form the two-term complex in degrees -1,0 with the specified differential and
augmentation. Exactness gives zero H^-1 and identifies H^0 with the final model by
that augmentation. Other cohomology vanishes, so precisely this augmentation is a
quasi-isomorphism. No completed derived category enters this argument. -/
theorem finite_constant_model_two_term_free_resolution
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :
    (∀ (P : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
      [Module.FinitePresentation (Padic.coefficientExtensionIntegers l E) P],
      HasResolution (integralModel l E T)
        (Mod.finiteFree (condensedRingObj (integralCoefficients l E) T)) P false) ∧
    (∀ (P : ModuleCat.{u + 1} E) [Module.FinitePresentation E P],
      HasResolution (rationalModel l E T)
        (Mod.finiteFree (condensedRingObj (rationalCoefficients l E) T)) P true) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteConstantModel
