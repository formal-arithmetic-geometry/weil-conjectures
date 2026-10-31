/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeCompletedScalarComparison
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars

/-! # Trace pairing for completed finite coefficient extensions

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-field-extension/
 sk-lem-sp-field-extension-towers.proof.md`, paragraph (1), Tags 0BIL and 04TT
(blueprint: lem-route-field-extension-trace-pairing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe t u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace WeilConjectures

/-- The completed base coefficient ring sheaf R. Source: the field-extension-towers
proof, paragraph (1) (blueprint: lem-route-field-extension-trace-pairing). -/
abbrev FieldExtensionTraceR (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) :=
  completedIntegralCommRingSheafUnrestricted l E T

/-- The completed extension coefficient ring sheaf S. Source: the field-extension-towers
proof, paragraph (1) (blueprint: lem-route-field-extension-trace-pairing). -/
abbrev FieldExtensionTraceS (l : ℕ) [Fact l.Prime] (F : Type u) [Field F]
    [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F] (T : Scheme.{t}) :=
  completedIntegralCommRingSheafUnrestricted l F T

/-- Sheaves of R-modules on the small pro-etale site. Source: Stacks, Sections 03EK/04TT
(blueprint: lem-route-field-extension-trace-pairing). -/
abbrev FieldExtensionTraceMod (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) :=
  SheafOfModules.{max u (t + 1)} ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat RingCat)).obj (FieldExtensionTraceR l E T))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (F : Type u) [Field F] [Algebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] F] (ι : E →ₐ[ℚ_[l]] F) (T : Scheme.{t})

/-- R itself as an R-module. Source: Stacks, Section 04TT
(blueprint: lem-route-field-extension-trace-pairing). -/
abbrev FieldExtensionTraceUnit : FieldExtensionTraceMod l E T :=
  SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat RingCat)).obj (FieldExtensionTraceR l E T))

/-- S_R is the restriction of the unit S-module along the canonical completed
coefficient map induced by ι. Source: field-extension-towers, paragraph (1)
(blueprint: lem-route-field-extension-trace-pairing). -/
abbrev FieldExtensionTraceSource : FieldExtensionTraceMod l E T :=
  (SheafOfModules.restrictScalars ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat RingCat)).map (completedCoefficientMap l E F ι T))).obj
    (SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat RingCat)).obj (FieldExtensionTraceS l F T)))

/-- The actual internal Hom_R(S_R,M), whose local sections are maps on slices.
Source: Stacks, Section 04TT (blueprint: lem-route-field-extension-trace-pairing). -/
abbrev FieldExtensionTraceHom (M : FieldExtensionTraceMod l E T) :=
  SheafOfModules.homObj (R := FieldExtensionTraceR l E T)
    (FieldExtensionTraceSource l E F ι T) M

/-- The sheaf tensor S tensor_R M, formed by sheafifying sectionwise extension of
scalars, with its canonical S-action. Source: Stacks, Section 03EK
(blueprint: lem-route-field-extension-trace-pairing). -/
abbrev FieldExtensionTraceTensor (M : FieldExtensionTraceMod l E T) :=
  (completedOrdinaryScalarExtension l E F ι T).obj M

/-- The underlying R-module of the sheaf tensor S tensor_R M. Source: Stacks,
Section 03EK (blueprint: lem-route-field-extension-trace-pairing). -/
abbrev FieldExtensionTraceTensorR (M : FieldExtensionTraceMod l E T) :=
  (SheafOfModules.restrictScalars ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat RingCat)).map (completedCoefficientMap l E F ι T))).obj
      (FieldExtensionTraceTensor l E F ι T M)

open scoped ChangeOfRings

/-- The local elementary tensor, using the sheafification unit, rather than an
identification of tensor sections with sectionwise tensors. Source: Stacks, Section 03EK
(blueprint: lem-route-field-extension-trace-pairing). -/
def fieldExtensionTracePure (M : FieldExtensionTraceMod l E T) (V : T.ProEtᵒᵖ)
    (s : (FieldExtensionTraceS l F T).obj.obj V) (m : M.val.obj V) :
    (FieldExtensionTraceTensor l E F ι T M).val.obj V :=
  completedScalarTensorSection l E F ι T M V s m

/-- Evaluation of a local internal-Hom section on its identity slice. Restrictions of
this evaluation cover every slice. Source: Stacks, Section 04TT
(blueprint: lem-route-field-extension-trace-pairing). -/
def fieldExtensionTraceEval (M : FieldExtensionTraceMod l E T) (V : T.ProEtᵒᵖ)
    (h : (FieldExtensionTraceHom l E F ι T M).val.obj V)
    (s : (FieldExtensionTraceS l F T).obj.obj V) : M.val.obj V :=
  (h.app (op (Over.mk (𝟙 V.unop)))) s

/-- A dual generator, its multiplication pairing, and the natural S-linear tensor-Hom
isomorphisms. Every endpoint is the actual completed coefficient sheaf, tensor or internal
Hom. S-linearity of Hom is expressed with its source-multiplication action
(a h)(t)=h(ta). Source: field-extension-towers, paragraph (1), Stacks 03EK/04TT
(blueprint: lem-route-field-extension-trace-pairing). -/
structure FieldExtensionTracePairingData where
  theta : (FieldExtensionTraceHom l E F ι T (FieldExtensionTraceUnit l E T)).sections
  generator : FieldExtensionTraceSource l E F ι T ≅
    FieldExtensionTraceHom l E F ι T (FieldExtensionTraceUnit l E T)
  generator_formula : ∀ (V : T.ProEtᵒᵖ) (s t : (FieldExtensionTraceS l F T).obj.obj V),
    fieldExtensionTraceEval l E F ι T (FieldExtensionTraceUnit l E T) V
      (generator.hom.val.app V s) t =
    (SheafOfModules.homObjSectionsEquiv
      (FieldExtensionTraceSource l E F ι T) (FieldExtensionTraceUnit l E T) theta).val.app V (s * t)
  pairing : ∀ (V : T.ProEtᵒᵖ), (FieldExtensionTraceS l F T).obj.obj V →
    (FieldExtensionTraceS l F T).obj.obj V → (FieldExtensionTraceR l E T).obj.obj V
  pairing_formula : ∀ (V : T.ProEtᵒᵖ) (s t : (FieldExtensionTraceS l F T).obj.obj V),
    pairing V s t = (SheafOfModules.homObjSectionsEquiv
      (FieldExtensionTraceSource l E F ι T) (FieldExtensionTraceUnit l E T) theta).val.app V (s * t)
  pairing_adjoint : ∀ (V : T.ProEtᵒᵖ) (s t : (FieldExtensionTraceS l F T).obj.obj V),
    fieldExtensionTraceEval l E F ι T (FieldExtensionTraceUnit l E T) V
      (generator.hom.val.app V s) t = pairing V s t
  phi : ∀ M : FieldExtensionTraceMod l E T,
    FieldExtensionTraceTensorR l E F ι T M ≅ FieldExtensionTraceHom l E F ι T M
  phi_formula : ∀ (M : FieldExtensionTraceMod l E T) (V : T.ProEtᵒᵖ)
    (s t : (FieldExtensionTraceS l F T).obj.obj V) (m : M.val.obj V),
    fieldExtensionTraceEval l E F ι T M V
      ((phi M).hom.val.app V (fieldExtensionTracePure l E F ι T M V s m)) t =
        (SheafOfModules.homObjSectionsEquiv
          (FieldExtensionTraceSource l E F ι T)
          (FieldExtensionTraceUnit l E T) theta).val.app V (s * t) • m
  phi_s_linear : ∀ (M : FieldExtensionTraceMod l E T) (V : T.ProEtᵒᵖ)
    (a t : (FieldExtensionTraceS l F T).obj.obj V)
    (x : (FieldExtensionTraceTensor l E F ι T M).val.obj V),
    fieldExtensionTraceEval l E F ι T M V ((phi M).hom.val.app V (a • x)) t =
      fieldExtensionTraceEval l E F ι T M V ((phi M).hom.val.app V x) (t * a)
  natural : ∀ (M N : FieldExtensionTraceMod l E T) (f : M ⟶ N),
    (phi M).hom ≫ SheafOfModules.homObjMap
      (R := FieldExtensionTraceR l E T)
      (M := FieldExtensionTraceSource l E F ι T) (N := M)
      (M' := FieldExtensionTraceSource l E F ι T) (N' := N) (𝟙 _) f =
      (SheafOfModules.restrictScalars ((sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat RingCat)).map (completedCoefficientMap l E F ι T))).map
          ((completedOrdinaryScalarExtension l E F ι T).map f) ≫
            (phi N).hom


/-- A chosen integral dual generator gives completed scalar coinduction.
Source: Stacks Project, Tags 0BIL, 0AUW and 04TT; the finite-free scalar-extension
and chosen dual-generator argument in `sk-lem-sp-field-extension-towers`
(blueprint: lem-route-field-extension-trace-pairing).

Proof, following the eight steps of the node:
1. Choose an integral basis of O_F over O_E using the integral-basis lemma. Clearing
   denominators and scaling by powers of l makes it an E-basis of F; O_F is a DVR.
2. The characteristic-zero trace-dual basis identifies Hom_{O_E}(O_F,O_E) with
   the lattice spanned by the trace-dual basis, with the source-multiplication action.
3. This lattice is finite torsion-free over O_F. DVR freeness and a fraction-field
   relation between any two basis members show its rank is one. Choose a generator;
   the resulting multiplication-pairing matrix has an integral inverse.
4. The adic basis-limit lemma extends the basis and both inverse matrices to the
   prescribed completed sheaves. Multiplication constants agree at every finite
   quotient, hence in the limit, including positive arbitrary ramification index.
5. Source multiplication makes the generator map S-linear, and its evaluation is
   precisely the adjoint of b_theta(s,t)=theta(st).
6. Apply the inverse adjoint to the coordinate functionals to obtain a dual basis
   a_i with theta(a_i t)=epsilon_i(t), and both dual-basis expansion identities.
7. Finite-free scalar coordinates identify the sheaf tensor with M^d; evaluation
   at the original basis identifies internal Hom with M^d. Their composite is phi,
   with inverse h ↦ sum_i a_i tensor h(e_i) and the stated pure-tensor equation.
   The tensor here is the sheafification of the sectionwise balanced tensor.
8. Commutativity gives phi(a s tensor m)(t)=phi(s tensor m)(ta). R-linearity of
   every f gives the naturality square. Slice-wise Hom with this action is the
   coextension equalizer, so these components identify extension and coextension.
   No unramified hypothesis was used. -/
theorem fieldExtensionTracePairing
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (T : Scheme.{t}) :
    Nonempty (FieldExtensionTracePairingData l E F ι T) := by
  sorry

end WeilConjectures
