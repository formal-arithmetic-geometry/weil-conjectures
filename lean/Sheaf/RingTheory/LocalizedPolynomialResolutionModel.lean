/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.LinearAlgebra.TensorProduct.Defs

/-!
# Localized augmented polynomial resolutions

Source: Stacks Project, Tags 08QP, 08QI, 00DK and 00CS
(blueprint: lem-trf-localized-polynomial-resolution-model).

The underlying module augmentation is obtained by lifting the given coefficient
cone to the category of algebras. This retains the supplied resolution and all
its operators. Tensor factors are written in the Mathlib order, with the new
coefficient ring on the left.
-/

@[expose] public noncomputable section

universe u v

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped TensorProduct

namespace Algebra.CotangentResolution

/-- The given simplicial algebra, viewed in the category of algebras over its base.
Source: Stacks, Tag 08QI (blueprint: lem-trf-localized-polynomial-resolution-model). -/
def resolutionAlgebras {f : Arrow CommRingCat.{u}} (P : Augmentation f) :
    SimplicialObject (CommAlgCat.{u} f.left) :=
  Under.lift P.algebra P.base ⋙ (commAlgCatEquivUnder f.left).inverse

/-- The target with the algebra structure of the given ring map.
Source: Stacks, Tag 08QI (blueprint: lem-trf-localized-polynomial-resolution-model). -/
def resolutionTarget (f : Arrow CommRingCat.{u}) : CommAlgCat.{u} f.left :=
  (commAlgCatEquivUnder f.left).inverse.obj (Under.mk f.hom)

/-- Forget multiplication while retaining the coefficient action.
Source: Stacks, Tag 08QP (blueprint: lem-trf-localized-polynomial-resolution-model). -/
def resolutionForgetModules (R : CommRingCat.{u}) :
    CommAlgCat.{u} R ⥤ ModuleCat.{u} R :=
  forget₂ (CommAlgCat R) (AlgCat R) ⋙ forget₂ (AlgCat R) (ModuleCat R)

/-- The actual module augmentation underlying the given augmented algebra.
Source: Stacks, Tags 08QI and 08QP
(blueprint: lem-trf-localized-polynomial-resolution-model). -/
def resolutionModuleAugmented {f : Arrow CommRingCat.{u}} (P : Augmentation f) :
    SimplicialObject.Augmented (ModuleCat.{u} f.left) :=
  ⟨resolutionAlgebras P ⋙ resolutionForgetModules f.left,
    (resolutionForgetModules f.left).obj (resolutionTarget f),
    ((resolutionForgetModules f.left).mapCocone
      ((commAlgCatEquivUnder f.left).inverse.mapCocone
        (Under.liftCocone P.algebra P.base ⟨f.right, P.augmentation⟩ f.hom
          (fun j ↦ P.triangle j.unop.len)))).ι⟩

/-- The alternating-face augmentation as a morphism of nonpositive complexes.
Source: Stacks, Tags 08QI and 08QP
(blueprint: lem-trf-localized-polynomial-resolution-model). -/
def resolutionModuleComplexAugmentation {f : Arrow CommRingCat.{u}}
    (P : Augmentation f) :=
  HomologicalComplex.extendMap
    (AlgebraicTopology.AlternatingFaceMapComplex.ε.app (resolutionModuleAugmented P))
    ComplexShape.embeddingDownNat

/-- Fractions in the target algebra, including the case that zero is inverted.
Source: Stacks, Tags 07JZ and 08QP
(blueprint: lem-trf-localized-polynomial-resolution-model). -/
def resolutionLocalizedTarget (f : Arrow CommRingCat.{u}) (S : Submonoid f.left) :
    CommAlgCat.{u} (Localization S) :=
  letI := LocalizedModule.algebraOfIsLocalization (S := S) (Localization S)
    (A := resolutionTarget f)
  CommAlgCat.of (Localization S) (LocalizedModule S (resolutionTarget f))

/-- Scalar extension of an individual term, in the coefficient-first tensor order.
Source: Stacks, Tag 08QP (blueprint: lem-trf-localized-polynomial-resolution-model). -/
def resolutionTensorTerm {f : Arrow CommRingCat.{u}} (P : Augmentation f)
    (S : Submonoid f.left) (n : ℕ) : CommAlgCat.{u} (Localization S) :=
  CommAlgCat.of (Localization S)
    (Localization S ⊗[f.left] (resolutionAlgebras P).obj (op ⦋n⦌))

/-- The augmented nonpositive alternating-face complex as an arrow.
Source: Stacks, Tag 08QP (blueprint: lem-trf-localized-polynomial-resolution-model). -/
def resolutionComplexArrow {f : Arrow CommRingCat.{u}} (P : Augmentation f) :=
  Arrow.mk (resolutionModuleComplexAugmentation P)

/-- An element of the term in cohomological degree `-n`, using extension by zero.
Source: Stacks, Tags 08QI and 08QP
(blueprint: lem-trf-localized-polynomial-resolution-model). -/
def resolutionComplexElement {f : Arrow CommRingCat.{u}} (P : Augmentation f) (n : ℕ)
    (p : (resolutionAlgebras P).obj (op ⦋n⦌)) : (resolutionComplexArrow P).left.X (-(n : ℤ)) :=
  (((AlgebraicTopology.alternatingFaceMapComplex _).obj
    (resolutionModuleAugmented P).left).extendXIso
      ComplexShape.embeddingDownNat (i := n) rfl).inv p

/-- The localization ring map on the target, with its specified coefficient action.
Source: Stacks, Tag 08QP (blueprint: lem-trf-localized-polynomial-resolution-model). -/
def resolutionLocalizedArrow (f : Arrow CommRingCat.{u}) (S : Submonoid f.left) :
    Arrow CommRingCat.{u} :=
  Arrow.mk (CommRingCat.ofHom
    (algebraMap (Localization S) (resolutionLocalizedTarget f S)))

/-- The full localized-resolution assertion, retaining fraction formulas, all simplicial
operators, arbitrary polynomial coordinates, and the actual augmented-complex isomorphism.
Source: Stacks, Tags 08QP, 08QI, 00DK and 00CS
(blueprint: lem-trf-localized-polynomial-resolution-model). -/
structure LocalizedPolynomialResolutionModel {f : Arrow CommRingCat.{u}}
    (P : Augmentation f) (S : Submonoid f.left) where
  moduleIso : ∀ M : ModuleCat.{v} f.left,
    Localization S ⊗[f.left] M ≃ₗ[Localization S] LocalizedModule S M
  fraction : ∀ (M : ModuleCat.{v} f.left) (r : f.left) (s : S) (m : M),
    moduleIso M (Localization.mk r s ⊗ₜ[f.left] m) = LocalizedModule.mk (r • m) s
  inverse_fraction : ∀ (M : ModuleCat.{v} f.left) (m : M) (s : S),
    (moduleIso M).symm (LocalizedModule.mk m s) = Localization.mk 1 s ⊗ₜ[f.left] m
  naturality : ∀ (M N : ModuleCat.{v} f.left) (h : M ⟶ N) (x : Localization S ⊗[f.left] M),
    moduleIso N (LinearMap.baseChange (Localization S) h.hom x) =
      LocalizedModule.map S h.hom (moduleIso M x)
  resolution : Augmentation (resolutionLocalizedArrow f S)
  polynomial : IsPolynomialResolution resolution
  termIso : ∀ n : ℕ, resolutionTensorTerm P S n ≅
    (resolutionAlgebras resolution).obj (op ⦋n⦌)
  operator : ∀ (m n : ℕ) (θ : ⦋m⦌ ⟶ ⦋n⦌) (b : Localization S)
      (p : (resolutionAlgebras P).obj (op ⦋n⦌)),
    (resolutionAlgebras resolution).map θ.op ((termIso n).hom (b ⊗ₜ[f.left] p)) =
      (termIso m).hom (b ⊗ₜ[f.left] (resolutionAlgebras P).map θ.op p)
  augmentation : ∀ (n : ℕ) (b : Localization S)
      (p : (resolutionAlgebras P).obj (op ⦋n⦌)),
    resolution.augmentation.app (op ⦋n⦌) ((termIso n).hom (b ⊗ₜ[f.left] p)) =
      b • (LocalizedModule.mk (P.augmentation.app (op ⦋n⦌) p) 1 :
        resolutionLocalizedTarget f S)
  complexIso : resolutionComplexArrow resolution ≅
    Arrow.mk (((ModuleCat.localizedModuleFunctor S).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (resolutionModuleComplexAugmentation P))
  complex_fraction : ∀ (n : ℕ) (r : f.left) (s : S)
      (p : (resolutionAlgebras P).obj (op ⦋n⦌)),
    complexIso.hom.left.f (-(n : ℤ))
        (resolutionComplexElement resolution n
          ((termIso n).hom (Localization.mk r s ⊗ₜ[f.left] p))) =
      equivShrink (LocalizedModule S ((resolutionComplexArrow P).left.X (-(n : ℤ))))
        (LocalizedModule.mk (r • resolutionComplexElement P n p) s)
  coordinates : ∀ (n : ℕ) (E : Type u)
      (c : CommAlgCat.of f.left (MvPolynomial E f.left) ≅
        (resolutionAlgebras P).obj (op ⦋n⦌)),
    ∃ d : CommAlgCat.of (Localization S) (MvPolynomial E (Localization S)) ≅
        (resolutionAlgebras resolution).obj (op ⦋n⦌),
      ∀ (b : Localization S) (p : MvPolynomial E f.left),
        d.hom (b • MvPolynomial.map (algebraMap f.left (Localization S)) p) =
          (termIso n).hom (b ⊗ₜ[f.left] c.hom p)

/-- Localization of any augmented polynomial resolution is a polynomial resolution,
with the specified natural tensor/fraction comparisons, augmented-complex isomorphism,
and coefficient maps in arbitrary polynomial coordinates.
Source: Stacks, Tags 08QP, 08QI, 00DK and 00CS
(blueprint: lem-trf-localized-polynomial-resolution-model).

Proof:
1. Apply lem-weil-pbc-localization-tensor-over-base with base and algebra both R,
   first module R and second module M. Compose with R tensor M = M to obtain
   m/s ↦ (1/s) tensor m. Its inverse sends (r/s) tensor m to rm/s.
   The tensor relations of def-weil-pbc-module-tensor-product prove B-linearity;
   the two naturality composites send each pure tensor to rh(m)/s.
2. Switch tensor factors to the order in the node. The comparison for an algebra
   is multiplicative by the tensor multiplication of def-weil-module-base-change.
   Extend every face and degeneracy by scalars. Functoriality preserves all
   simplicial identities, and the fraction comparisons identify these operators
   with termwise localization. The augmentation sends b tensor p to b times ε(p)/1.
3. For every supplied polynomial coordinate isomorphism R[E] = P_n, apply
   lem-weil-pbc-polynomial-scalar-extension. Its coefficient formula gives the
   coordinates field, for empty, finite or infinite E without a finiteness assumption.
4. The alternating differential is a finite signed sum of faces. Scalar extension
   is linear on maps, so the fraction formulas commute with this differential.
   They also commute with the augmentation. Extend by zero to positive degrees;
   the inverse fraction formulas give an actual isomorphism in the arrow category
   of complexes, as specified by complexIso and complex_fraction.
5. Apply lem-weil-pbc-localization-module-exact to every consecutive triple in the
   exact augmented alternating complex, including its last two triples. Thus the
   localized augmentation is a quasi-isomorphism. For each t/s, lift t through
   P_n → T and take (1/s) tensor p; this proves levelwise surjectivity. Together
   with step 3 these are exactly the clauses of IsPolynomialResolution.
6. No step requires 0 outside S. If 0 belongs to S, the fraction relation makes
   B, all localized modules and all tensor terms zero. The same formulas and
   augmented-complex isomorphism still apply, including polynomial rings on an
   empty or infinite set of variables. -/
theorem exists_localized_polynomial_resolution_model {f : Arrow CommRingCat.{u}}
    (P : Augmentation f) (hP : IsPolynomialResolution P) (S : Submonoid f.left) :
    Nonempty (LocalizedPolynomialResolutionModel.{u, v} P S) := by
  sorry

/-- The canonical localization ring map, also when zero is inverted.
Source: Stacks, Tags 00CM and 08QP
(blueprint: lem-trf-localized-polynomial-resolution-model). -/
def resolutionLocalizationArrow (R : CommRingCat.{u}) (S : Submonoid R) :
    Arrow CommRingCat.{u} :=
  Arrow.mk (CommRingCat.ofHom (algebraMap R (Localization S)))

/-- When the target already is the localized coefficient ring, identify its further
localization with itself and obtain a resolution of B over B with augmentation ε(p)b.
The natural isomorphism `e` identifies this with the general localized resolution.
Source: Stacks, Tags 08QP, 08QI, 07JZ and 00CM
(blueprint: lem-trf-localized-polynomial-resolution-model).

Proof: Apply the preceding six-step localization construction with T = B. Each s/1
is invertible in B, with inverse 1/s. Thus ψ(b/s) = (1/s)b is well defined: a
fraction relation u(tb-sc) = 0 can be cancelled by the units u/1, s/1 and t/1.
The fraction operations of def-weil-pbc-module-localization show that ψ is a
B-algebra homomorphism. The map b ↦ b/1 is its inverse, since ((1/s)b)/1 = b/s.
Transport the augmentation of the general localized resolution through ψ, keeping
the simplicial terms and operators. Polynomiality, levelwise surjectivity and
quasi-isomorphy are invariant under this target isomorphism, so it is a polynomial
resolution of B over B. Its augmentation sends b tensor p to ε(p)b, as claimed.
If zero belongs to S, all these rings and modules are zero and the formulas persist. -/
theorem exists_self_localized_polynomial_resolution_model
    (R : CommRingCat.{u}) (S : Submonoid R)
    (P : Augmentation (resolutionLocalizationArrow R S)) (hP : IsPolynomialResolution P) :
    ∃ (L : LocalizedPolynomialResolutionModel.{u, v} P S)
      (ψ : resolutionLocalizedTarget (resolutionLocalizationArrow R S) S ≃ₐ[Localization S]
        Localization S)
      (Q : Augmentation (Arrow.mk (𝟙 (CommRingCat.of (Localization S)))))
      (e : L.resolution.algebra ≅ Q.algebra),
      IsPolynomialResolution Q ∧
      (∀ (b : Localization S) (s : S),
        ψ (LocalizedModule.mk b s) = Localization.mk 1 s * b) ∧
      (∀ (n : ℕ) (b : Localization S),
        e.hom.app (op ⦋n⦌) (L.resolution.base.app (op ⦋n⦌) b) =
          Q.base.app (op ⦋n⦌) b) ∧
      (∀ (n : ℕ) (x : L.resolution.algebra.obj (op ⦋n⦌)),
        Q.augmentation.app (op ⦋n⦌) (e.hom.app (op ⦋n⦌) x) =
          ψ (L.resolution.augmentation.app (op ⦋n⦌) x)) ∧
      (∀ (n : ℕ) (b : Localization S)
          (p : (resolutionAlgebras P).obj (op ⦋n⦌)),
        Q.augmentation.app (op ⦋n⦌)
            (e.hom.app (op ⦋n⦌) ((L.termIso n).hom
              (b ⊗ₜ[(resolutionLocalizationArrow R S).left] p))) =
          @_root_.id (Localization S) (P.augmentation.app (op ⦋n⦌) p) * b) := by
  sorry

end Algebra.CotangentResolution
