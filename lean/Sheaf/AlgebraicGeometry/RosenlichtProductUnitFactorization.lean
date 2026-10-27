/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.FunctionField
import Sheaf.RingTheory.BoundedInverseUnitLines
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz

/-!
# Rosenlicht factorization of units on a product

Source: Milne, Algebraic Groups (2017), Proposition 12.48, printed pp. 246-247,
identity (79), and Remark 12.50 (blueprint: lem-sfb-rosenlicht-product-unit-factorization).

The factors and their product are schemes, and units belong to their global section rings.
The two slice maps below are constructed by the scheme pullback universal property.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The slice `x ↦ (x,y₀)` in a scheme fibre product, constructed by its universal property.
Source: Milne, Algebraic Groups, Proposition 12.48, identity (79), pp. 246-247
(blueprint: lem-sfb-rosenlicht-product-unit-factorization). -/
noncomputable def rosenlichtSliceX {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (y₀ : S ⟶ Y) (hy : y₀ ≫ g = 𝟙 S) : X ⟶ pullback f g :=
  pullback.lift (𝟙 X) (f ≫ y₀)
    ((Category.id_comp f).trans
      (((Category.assoc f y₀ g).trans
        (congrArg (fun t => f ≫ t) hy)).trans (Category.comp_id f)).symm)

/-- The slice `y ↦ (x₀,y)` in a scheme fibre product, constructed by its universal property.
Source: Milne, Algebraic Groups, Proposition 12.48, identity (79), pp. 246-247
(blueprint: lem-sfb-rosenlicht-product-unit-factorization). -/
noncomputable def rosenlichtSliceY {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (x₀ : S ⟶ X) (hx : x₀ ≫ f = 𝟙 S) : Y ⟶ pullback f g :=
  pullback.lift (g ≫ x₀) (𝟙 Y)
    ((((Category.assoc g x₀ f).trans
      (congrArg (fun t => g ≫ t) hx)).trans (Category.comp_id g)).trans
        (Category.id_comp g).symm)

/-- Every global unit on the product of two integral separated finite-type schemes over an
algebraically closed field is a product of units pulled back from the factors. For every
pair of rational basepoints the normalized slice formula holds as an equality of global units,
hence also of regular functions. The scalar term is pulled back from `Γ(Spec F, ⊤)`;
under `Scheme.ΓSpecIso` it is precisely `u(x₀,y₀)⁻¹` in `Fˣ`.

Source: Milne, Algebraic Groups (2017), Proposition 12.48, printed pp. 246-247,
identity (79), and Remark 12.50 (blueprint: lem-sfb-rosenlicht-product-unit-factorization).

Proof (the DAG's affine bounded-inverse proof of the printed normalization identity):
1. Choose any prescribed rational basepoints. They exist by
   lem-sc-lft-over-field-jacobson-space and lem-weil-pbc-closed-point-residue-field-base.
   Put c = u(x₀,y₀) and normalize w = u*c/(u(-,y₀)*u(x₀,-)). Its two slices are one.
2. Choose finite-type affine neighborhoods U = Spec A, T = Spec B of the basepoints.
   Integrality makes A and B domains. By lem-weil-pbc-open-fibre-product and
   lem-weil-pbc-fibre-product-affine-spectra, their product is an open chart with ring
   A tensor_F B. Finite tensor expressions for w and its inverse give finite-dimensional
   subspaces V,W of A. For every y in T(F), w_y belongs to V and its inverse to W.
   Apply lem-sfb-bounded-inverse-unit-lines. Since w_y(x₀) = 1, there are finitely many
   actual possibilities f_j for w_y, rather than just finitely many scalar lines.
3. In a basis a_i of V, write w = sum a_i tensor b_i and f_j = sum c_ij a_i.
   The ideals I_j = (b_i-c_ij) cover the rational points by their zero loci.
   If all I_j were nonzero, a product of nonzero elements h_j in I_j would vanish at
   all rational points of T. By lem-wf-affine-nullstellensatz-vanishing it is zero,
   contradicting that B is a domain. Some I_j is zero, so w = f_j tensor 1.
   Its slice at y₀ is one; hence w = 1 on U times_F T.
4. By lem-sc-integral-scheme-stalks-in-function-field, sections of X inject into its
   function field. Thus for each y in T(F), w(-,y) = 1 globally on X. Fix x in X(F).
   The affine vanishing principle on T and then function-field injectivity on Y give
   w(x,-) = 1 globally. Consequently w is one on all pairs of rational points.
5. Cover X and Y by finite-type affine charts P = Spec C and Q = Spec D. Their products
   are open charts covering the fibre product. Express w-1 in C tensor_F D with linearly
   independent first coordinates. The affine vanishing principle on C kills each
   specialization at y in Q(F); independence kills the coefficients there. The same
   principle on D kills every coefficient. Thus w = 1 on every chart, hence globally.
6. Expand w = 1 to obtain the displayed identity for the arbitrary prescribed basepoints.
   Taking a = u(-,y₀) and b = u(x₀,-)*c⁻¹ gives the existential factorization.
-/
theorem rosenlicht_product_unit_factorization
    (F : Type u) [Field F] [IsAlgClosed F]
    (X Y : Scheme.{u}) (f : X ⟶ Spec (.of F)) (g : Y ⟶ Spec (.of F))
    [IsIntegral X] [IsIntegral Y] [IsSeparated f] [IsSeparated g]
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType g] [QuasiCompact g]
    (u : (Γ(pullback f g, ⊤))ˣ) :
    (∃ (a : (Γ(X, ⊤))ˣ) (b : (Γ(Y, ⊤))ˣ),
      u = Units.map (pullback.fst f g).appTop.hom.toMonoidHom a *
        Units.map (pullback.snd f g).appTop.hom.toMonoidHom b) ∧
    (∀ (x₀ : Spec (.of F) ⟶ X) (y₀ : Spec (.of F) ⟶ Y)
      (hx : x₀ ≫ f = 𝟙 (Spec (.of F))) (hy : y₀ ≫ g = 𝟙 (Spec (.of F))),
      u = Units.map (pullback.fst f g).appTop.hom.toMonoidHom
          (Units.map (rosenlichtSliceX f g y₀ hy).appTop.hom.toMonoidHom u) *
        Units.map (pullback.snd f g).appTop.hom.toMonoidHom
          (Units.map (rosenlichtSliceY f g x₀ hx).appTop.hom.toMonoidHom u) *
        Units.map (pullback.fst f g ≫ f).appTop.hom.toMonoidHom
          ((Units.map (x₀ ≫ rosenlichtSliceX f g y₀ hy).appTop.hom.toMonoidHom u)⁻¹)) := by
  sorry

end AlgebraicGeometry
