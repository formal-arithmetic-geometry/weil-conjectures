module

public import Sheaf.AlgebraicGeometry.SplitTorusTorsorFrameGeometry
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.AlgebraicGeometry.ModuleSheafificationAffineRestriction
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Yoneda

/-! # Laurent algebra of simultaneous line-module frames

Source: Stacks Project, constructions.tex, Tags 01M2 and 01LX (1), (3),
with the explicit Laurent frame-open calculation in the DAG proof.
(blueprint: lem-sfb-frame-product-laurent-algebra).

The algebra and its inclusions are specified by the coproduct universal property
and their multiplication on local tensor generators. Thus no unconstructed
algebra is chosen from an existence theorem. All tensor summands are explicit.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.FrameProductLaurentAlgebra

open Scheme.Modules

/-- Integer tensor powers, with negative powers taken on the actual internal dual.
Source: Stacks, 01M2, Laurent frame-open calculation.
(blueprint: lem-sfb-frame-product-laurent-algebra). -/
def signedPower {S : Scheme.{u}} (A : S.Modules) : ℤ → S.Modules
  | .ofNat m => A.tensorPow m
  | .negSucc m => (dual A).tensorPow (m + 1)

/-- The ordered finite tensor product; the empty product is the structure module.
Source: Stacks, 01M2, finite product of frame opens.
(blueprint: lem-sfb-frame-product-laurent-algebra). -/
def finiteTensor {S : Scheme.{u}} : (r : ℕ) → (Fin r → S.Modules) → S.Modules
  | 0, _ => 𝟙_ S.Modules
  | r + 1, A => A 0 ⊗ finiteTensor r (fun i ↦ A i.succ)

/-- The summand N_n = tensor_i A_i^(-n_i), including rank zero.
Source: Stacks, 01M2, Laurent frame-open calculation.
(blueprint: lem-sfb-frame-product-laurent-algebra). -/
def summand {S : Scheme.{u}} {r : ℕ} (A : Fin r → S.Modules) (n : Fin r → ℤ) :
    S.Modules :=
  finiteTensor r (fun i ↦ signedPower (A i) (-n i))

/-- The tensor power of a section, with the scalar section 1 in degree zero.
Source: Stacks, 01M2, local generators of the Laurent summands.
(blueprint: lem-sfb-frame-product-laurent-algebra). -/
def powerSection {S : Scheme.{u}} {A : S.Modules} {V : S.Opens} (e : Γ(A, V)) :
    (m : ℕ) → Γ(A.tensorPow m, V)
  | 0 => unitSectionsEquiv V 1
  | m + 1 => tmulSection e (powerSection e m)

/-- A signed tensor generator from a frame and its evaluation-normalized dual frame.
Source: Stacks, 01M2, local generators of the Laurent summands.
(blueprint: lem-sfb-frame-product-laurent-algebra). -/
def signedSection {S : Scheme.{u}} {A : S.Modules} {V : S.Opens}
    (e : Γ(A, V)) (d : Γ(dual A, V)) : (m : ℤ) → Γ(signedPower A m, V)
  | .ofNat m => powerSection e m
  | .negSucc m => powerSection d (m + 1)

/-- Tensor sections in the same order as the finite tensor product.
Source: Stacks, 01M2, local generators of the Laurent summands.
(blueprint: lem-sfb-frame-product-laurent-algebra). -/
def finiteTensorSection {S : Scheme.{u}} {V : S.Opens} :
    (r : ℕ) → (A : Fin r → S.Modules) → ((i : Fin r) → Γ(A i, V)) →
      Γ(finiteTensor r A, V)
  | 0, _, _ => unitSectionsEquiv V 1
  | r + 1, A, e => tmulSection (e 0)
      (finiteTensorSection r (fun i ↦ A i.succ) (fun i ↦ e i.succ))

/-- The generator b_n = tensor_i e_i^(-n_i), using dual frames for positive n_i.
Source: Stacks, 01M2, local generators of the Laurent summands.
(blueprint: lem-sfb-frame-product-laurent-algebra). -/
def monomialSection {S : Scheme.{u}} {r : ℕ} {A : Fin r → S.Modules} {V : S.Opens}
    (e : (i : Fin r) → Γ(A i, V)) (d : (i : Fin r) → Γ(dual (A i), V))
    (n : Fin r → ℤ) : Γ(summand A n, V) :=
  finiteTensorSection r (fun i ↦ signedPower (A i) (-n i))
    (fun i ↦ signedSection (e i) (d i) (-n i))

/-- Direct image of the structure sheaf, with the scheme's actual scalar map.
Source: Stacks, 01LX (3).
(blueprint: lem-sfb-frame-product-laurent-algebra). -/
def structureAlgebra {S P : Scheme.{u}} (q : P ⟶ S) : S.CommAlgebraSheaf :=
  Under.mk (⟨q.c⟩ : S.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat.{u} q.base).obj P.sheaf)

/-- The frame product is affine and its algebra is the sheafified Laurent tensor sum.

Source: Stacks, constructions.tex, 01M2 and 01LX (1), (3), Laurent frame-open variant.
(blueprint: lem-sfb-frame-product-laurent-algebra).

Proof:
1. For R, the additive group algebra of Z^r is the finite-support Laurent ring.
   Its single n a is a*z^n. Convolution adds exponents; single 0 1 is the unit.
   Substitution of units gives the unique R-algebra map, including r = 0.
2. Choose common local frames of the finitely many A_i and refine to affine opens
   by lem-weil-pbc-affine-opens-basis. Tensor pullback identifies frames with units.
   By lem-weil-pbc-morphism-into-affine-scheme and lem-pc-yoneda the representing
   scheme over each chart is Spec of that Laurent ring, with universal frame z_i*e_i.
3. Apply pqf-lem-affine-local-target to this cover to obtain affineness of q.
4. Each summand is locally free on b_n = tensor e_i^(-n_i). Its sheafified
   presheaf direct sum is the coproduct characterized by IsColimit below.
   Evaluation gives b_n*b_m = b_(n+m) and b_0 = 1. The affine-chart map b_n to z^n
   is bijective, with inverse reading the unique finite coefficients. It commutes
   with restriction. Lem-sc-module-sheafification-affine-restriction extends it
   to the sheafified sum. The local multiplication makes this an algebra map.
5. Replacing e_i by g_i*e_i replaces z_i by g_i^(-1)*z_i and b_n by
   (product g_i^(-n_i))*b_n. Hence the local maps and their inverses agree and glue.
   Evaluation of a covector on the tautological frame gives z_i; applying the
   inverse frame to a vector gives z_i^(-1). Thus the displayed normalization
   specifies evaluation on every summand, with the required sign. No finite cover
   or condition on the base ring is used; the empty product gives the identity. -/
theorem frame_product_laurent_algebra
    {S P : Scheme.{u}} (q : P ⟶ S) (r : ℕ) (A : Fin r → S.Modules)
    [hinv : ∀ i, (A i).IsInvertible]
    (τ : (i : Fin r) → 𝟙_ P.Modules ≅ (tensorPullback q).obj (A i))
    (hrep : ∀ U : Over S, Function.Bijective fun a : U ⟶ Over.mk q ↦
      fun i : Fin r ↦ SplitTorusFrames.pullFrame (A i) q (τ i) a.left ≪≫
        eqToIso (congrArg (fun f ↦ (tensorPullback f).obj (A i)) a.w)) :
    IsAffineHom q ∧
      ∃ (B : S.CommAlgebraSheaf) (j : (n : Fin r → ℤ) → summand A n ⟶ B.toModule),
        Nonempty (IsColimit (Cofan.mk B.toModule j)) ∧
        ∃ φ : B ≅ structureAlgebra q,
          ∀ (V : S.Opens) (e : (i : Fin r) → Γ(A i, V))
            (d : (i : Fin r) → Γ(dual (A i), V)),
            (∀ i, IsFreeGenerator (e i)) →
            (∀ i, IsFreeGenerator (d i)) →
            (∀ i, (dualEvaluation (A i)).app V (tmulSection (e i) (d i)) =
              unitSectionsEquiv V 1) →
            (∀ a : Γ(S, V),
              (j 0).app V (a • monomialSection e d 0) = B.hom.hom.app (op V) a) ∧
            (∀ n m : Fin r → ℤ,
              @id (B.right.obj.obj (op V)) ((j n).app V (monomialSection e d n)) *
                @id (B.right.obj.obj (op V)) ((j m).app V (monomialSection e d m)) =
                  (j (n + m)).app V (monomialSection e d (n + m))) ∧
            ∃ z : Fin r → Γ(P, q ⁻¹ᵁ V)ˣ,
              (∀ i, (τ i).hom.app (q ⁻¹ᵁ V) (unitSectionsEquiv (q ⁻¹ᵁ V) 1) =
                (z i : Γ(P, q ⁻¹ᵁ V)) • tensorPullbackSection q (A i) V (e i)) ∧
              (∀ n : Fin r → ℤ,
                φ.hom.right.hom.app (op V) ((j n).app V (monomialSection e d n)) =
                  ∏ i : Fin r, ((z i ^ n i : Γ(P, q ⁻¹ᵁ V)ˣ) : Γ(P, q ⁻¹ᵁ V))) ∧
              ∀ hV : IsAffineOpen V,
                ∃ c : AddMonoidAlgebra Γ(S, V) (Fin r → ℤ) ≃+* Γ(P, q ⁻¹ᵁ V),
                  (∀ (n : Fin r → ℤ) (a : Γ(S, V)),
                    c (AddMonoidAlgebra.single n a) =
                      q.app V a *
                        ∏ i : Fin r, ((z i ^ n i : Γ(P, q ⁻¹ᵁ V)ˣ) : Γ(P, q ⁻¹ᵁ V))) ∧
                  ∃ χ : (q ⁻¹ᵁ V).toScheme ≅
                    Spec (.of (AddMonoidAlgebra Γ(S, V) (Fin r → ℤ))),
                    χ.hom ≫ Spec.map (CommRingCat.ofHom
                      (AddMonoidAlgebra.singleZeroRingHom (R := Γ(S, V))
                        (M := Fin r → ℤ))) = (q ∣_ V) ≫ hV.isoSpec.hom ∧
                    ∀ f : AddMonoidAlgebra Γ(S, V) (Fin r → ℤ),
                      χ.hom.appTop ((Scheme.ΓSpecIso
                        (.of (AddMonoidAlgebra Γ(S, V) (Fin r → ℤ)))).inv f) =
                          (q ⁻¹ᵁ V).topIso.inv (c f) := by
  sorry

end AlgebraicGeometry.FrameProductLaurentAlgebra
