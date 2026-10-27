/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces
public import Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData
public import WeilConjectures.AlgebraicGeometry.FunctionField
import Sheaf.AlgebraicGeometry.GroupScheme.BruhatLongestCellCharts
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Normality and character functions on the open Bruhat cell

Source: Milne, Algebraic Groups (2017), Corollary 1.35, Theorem 21.73(b),
Definition 21.72, Proposition 22.22 and Lemmas 22.23--22.25, pp.468--470.
(blueprint: lem-sfb-normal-big-cell-character-functions)

Characters are actual group-scheme homomorphisms. The automorphism s is conjugation
by the chosen representative; pullback along its inverse is the Weyl action on characters.
The induced subspace is specified by right covariance on every algebra, and its coaction
is required to restrict the canonical inverse-left-translation coaction.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj TensorProduct

namespace AlgebraicGeometry.NormalBigCell

variable {F : Type u} [Field F]

/-- The multiplication chart (u,b) ↦ u n b.
Source: Milne, proof of 22.22 (blueprint: lem-sfb-normal-big-cell-character-functions). -/
def chart {H U B : Grp (Over (Spec (.of F)))}
    (iU : U ⟶ B) (iB : B ⟶ H)
    (n : 𝟙_ (Over (Spec (.of F))) ⟶ H.X) : U.X ⊗ B.X ⟶ H.X :=
  (fst U.X B.X ≫ iU.hom.hom ≫ iB.hom.hom) *
    (toUnit (U.X ⊗ B.X) ≫ n) * (snd U.X B.X ≫ iB.hom.hom)

/-- Evaluate a global regular function at an algebra-valued point.
Source: Milne, 22.21--22.22 (blueprint: lem-sfb-normal-big-cell-character-functions). -/
def value {X : Over (Spec (.of F))} (A : CommAlgCat.{u} F)
    (g : StandardGroupSchemes.affine F A ⟶ X) (r : Γ(X.left, ⊤)) : A :=
  (Scheme.ΓSpecIso (.of A)).hom (g.left.appTop r)

/-- The regular function q(b) inverse, q = (w₀χ) p, pulled back to U × B.
The inverse is in the multiplicative group, so this is a unit over every algebra.
Source: Milne, 22.22--22.25 (blueprint: lem-sfb-normal-big-cell-character-functions). -/
def chartFunction {T U B : Grp (Over (Spec (.of F)))}
    (p : B ⟶ T) (s : Aut T) (χ : RankOneRoots.Character T) : Γ((U.X ⊗ B.X).left, ⊤) :=
  ((snd U.X B.X ≫ p.hom.hom ≫ s.inv.hom.hom ≫ χ.hom.hom)⁻¹).left.appTop
    ((Scheme.ΓSpecIso (.of (LaurentPolynomial F))).inv (LaurentPolynomial.T 1))

/-- The canonical left-translation coaction δ(f)(g,a)=f(a inverse g), namely
flip Delta followed by the antipode on its second tensor factor.
Source: Milne, 22.21 and Chapter 4 (blueprint: lem-sfb-normal-big-cell-character-functions). -/
def leftCoaction (H : Grp (Over (Spec (.of F)))) [IsAffine H.X.left] :
    Γ(H.X.left, ⊤) →ₗ[F] Γ(H.X.left, ⊤) ⊗[F] Γ(H.X.left, ⊤) :=
  (HopfAlgebra.antipode F).lTensor Γ(H.X.left, ⊤) ∘ₗ
    (TensorProduct.comm F Γ(H.X.left, ⊤) Γ(H.X.left, ⊤)).toLinearMap ∘ₗ
    Coalgebra.comul

end AlgebraicGeometry.NormalBigCell

namespace AlgebraicGeometry

/-- The open longest-cell chart, normal coordinate ring, character units, and their
scheme-theoretic equivariance and rational induced modules.
Source: Milne, 21.72--21.73, proof of 22.22 and 22.23--22.25, pp.468--470.
(blueprint: lem-sfb-normal-big-cell-character-functions)

Proof plan:
1. lem-sfb-bruhat-longest-cell-charts and lem-sfb-longest-weyl-open-cell give
   integrality and the dense open chart for the specified representative.
   lem-sfb-reductive-borel-pair-structure gives the radical and projection.
2. lem-weil-pbc-smooth-scheme-over-field-regular gives regular local rings;
   rem-pc-regular-normal makes them integrally closed domains.
3. lem-sc-integral-function-field-affine-fraction identifies the generic stalk
   with Frac(F[H]). lem-sc-integral-scheme-stalks-in-function-field gives injective
   germ maps. An element integral over F[H] is integral over each local ring,
   hence belongs to every local ring. lem-sc-function-field-sections-glue glues it.
4. Pull the inverse Laurent coordinate of (w₀χ)p back through the B-coordinate
   and the inverse chart. This is a unit; the multiplicative law for characters
   gives f_(χ+ψ)=f_χ f_ψ, also in the function field.
5. Left U-translation changes only u. Right B-translation multiplies the value
   by q(b) inverse. For t in T use t inverse u n b = (t inverse u t)n(sb),
   s=n inverse t inverse n. The longest Weyl element squares to one, so n squared
   lies in the commutative torus and q(s)=χ(t) inverse. This gives weight χ.
6. If f extends, these identities extend over U×H, T×H and H×B: restriction
   to the products with the cell is tensoring an injection of vector spaces.
   lem-weil-pbc-fibre-product-affine-spectra identifies these coordinate maps.
   Evaluation gives the identities over every algebra, including nonreduced ones.
7. lem-sfb-affine-group-coordinate-hopf gives the left coaction flip Delta
   followed by 1 tensor antipode. The group law gives its two coaction identities.
   Left and right translations commute, so it preserves the kernel defining E.
   Over a field ker(D tensor 1)=ker(D) tensor F[H], by a basis of F[H].
   Restricting the coaction to E gives the asserted rational module and laws.
No finite-dimensionality or characteristic-zero assumption is used. -/
theorem normal_big_cell_character_functions
    {F : Type u} [Field F] [IsAlgClosed F]
    (H T B U : Grp (Over (Spec (.of F))))
    (hH : ReductiveTorusCentralizer.IsReductive H)
    (iT : T ⟶ H) (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (iB : B ⟶ H) (hB : IsBorelGroupScheme iB.hom.hom)
    (j : T ⟶ B) (hj : j ≫ iB = iT)
    (iU : U ⟶ B)
    (hU : IsClosedSubgroupScheme iU.hom.hom ∧ IsNormalSubgroupScheme iU.hom.hom ∧
      Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧ SolvableGroupStructure.IsUnipotent U ∧
      ∀ (N : Grp (Over (Spec (.of F)))) (iN : N ⟶ B),
        IsClosedSubgroupScheme iN.hom.hom → IsNormalSubgroupScheme iN.hom.hom →
        Smooth N.X.hom → ConnectedSpace N.X.left → SolvableGroupStructure.IsUnipotent N →
        ∃ f : N ⟶ U, f ≫ iU = iN)
    (p : B ⟶ T) (hp : j ≫ p = 𝟙 T)
    (hker : IsPullback iU.hom.hom (toUnit U.X) p.hom.hom η[T.X])
    (aB : ModObj T.X B.X)
    (haB : aB.smul = (j.hom.hom ⊗ₘ 𝟙 B.X) ≫ GrpObj.conj B.X)
    (Φplus : Finset (RankOneRoots.Character T))
    (hΦplus : ∀ χ : RankOneRoots.Character T, χ ∈ Φplus ↔
      χ.hom.hom ≠ 1 ∧ @TorusCharacterTangent.weightSpace F _ T B aB χ ≠ ⊥)
    (n₀ : RankOneRoots.normalizer iT) (s : Aut T)
    (hs : ∀ (A : Over (Spec (.of F))) (t : A ⟶ T.X),
      t ≫ s.hom.hom.hom ≫ iT.hom.hom =
        (toUnit A ≫ n₀.val) * (t ≫ iT.hom.hom) * (toUnit A ≫ n₀.val)⁻¹)
    (hlong : Set.image (fun χ : RankOneRoots.Character T ↦ s.inv.hom.hom ≫ χ.hom.hom)
        (Φplus : Set _) = Set.image (fun χ : RankOneRoots.Character T ↦ χ.hom.hom⁻¹)
          (Φplus : Set _)) :
    IsOpenImmersion (NormalBigCell.chart iU iB n₀.val).left ∧
    DenseRange (NormalBigCell.chart iU iB n₀.val).left ∧
    ∃ (_ : IsIntegral H.X.left) (_ : IsAffine H.X.left)
      (_ : Nonempty (⊤ : H.X.left.Opens)),
      IsDomain Γ(H.X.left, ⊤) ∧ IsIntegrallyClosed Γ(H.X.left, ⊤) ∧
      IsFractionRing Γ(H.X.left, ⊤) H.X.left.functionField ∧
      Function.Injective (H.X.left.germToFunctionField ⊤) ∧
    ∃ (C : H.X.left.Opens) (_ : Nonempty C)
      (e : (U.X ⊗ B.X).left ≅ C.toScheme),
      e.hom ≫ C.ι = (NormalBigCell.chart iU iB n₀.val).left ∧
      Function.Injective (H.X.left.germToFunctionField C) ∧
    ∃ f : RankOneRoots.Character T → (Γ(H.X.left, C))ˣ,
      (∀ χ, e.hom.appTop (C.topIso.inv (f χ).val) =
        NormalBigCell.chartFunction (U := U) p s χ) ∧
      (∀ χ, H.X.left.germToFunctionField C (f χ).val ≠ 0) ∧
      (∀ χ ψ ξ : RankOneRoots.Character T,
        ξ.hom.hom = χ.hom.hom * ψ.hom.hom → f ξ = f χ * f ψ) ∧
      (∀ (χ : RankOneRoots.Character T) (r : Γ(H.X.left, ⊤)),
        H.X.left.germToFunctionField ⊤ r = H.X.left.germToFunctionField C (f χ).val →
        (∀ (A : CommAlgCat.{u} F)
          (u : StandardGroupSchemes.affine F A ⟶ U.X)
          (t : StandardGroupSchemes.affine F A ⟶ T.X)
          (g : StandardGroupSchemes.affine F A ⟶ H.X)
          (b : StandardGroupSchemes.affine F A ⟶ B.X),
          NormalBigCell.value A ((u ≫ iU.hom.hom ≫ iB.hom.hom)⁻¹ * g) r =
            NormalBigCell.value A g r ∧
          NormalBigCell.value A ((t ≫ iT.hom.hom)⁻¹ * g) r =
            RankOneRoots.multiplicativeValue A (t ≫ χ.hom.hom) * NormalBigCell.value A g r ∧
          NormalBigCell.value A (g * (b ≫ iB.hom.hom)) r =
            RankOneRoots.multiplicativeValue A
              ((b ≫ p.hom.hom ≫ s.inv.hom.hom ≫ χ.hom.hom)⁻¹) *
                NormalBigCell.value A g r)) ∧
      (∀ χ : RankOneRoots.Character T,
        ∃ (E : Submodule F Γ(H.X.left, ⊤))
          (δ : E →ₗ[F] E ⊗[F] Γ(H.X.left, ⊤)),
          (∀ r : Γ(H.X.left, ⊤), r ∈ E ↔
            ∀ (A : CommAlgCat.{u} F) (g : StandardGroupSchemes.affine F A ⟶ H.X)
              (b : StandardGroupSchemes.affine F A ⟶ B.X),
              NormalBigCell.value A (g * (b ≫ iB.hom.hom)) r =
                RankOneRoots.multiplicativeValue A
                  ((b ≫ p.hom.hom ≫ s.inv.hom.hom ≫ χ.hom.hom)⁻¹) *
                    NormalBigCell.value A g r) ∧
          E.subtype.rTensor Γ(H.X.left, ⊤) ∘ₗ δ =
            NormalBigCell.leftCoaction H ∘ₗ E.subtype ∧
          HopfAction.Coassociative F Γ(H.X.left, ⊤) E δ ∧
          HopfAction.Counital F Γ(H.X.left, ⊤) E δ ∧
          ∀ r : Γ(H.X.left, ⊤),
            H.X.left.germToFunctionField ⊤ r = H.X.left.germToFunctionField C (f χ).val →
              r ∈ E) := by
  sorry

end AlgebraicGeometry
