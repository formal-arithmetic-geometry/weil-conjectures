module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Data.List.OfFn
import Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality
import Sheaf.AlgebraicGeometry.GroupScheme.BruhatLongestCellCharts
import Sheaf.AlgebraicGeometry.GroupScheme.BorelRootProductCoordinates
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage
import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization
import Sheaf.AlgebraicGeometry.GroupScheme.SmoothGroupOrbitGeometry
import Sheaf.AlgebraicGeometry.ReductiveTorusSelfCentralizer
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Root monomials and scheme-theoretic kernel coordinates

Source: Milne, Algebraic Groups (2017), Lemma 23.10, p.487; Proposition 23.5,
pp.485--486, (144)--(147); Theorem 21.84 and Summary 21.86, p.451.
(blueprint: lem-sfb-root-monomial-kernel-coordinates)

The explicit quotient spectra and ordered multiplication maps below are coordinate
helpers for this statement. The kernel comparison is an isomorphism of F-schemes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.RootMonomial

/-- The coordinate factor Spec F[z]/(z^q), including its nilpotents. This is the
recorded scheme `StandardGroupSchemes.alpha F q` of def-sc-gm-ga, used here only as
an F-scheme (no group law, no characteristic assumption).
Source: Milne, (145), p.485, identity fibre in the chart of Theorem 21.84, p.451
(blueprint: lem-sfb-root-monomial-kernel-coordinates). -/
abbrev factor (F : Type u) [Field F] (q : ℕ) : Over (Spec (.of F)) :=
  StandardGroupSchemes.alpha F q

/-- The specified closed embedding into the additive parameter line, the recorded
`StandardGroupSchemes.alphaInclusion F q` of def-sc-gm-ga (induced by z ↦ z).
Source: Milne, (145), p.485, identity fibre in Theorem 21.84, p.451
(blueprint: lem-sfb-root-monomial-kernel-coordinates). -/
abbrev factorι (F : Type u) [Field F] (q : ℕ) :
    factor F q ⟶ StandardGroupSchemes.additive F :=
  StandardGroupSchemes.alphaInclusion F q

/-- Ordered negative factors, the middle factor, then ordered positive factors.
The products are products of schemes over F; no group law on them is asserted.
Source: Milne, Theorem 21.84 and Summary 21.86, p.451
(blueprint: lem-sfb-root-monomial-kernel-coordinates). -/
def orderedMap {F : Type u} [Field F] (G : Grp (Over (Spec (.of F))))
    {n m : ℕ} (N : Fin n → Over (Spec (.of F))) (H : Over (Spec (.of F)))
    (P : Fin m → Over (Spec (.of F)))
    (a : ∀ i, N i ⟶ G.X) (h : H ⟶ G.X) (b : ∀ i, P i ⟶ G.X) :
    ((∏ᶜ N) ⊗ H) ⊗ (∏ᶜ P) ⟶ G.X :=
  (fst _ _ ≫ fst _ _ ≫ (List.ofFn (fun i ↦ Pi.π N i ≫ a i)).prod) *
    (fst _ _ ≫ snd _ _ ≫ h) *
    (snd _ _ ≫ (List.ofFn (fun i ↦ Pi.π P i ≫ b i)).prod)

/-- A homomorphism inducing an isogeny of the actual character root data is
surjective and faithfully flat with finite scheme-theoretic kernel. Every root
parameter maps by a unit times the specified p-power. Every ordered big cell
contains the kernel, and its identity fibre has exactly the truncated coordinate
factors and torus kernel displayed in the source node.

Source: Milne, Lemma 23.10, p.487; Proposition 23.5, pp.485--486, (144)--(147);
Theorem 21.84 and Summary 21.86, p.451; Proposition 5.43, p.109
(blueprint: lem-sfb-root-monomial-kernel-coordinates).

Proof plan:
1. By lem-sfb-multiplicative-character-antiduality the torus coordinate map is
   e_m ↦ e_u(m). Coset representatives for its finite cokernel are a positive
   finite free basis. The torus kernel is the diagonalizable group of that cokernel.
2. Use lem-sfb-regular-cocharacter-borel-description and
   lem-sfb-bruhat-longest-cell-charts to translate the longest cell to U⁻TU⁺.
   By lem-sfb-borel-root-product-coordinates, any enumeration gives these coordinates.
   Uniqueness of root groups in lem-sfb-reductive-root-subgroup-parametrizations
   identifies the translated negative factors. The cell is dense open and integral.
   Uniqueness of its coordinates already proves T ∩ U_alpha = 1 scheme-theoretically.
3. Equivariance makes the inverse image of the target cell under f x_alpha an open
   neighbourhood of zero invariant under F× scaling. Algebraic closedness and
   infinitude force it to be the whole line, so this morphism factors through the cell.
4. Its torus coordinate is constant one, since polynomial units are constant.
   Comparing Laurent characters in F[M₁][a] forces a nonzero coefficient of a^n
   in the beta coordinate to satisfy n alpha = u(beta). Reducedness leaves only
   beta = b(alpha) and n = q_alpha. This is a polynomial identity on every algebra.
5. The coefficient cannot vanish: the SL₂ morphism from
   lem-sfb-reductive-rank-one-reflections would then kill both root groups, hence
   their diagonal products. Evaluating b(alpha) on that diagonal gives s^(2q),
   which is not constant on the infinite field, also in characteristic two.
6. Transport a regular positive functional across the rational lattice isomorphism.
   Positive systems correspond, b preserves negatives and q agrees on opposite roots.
   On the cells f is the product of the torus map and the monomials c a^q. Each
   monomial has positive finite free basis 1,a,...,a^(q-1); tensor with the coset basis.
7. Apply lem-sfb-affine-homomorphism-flat-image. Its image ideal vanishes on the
   target cell by the injection of its coordinate algebra into the source cell's.
   Integrality and density, from lem-sfb-bruhat-longest-cell-charts, kill the image
   ideal globally. Thus f is faithfully flat. Apply
   lem-weil-pbc-faithfully-flat-surjective-spectrum for surjectivity.
8. The open part of the kernel in the cell is the identity fibre of this product:
   h(t)=1 and c a^q=0, equivalently a^q=0 since c is a unit. This gives the displayed
   scheme isomorphism on that open part and a finite-dimensional coordinate algebra.
9. By lem-sfb-algebraic-group-homomorphism-factorization the kernel is closed affine
   finite type. Every closed point is rational by lem-weil-pbc-closed-point-residue-field-base.
   Its translates of the finite open neighbourhood cover all closed points, hence
   everything by lem-sc-lft-over-field-jacobson-space. A finite subcover injects
   global sections into a finite product of finite-dimensional algebras, proving finiteness.
10. Conjugation on each kernel point has reduced orbit by
    lem-sfb-smooth-group-orbit-geometry. Connectedness and the finite discrete kernel
    make the orbit a single rational point, so conjugation is constant as a morphism.
    By lem-sfb-reductive-torus-self-centralizer the point lies in T₁.
11. Thus every kernel point lies in the big cell. Its open inverse image is the
    whole kernel scheme, even with nilpotents. Step 8 gives the asserted isomorphism
    over G₁. For q=1 the quotient is F; with no roots the entire statement is the
    torus calculation in step 1. No smoothness or reducedness of the kernel is used. -/
theorem root_monomial_kernel_coordinates
    {F : Type u} [Field F] [IsAlgClosed F] (p : ℕ) [ExpChar F p]
    (G T : Fin 2 → Grp (Over (Spec (.of F)))) (iT : ∀ i, T i ⟶ G i)
    (hG : ∀ i, ReductiveTorusCentralizer.IsReductive (G i))
    (hT : ∀ i, ReductiveTorusCentralizer.IsMaximalTorus (iT i))
    (hsplit : ∀ i, ∃ r : ℕ, Nonempty (T i ≅ MultiplicativeType.splitTorus F r))
    [∀ i, IsCommMonObj (T i).X]
    [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    (aG : ∀ i, ModObj (T i).X (G i).X)
    (hconj : ∀ i, (aG i).smul = ((iT i).hom.hom ⊗ₘ 𝟙 (G i).X) ≫ GrpObj.conj (G i).X)
    (Φ : ∀ i, Finset (Additive (T i ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    (D : ∀ i, RootDatum (Φ i)
      (Additive (T i ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T i)))
    (hred : ∀ i, (D i).IsReduced)
    (hroot : ∀ i (α : Φ i), (D i).root α = α.val)
    (hpair : ∀ i (χ : Additive (T i ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T i)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ ((D i).toLinearMap χ ν))
    (hweights : ∀ i (χ : Additive (T i ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))),
      χ ∈ Φ i ↔ χ ≠ 0 ∧
        @TorusCharacterTangent.weightSpace F _ (T i) (G i) (aG i) χ.toMul ≠ ⊥)
    (U : ∀ i, Φ i → Grp (Over (Spec (.of F)))) (iU : ∀ i α, U i α ⟶ G i)
    (hU : ∀ i α,
      IsClosedSubgroupScheme (iU i α).hom.hom ∧ Smooth (U i α).X.hom ∧
      ConnectedSpace (U i α).X.left ∧
      @TorusCharacterTangent.IsStable F _ (T i) (G i) (aG i) _ (iU i α) ∧
      (GrpObj.differential (iU i α).hom.hom).toLinearMap.range =
        @TorusCharacterTangent.weightSpace F _ (T i) (G i) (aG i) α.val.toMul)
    (x : ∀ i α, Grp.mk (StandardGroupSchemes.additive F) ≅ U i α)
    (f : G 1 ⟶ G 0) (h : T 1 ⟶ T 0) (hfT : iT 1 ≫ f = h ≫ iT 0)
    (u : Additive (T 0 ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) →+
      Additive (T 1 ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (hu : ∀ χ, u χ = Additive.ofMul (h ≫ χ.toMul))
    (hinj : Function.Injective u) (hfinite : Finite (_ ⧸ u.range))
    (b : Φ 1 ≃ Φ 0) (q : Φ 1 → ℕ) (hq : ∀ α, ∃ e : ℕ, q α = p ^ e)
    (hrootmap : ∀ α, u ((D 0).root (b α)) = q α • (D 1).root α)
    (hcorootmap : ∀ α, Additive.ofMul (((D 1).coroot α).toMul ≫ h) =
      q α • (D 0).coroot (b α)) :
    Surjective f.hom.hom.left ∧ f.hom.hom.left.appTop.hom.FaithfullyFlat ∧
    IsFinite (GrpObj.ker f.hom.hom).hom ∧
    (∃ c : Φ 1 → Fˣ, ∀ (α : Φ 1) (A : Type u) [CommRing A] [Algebra F A] (a : A),
      TorusCharacterTangent.additiveParameterPoint F a ≫
          (x 1 α).hom.hom.hom ≫ (iU 1 α).hom.hom ≫ f.hom.hom =
        TorusCharacterTangent.additiveParameterPoint F (algebraMap F A (c α) * a ^ q α) ≫
          (x 0 (b α)).hom.hom.hom ≫ (iU 0 (b α)).hom.hom) ∧
    (∀ (base : (D 1).Base) (n m : ℕ)
      (neg : Fin n ≃ {α : Φ 1 // ¬ base.IsPos α})
      (pos : Fin m ≃ {α : Φ 1 // base.IsPos α}),
      IsOpenImmersion (orderedMap (G 1)
        (fun j ↦ (U 1 (neg j).val).X) (T 1).X (fun j ↦ (U 1 (pos j).val).X)
        (fun j ↦ (iU 1 (neg j).val).hom.hom) (iT 1).hom.hom
        (fun j ↦ (iU 1 (pos j).val).hom.hom)).left ∧
      DenseRange (orderedMap (G 1)
        (fun j ↦ (U 1 (neg j).val).X) (T 1).X (fun j ↦ (U 1 (pos j).val).X)
        (fun j ↦ (iU 1 (neg j).val).hom.hom) (iT 1).hom.hom
        (fun j ↦ (iU 1 (pos j).val).hom.hom)).left ∧
      Set.range (GrpObj.kerι f.hom.hom).left ⊆ Set.range (orderedMap (G 1)
        (fun j ↦ (U 1 (neg j).val).X) (T 1).X (fun j ↦ (U 1 (pos j).val).X)
        (fun j ↦ (iU 1 (neg j).val).hom.hom) (iT 1).hom.hom
        (fun j ↦ (iU 1 (pos j).val).hom.hom)).left ∧
      ∃ e : (((∏ᶜ fun j : Fin n ↦ factor F (q (neg j).val)) ⊗
        GrpObj.ker h.hom.hom) ⊗ (∏ᶜ fun j : Fin m ↦ factor F (q (pos j).val))) ≅
          GrpObj.ker f.hom.hom,
        e.hom ≫ GrpObj.kerι f.hom.hom = orderedMap (G 1)
          (fun j : Fin n ↦ factor F (q (neg j).val)) (GrpObj.ker h.hom.hom)
          (fun j : Fin m ↦ factor F (q (pos j).val))
          (fun j ↦ factorι F (q (neg j).val) ≫
            (x 1 (neg j).val).hom.hom.hom ≫ (iU 1 (neg j).val).hom.hom)
          (GrpObj.kerι h.hom.hom ≫ (iT 1).hom.hom)
          (fun j ↦ factorι F (q (pos j).val) ≫
            (x 1 (pos j).val).hom.hom.hom ≫ (iU 1 (pos j).val).hom.hom)) ∧
    (∀ α : Φ 1, IsPullback η[(T 1).X] η[(U 1 α).X]
      (iT 1).hom.hom (iU 1 α).hom.hom) ∧
    IsIso (toUnit (factor F 1)) := by
  sorry

end AlgebraicGeometry.RootMonomial
