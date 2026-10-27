/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.SimplyConnectedCharacterLattice
public import Sheaf.AlgebraicGeometry.GroupScheme.BruhatLongestCellCharts
public import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections
public import WeilConjectures.AlgebraicGeometry.Modules.ResidueFiber
public import Mathlib.Topology.Irreducible
import WeilConjectures.AlgebraicGeometry.EffectiveCartier

/-! # Fundamental flag sections and the Bruhat boundary

Source: Milne, Algebraic Groups (2017), Remark 22.49, printed p.480;
Brion--Kumar, Frobenius Splitting Methods, Section 2.1 (6)--(7), p.63,
and Exercises 2.2.E(2)--(3), pp.70--71.
(blueprint: lem-sfb-fundamental-flag-boundary-sections)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

open Classical in
/-- Nonzero sections of the individual fundamental homogeneous bundles cut out exactly
the distinct irreducible components of the complement of the longest Bruhat cell.
The auxiliary family Z names their zero sets in the actual residue-field fibres.
The components on the boundary subtype are mapped into Q by its inclusion.
The automorphism nT is conjugation by the chosen representative n₀, and hlongest
says its inverse carries the B-positive characters to their negatives. The characters
χ specify the negative fundamental weights, so their quotient action multiplies z
by the positive fundamental character. Every presentation of these bundles is allowed.

Source: Milne, Remark 22.49, p.480 (with its opposite-positive-system warning);
Brion--Kumar, Section 2.1 (6)--(7) and Exercises 2.2.E(2)--(3), pp.63,70--71.
(blueprint: lem-sfb-fundamental-flag-boundary-sections)

Proof plan:
1. Apply lem-sfb-opposite-schubert-picard-basis: the opposite Cartier divisors E_i
   have degree vectors δ_ij on the simple Schubert curves, and degree identifies
   Pic(Q) with the integer lattice. Their n₀-translates D_i have exactly the
   pairwise distinct irreducible supports comprising the Bruhat boundary.
2. By lem-sfb-simply-connected-character-lattice the fundamental characters are
   genuine characters. Apply lem-sfb-homogeneous-line-schubert-curve-degree to
   ω_i. The quotient sign gives degree δ_ij for M_ω_i. Injectivity of the degree
   map identifies M_ω_i with O_Q(E_i).
3. Use def-pc-divisor-line-bundle: the inclusion I_E_i → O_Q is a section t_i
   of the dual ideal. In a local frame with I_E_i=(f), it is f times the dual
   frame, so its residue-fibre zero set is precisely |E_i|. Transport t_i by
   the preceding line-bundle isomorphism and then by n₀ using the left action
   of lem-sfb-homogeneous-line-bundle-sections. Fibre isomorphisms preserve zero,
   giving Z(s_i)=|D_i|.
4. The component description in step 1 gives closedness, irreducibility,
   distinctness, exhaustion of the components, and the displayed union.
   Each s_i is nonzero since its fibre is nonzero on the nonempty open cell.
   For the trivial group the simple-root support and the boundary are empty,
   so the empty section family satisfies the same assertion. No step restricts
   the characteristic or chooses an ordering of the Schubert components. -/
theorem exists_fundamental_flag_boundary_sections
    {F : Type u} [Field F] [IsAlgClosed F]
    (G : Grp (Over (Spec (.of F)))) (hG : IsSemisimpleGroupScheme G.X)
    (hsc : ∀ (G' : Over (Spec (.of F))) [GrpObj G'],
      IsSemisimpleGroupScheme G' → ∀ (f : G' ⟶ G.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (g : StandardGroupSchemes.affine F A ⟶ G'),
        (x ≫ GrpObj.kerι f) * g = g * (x ≫ GrpObj.kerι f)) → IsIso f)
    (T B : Grp (Over (Spec (.of F)))) (iT : T ⟶ G) (iB : B ⟶ G) (j : T ⟶ B)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (hB : IsBorelGroupScheme iB.hom.hom) (hj : j ≫ iB = iT)
    [IsCommMonObj T.X] [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    (aG : ModObj T.X G.X) (aB : ModObj T.X B.X)
    (haG : aG.smul = (iT.hom.hom ⊗ₘ 𝟙 G.X) ≫ CategoryTheory.GrpObj.conj G.X)
    (haB : aB.smul = (j.hom.hom ⊗ₘ 𝟙 B.X) ≫ CategoryTheory.GrpObj.conj B.X)
    (Φ : Finset (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    (P : RootDatum Φ
      (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)))
    (b : P.Base)
    (hroot : ∀ α : Φ, P.root α = α.val)
    (hpair : ∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (P.toLinearMap χ ν))
    (hweights : ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ T G aG χ.toMul ≠ ⊥)
    (hpositive : ∀ α : Φ,
      b.IsPos α ↔ @TorusCharacterTangent.weightSpace F _ T B aB α.val.toMul ≠ ⊥)
    (ω : b.support → Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (hω : ∀ i j : b.support, P.toLinearMap (ω i) (P.coroot j) =
      if i = j then 1 else 0)
    (U : Grp (Over (Spec (.of F)))) (iU : U ⟶ B) (p : B ⟶ T)
    (hU : IsClosedSubgroupScheme iU.hom.hom ∧ IsNormalSubgroupScheme iU.hom.hom ∧
      Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧ SolvableGroupStructure.IsUnipotent U ∧
      ∀ (V : Grp (Over (Spec (.of F)))) (iV : V ⟶ B),
        IsClosedSubgroupScheme iV.hom.hom → IsNormalSubgroupScheme iV.hom.hom →
        Smooth V.X.hom → ConnectedSpace V.X.left → SolvableGroupStructure.IsUnipotent V →
        ∃ f : V ⟶ U, f ≫ iU = iV)
    (hp : j ≫ p = 𝟙 T)
    (hkernel : IsPullback iU.hom.hom (toUnit U.X) p.hom.hom η[T.X])
    (hsemidirect : IsIso ((fst U.X T.X ≫ iU.hom.hom) * (snd U.X T.X ≫ j.hom.hom)))
    (Q : Over (Spec (.of F))) (π : G.X ⟶ Q)
    (hπflat : Flat π.left) (hπsurj : Surjective π.left)
    (hπinv : (fst G.X B.X * (snd G.X B.X ≫ iB.hom.hom)) ≫ π = fst G.X B.X ≫ π)
    (hπtorsor : IsPullback (fst G.X B.X)
      (fst G.X B.X * (snd G.X B.X ≫ iB.hom.hom)) π π)
    (n₀ : RankOneRoots.normalizer iT) (nT : Aut T)
    (hnT : ∀ (A : Over (Spec (.of F))) (t : A ⟶ T.X),
      t ≫ nT.hom.hom.hom ≫ iT.hom.hom =
        (toUnit A ≫ n₀.val) * (t ≫ iT.hom.hom) * (toUnit A ≫ n₀.val)⁻¹)
    (hlongest :
      Set.image (fun α : Φ ↦ nT.inv.hom.hom ≫ α.val.toMul.hom.hom)
        {α : Φ | b.IsPos α} =
      Set.image (fun α : Φ ↦ α.val.toMul.hom.hom⁻¹) {α : Φ | b.IsPos α})
    (C : Over (Spec (.of F))) (c : C ⟶ Q) (eC : U.X ≅ C)
    (hc : IsOpenImmersion c.left)
    (hcell : eC.hom ≫ c = ((iU.hom.hom ≫ iB.hom.hom) * (toUnit U.X ≫ n₀.val)) ≫ π)
    (χ : b.support → (B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (hχ : ∀ i, (χ i).hom.hom = (p ≫ (ω i).toMul).hom.hom⁻¹)
    (M : ∀ i, AssociatedCharacterLineBundle.Presentation G B iB Q π (χ i)) :
    ∃ (s : ∀ i : b.support, Γ((M i).L, ⊤)) (Z : b.support → Set Q.left),
      (∀ i, s i ≠ 0) ∧
      (∀ i, Z i = {x : Q.left | Scheme.Modules.residueValue (s i) x (Set.mem_univ x) = 0}) ∧
      (∀ i, IsClosed (Z i) ∧ IsIrreducible (Z i)) ∧
      Function.Injective Z ∧
      Set.range Z = Set.image (fun D : Set ((Set.range c.left)ᶜ : Set Q.left) ↦
        Subtype.val '' D) (irreducibleComponents ((Set.range c.left)ᶜ : Set Q.left)) ∧
      (Set.range c.left)ᶜ = ⋃ i, Z i := by
  sorry

end AlgebraicGeometry
