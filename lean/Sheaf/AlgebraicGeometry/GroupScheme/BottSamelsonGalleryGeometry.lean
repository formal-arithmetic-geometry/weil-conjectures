module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.BruhatLongestCellCharts
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Sheaf.AlgebraicGeometry.GroupScheme.StandardParabolicLeviCharts
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition

/-! # Bott--Samelson galleries, endpoint maps and fixed subexpressions

Source: Brion--Kumar, Frobenius Splitting Methods, Section 2.2.1, pp.64--66,
equations (1)--(8), and the opening paragraph of Section 2.2.
(blueprint: lem-sfb-bott-samelson-gallery-geometry)

The quotient is specified by its fppf sheaf universal property. All products are ordered
by the word, including the empty word. Fixedness is tested on every scheme over the
point's field, and makes no assertion about reducedness of a fixed subscheme.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.BottSamelson

/-- The preceding B-coordinate, with b₀ = 1, in the twisted quotient action.
Source: Brion--Kumar 2.2.1, equation (1).
(blueprint: lem-sfb-bott-samelson-gallery-geometry) -/
def previous {H : Type u} [Group H] {m : ℕ} (b : Fin m → H) (k : Fin m) : H :=
  if k.val = 0 then 1 else b ⟨k.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩

/-- Geometry of the iterated minimal-parabolic quotient for every finite word.
Source: Brion--Kumar 2.2.1, pp.64--66, equations (1)--(8), the open-cell and
subsequence paragraphs; characteristic zero is permitted in the opening of 2.2.
(blueprint: lem-sfb-bott-samelson-gallery-geometry)

Proof plan:
1. Apply lem-sfb-standard-parabolic-levi-charts with I = {α}. The rank-one
   projection of lem-sfb-minimal-parabolic-flag-projection supplies its two double
   cosets and the Zariski locally trivial projective-line fibration Q → G/Pα.
   Starting at Spec F, form successive fibre products with these projections
   (def-pc-fibre-product); the last projection is the endpoint.
2. Send a tuple to its cumulative flags. Zariski locally lift each flag using
   lem-sfb-bruhat-longest-cell-charts. The Pα-torsor kernel pair from
   lem-sfb-standard-parabolic-levi-charts makes successive ratios belong to Pα.
   Changing lifts gives exactly b_(j-1)⁻¹ p_j b_j. The inverse local formulas glue
   in the fppf topology, giving the represented quotient, also for the empty word.
   Simultaneous left B-translation of flags is the action on the first factor.
3. Smooth base change (lem-pc-proper-base-change) and lem-trf-smooth-composition
   give smoothness. Use lem-pc-projective-base-change and
   lem-trf-h-projective-composition for projectivity. For integrality use the
   two A[t] charts of each projective line over an integral affine open; their
   intersection A[t,t⁻¹] is nonempty. Trivializing opens intersect because the
   base is irreducible. The endpoint is proper by lem-pc-projective-proper and
   lemma-nagata-proper-to-separated-target, since Q is separated.
4. The rank-one coordinates p = uα(a)n_s b gauge each factor successively and
   uniquely to uα(a)n_s. They give regular inverse affine-space coordinates.
   The locus is open, nonempty and hence dense by integrality. Repetitions in
   the word cause no problem.
5. For a reduced word, lem-sfb-simple-bruhat-double-coset-product identifies
   the product of its open double cosets with B n_w B over every algebraically
   closed extension. Thus the endpoint image of the open locus is C_w.
6. Induct on length for fixed points. A fixed prefix has representative h in
   the normalizer. The last fibre has its torus action conjugated by h. Its
   affine coordinate has nontrivial character α(h⁻¹th); (χ-1)a = 0 in the
   Laurent coordinate ring over K forces a = 0. The other fixed point is B.
   Append 1 or n_s; distinct prefixes and the two distinct fibre points give
   exactly 2^m galleries. The product of representatives has Weyl class the
   subexpression product, so its endpoint is the indicated e_x. This uses
   characters rather than their differentials, including in characteristic two.
-/
theorem bottSamelson_gallery_geometry
    {F : Type u} [Field F] [IsAlgClosed F]
    (G T B : Grp (Over (Spec (.of F)))) (hG : IsSemisimpleGroupScheme G.X)
    (hsc : ∀ (G' : Over (Spec (.of F))) [GrpObj G'],
      IsSemisimpleGroupScheme G' → ∀ (f : G' ⟶ G.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (g : StandardGroupSchemes.affine F A ⟶ G'),
        (x ≫ GrpObj.kerι f) * g = g * (x ≫ GrpObj.kerι f)) → IsIso f)
    (iT : T ⟶ G) (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (iB : B ⟶ G) (hB : IsBorelGroupScheme iB.hom.hom)
    (j : T ⟶ B) (hj : j ≫ iB = iT)
    [IsCommMonObj T.X] [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    (aG : ModObj T.X G.X) (aB : ModObj T.X B.X)
    (haG : aG.smul = (iT.hom.hom ⊗ₘ 𝟙 G.X) ≫ GrpObj.conj G.X)
    (haB : aB.smul = (j.hom.hom ⊗ₘ 𝟙 B.X) ≫ GrpObj.conj B.X)
    (Φ : Finset (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    (D : RootDatum Φ
      (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)))
    (base : D.Base) (hred : D.IsReduced)
    (hroot : ∀ α : Φ, D.root α = α.val)
    (hpair : ∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (D.toLinearMap χ ν))
    (hΦ : ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ T G aG χ.toMul ≠ ⊥)
    (hpos : ∀ α : Φ,
      base.IsPos α ↔ @TorusCharacterTangent.weightSpace F _ T B aB α.val.toMul ≠ ⊥)
    (U : Φ → Grp (Over (Spec (.of F)))) (iU : ∀ α : Φ, U α ⟶ G)
    (hU : ∀ α : Φ,
      IsClosedSubgroupScheme (iU α).hom.hom ∧ Smooth (U α).X.hom ∧
      ConnectedSpace (U α).X.left ∧ @TorusCharacterTangent.IsStable F _ T G aG _ (iU α) ∧
      (GrpObj.differential (iU α).hom.hom).toLinearMap.range =
        @TorusCharacterTangent.weightSpace F _ T G aG α.val.toMul)
    (Q : Over (Spec (.of F))) (π : G.X ⟶ Q)
    (hQ : IsProper Q.hom ∧ LocallyOfFiniteType Q.hom ∧ QuasiCompact Q.hom)
    (hπflat : Flat π.left) (hπsurj : Surjective π.left)
    (hπinv : (fst G.X B.X * (snd G.X B.X ≫ iB.hom.hom)) ≫ π = fst G.X B.X ≫ π)
    (hπtorsor : IsPullback (fst G.X B.X)
      (fst G.X B.X * (snd G.X B.X ≫ iB.hom.hom)) π π)
    (act : RankOneRoots.Weyl iT →* Aut T)
    (hact : ∀ (n : RankOneRoots.normalizer iT) (A : Over (Spec (.of F))) (t : A ⟶ T.X),
      t ≫ (act (QuotientGroup.mk n)).hom.hom.hom ≫ iT.hom.hom =
        (toUnit A ≫ n.val) * (t ≫ iT.hom.hom) * (toUnit A ≫ n.val)⁻¹)
    (s : base.support → RankOneRoots.Weyl iT)
    (hs : ∀ (α : base.support) (χ : RankOneRoots.Character T),
      (act (s α)).inv ≫ χ = (D.reflection α.val (Additive.ofMul χ)).toMul)
    (n : RankOneRoots.Weyl iT → RankOneRoots.normalizer iT)
    (hn : ∀ w, QuotientGroup.mk (n w) = w)
    (m : ℕ) (word : Fin m → base.support) :
    ∃ (P : base.support → Grp (Over (Spec (.of F))))
      (iP : ∀ α, P α ⟶ G) (bP : ∀ α, B ⟶ P α),
      (∀ α, IsClosedSubgroupScheme (iP α).hom.hom ∧ bP α ≫ iP α = iB ∧
        (∀ β : Φ, β.val = -α.val.val → ∃ f : U β ⟶ P α, f ≫ iP α = iU β) ∧
        (∀ (H : Grp (Over (Spec (.of F)))) (k : H ⟶ G),
          IsClosedSubgroupScheme k.hom.hom → (∃ f : B ⟶ H, f ≫ k = iB) →
          (∀ β : Φ, β.val = -α.val.val → ∃ f : U β ⟶ H, f ≫ k = iU β) →
          ∃ f : P α ⟶ H, f ≫ k = iP α)) ∧
      (∀ (α : base.support) (K : Type u) [Field K] [Algebra F K] [IsAlgClosed K],
        (RankOneRoots.pointImage (iP α) (StandardGroupSchemes.affine F K) : Set _) =
          (RankOneRoots.pointImage iB (StandardGroupSchemes.affine F K) : Set _) ∪
          {g | ∃ b c : StandardGroupSchemes.affine F K ⟶ B.X,
            g = (b ≫ iB.hom.hom) * (toUnit _ ≫ (n (s α)).val) * (c ≫ iB.hom.hom)} ∧
        Disjoint (RankOneRoots.pointImage iB (StandardGroupSchemes.affine F K) : Set _)
          {g | ∃ b c : StandardGroupSchemes.affine F K ⟶ B.X,
            g = (b ≫ iB.hom.hom) * (toUnit _ ≫ (n (s α)).val) * (c ≫ iB.hom.hom)}) ∧
      ∃ (Z : Over (Spec (.of F)))
        (q : (∏ᶜ fun k : Fin m ↦ (P (word k)).X) ⟶ Z)
        (ρ : (∏ᶜ fun k : Fin m ↦ (P (word k)).X) ⊗
          (∏ᶜ fun _ : Fin m ↦ B.X) ⟶ ∏ᶜ fun k : Fin m ↦ (P (word k)).X)
        (endpoint : Z ⟶ Q) (aZ : ModObj B.X Z) (aQ : ModObj B.X Q),
        Smooth Z.hom ∧ IsIntegral Z.left ∧ IsProjective Z.hom ∧ IsProper endpoint.left ∧
        (m = 0 → Nonempty (Z ≅ 𝟙_ (Over (Spec (.of F))))) ∧
        (∀ (A : Over (Spec (.of F)))
          (p : A ⟶ ∏ᶜ fun k : Fin m ↦ (P (word k)).X)
          (b : A ⟶ ∏ᶜ fun _ : Fin m ↦ B.X) (k : Fin m),
          lift p b ≫ ρ ≫ Pi.π _ k ≫ (iP (word k)).hom.hom =
            (previous (fun l : Fin m ↦ b ≫ Pi.π _ l ≫ iB.hom.hom) k)⁻¹ *
              (p ≫ Pi.π _ k ≫ (iP (word k)).hom.hom) * (b ≫ Pi.π _ k ≫ iB.hom.hom)) ∧
        Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (.of F))) (yoneda.obj Z) ∧
        (∃ ηq : coequalizer (yoneda.map (fst _ _)) (yoneda.map ρ) ⟶ yoneda.obj Z,
          coequalizer.π _ _ ≫ ηq = yoneda.map q ∧
          ∀ Y : Sheaf (Scheme.fppfTopology.over (Spec (.of F))) (Type u),
            Function.Bijective (fun f : yoneda.obj Z ⟶ Y.obj ↦ ηq ≫ f)) ∧
        (∀ (A : Over (Spec (.of F)))
          (p : A ⟶ ∏ᶜ fun k : Fin m ↦ (P (word k)).X),
          p ≫ q ≫ endpoint = (List.ofFn
            (fun k : Fin m ↦ p ≫ Pi.π _ k ≫ (iP (word k)).hom.hom)).prod ≫ π) ∧
        (∀ (A : Over (Spec (.of F))) (b : A ⟶ B.X) (g : A ⟶ G.X),
          lift b (g ≫ π) ≫ aQ.smul = ((b ≫ iB.hom.hom) * g) ≫ π) ∧
        aZ.smul ≫ endpoint = (𝟙 B.X ⊗ₘ endpoint) ≫ aQ.smul ∧
        (∀ (A : Over (Spec (.of F))) (b : A ⟶ B.X)
          (p : A ⟶ ∏ᶜ fun k : Fin m ↦ (P (word k)).X),
          ∃ p' : A ⟶ ∏ᶜ fun k : Fin m ↦ (P (word k)).X,
            (∀ k : Fin m, p' ≫ Pi.π _ k ≫ (iP (word k)).hom.hom =
              (if k.val = 0 then b ≫ iB.hom.hom else 1) *
                (p ≫ Pi.π _ k ≫ (iP (word k)).hom.hom)) ∧
            p' ≫ q = lift b (p ≫ q) ≫ aZ.smul) ∧
        (∃ (tower : Fin (m + 1) → Over (Spec (.of F)))
          (f : ∀ k : Fin m, tower k.succ ⟶ tower k.castSucc),
          Nonempty (tower 0 ≅ 𝟙_ (Over (Spec (.of F)))) ∧ Nonempty (tower (Fin.last m) ≅ Z) ∧
          ∀ (k : Fin m) (x : (tower k.castSucc).left),
            ∃ (V : Scheme.{u}) (v : V ⟶ (tower k.castSucc).left)
              (e : pullback (f k).left v ≅ ProjectiveLine V),
              IsOpenImmersion v ∧ x ∈ Set.range v ∧
              e.hom ≫ (ProjectiveLine V ↘ V) = pullback.snd (f k).left v) ∧
        ∃ (O : Over (Spec (.of F))) (o : O ⟶ Z),
          IsOpenImmersion o.left ∧ DenseRange o.left ∧
          Nonempty (O ≅ Over.mk
            (AffineSpace (ULift.{u} (Fin m)) (Spec (.of F)) ↘ Spec (.of F))) ∧
          (∀ (K : Type u) [Field K] [Algebra F K] [IsAlgClosed K]
            (p : StandardGroupSchemes.affine F K ⟶ ∏ᶜ fun k : Fin m ↦ (P (word k)).X),
            (∃ z : StandardGroupSchemes.affine F K ⟶ O, z ≫ o = p ≫ q) ↔
              ∀ k : Fin m, ∃ b c : StandardGroupSchemes.affine F K ⟶ B.X,
                p ≫ Pi.π _ k ≫ (iP (word k)).hom.hom =
                  (b ≫ iB.hom.hom) * (toUnit _ ≫ (n (s (word k))).val) * (c ≫ iB.hom.hom)) ∧
          ((∀ l : List base.support,
              (l.map s).prod = (List.ofFn (fun k ↦ s (word k))).prod → m ≤ l.length) →
            ∀ (K : Type u) [Field K] [Algebra F K] [IsAlgClosed K]
              (x : StandardGroupSchemes.affine F K ⟶ Q),
              (∃ z : StandardGroupSchemes.affine F K ⟶ O, z ≫ o ≫ endpoint = x) ↔
                ∃ b : StandardGroupSchemes.affine F K ⟶ B.X,
                  x = ((b ≫ iB.hom.hom) *
                    (toUnit _ ≫ (n ((List.ofFn (fun k ↦ s (word k))).prod)).val)) ≫ π) ∧
          ∀ (K : Type u) [Field K] [Algebra F K] [IsAlgClosed K],
            ∃ c : (Fin m → Bool) → (StandardGroupSchemes.affine F K ⟶ Z),
              Function.Injective c ∧
              (∀ ε : Fin m → Bool,
                ∃ p : StandardGroupSchemes.affine F K ⟶ ∏ᶜ fun k : Fin m ↦ (P (word k)).X,
                  p ≫ q = c ε ∧
                  ∀ k : Fin m, p ≫ Pi.π _ k ≫ (iP (word k)).hom.hom =
                    if ε k then toUnit _ ≫ (n (s (word k))).val else 1) ∧
              (∀ z : StandardGroupSchemes.affine F K ⟶ Z,
                (∀ (A : Over (Spec (.of F))) (f : A ⟶ StandardGroupSchemes.affine F K)
                  (t : A ⟶ T.X),
                  lift (t ≫ j.hom.hom) (f ≫ z) ≫ aZ.smul = f ≫ z) ↔ ∃ ε, c ε = z) ∧
              ∀ ε : Fin m → Bool,
                c ε ≫ endpoint = (toUnit _ ≫
                  (n ((List.ofFn (fun k ↦ if ε k then s (word k) else 1)).prod)).val) ≫ π := by
  sorry

end AlgebraicGeometry.BottSamelson
