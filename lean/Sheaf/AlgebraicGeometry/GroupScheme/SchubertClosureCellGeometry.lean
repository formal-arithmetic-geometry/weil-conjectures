module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
public import Sheaf.AlgebraicGeometry.GroupScheme.BruhatLongestCellCharts
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
import Sheaf.AlgebraicGeometry.GroupScheme.BorelRootProductCoordinates
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
import Sheaf.AlgebraicGeometry.GroupScheme.BottSamelsonGalleryGeometry
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.DenseCompactification
import Mathlib.RingTheory.KrullDimension.Polynomial

/-! # Schubert closure order and complementary tangent spaces

Source: Brion--Kumar, Section 2.1, pp.61--63, equations (2)--(6);
Milne, Algebraic Groups (2017), 21.70--21.79, pp.446--449.
(blueprint: lem-sfb-schubert-closure-cell-geometry)

Cells are pinned on geometric points. Reduced closures use the existing vanishing ideal.
The tangent equivalence is pinned on every Lie vector by the actual orbit-map formula.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.Schubert

/-- Minimum simple-word length, including the empty word. Generation is asserted below,
so the infimum is attained for every Weyl element.
Source: Brion--Kumar 2.1, p.62 (blueprint: lem-sfb-schubert-closure-cell-geometry). -/
def wordLength {W I : Type u} [Group W] (s : I → W) (w : W) : ℕ :=
  sInf {m | ∃ l : List I, (l.map s).prod = w ∧ l.length = m}

/-- The reduced-subword relation, defined before any order structure is asserted.
Source: Brion--Kumar 2.1, pp.62--63
(blueprint: lem-sfb-schubert-closure-cell-geometry). -/
def SubwordLE {W I : Type u} [Group W] (s : I → W) (x w : W) : Prop :=
  ∃ a b : List I, a.Sublist b ∧ (a.map s).prod = x ∧ (b.map s).prod = w ∧
    a.length = wordLength s x ∧ b.length = wordLength s w

/-- Reduced induced closed scheme on the closure of an immersed cell.
Source: Brion--Kumar 2.1, p.62; Stacks 01IZ
(blueprint: lem-sfb-schubert-closure-cell-geometry). -/
def reducedClosure {F : Type u} [Field F] {Q C : Over (Spec (.of F))}
    (c : C ⟶ Q) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal
    (TopologicalSpace.Closeds.closure (Set.range c.left))).subscheme

/-- The image of Lie(B) under conjugation by a rational normalizer representative.
The formula uses tangent points and retains the group scheme in every characteristic.
Source: Milne 21.73 and 21.79 (blueprint: lem-sfb-schubert-closure-cell-geometry). -/
def conjugateLie {F : Type u} [Field F] {G B : Grp (Over (Spec (.of F)))}
    (iB : B ⟶ G) (n : 𝟙_ (Over (Spec (.of F))) ⟶ G.X) :
    Submodule F (GrpObj.Lie G.X) :=
  Submodule.span F {v | ∃ b : GrpObj.Lie B.X,
    GrpObj.tangentPoint v =
      (toUnit _ ≫ n) * (GrpObj.tangentPoint b ≫ iB.hom.hom) * (toUnit _ ≫ n)⁻¹}

/-- Bruhat subword order, affine cells, integral reduced closures and their tangent spaces.
Source: Brion--Kumar 2.1, pp.61--63; Milne 21.70--21.79, pp.446--449.
(blueprint: lem-sfb-schubert-closure-cell-geometry)

Proof plan:
1. Use reductive-borel-pair-structure and weyl-reflection-realization. Average a real
   inner product over W; simple-root-reflection-generation gives simple generation.
2. Root-sign-word-deletion proves length equals the number of inverted positive roots,
   length(w₀w)=N-length(w), and extraction of reduced subwords from arbitrary words.
3. Flag-torus-fixed-geometry and projective-attracting-cells identify both orbit families
   with the attracting cells for opposite regular cocharacters. Borel-root-product-
   coordinates and reductive-root-subgroup-parametrizations contract the positive radical.
4. Bott-samelson-gallery-geometry and simple-bruhat-double-coset-product identify the proper
   endpoint image of any reduced word with the closure of its dense open cell.
5. Proper-fp-permanence and solvable-proper-fixed-point give a torus-fixed gallery over
   every fixed flag in that image. Fixed galleries are exactly the subexpressions.
6. Extract reduced subwords. This proves expression independence and the closure formula.
   Closure inclusion gives transitivity; disjoint open dense cells give antisymmetry;
   equal-length subwords coincide, giving strict length growth.
7. Reduced-induced-closed-subscheme makes each closure reduced; irreducibility follows
   from its affine dense cell. Dense-open-dimension-comparison and noetherian-polynomial-
   dimension give its dimension. Local closedness makes the cell open in its closure.
8. Translate by n₀ and use longest-subword-order-duality for the opposite closure formula.
   The translated longest cell is the open dense opposite identity cell.
9. Differentiate the locally trivial right B-torsor orbit map. Its kernel is Ad(n_w)Lie(B).
   Apply the attracting functor to dual numbers: positive, respectively negative,
   character weights give exactly the two tangent subspaces, which are complementary.
10. Empty roots give W={1}, Q=A⁰, zero tangent spaces, and the empty reduced word.
    Every argument uses torus characters, so no characteristic is excluded. -/
theorem schubert_closure_cell_geometry
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
    (w₀ : RankOneRoots.Weyl iT)
    (hw₀ : Set.image
      (fun α : {α : Φ // base.IsPos α} ↦ (act w₀).inv ≫ α.val.val.toMul) Set.univ =
      Set.image (fun α : {α : Φ // base.IsPos α} ↦ (-α.val.val).toMul) Set.univ) :
    (∀ w : RankOneRoots.Weyl iT, ∃ l : List base.support, (l.map s).prod = w) ∧
    (∀ x, SubwordLE s x x) ∧
    (∀ x y z, SubwordLE s x y → SubwordLE s y z → SubwordLE s x z) ∧
    (∀ x y, SubwordLE s x y → SubwordLE s y x → x = y) ∧
    (∀ (w : RankOneRoots.Weyl iT) (b : List base.support),
      (b.map s).prod = w → b.length = wordLength s w →
      ∀ x : RankOneRoots.Weyl iT, SubwordLE s x w ↔
        ∃ a : List base.support, a.Sublist b ∧ (a.map s).prod = x ∧
          a.length = wordLength s x) ∧
    (∀ x w : RankOneRoots.Weyl iT,
      SubwordLE s x w → x ≠ w → wordLength s x < wordLength s w) ∧
    wordLength s w₀ = Nat.card {α : Φ // base.IsPos α} ∧
    ∃ (C Cminus : RankOneRoots.Weyl iT → Over (Spec (.of F)))
      (c : ∀ w, C w ⟶ Q) (cminus : ∀ w, Cminus w ⟶ Q),
      (∀ w, IsImmersion (c w).left ∧ IsImmersion (cminus w).left ∧
        Smooth (C w).hom ∧ Smooth (Cminus w).hom ∧
        Nonempty (C w ≅ Over.mk
          (AffineSpace (ULift.{u} (Fin (wordLength s w))) (Spec (.of F)) ↘ Spec (.of F))) ∧
        Nonempty (Cminus w ≅ Over.mk
          (AffineSpace (ULift.{u} (Fin (Nat.card {α : Φ // base.IsPos α} -
            wordLength s w))) (Spec (.of F)) ↘ Spec (.of F)))) ∧
      (∀ (K : Type u) [Field K] [Algebra F K] [IsAlgClosed K]
        (w : RankOneRoots.Weyl iT) (x : StandardGroupSchemes.affine F K ⟶ Q),
        ((∃ z : StandardGroupSchemes.affine F K ⟶ C w, z ≫ c w = x) ↔
          ∃ b : StandardGroupSchemes.affine F K ⟶ B.X,
            x = ((b ≫ iB.hom.hom) * (toUnit _ ≫ (n w).val)) ≫ π) ∧
        ((∃ z : StandardGroupSchemes.affine F K ⟶ Cminus w, z ≫ cminus w = x) ↔
          ∃ b : StandardGroupSchemes.affine F K ⟶ B.X,
            x = ((toUnit _ ≫ (n w₀).val) * (b ≫ iB.hom.hom) *
              (toUnit _ ≫ (n w₀).val)⁻¹ * (toUnit _ ≫ (n w).val)) ≫ π)) ∧
      (∀ x : Q.left, ∃! w, x ∈ Set.range (c w).left) ∧
      (∀ x : Q.left, ∃! w, x ∈ Set.range (cminus w).left) ∧
      IsOpenImmersion (cminus 1).left ∧ DenseRange (cminus 1).left ∧
      (∀ w, IsIntegral (reducedClosure (c w)) ∧
        IsIntegral (reducedClosure (cminus w)) ∧
        topologicalKrullDim (reducedClosure (c w)) = (wordLength s w : WithBot ℕ∞) ∧
        topologicalKrullDim (reducedClosure (cminus w)) =
          (Nat.card {α : Φ // base.IsPos α} - wordLength s w : ℕ) ∧
        closure (Set.range (c w).left) =
          ⋃ x : {x : RankOneRoots.Weyl iT // SubwordLE s x w}, Set.range (c x.val).left ∧
        closure (Set.range (cminus w).left) =
          ⋃ x : {x : RankOneRoots.Weyl iT // SubwordLE s w x},
            Set.range (cminus x.val).left ∧
        IsOpen (Subtype.val ⁻¹' Set.range (c w).left :
          Set (closure (Set.range (c w).left))) ∧
        IsOpen (Subtype.val ⁻¹' Set.range (cminus w).left :
          Set (closure (Set.range (cminus w).left)))) ∧
      ∀ w : RankOneRoots.Weyl iT,
        ∃ E : (GrpObj.Lie G.X ⧸ conjugateLie iB (n w).val) ≃+
          schemeTangentSpace F Q.left Q.hom
            (((n w).val ≫ π).left (IsLocalRing.closedPoint F)),
          (∀ (a : F) (v : GrpObj.Lie G.X ⧸ conjugateLie iB (n w).val),
            E (a • v) =
              ((StructureSheaf.toStalk F
                (Q.hom (((n w).val ≫ π).left (IsLocalRing.closedPoint F))) ≫
                Q.hom.stalkMap (((n w).val ≫ π).left (IsLocalRing.closedPoint F)) ≫
                Q.left.residue (((n w).val ≫ π).left (IsLocalRing.closedPoint F))).hom a) •
                  E v) ∧
          (∀ v : GrpObj.Lie G.X,
            (E ((conjugateLie iB (n w).val).mkQ v)).val =
              Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom
                (StructureSheaf.toStalk F
                  (Q.hom (((n w).val ≫ π).left (IsLocalRing.closedPoint F))) ≫
                  Q.hom.stalkMap (((n w).val ≫ π).left (IsLocalRing.closedPoint F)) ≫
                  Q.left.residue (((n w).val ≫ π).left (IsLocalRing.closedPoint F))).hom)) ≫
                ((GrpObj.tangentPoint v * (toUnit _ ≫ (n w).val)) ≫ π).left) ∧
          (∀ v : GrpObj.Lie G.X ⧸ conjugateLie iB (n w).val,
            (∃ t : Spec (.of (DualNumber
                (Q.left.residueField (((n w).val ≫ π).left (IsLocalRing.closedPoint F))))) ⟶
                (C w).left,
              t ≫ (c w).left = (E v).val) ↔
              v ∈ Submodule.map (conjugateLie iB (n w).val).mkQ
                (⨆ (α : Φ) (_ : base.IsPos α)
                  (_ : ¬ ∃ β : Φ, base.IsPos β ∧
                    (act w).inv ≫ β.val.toMul = α.val.toMul),
                    @TorusCharacterTangent.weightSpace F _ T G aG α.val.toMul)) ∧
          (∀ v : GrpObj.Lie G.X ⧸ conjugateLie iB (n w).val,
            (∃ t : Spec (.of (DualNumber
                (Q.left.residueField (((n w).val ≫ π).left (IsLocalRing.closedPoint F))))) ⟶
                (Cminus w).left,
              t ≫ (cminus w).left = (E v).val) ↔
              v ∈ Submodule.map (conjugateLie iB (n w).val).mkQ
                (⨆ (α : Φ) (_ : ¬ base.IsPos α)
                  (_ : ¬ ∃ β : Φ, base.IsPos β ∧
                    (act w).inv ≫ β.val.toMul = α.val.toMul),
                    @TorusCharacterTangent.weightSpace F _ T G aG α.val.toMul)) ∧
          IsCompl
            (Submodule.map (conjugateLie iB (n w).val).mkQ
              (⨆ (α : Φ) (_ : base.IsPos α)
                (_ : ¬ ∃ β : Φ, base.IsPos β ∧
                  (act w).inv ≫ β.val.toMul = α.val.toMul),
                    @TorusCharacterTangent.weightSpace F _ T G aG α.val.toMul))
            (Submodule.map (conjugateLie iB (n w).val).mkQ
              (⨆ (α : Φ) (_ : ¬ base.IsPos α)
                (_ : ¬ ∃ β : Φ, base.IsPos β ∧
                  (act w).inv ≫ β.val.toMul = α.val.toMul),
                    @TorusCharacterTangent.weightSpace F _ T G aG α.val.toMul)) := by
  sorry

end AlgebraicGeometry.Schubert
