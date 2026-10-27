module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.BruhatLongestCellCharts
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
public import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Sheaf.AlgebraicGeometry.GroupScheme.StandardParabolicLeviCharts
import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage
import Sheaf.AlgebraicGeometry.GroupScheme.CentralIsogenyBorelRootCompatibility
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry
import Sheaf.AlgebraicGeometry.GroupScheme.BorelRootProductCoordinates
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre

/-! # Coroot degree on simple Schubert curves

Source: Brion--Kumar, Section 2.1, pp.62--63, equation (7), and Exercise 2.2.E(3), p.71;
Milne, Algebraic Groups (2017), Theorem 21.11(b),(e), pp.429--430, and 21.24, p.432.
(blueprint: lem-sfb-homogeneous-line-schubert-curve-degree)

SL2 maps use the natural matrix-point interface of RankOneRoots.SL2Hom. The quotient
SL2/B2 is identified with the existing projective line by its actual first-column map.
The reduced closed subscheme is specified by its topological image and reducedness.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The rank-one map identifies the simple Schubert curve with SL2/B2 = P1 by the first
column, and pulls M_λ back to the twist of degree <λ,α∨>, with the same integer degree.
The character χ below is -λp, expressed by pointwise inversion. The retraction p is
canonical: every B-character is determined by its restriction to T. The unused longest
cell is setup from the Bruhat theorem, rather than additional data for this calculation.

Source: Brion--Kumar, Section 2.1, pp.62--63, equation (7), Exercise 2.2.E(3), p.71;
Milne, Theorem 21.11(b),(e), pp.429--430, 21.24, p.432.
(blueprint: lem-sfb-homogeneous-line-schubert-curve-degree)

Proof plan:
1. For I={α}, lem-sfb-standard-parabolic-levi-charts gives P=R⋊H and B=R⋊B_H.
   Lemma lem-sfb-reductive-rank-one-reflections gives the SL2 map into H with diagonal
   α∨, upper root subgroup U_α, central kernel, and image H_der. Upper triangular
   matrices factor into diagonal and upper unipotent matrices, so their images lie in B.
2. The SL2/PGL2/GL2 models of lem-sfb-split-rank-one-classification and the matrix-limit
   condition of lem-sfb-regular-cocharacter-borel-description identify B_H as upper
   triangular. Central torus factors lie in B_H. In GL2, factor g as
   [g diag(det(g)⁻¹,1)] diag(det(g),1). Thus H_der/(H_der∩B_H)=H/B_H as fppf quotients.
3. The central kernel in SL2 is contained in μ2: commuting with universal upper and lower
   unipotents forces a scalar matrix, whose scalar square is one. This includes char 2.
   Use lem-sfb-split-torus-subgroups-diagonalizable and
   lem-sfb-affine-homomorphism-flat-image. Theorems
   lem-sfb-central-isogeny-borel-root-compatibility and
   lem-sfb-multiplicative-isogeny-borel-comparison give SL2/B2 ≅ H/B_H.
4. The first-column map has sections a0(t)=[[1,0],[t,1]] and a1(s)=[[s,-1],[1,0]].
   Equal first-column lines mean right multiplication by B2 locally; these sections
   identify the fppf quotient with P1 over all test algebras.
5. The semidirect products identify P/B with H/B_H by rhB ↦ hB_H. By
   lem-sfb-homogeneous-orbit-quotient-geometry, P/B → G/B is a monomorphism. Its source
   is proper and its target separated (lem-sfb-reductive-borel-pair-structure), so
   lemma-nagata-proper-to-separated-target and lem-pc-proper-monomorphism-closed make
   it a closed immersion. Its source is P1, hence reduced.
6. The rank-one matrix models have just the fixed first-column line and its affine-line
   complement as upper triangular orbits. The antidiagonal representative gives s_α
   (lem-sfb-reductive-rank-one-reflections); its B-orbit is dense. Thus the reduced
   image is exactly the reduced closure of B n_s B/B, independently of representative.
7. By the pairing identity, λ(α∨(a))=a^m. By lem-sfb-borel-root-product-coordinates,
   λp is trivial on the upper root subgroup. Pulling back the quotient presentation of
   lem-sfb-homogeneous-line-bundle-sections gives (g,z)∼(gb,a^m z). The map is
   [g,z] ↦ (gB2,[v(g),z]); on the two standard sections it is the identity on fibres.
8. Direct multiplication gives a0(t)⁻¹a1(t⁻¹)=[[t⁻¹,-1],[0,t]]. Therefore the frames
   satisfy e0=t^(-m)e1, exactly def-pc-projective-space-twist. Tautological frames
   (1,t), (t⁻¹,1) have ratio t, so their duals have ratio t⁻¹. Tensor powers and
   duals give the asserted sign for all integers m.
9. Lemma lem-pc-projective-space-twist-cohomology gives χ(O(m))=m+1: H0 has dimension
   m+1 for m≥0, all groups vanish for m=-1, and H1 has dimension -m-1 for m≤-2.
   Since χ(O)=1, def-pc-degree-line-bundle gives degree m. The isomorphism preserves
   cohomology. No division or characteristic hypothesis occurs; an empty base has
   no indexed assertion. -/
theorem homogeneousLine_schubertCurve_degree
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
    (p : B ⟶ T) (hp : j ≫ p = 𝟙 T)
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
    (hn : ∀ w, QuotientGroup.mk (n w) = w) :
    ∀ α : base.support,
      ∃ (v : RankOneRoots.SL2Hom G) (R : Over (Spec (.of F))) (iR : R ⟶ Q)
        (e : (ProjectiveLine (Spec (.of F))).asOver (Spec (.of F)) ≅ R),
        IsClosedImmersion iR.left ∧ IsReduced R.left ∧
        Set.range iR.left = closure (Set.range
          (((iB.hom.hom * (toUnit B.X ≫ (n (s α)).val)) ≫ π).left)) ∧
        (∀ (A : CommAlgCat.{u} F)
          (z : StandardGroupSchemes.affine F A ⟶ StandardGroupSchemes.multiplicative F)
          (g : Matrix.SpecialLinearGroup (Fin 2) A),
          g.val = !![RankOneRoots.multiplicativeValue A z, 0;
            0, RankOneRoots.multiplicativeValue A z⁻¹] →
          v.app A g = z ≫ (D.coroot α.val).toMul.hom.hom ≫ iT.hom.hom) ∧
        (∀ (A : CommAlgCat.{u} F) (g : Matrix.SpecialLinearGroup (Fin 2) A),
          g.val 1 0 = 0 → v.app A g ∈
            RankOneRoots.pointImage iB (StandardGroupSchemes.affine F A)) ∧
        (∀ (A : CommAlgCat.{u} F) (g : Matrix.SpecialLinearGroup (Fin 2) A),
          ∃ h : Ideal.span (Set.range (fun k : ULift.{u} (Fin 2) ↦
            (Scheme.ΓSpecIso (.of A)).inv (g.val k.down 0))) = ⊤,
          ProjectiveSpace.homOfSections (StandardGroupSchemes.affine F A).hom
            (fun k : ULift.{u} (Fin 2) ↦
              (Scheme.ΓSpecIso (.of A)).inv (g.val k.down 0)) h ≫ e.hom.left ≫ iR.left =
              (v.app A g ≫ π).left) ∧
        ∀ (lam : RankOneRoots.Character T) (χ : RankOneRoots.Character B),
          χ.hom.hom = (p ≫ lam).hom.hom⁻¹ →
          ∀ P : AssociatedCharacterLineBundle.Presentation G B iB Q π χ,
            Nonempty ((Scheme.Modules.pullback e.hom.left).obj
              ((Scheme.Modules.pullback iR.left).obj P.L) ≅
                ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of F))
                  (D.toLinearMap (Additive.ofMul lam) (D.coroot α.val))) ∧
            @Scheme.Modules.degree F _ R.left ⟨R.hom⟩
              ((Scheme.Modules.pullback iR.left).obj P.L) =
                D.toLinearMap (Additive.ofMul lam) (D.coroot α.val) := by
  sorry

end AlgebraicGeometry
