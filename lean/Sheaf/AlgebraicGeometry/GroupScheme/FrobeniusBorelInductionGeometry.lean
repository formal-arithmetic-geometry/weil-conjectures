/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
public import Sheaf.AlgebraicGeometry.GroupScheme.RightCosetPresentation
public import Sheaf.AlgebraicGeometry.GroupScheme.LeftTranslationCoaction
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotient
import Sheaf.AlgebraicGeometry.GroupScheme.BorelQuotientProperGeometry
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus

/-! # Frobenius Borel thickenings and restriction of induced functions

Source: Kaneda, On the Frobenius morphism of flag schemes (1994), Sections 2.3--2.5,
printed pp.320--323; subgroup-product descent as expanded in the DAG proof.
(blueprint: lem-sfb-frobenius-borel-induction-geometry)

The helpers specialize existing base change, sheafification and rational-coaction
interfaces. Every subgroup is fixed by a scheme-theoretic pullback square. The map
called Frobenius is fixed by its absolute-Frobenius first projection. In particular,
none of the existential morphisms substitutes an arbitrary map for a canonical map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj TensorProduct

namespace AlgebraicGeometry.FrobeniusBorelInduction

/-- Base change of group schemes along the specified iterated field Frobenius.
The second projection supplies the F-structure and mapGrp supplies the base-changed
operations. On affine coordinates this is C tensor over F with its q-power F-action.
Source: Kaneda, introduction p.315 and Section 2.5, p.322.
(blueprint: lem-sfb-frobenius-borel-induction-geometry) -/
def twistFunctor (F : Type u) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (r : ℕ) :
    Grp (Over (Spec (.of F))) ⥤ Grp (Over (Spec (.of F))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom
    (iterateFrobeniusOfPrime F (Fact.out : p.Prime) (CharP.cast_eq_zero F p) r)))).mapGrp

/-- The twisted flag scheme is the fppf quotient by the Frobenius Borel thickening,
and restriction gives the stated equivariant linear equivalence of actual induced
function spaces. All inverse images and intersections are scheme-theoretic.

Source: Kaneda, Sections 2.3--2.5, printed pp.320--323; the explicit restriction
isomorphism is the subgroup-product descent argument recorded in the DAG.
(blueprint: lem-sfb-frobenius-borel-induction-geometry)

Proof plan:
1. Frobenius on the algebraically closed field is an automorphism. Base change
   preserves the group and Borel hypotheses. Apply
   lem-sfb-algebraic-group-homogeneous-quotient and
   lem-sfb-borel-quotient-proper-geometry to the twisted Borel inclusion to obtain
   the proper geometrically integral flag quotient and its Borel torsor.
2. By lem-sfb-smooth-connected-group-frobenius-flat the relative Frobenius of S
   is finite and fppf. Compose the coverings using
   lem-sfb-space-fppf-covering-calculus. The Borel torsor identity gives the
   kernel pair of the composite, with inverse (g,g') mapping to (g,g inverse g').
   Finite affine covers give quasi-compactness. The fppf coset sheaf is therefore
   represented by Q. Lemmas lem-trf-fppf-covering-base-change,
   lem-trf-fppf-covering-is-fpqc and lem-weil-pbc-fpqc-representable-descent give
   the unique descent of invariant morphisms to every F-scheme.
3. Apply the smooth-connected Frobenius lemma also to B. On the fpqc cover
   W = H times over B-twist with B, write h = l b with l = h b inverse in S_r.
   For f on L define g_0(h,b) = chi(b) inverse times f(h b inverse).
   On two lifts b,b' the element a = b b' inverse lies in B_r, inside P, and
   l' = l a. The inverse-character factors cancel by covariance of f.
   Lemmas lem-galois-fpqc-covering-base-change and
   lem-weil-pbc-fpqc-representable-descent descend g_0 to a regular function g.
4. The map (h,b) to (hc,bc) proves right B-covariance. Over L the second
   coordinate b lies in P, so g_0(h,b) = f(h). The same base-change and descent
   lemmas give covariance and the restriction identity on all algebras.
5. A covariant function already on H satisfies g(lb) = chi(b) inverse times g(l),
   so descent uniqueness proves the other inverse identity. Restriction preserves
   F-linear combinations. Left and right multiplications commute, so the actual
   left-translation coactions restrict to the two covariance subspaces. Tensoring
   over the field preserves their defining kernels. Restriction commutes with
   these coactions by f(a inverse l) on every algebra. For S trivial both spaces
   are F and restriction is the identity. No step divides by 2 or reduces test
   algebras; this includes characteristic 2. -/
theorem frobenius_borel_induction_geometry
    (F : Type u) [Field F] [IsAlgClosed F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (S T B : Grp (Over (Spec (.of F))))
    (hS : IsSemisimpleGroupScheme S.X)
    (hsc : ∀ (S' : Over (Spec (.of F))) [GrpObj S'],
      IsSemisimpleGroupScheme S' → ∀ (f : S' ⟶ S.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (s : StandardGroupSchemes.affine F A ⟶ S'),
        (x ≫ GrpObj.kerι f) * s = s * (x ≫ GrpObj.kerι f)) → IsIso f)
    (iT : T ⟶ S) (iB : B ⟶ S) (jT : T ⟶ B)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ n : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F n))
    (hB : IsBorelGroupScheme iB.hom.hom) (hTB : jT ≫ iB = iT)
    (r : ℕ) (hr : 1 ≤ r) :
    ∃ (hchar : (p : Γ(S.X.left, ⊤)) = 0)
      (φ : S ⟶ (twistFunctor F p r).obj S),
      φ.hom.hom.left ≫ pullback.fst S.X.hom
        (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime F
          (Fact.out : p.Prime) (CharP.cast_eq_zero F p) r))) =
            S.X.left.iterateFrobenius (Fact.out : p.Prime) hchar r ∧
      ∃ (L H P : Grp (Over (Spec (.of F))))
        (iL : L ⟶ S) (iH : H ⟶ S)
        (toT : L ⟶ (twistFunctor F p r).obj T)
        (toB : H ⟶ (twistFunctor F p r).obj B)
        (k : L ⟶ H) (bH : B ⟶ H) (pB : P ⟶ B) (pL : P ⟶ L),
        IsPullback iL.hom.hom toT.hom.hom φ.hom.hom
          ((twistFunctor F p r).map iT).hom.hom ∧
        IsPullback iH.hom.hom toB.hom.hom φ.hom.hom
          ((twistFunctor F p r).map iB).hom.hom ∧
        IsPullback pB.hom.hom pL.hom.hom iB.hom.hom iL.hom.hom ∧
        IsClosedSubgroupScheme iL.hom.hom ∧ IsClosedSubgroupScheme iH.hom.hom ∧
        IsClosedSubgroupScheme pB.hom.hom ∧ IsClosedSubgroupScheme pL.hom.hom ∧
        k ≫ iH = iL ∧ bH ≫ iH = iB ∧ pB ≫ bH = pL ≫ k ∧
        ∃ (_ : IsAffine L.X.left) (Q : Over (Spec (.of F)))
          (pq : ((twistFunctor F p r).obj S).X ⟶ Q),
          IsProper Q.hom ∧ GeometricallyIntegral Q.hom ∧
          IsRightCosetPresentation ((twistFunctor F p r).map iB) pq ∧
          Flat (φ.hom.hom ≫ pq).left ∧ Surjective (φ.hom.hom ≫ pq).left ∧
          QuasiCompact (φ.hom.hom ≫ pq).left ∧
          IsRightCosetPresentation iH (φ.hom.hom ≫ pq) ∧
          (∀ (Z : Over (Spec (.of F))) (v : S.X ⟶ Z),
            (fst S.X H.X * (snd S.X H.X ≫ iH.hom.hom)) ≫ v = fst S.X H.X ≫ v →
              ∃! w : Q ⟶ Z, φ.hom.hom ≫ pq ≫ w = v) ∧
          ∀ χ : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F),
            ∃ ψ : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F),
              ψ.hom.hom = χ.hom.hom⁻¹ ∧
              ∃ (e : RhoSection.sectionModule H B bH ψ 1 ≃ₗ[F]
                  RhoSection.sectionModule L P pL (pB ≫ ψ) 1)
                (cH : RhoSection.sectionModule H B bH ψ 1 →ₗ[F]
                  RhoSection.sectionModule H B bH ψ 1 ⊗[F] RhoSection.Coordinate L.X)
                (cL : RhoSection.sectionModule L P pL (pB ≫ ψ) 1 →ₗ[F]
                  RhoSection.sectionModule L P pL (pB ≫ ψ) 1 ⊗[F]
                    RhoSection.Coordinate L.X),
                (∀ f : RhoSection.sectionModule H B bH ψ 1,
                  (e f).val = ((algΓ (.of F)).map k.hom.hom).unop.hom f.val) ∧
                IsLeftTranslationCoaction k (RhoSection.sectionModule H B bH ψ 1) cH ∧
                IsLeftTranslationCoaction (𝟙 L)
                  (RhoSection.sectionModule L P pL (pB ≫ ψ) 1) cL ∧
                e.toLinearMap.rTensor (RhoSection.Coordinate L.X) ∘ₗ cH =
                  cL ∘ₗ e.toLinearMap := by
  sorry

end AlgebraicGeometry.FrobeniusBorelInduction
