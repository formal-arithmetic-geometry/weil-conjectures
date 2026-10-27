module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import Sheaf.AlgebraicGeometry.RelativeProjectiveSpace
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension

/-! # Coefficient pullback of homogeneous polynomial quotients

Source: Stacks Project, Constructions, Tags 01O3, 01N2, 01MY and 07ZK
(blueprint: lem-sfb-polynomial-quotient-proj-cartesian).

A surjective graded map `q` from the specified polynomial algebra presents `B = S/J`,
with `J(V) = ker(q.app V)`. This presentation allows arbitrary quasi-coherent homogeneous
ideals, including degree-zero equations. All relative Proj constructions and projective
spaces are the recorded canonical constructions. `PullbackData` specifies degreewise
scalar extension, with its normalized map `b ↦ 1 ⊗ b`; the extra equations below fix that
map on polynomial representatives and on the actual tensor-pullback sections.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.GradedAlgebraData

namespace AlgebraicGeometry.RelativeProjectiveSpace

/-- Arbitrary coefficient pullback preserves the quotient equations and the specified
closed Proj embedding, including its chart comorphisms and its degreewise module pullback.
Here `q` is the quotient presentation of `B`, so its homogeneous kernel is exactly `J`.
No finite generation of this kernel, flatness of `g`, or injectivity of its pullback occurs.
Source: Stacks Project, Constructions, Tags 01O3, 01N2, 01MY and 07ZK
(blueprint: lem-sfb-polynomial-quotient-proj-cartesian).

Proof:
1. On affine tests V = Spec R, W = Spec R', apply the quasi-coherent cokernel/image
   theorem to J → S and the affine tensor-pullback theorem to J, S and every B_d.
   These are lem-weil-pbc-quasi-coherent-module-cokernel-image,
   lem-weil-pbc-module-pullback-quasi-coherent and
   lem-weil-pbc-module-pullback-affine-sections. Thus the pulled-back ideal is the
   image of R' tensor J, without an injectivity claim.
2. Identify R' tensor R[x] with R'[x] by a tensor p ↦ a p_R'. The inverse expands
   a polynomial as the finite sum of coefficient tensors of its monomials. These
   maps preserve multiplication, the unit and total degree. The image of the ideal
   consists of finite sums a p_R' with p in J, and equals the generated image ideal.
   It is homogeneous because each homogeneous component of p belongs to J.
3. Descend a tensor pbar ↦ a p_R'bar to R' tensor (R[x]/J). Its inverse sends
   coefficients to a tensor 1 and variables to 1 tensor xbar. It kills every
   substituted equation. The composites fix coefficients and variables, hence are
   identities. This proves the graded algebra comparison without flatness.
4. Both formulas commute with affine restriction, on coefficients, variables and
   pure tensors. Glue on affine refinements of overlaps. The same affine pullback
   theorem gives the actual tensor-pullback isomorphisms of all homogeneous sheaves,
   normalized by the section 1 tensor b. Intersections need not be affine.
5. The quotient maps induce the closed immersions by the surjection clause of
   prop-nagata-relative-proj-functoriality. Their coordinate-chart comorphisms are
   quotient localization maps. The variables cover Proj, by
   prop-nagata-proj-standard-open, also when a variable is nilpotent and its chart empty.
6. Apply lemma-nagata-relative-proj-base-change-arbitrary to the polynomial and
   quotient algebras separately. Use def-sfb-relative-proj-iso-of-graded-iso for the
   graded identification in step 3. The comparison on every coordinate chart is
   the map in lem-nagata-affine-proj-scalar-extension: b/x_j^d ↦ b_R'/x_j^d.
7. Quotient then substitute, and substitute then quotient, send every chart fraction
   p/x_j^d to the same fraction p_R'bar/x_j^d. They also agree on coefficients.
   Hence their ring maps, and therefore their scheme maps, agree. This identifies
   the specified closed embeddings, including their scheme structures.
8. The square of the two pullbacks of i is cartesian: a compatible pair (t,p), a
   with i a = p factors uniquely as (t,a). Transport through the canonical Proj
   comparisons of step 6 and the equality in step 7. This gives the displayed
   IsPullback square and both normalized isomorphisms to the chosen fibre products. -/
theorem polynomialQuotient_proj_cartesian
    {U T : Scheme.{u}} (g : T ⟶ U) (n : ℕ) (B : RelativeProjAlgebra U)
    (q : (algebra U n).affineData ⟶ B.affineData)
    (hq : ∀ V : U.affineOpens, Function.Surjective (q.app V)) :
    ∃ (BT : RelativeProjAlgebra T)
      (qT : (algebra T n).affineData ⟶ BT.affineData)
      (hqT : ∀ W : T.affineOpens, Function.Surjective (qT.app W))
      (DS : PullbackData g (algebra U n).affineData (algebra T n).affineData)
      (DB : PullbackData g B.affineData BT.affineData),
      (∀ (V : U.affineOpens) (W : T.affineOpens) (h : W.1 ≤ g ⁻¹ᵁ V.1)
          (p : MvPolynomial (Fin (n + 1)) Γ(U, V.1)),
        DS.map h (affinePolynomialEquiv U n V p) =
          affinePolynomialEquiv T n W (MvPolynomial.map (g.appLE V.1 W.1 h).hom p)) ∧
      (∀ (V : U.affineOpens) (W : T.affineOpens) (h : W.1 ≤ g ⁻¹ᵁ V.1),
        RingHom.ker (qT.app W).toRingHom =
          Ideal.map (DS.map h).toRingHom (RingHom.ker (q.app V).toRingHom)) ∧
      (∀ (V : U.affineOpens) (W : T.affineOpens) (h : W.1 ≤ g ⁻¹ᵁ V.1),
        letI : Algebra Γ(U, V.1) Γ(T, W.1) := (g.appLE V.1 W.1 h).hom.toAlgebra
        ∃ β : TensorProduct Γ(U, V.1) Γ(T, W.1) (B.affineData.obj V) ≃ₐ[Γ(T, W.1)]
            BT.affineData.obj W,
          (∀ b : B.affineData.obj V,
            β (TensorProduct.tmul Γ(U, V.1) (1 : Γ(T, W.1)) b) = DB.map h b) ∧
          (∀ (a : Γ(T, W.1)) (p : MvPolynomial (Fin (n + 1)) Γ(U, V.1)),
            β (TensorProduct.tmul Γ(U, V.1) a (q.app V (affinePolynomialEquiv U n V p))) =
              a • qT.app W (affinePolynomialEquiv T n W
                (MvPolynomial.map (g.appLE V.1 W.1 h).hom p))) ∧
          (∀ d : ℕ, ((B.affineData.grading V d).baseChange Γ(T, W.1)).map β.toLinearMap =
            BT.affineData.grading W d)) ∧
      (∃ e : ∀ d : ℕ, (Scheme.Modules.tensorPullback g).obj (B.piece d) ≅ BT.piece d,
        ∀ (V : U.affineOpens) (W : T.affineOpens) (h : W.1 ≤ g ⁻¹ᵁ V.1)
            (d : ℕ) (b : Γ(B.piece d, V.1)),
          (Sigma.ι BT.piece d ≫ BT.decomposition.hom).app W.1
              ((e d).hom.app W.1
                (((Scheme.Modules.tensorPullback g).obj (B.piece d)).val.map
                  (homOfLE h).op (Scheme.Modules.tensorPullbackSection g (B.piece d) V.1 b))) =
            DB.map h ((Sigma.ι B.piece d ≫ B.decomposition.hom).app V.1 b)) ∧
      IsClosedImmersion
        (relProjMap q (irrelevantLE_of_surjective q hq) : B.affineData.relProj ⟶ scheme U n) ∧
      IsClosedImmersion
        (relProjMap qT (irrelevantLE_of_surjective qT hqT) :
          BT.affineData.relProj ⟶ scheme T n) ∧
      IsPullback (relProjMap qT (irrelevantLE_of_surjective qT hqT))
        DB.relProjComparison DS.relProjComparison (relProjMap q (irrelevantLE_of_surjective q hq)) ∧
      (∀ (V : U.affineOpens) (W : T.affineOpens) (h : W.1 ≤ g ⁻¹ᵁ V.1)
          (j : Fin (n + 1)),
        Proj.awayι (BT.affineData.grading W)
            (DB.map h (q.app V (coordinate U n V j)))
            ((DB.map h).map_mem ((q.app V).map_mem (coordinate_mem U n V j))) (by decide) ≫
            BT.affineData.relProjι W ≫ DB.relProjComparison =
          Spec.map (CommRingCat.ofHom
            (HomogeneousLocalization.Away.map (DB.map h) (q.app V (coordinate U n V j)))) ≫
              Proj.awayι (B.affineData.grading V) (q.app V (coordinate U n V j))
                ((q.app V).map_mem (coordinate_mem U n V j)) (by decide) ≫
                  B.affineData.relProjι V) ∧
      (∀ (V : U.affineOpens) (W : T.affineOpens) (h : W.1 ≤ g ⁻¹ᵁ V.1)
          (j : Fin (n + 1)) (d : ℕ) (b : B.affineData.grading V (d • 1)),
        HomogeneousLocalization.Away.map (DB.map h) (q.app V (coordinate U n V j))
            (HomogeneousLocalization.Away.mk (B.affineData.grading V)
              ((q.app V).map_mem (coordinate_mem U n V j)) d b b.property) =
          HomogeneousLocalization.Away.mk (BT.affineData.grading W)
            ((DB.map h).map_mem ((q.app V).map_mem (coordinate_mem U n V j))) d
            (DB.map h b) ((DB.map h).map_mem b.property)) := by
  sorry

end AlgebraicGeometry.RelativeProjectiveSpace
