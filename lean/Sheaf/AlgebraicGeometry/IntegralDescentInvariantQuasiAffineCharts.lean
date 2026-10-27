module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.FpqcSingletonAffineRefinement
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget
import Mathlib.Topology.Constructible
import Mathlib.Topology.Spectral.Basic
import WeilConjectures.Topology.ProconstructibleClosureSpecialization
import WeilConjectures.AlgebraicGeometry.DescentOrbitSaturated
import Sheaf.AlgebraicGeometry.QuasiAffineTargetLocality
import Sheaf.AlgebraicGeometry.QuasiAffineBaseChange
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent

/-!
# Integral orbit neighbourhoods and invariant quasi-affine charts

Source: Raynaud, Un critère d'effectivité de descente, Theorem 4.1, proof,
printed pp. 5-17--5-21 (blueprint: lem-sfb-integral-descent-invariant-quasiaffine-charts).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Affine neighbourhoods of the integral descent orbits give an invariant open cover
by relatively quasi-affine charts, with the restricted canonical descent data.

Source: Raynaud, Theorem 4.1, proof, printed pp. 5-17--5-21.
(blueprint: lem-sfb-integral-descent-invariant-quasiaffine-charts)

Proof:
1. Localize on an affine open of the locally Noetherian base. Its ring is Noetherian
   (pqf-lem-affine-open-locnoeth). Intersect the affine orbit neighbourhoods with this
   localization: these intersections are quasi-compact quasi-affine opens. Integral
   surjections and fpqc covers survive base change. Use
   lem-galois-fpqc-singleton-affine-refinement to replace the cover by an affine fpqc cover A.
2. For a point x of the model over A, use
   lem-sfb-integral-orbit-finite-diagram-approximation. In its notation the invariant image
   E = g(j_B(L times B)) contains the image of x, and g inverse E is the image of j_B.
   The finite-presentation models X and Z are Noetherian and quasi-separated, by
   pqf-lem-locnoeth-lft and lem-pc-separated-quasi-separated.
3. Base change makes j_B a quasi-compact flat monomorphism. Apply
   lem-sfb-integral-descent-flat-monomorphism-subset to obtain M mapping to X with image E.
   Its integral surjective pullback is affine (lem-weil-pbc-fibre-product-affine-spectra),
   so M is affine by lem-weil-pbc-surjective-universally-closed-affine-target and
   pqf-lem-integral-univclosed. Apply lem-sfb-flat-monomorphism-quasiaffine-neighbourhood
   to enclose E in a quasi-compact quasi-affine open H of X.
4. The image N in Z of the complement of g inverse H is constructible by
   lem-weil-pbc-chevalley-constructible-image. It misses j(L), by
   lem-weil-pbc-base-change-image. The generalization-stable image j(L) misses its closure,
   by lem-weil-pbc-qcqs-scheme-spectral and
   lem-weil-pbc-spectral-proconstructible-closure-specialization. Thus the complement V
   of that closure is a neighbourhood of j(L), whose pullback maps into H.
5. Remove the saturation of the closed complement of V under the two integral relation
   maps. They are closed by pqf-lem-integral-univclosed. By lem-pd-descent-orbit-saturated
   the remaining open V_star is invariant and still contains j(L).
6. Descend its inverse image to the open U = X minus g(Z_B minus V_star_B).
   Integrality, surjectivity and invariance give g inverse U = V_star_B. Moreover U lies
   in H and contains E. Since X is Noetherian, U is quasi-compact and quasi-affine.
   Use lem-a1-quasi-affine-target-locality to see that U to B is quasi-affine, and
   lem-trf-quasi-affine-base-change for its pullback U_A, containing x.
7. The two inverse images of U_A agree after the integral surjective base change by T,
   since both come from V_star. Surjectivity detects their equality, also in the full
   functor model. The canonical datum restricts and its cocycle restricts with it.
8. Descend U_A to the original model P using lem-weil-pbc-open-subscheme-fpqc-descent.
   Its morphism to the original covering base is quasi-affine by
   lem-sfb-scheme-quasi-affine-fpqc-descent. Invariance is detected on the affine fpqc
   refinement, and the restricted datum inherits the cocycle. Varying x covers P.
9. Finally vary the affine base open. Its inclusion is a quasi-affine morphism, since
   the base is locally Noetherian. Use lem-sfb-quasiaffine-morphism-composition and
   lem-trf-quasi-affine-base-change to regard all charts over the original covering
   base. The relation maps have the same base coordinate, so invariance is preserved.
   The empty model permits the empty index set. -/
theorem exists_integral_descent_invariant_quasiaffine_charts
    {S S' T : Scheme.{u}} [IsLocallyNoetherian S]
    (p : S' ⟶ S) [Flat p] [Surjective p] [QuasiCompact p]
    (F : (Over S)ᵒᵖ ⥤ Type v)
    (hF : Presheaf.IsSheaf (Scheme.fpqcTopology.over S) F)
    (P : Over S') [LocallyOfFinitePresentation P.hom]
    (rP : ((Over.map p).op ⋙ F).RepresentableBy P)
    (q : T ⟶ S) [IsIntegralHom q] [Surjective q]
    (Y : Over T) (rY : ((Over.map q).op ⋙ F).RepresentableBy Y)
    (horbit : ∀ y : Y.left, ∃ V : Y.left.Opens, IsAffineOpen V ∧
      rY.overDescentDatum.toHom ''
        ((pullback.fst (Y.hom ≫ q) q) ⁻¹' {y}) ⊆ (V : Set Y.left)) :
    ∃ (I : Type u) (U : I → P.left.Opens),
      (∀ x : P.left, ∃ i : I, x ∈ U i) ∧
      ∀ i : I, IsQuasiAffineHom ((U i).ι ≫ P.hom) ∧
        (pullback.fst (P.hom ≫ p) p ⁻¹ᵁ U i) =
          (rP.overDescentDatum.toHom ⁻¹ᵁ U i) ∧
        ∃ E : Over.DescentDatum p (Over.mk ((U i).ι ≫ P.hom)),
          ∀ {A : Scheme.{u}} (f₀ f₁ : A ⟶ S')
            (h : f₀ ≫ p = f₁ ≫ p)
            (a : Over.mk f₀ ⟶ Over.mk ((U i).ι ≫ P.hom)),
            (E.transport f₀ f₁ h a).left ≫ (U i).ι =
              (rP.overDescentDatum.transport f₀ f₁ h
                (Over.homMk (a.left ≫ (U i).ι)
                  (by simpa only [Over.mk_hom, Category.assoc] using Over.w a))).left := by
  sorry

end AlgebraicGeometry
