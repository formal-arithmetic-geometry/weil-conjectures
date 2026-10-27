module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQCohTriangulated
public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Functor.Currying
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import Sheaf.AlgebraicGeometry.SpaceDerivedCoheratorAdjunction
import Sheaf.CategoryTheory.RingedSitePerfectDuality
import Sheaf.AlgebraicGeometry.SpaceDerivedQCohPullbackTensor
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.Paper.ModuleCupHomologyRepresentability
import Sheaf.CategoryTheory.Triangulated.DerivedLimitLevelwiseIsomorphism

/-! # Perfect tensor global sections preserve intrinsic derived products and limits

Source: Stacks Project, spaces-flat.tex, Tag 0CX6, proof of
lemma-compute-against-perfect; Tags 0CR4, 0BK6, 08JJ, 0B6E and 08TC
(blueprint: lem-sfb-space-perfect-tensor-global-limits).

The equality specifying T names the actual tensor/sections bifunctor, including its
maps in both arguments. No second tensor-test definition or chosen cone is introduced.
Products are arbitrary limiting fans in D_QCoh, not ambient derived products.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.AlgebraicSpace

/-- Perfect tensor global sections are exact, preserve all products in the chosen
universe, and carry every specified Roos triangle to a Roos triangle. The comparison
is natural in the family and in perfect coefficients. The final isomorphism preserves
the given limit projections; no unique or canonical cone completion is asserted.

Source: Stacks Project, spaces-flat.tex, Tag 0CX6, lemma-compute-against-perfect,
exact global Hom paragraph and dual-perfect translation; Tags 0CR4, 0BK6, 08JJ,
0B6E and 08TC (blueprint: lem-sfb-space-perfect-tensor-global-limits).

Proof:
1. On def-sfb-space-small-ringed-model, sectionwise products of module sheaves
   exist, with coordinate scalar multiplication, restrictions and gluing. Resolve
   each object K-injectively by prop-pur-kinjective-resolutions-exist. By
   lem-pc-ringed-space-product-kinjective the termwise product is K-injective and
   represents the ambient derived product. Apply the same argument to A-modules.
   This covers the empty family without assuming exactness of sheaf products.
2. By lem-sfb-space-quasicompact-affine-tests and lem-sfb-space-qcqs-source-products,
   the relative qcqs hypotheses over the affine base give a quasi-compact atlas and
   quasi-compact affine chart intersections. The adjunction I_X |- DQ_X of
   lem-sfb-space-derived-coherator-adjunction sends an ambient product B to the
   intrinsic product DQ_X B. Its projections are the counit followed by the ambient
   projections; the adjunction and the product universal property verify this,
   including the empty product.
3. Put D = E-dual. By lem-sfb-ringed-site-perfect-duality, D is perfect and
   E is its bidual. Its cohomology is quasi-coherent by local finite-free retract
   models and lem-sfb-space-qcoh-kernels-colimits. Perfect evaluation identifies
   H tensor E with internal RHom(D,H). The cohomology clause of
   lem-sfb-ringed-site-global-rhom-derived-limits gives H^q F_E(H) = Hom(D[-q],H),
   naturally and with its A-action. Only that clause, not ambient limit preservation,
   is used here.
4. By lem-sfb-space-derived-qcoh-pullback-tensor the tensor stays quasi-coherent.
   A flat-term K-flat resolution from lem-pc-kflat-resolution and
   lem-weil-pbc-kflat-fixed-tensor-triangulated make fixed tensor exact, with signed
   shift comparison. The additive scalar sections functor has K-injective derived
   functor; lem-pc-right-derived-functor-triangulated makes this exact. Compose and
   restrict to D_QCoh to obtain the coherent shifts and exactness asserted below.
5. By lem-sc-module-cup-homology-representability, H^q in D(A) is represented by
   A[-q]. Thus the cohomology of an arbitrary product is the product of its
   cohomologies, with the specified projection maps, including the empty case.
6. Apply step 3 to the intrinsic product. Its universal property identifies source
   cohomology of the comparison with the product of H^q F_E(H_j). Step 5 identifies
   target cohomology with the same product. Naturality identifies the comparison
   with the identity on these components, so it is a cohomology isomorphism in every
   degree. Apply lem-weil-pbc-unbounded-derived-iso-cohomology.
7. For family maps, both comparison composites have j-th component F_E(u_j pr_j).
   For a perfect coefficient map v, bifunctoriality of tensor gives the square on
   each projection. Product uniqueness proves both naturality equalities.
8. For a tower, projectionwise calculation and additivity show that the product
   comparison conjugates F_E(1-s) to 1-s'. Exactness sends the source distinguished
   triangle to a distinguished triangle. Transport both product vertices by the
   same comparison, and the last arrow by its inverse and the shift comparison.
   This is precisely a derived-limit triangle as in def-weil-derived-limit.
9. Rotate this triangle and any specified target Roos triangle to start with
   1-s'. TR3 completes the identity on the two product vertices. Rotate back and
   apply lemma-weil-pbc-r-lim-levelwise-isomorphism to get an isomorphism on the
   limit vertices. Its first square gives the stated projection compatibility.
   No surjectivity, concentration, finiteness, support or nilpotence condition
   on the tower has entered the argument. -/
theorem perfectTensorGlobal_preserves_products_limits
    (A : Type u) [CommRing A]
    (Y : Over (Spec (.of (ULift.{u} ℤ)))) (e : Y.left ≅ Spec (.of A))
    (X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))) (f : X ⟶ schemeSpace Y)
    [HasDerivedCategory.{w} X.SmallModules]
    (_hqc : IsQuasiCompactPresheafMap f.hom.hom)
    (_hqs : IsQuasiCompactPresheafMap (pullback.diagonal f.hom.hom))
    (T : X.DerivedQCoh ⥤ X.DerivedQCoh ⥤ DerivedCategory (ModuleCat.{u} A))
    (_hT : T = (Functor.curry.obj
      ((X.derivedQCohProperty.ι.prod X.derivedQCohProperty.ι) ⋙
        X.derivedDualityModel.closed.tensor ⋙ affineDerivedSections A Y e X f)).flip)
    (E : X.DerivedQCoh)
    (_hE : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
      X.smallStructureSheaf E.obj) :
    (T.obj E).Additive ∧
    ∃ σ : (T.obj E).CommShift ℤ,
      (∀ Δ : Triangle X.DerivedQCoh, Δ ∈ distTriang X.DerivedQCoh →
        Triangle.mk ((T.obj E).map Δ.mor₁) ((T.obj E).map Δ.mor₂)
          ((T.obj E).map Δ.mor₃ ≫ (σ.commShiftIso (1 : ℤ)).hom.app Δ.obj₁) ∈
            distTriang (DerivedCategory (ModuleCat.{u} A))) ∧
      (∀ (I : Type u) (H : I → X.DerivedQCoh),
        HasProduct H ∧ HasProduct (fun j ↦ (T.obj E).obj (H j)) ∧
        ∀ (P : Fan H) (_hP : IsLimit P)
          (Q : Fan (fun j ↦ (T.obj E).obj (H j))) (_hQ : IsLimit Q)
          (c : (T.obj E).obj P.pt ⟶ Q.pt)
          (_hc : ∀ j, c ≫ Q.proj j = (T.obj E).map (P.proj j)), IsIso c) ∧
      (∀ (I : Type u) (H H' : I → X.DerivedQCoh) (v : ∀ j, H j ⟶ H' j)
        (P : Fan H) (_hP : IsLimit P) (P' : Fan H') (hP' : IsLimit P')
        (Q : Fan (fun j ↦ (T.obj E).obj (H j))) (_hQ : IsLimit Q)
        (Q' : Fan (fun j ↦ (T.obj E).obj (H' j))) (hQ' : IsLimit Q')
        (c : (T.obj E).obj P.pt ⟶ Q.pt)
        (_hc : ∀ j, c ≫ Q.proj j = (T.obj E).map (P.proj j))
        (c' : (T.obj E).obj P'.pt ⟶ Q'.pt)
        (_hc' : ∀ j, c' ≫ Q'.proj j = (T.obj E).map (P'.proj j)),
        (T.obj E).map (hP'.lift (Fan.mk P.pt (fun j ↦ P.proj j ≫ v j))) ≫ c' =
          c ≫ hQ'.lift (Fan.mk Q.pt (fun j ↦ Q.proj j ≫ (T.obj E).map (v j)))) ∧
      (∀ (E' : X.DerivedQCoh)
        (_hE' : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
          X.smallStructureSheaf E'.obj)
        (v : E ⟶ E') (I : Type u) (H : I → X.DerivedQCoh)
        (P : Fan H) (_hP : IsLimit P)
        (Q : Fan (fun j ↦ (T.obj E).obj (H j))) (_hQ : IsLimit Q)
        (Q' : Fan (fun j ↦ (T.obj E').obj (H j))) (hQ' : IsLimit Q')
        (c : (T.obj E).obj P.pt ⟶ Q.pt)
        (_hc : ∀ j, c ≫ Q.proj j = (T.obj E).map (P.proj j))
        (c' : (T.obj E').obj P.pt ⟶ Q'.pt)
        (_hc' : ∀ j, c' ≫ Q'.proj j = (T.obj E').map (P.proj j)),
        (T.map v).app P.pt ≫ c' =
          c ≫ hQ'.lift (Fan.mk Q.pt (fun j ↦ Q.proj j ≫ (T.map v).app (H j)))) ∧
      (∀ (H : ℕ → X.DerivedQCoh) (t : ∀ n, H (n + 1) ⟶ H n)
        (P : Fan H) (_hP : IsLimit P) (s : P.pt ⟶ P.pt)
        (_hs : ∀ n, s ≫ P.proj n = P.proj n - (P.proj (n + 1) ≫ t n))
        (L : X.DerivedQCoh) (p : L ⟶ P.pt) (δ : P.pt ⟶ L⟦(1 : ℤ)⟧)
        (_hL : Triangle.mk p s δ ∈ distTriang X.DerivedQCoh)
        (Q : Fan (fun n ↦ (T.obj E).obj (H n))) (_hQ : IsLimit Q)
        (s' : Q.pt ⟶ Q.pt)
        (_hs' : ∀ n, s' ≫ Q.proj n = Q.proj n -
          (Q.proj (n + 1) ≫ (T.obj E).map (t n))),
        ∃ c : (T.obj E).obj P.pt ≅ Q.pt,
          (∀ n, c.hom ≫ Q.proj n = (T.obj E).map (P.proj n)) ∧
          Triangle.mk ((T.obj E).map p ≫ c.hom) s'
            (c.inv ≫ (T.obj E).map δ ≫ (σ.commShiftIso (1 : ℤ)).hom.app L) ∈
              distTriang (DerivedCategory (ModuleCat.{u} A)) ∧
          ∀ (R : DerivedCategory (ModuleCat.{u} A)) (p' : R ⟶ Q.pt)
            (δ' : Q.pt ⟶ R⟦(1 : ℤ)⟧)
            (_hR : Triangle.mk p' s' δ' ∈ distTriang (DerivedCategory (ModuleCat.{u} A))),
            ∃ φ : (T.obj E).obj L ≅ R,
              φ.hom ≫ p' = (T.obj E).map p ≫ c.hom) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
