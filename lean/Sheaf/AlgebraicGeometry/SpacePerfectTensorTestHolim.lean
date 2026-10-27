module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQCohTriangulated
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Sheaf.AlgebraicGeometry.SpacePerfectUniformTor
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses

/-! # Perfect tensor tests preserve products and derived limits

Source: Stacks Project, spaces-flat.tex, Tag 0CX6, proof of
lemma-compute-against-perfect; sites-cohomology.tex, Tag 08JJ
(blueprint: lem-sfb-space-perfect-tensor-test-holim).
Products are intrinsic to the full quasi-coherent derived subcategory.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w c v d vD i

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.AlgebraicSpace

/-- The stated tensor test, with K-flat-normalized tensor and the structure-induced
scalar action on derived global sections.
Source: Stacks Project, Tags 0CX6 and 08JJ
(blueprint: lem-sfb-space-perfect-tensor-test-holim). -/
def perfectTensorTest {S : Scheme.{u}} (A : Type u) [CommRing A]
    (Y : Over S) (e : Y.left ≅ Spec (.of A))
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)
    [HasDerivedCategory.{w} X.SmallModules] (E : X.DerivedModules) :
    X.DerivedQCoh ⥤ DerivedCategory (ModuleCat.{u} A) :=
  X.derivedQCohProperty.ι ⋙ Prod.sectL X.DerivedModules E ⋙
    X.derivedDualityModel.closed.tensor ⋙ affineDerivedSections A Y e X f

/-- The canonical comparison into an arbitrary specified product of tensor tests.
Its components are precisely the images of the source product projections.
Source: Stacks Project, Tag 0CX6
(blueprint: lem-sfb-space-perfect-tensor-test-holim). -/
def perfectTensorTestProductComparison
    {C : Type c} [Category.{v} C] {D : Type d} [Category.{vD} D]
    (T : C ⥤ D) {I : Type i} (F : I → C)
    (P : Fan F) (Q : Fan (fun i ↦ T.obj (F i))) (hQ : IsLimit Q) :
    T.obj P.pt ⟶ Q.pt :=
  hQ.lift (Fan.mk (T.obj P.pt) (fun i ↦ T.map (P.proj i)))

/-- Exactness, arbitrary small products, and the product-arrow-compatible derived
limit comparison for the perfect tensor test. Limit cones allow all choices of
products, without identifying intrinsic products with ambient derived products.
The Roos triangles below are the defining condition of IsDerivedLimitTriangle,
written with arbitrary product fans and their transition endomorphisms.
Source: Stacks Project, Tags 0CX6, 08JJ, 0CR4, 07D9 and 08TC
(blueprint: lem-sfb-space-perfect-tensor-test-holim).

Proof:
1. A quasi-compact point space supplies an affine etale atlas. Absolute
   quasi-separatedness gives quasi-compact affine chart intersections. The affine
   base is quasi-separated, so the map to it is qcqs. A perfect E has quasi-coherent
   cohomology. These verify the hypotheses of the derived coherator and the general
   perfect-tensor-global-limits lemma.
2. Choose K-injective representatives of any family. Their termwise product is
   K-injective: maps from acyclic complexes have coordinate null-homotopies, whose
   product is a null-homotopy. Chain maps and homotopies are coordinate families, so
   derived Hom verifies the ambient product universal property.
3. Apply the right derived coherator to this ambient product. Its adjunction to the
   full inclusion gives the intrinsic D_QCoh product and its projections. This does
   not assert that the ambient product is quasi-coherent.
4. Apply lem-sfb-space-perfect-tensor-global-limits. Perfect duality identifies this
   test with global derived Hom from the dual perfect complex. It is exact and
   preserves the intrinsic products. The product comparison has components T(pr_i),
   so it is precisely the lift defined above, for every choice of product fans.
5. For a tower, the coordinate transition equations show that this comparison
   intertwines T(1-shift) with 1-shift on the image tower. Additivity handles the
   subtraction. Exactness therefore makes the image source Roos triangle a target
   Roos triangle after identifying its product vertices. Rotate it and any given
   target Roos triangle; the triangle morphism axiom completes the identity on the
   two product vertices to an isomorphism on the limit vertices. Its first square
   is the displayed compatibility. No uniqueness or functorial cone choice is used.
   Strict towers of complexes are included by applying localization to their maps. -/
theorem perfectTensorTest_preserves_products_holim
    {S : Scheme.{u}} (A : Type u) [CommRing A]
    (Y : Over S) (e : Y.left ≅ Spec (.of A))
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)
    [HasDerivedCategory.{w} X.SmallModules]
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : X.IsAbsolutelyQuasiSeparated)
    (E : X.DerivedModules)
    (hE : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
      X.smallStructureSheaf E) :
    (perfectTensorTest A Y e X f E).Additive ∧
    (∃ σ : shiftFunctor X.DerivedQCoh (1 : ℤ) ⋙ perfectTensorTest A Y e X f E ≅
        perfectTensorTest A Y e X f E ⋙
          shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ),
      ∀ Δ : Triangle X.DerivedQCoh, Δ ∈ distTriang X.DerivedQCoh →
        Triangle.mk ((perfectTensorTest A Y e X f E).map Δ.mor₁)
          ((perfectTensorTest A Y e X f E).map Δ.mor₂)
          ((perfectTensorTest A Y e X f E).map Δ.mor₃ ≫ σ.hom.app Δ.obj₁) ∈
            distTriang (DerivedCategory (ModuleCat.{u} A))) ∧
    (∀ (I : Type u) (F : I → X.DerivedQCoh),
      HasProduct F ∧ HasProduct (fun i ↦ (perfectTensorTest A Y e X f E).obj (F i)) ∧
      ∀ (P : Fan F) (_hP : IsLimit P)
        (Q : Fan (fun i ↦ (perfectTensorTest A Y e X f E).obj (F i))) (hQ : IsLimit Q),
        IsIso (perfectTensorTestProductComparison (perfectTensorTest A Y e X f E)
          F P Q hQ)) ∧
    (∀ (F : ℕ → X.DerivedQCoh) (t : ∀ n, F (n + 1) ⟶ F n)
      (P : Fan F) (_hP : IsLimit P) (s : P.pt ⟶ P.pt)
      (_hs : ∀ n, s ≫ P.proj n = P.proj n - (P.proj (n + 1) ≫ t n))
      (K : X.DerivedQCoh) (p : K ⟶ P.pt) (δ : P.pt ⟶ K⟦(1 : ℤ)⟧)
      (_hK : Triangle.mk p s δ ∈ distTriang X.DerivedQCoh)
      (Q : Fan (fun n ↦ (perfectTensorTest A Y e X f E).obj (F n))) (hQ : IsLimit Q)
      (s' : Q.pt ⟶ Q.pt)
      (_hs' : ∀ n, s' ≫ Q.proj n = Q.proj n -
        (Q.proj (n + 1) ≫ (perfectTensorTest A Y e X f E).map (t n)))
      (R : DerivedCategory (ModuleCat.{u} A)) (p' : R ⟶ Q.pt)
      (δ' : Q.pt ⟶ R⟦(1 : ℤ)⟧)
      (_hR : Triangle.mk p' s' δ' ∈ distTriang (DerivedCategory (ModuleCat.{u} A))),
      ∃ φ : (perfectTensorTest A Y e X f E).obj K ≅ R,
        φ.hom ≫ p' = (perfectTensorTest A Y e X f E).map p ≫
          perfectTensorTestProductComparison (perfectTensorTest A Y e X f E) F P Q hQ) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
