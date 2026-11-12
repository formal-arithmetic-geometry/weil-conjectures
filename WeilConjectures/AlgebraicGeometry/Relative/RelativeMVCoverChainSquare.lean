/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.HomotopySquareRectification
import WeilConjectures.AlgebraicGeometry.Relative.RelativeMVDirectImageHomotopyComparison
import WeilConjectures.AlgebraicGeometry.Derived.DerivedPullbackConeSquareTransposition
/-! # A strict relative cover comparison before cylinder replacement

Source: Stacks Project, Cohomology, Tags 08BV, 08HZ, 08FE and 08HY.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Chain representatives for the unrestricted relative Mayer--Vietoris square.
Source: Stacks Project, Cohomology, Tags 08BV, 08HZ, 08FE and 08HY.
(blueprint: lem-pc-relative-mv-cover-chain-square).
Proof: Choose injective-term K-injective representatives of K and K'. Their
restriction-pair and restriction-difference sequences are exact on sections by
sheaf gluing and injective flasqueness. Restriction preserves K-injectivity, so
applying direct image computes the relative vertices (Tags 08BV and 08HZ).
Transpose φ along the derived adjunction for g'. A map into the target
K-injective representative represents the transpose; restriction gives a map
of the cover diagrams. Compute source pullback with a K-flat resolution of the
finite diagram, retaining its specified square homotopies. Exact tensor on
K-flat models carries the restriction triangle to its cone triangle. The
underived open counit square of Tag 08FE identifies the restricted comparison.
Represent the first arrows and comparison components by chain maps t,t',α,β
and retain the resulting homotopy H of their square. The induced cone map is
mapOfHomotopy H, and the original exact restriction sequences identify its
localization with the overlap comparison. This uses the map of resolved rows,
not an arbitrary completion of a morphism of triangles.
Rectify that specified square using homotopy_square_cone_rectification: replace
B by B plus Cone(id A), and correct β on the contractible summand using H.
Its projection to B is a homotopy equivalence, and the rectification theorem
preserves the localized specified cone map. Compose this projection with the
original middle comparison. Compare direct-image compositions by adjunction
mates; use the biproduct comparison at the middle vertex. Expanding the
base-change mate (Tag 08HY) and composing counits identifies α with the global
map, β with the sum of the two local maps, and the functorial cone map with the
overlap map. These are the three asserted equations. No short exact cylinder
presentation is required here. Empty opens give zero local terms; repeated
opens give split restriction rows; zero objects and φ=0 give zero comparisons.
-/
theorem relativeMV_cover_chain_square
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    let a := relativeMVGlobalArrow f f' g g' hpull K K' φ
    let b := relativeMVLocalArrow f f' g g' hpull K K' φ
    ∃ (A B A' B' : CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ)
      (t : A ⟶ B) (t' : A' ⟶ B') (α : A ⟶ A') (β : B ⟶ B')
      (hc : t ≫ β = α ≫ t')
      (e₁ : DerivedCategory.Q.obj A ≅ a.left)
      (e₂ : DerivedCategory.Q.obj B ≅ (b U).left ⊞ (b V).left)
      (e₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone t) ≅
        (b (U ⊓ V)).left)
      (e₁' : DerivedCategory.Q.obj A' ≅ a.right)
      (e₂' : DerivedCategory.Q.obj B' ≅ (b U).right ⊞ (b V).right)
      (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅
        (b (U ⊓ V)).right),
      DerivedCategory.Q.map α ≫ e₁'.hom = e₁.hom ≫ a.hom ∧
      DerivedCategory.Q.map β ≫ e₂'.hom =
        e₂.hom ≫ biprod.map (b U).hom (b V).hom ∧
      DerivedCategory.Q.map (CochainComplex.mappingCone.map t t' α β hc) ≫ e₃'.hom =
        e₃.hom ≫ (b (U ⊓ V)).hom := by
  obtain ⟨A, B, A', B', t, t', α, β, H, e₁, e₂, e₃, e₁', e₂', e₃', hα, hβ, hγ⟩ :=
    relativeMV_direct_image_homotopy_comparison f f' g g' hpull K K' φ U V hcover
  obtain ⟨C, D, s, a, b, H', d₁, d₂, d₃, ha, hb, hc⟩ :=
    derivedPullback_cone_square_transposition g A B A' B' t t' α β H
  obtain ⟨T, i, c, hcomm, r₂, r₃, hr₂, hr₃⟩ :=
    CochainComplex.homotopy_square_cone_rectification s t' a b H'
  refine ⟨C, T, A', B', i, t', a, c, hcomm,
    d₁ ≪≫ e₁, r₂ ≪≫ d₂ ≪≫ e₂, r₃ ≪≫ d₃ ≪≫ e₃, e₁', e₂', e₃', ?_, ?_, ?_⟩
  · simpa only [Iso.trans_hom, Category.assoc, hα] using
      congrArg (fun k ↦ k ≫ e₁'.hom) ha
  · simpa only [Iso.trans_hom, Category.assoc, hb, hβ] using
      congrArg (fun k ↦ k ≫ e₂'.hom) hr₂
  · simpa only [Iso.trans_hom, Category.assoc, hc, hγ] using
      congrArg (fun k ↦ k ≫ e₃'.hom) hr₃
end AlgebraicGeometry
