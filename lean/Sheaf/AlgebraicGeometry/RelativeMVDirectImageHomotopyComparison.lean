/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.RelativeMVMaps
public import Sheaf.AlgebraicGeometry.MayerVietorisImageChainData
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisPresentation
import Sheaf.AlgebraicGeometry.DerivedMayerVietorisUnderivedOpenCounitSquare

/-! # Relative comparison before tensor pullback -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The resolved comparison before performing tensor pullback on chain models.
The source complexes live on S, the target complexes on S', and the square is
formed with the underived direct-image functor of g. No chain model for derived
pullback, and no strict square on S', is asserted.
Source: Stacks Project, Cohomology, Tags 08BV, 08HZ, 08FE and 08HY.
(blueprint: lem-pc-relative-mv-direct-image-homotopy-comparison).

Proof: Resolve K and K' by injective-term K-injective complexes I and J.
Transpose phi along the pinned adjunction for g'. Replace the underived
complex g'_* J by an injective-term K-injective complex L before representing
this transpose
by a chain map I -> L: g'_* J itself need not be K-injective. Its terms are
flasque, as direct images of injective sheaves. Restriction and open direct
image therefore compute its derived open terms, so g'_* J -> L induces
quasi-isomorphisms on the three restriction-row terms. The Mayer--Vietoris
rows of I, J and L are exact by gluing and injective flasqueness; the row of
g'_* J is exact by flasqueness. The chain map I -> L gives a map of rows.
Apply Rf_* to this row comparison, computing it with K-injective
replacements of the row diagram; termwise flasqueness alone is not used to
compute an unbounded derived direct image.
The sectionwise direct-image composition and inverse-open comparisons
identify the latter with g_* of the target row on S'. Thus this is a roof of
row diagrams, retaining its quotient component. Use right fractions on this
finite arrow diagram and refine their common source denominators; retain the
square homotopy induced by the row comparison. This yields alpha, beta and H
from replacement source complexes on S into g_* of the target complexes on
S'. Replacing the source diagram changes its vertex and cone comparisons by
quasi-isomorphisms, and does not require g_* to preserve quasi-isomorphisms.
The cone map
of this homotopy, followed by the inverse additive cone comparison, represents
the quotient-row map. This last claim uses the actual map of resolved rows,
not an arbitrary completion of a derived square. The right-derived unit eta
compares the underived images to Rg_* of the target vertices. Compose the
source vertex comparisons with Lg*, and the target comparisons with the
exact-open and direct-image composition comparisons. Their adjunction mates,
computed by the composite counit formula, are precisely the global arrow and
the two local arrows in relativeMVMaps; biproduct extensionality gives the
middle equality. The same computation on the quotient gives the overlap
equality. Only these derived mates are taken here: constructing chain models
for Lg* and strictifying their square are separate steps. For an empty open
the corresponding row terms vanish; repeated opens yield split restriction
rows. Zero coefficients and phi = 0 give the zero row and zero row map. -/
theorem relativeMV_direct_image_homotopy_comparison
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    let G := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let F := G.mapHomologicalComplex (.up ℤ)
    let η := schemeMVDirectImageLocalization g
    let adj := relativeMVAdj g
    let a := relativeMVGlobalArrow f f' g g' hpull K K' φ
    let b := relativeMVLocalArrow f f' g g' hpull K K' φ
    ∃ (A B : CochainComplex
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
      (A' B' : CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ)
      (t : A ⟶ B) (t' : A' ⟶ B')
      (α : A ⟶ F.obj A') (β : B ⟶ F.obj B')
      (H : Homotopy (t ≫ β) (α ≫ F.map t'))
      (e₁ : (derivedPullback g).obj (DerivedCategory.Q.obj A) ≅ a.left)
      (e₂ : (derivedPullback g).obj (DerivedCategory.Q.obj B) ≅
        (b U).left ⊞ (b V).left)
      (e₃ : (derivedPullback g).obj
        (DerivedCategory.Q.obj (CochainComplex.mappingCone t)) ≅ (b (U ⊓ V)).left)
      (e₁' : DerivedCategory.Q.obj A' ≅ a.right)
      (e₂' : DerivedCategory.Q.obj B' ≅ (b U).right ⊞ (b V).right)
      (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅
        (b (U ⊓ V)).right),
      (adj.homEquiv _ _).symm (DerivedCategory.Q.map α ≫ η.app A') ≫ e₁'.hom =
        e₁.hom ≫ a.hom ∧
      (adj.homEquiv _ _).symm (DerivedCategory.Q.map β ≫ η.app B') ≫ e₂'.hom =
        e₂.hom ≫ biprod.map (b U).hom (b V).hom ∧
      (adj.homEquiv _ _).symm
          (DerivedCategory.Q.map (CochainComplex.mappingCone.mapOfHomotopy H ≫
            (CochainComplex.mappingCone.mapHomologicalComplexIso t' G).inv) ≫
              η.app (CochainComplex.mappingCone t')) ≫ e₃'.hom =
        e₃.hom ≫ (b (U ⊓ V)).hom := by sorry

end AlgebraicGeometry
