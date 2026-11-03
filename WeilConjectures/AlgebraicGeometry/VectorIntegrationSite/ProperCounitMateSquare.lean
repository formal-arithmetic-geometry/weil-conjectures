/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleProjectiveCoefficient
public import WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
import all WeilConjectures.AlgebraicGeometry.Sp.SpDirectImageEtaleMate
import all WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
import all WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTensoratorSignedSymmetry

/-!
# Proper counit mate and projection square

This isolates the etale/pro-etale projection compatibility used by the proper counit
comparison: the canonical qcqs projection comparison at the projective-line map,
conjugated by the signed tensor symmetries. It does not involve the trace or the
Chern class (blueprint: lem-route-line-proper-counit-mate-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

attribute [local instance 100000] CategoryTheory.catToReflQuiver

namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

-- Reuse the ordinary module category's cached localization instances.
set_option linter.auxLemma false in
attribute [local instance 100000]
  Etale.DerivedCategoryModule._proof_1 Etale.DerivedCategoryModule._proof_2

-- Match the canonical sheaf braidings used by the signed comparison theorem.
attribute [local instance 40000] CategoryTheory.sheafIsAbelian
attribute [local instance high] CategoryTheory.SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace

/-- Paste a projection square with the two naturality squares for the symmetry. -/
private theorem paste_projection_symmetry
    {B X : Type*} [Category B] [Category X] (R : X ⥤ B)
    {U₀ U₁ U₂ U₃ U₄ U₅ U₆ U₇ : B} {V₀ V₁ V₂ V₃ : X}
    {s : U₀ ⟶ U₁} {p : U₁ ⟶ U₂} {u : U₂ ⟶ U₃}
    {b₀ : U₃ ⟶ R.obj V₁} {b₁ : U₂ ⟶ R.obj V₀}
    {v : V₀ ⟶ V₁} {w : V₁ ⟶ V₃} {t : V₀ ⟶ V₂} {z : V₂ ⟶ V₃}
    {e : U₁ ⟶ U₄} {f : U₄ ⟶ U₅} {pp : U₅ ⟶ R.obj V₂}
    {g : U₀ ⟶ U₆} {h : U₆ ⟶ U₇} {k : U₇ ⟶ U₅}
    (hn : u ≫ b₀ = b₁ ≫ R.map v) (hf : v ≫ w = t ≫ z)
    (hp : p ≫ b₁ ≫ R.map t = e ≫ f ≫ pp)
    (hb : s ≫ e ≫ f = g ≫ h ≫ k) :
    s ≫ p ≫ u ≫ b₀ ≫ R.map w = g ≫ h ≫ k ≫ pp ≫ R.map z := by
  rw [reassoc_of% hn, ← R.map_comp, hf, R.map_comp]
  rw [reassoc_of% hp, reassoc_of% hb]

/-- The canonical derived tensor symmetry is the Koszul-signed symmetry (by definition). -/
private theorem canonical_symmetry_hom.{v, v₁} {C : Type v₁} [Category.{v + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{v + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    (J K : _root_.DerivedCategory C) :
    ((_root_.DerivedCategory.canonicalTensorSymmetry C).hom.app J).app K =
      (derivedTensorKoszulSymmetry C J K).hom := by
  rfl

-- Keep the coherence calculation generic to avoid unfolding concrete coefficient objects.
/-- The canonical projection/mate square in coefficient-first order for arbitrary
objects. This is the symmetry-conjugation calculation of
`lem-route-line-proper-counit-mate-square`, before specializing its coefficients. -/
private theorem ordered_projection_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {P T : Scheme.{u}} (q : P ⟶ T)
    (W : Etale.DerivedCategoryModule A P) (K : Etale.DerivedCategoryModule A T) :
    (comparison A T).map (Etale.ordinaryFiniteProjection A q W K) ≫
        geoP1PushComparison A q
          (((Etale.derivedTensor (ModuleCat.{u + 1} A) P).obj
            ((Etale.ordinaryFinitePullback A q).obj K)).obj W) ≫
        (lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctor.map
          (tensorPullbackComparison A q K W).hom =
      (tensorComparison A T K ((Etale.ordinaryFinitePushforward A q).obj W)).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} A) T).obj ((comparison A T).obj K)).map
          (geoP1PushComparison A q W) ≫
        properProjection (ModuleCat.{u + 1} A) q ((comparison A P).obj W)
          ((comparison A T).obj K) := by
  let C := comparison A T
  let D := comparison A P
  let R := (lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctor
  let Re := Etale.ordinaryFinitePushforward A q
  let V := (Etale.upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj K
  let a := ((pullback A q).app K).hom
  let b := BoundaryComparison.directImageMate (ModuleCat.{u + 1} A) q
  have h := sp_projection_square (ModuleCat.{u + 1} A) q W K
  have hn := b.naturality
    (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) P).hom.app W).app V)
  dsimp only [Functor.comp_map] at hn
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  have hs (X : Scheme.{u}) (U V : Etale.DerivedCategoryModule A X) :
      (comparison A X).map
          (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app U).app V) ≫
        (tensorComparison A X V U).hom =
      (tensorComparison A X U V).hom ≫
        (((symmetry (ModuleCat.{u + 1} A) X).hom.app
          ((comparison A X).obj U)).app ((comparison A X).obj V)) := by
    have hsigma (U V : DerivedCategory
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
        (derivedTensorKoszulSymmetry
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) U V).hom =
        (((symmetry (ModuleCat A) X).hom.app U).app V) := by
      simpa only [symmetry] using
        (canonical_symmetry_hom
          (C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) U V).symm
    simpa only [tensorComparison, Iso.app_hom, hsigma, comparison, geoP1Comparison] using
      comparisonTensorator_signedSymmetry A X U V
  have hfiber :
      D.map (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) P).hom.app W).app V) ≫
        (tensorPullbackComparison A q K W).hom =
      ((tensorComparison A P W V).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} A) P).obj (D.obj W)).map a) ≫
        (((symmetry (ModuleCat.{u + 1} A) P).hom.app (D.obj W)).app
          ((upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj (C.obj K))) := by
    simp only [tensorPullbackComparison, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom, Etale.ordinaryFinitePullback]
    rw [reassoc_of% hs P W V]
    rw [Category.assoc]
    exact congrArg (fun f ↦ (tensorComparison A P W V).hom ≫ f)
      (((symmetry (ModuleCat.{u + 1} A) P).hom.app (D.obj W)).naturality a).symm
  have hbase :
      C.map (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app K).app
          (Re.obj W)) ≫
        (tensorComparison A T (Re.obj W) K).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} A) T).map (b.app W)).app (C.obj K) =
      (tensorComparison A T K (Re.obj W)).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} A) T).obj (C.obj K)).map (b.app W) ≫
        (((symmetry (ModuleCat.{u + 1} A) T).hom.app (C.obj K)).app
          (R.obj (D.obj W))) := by
    rw [reassoc_of% hs T K (Re.obj W)]
    exact congrArg (fun f ↦ (tensorComparison A T K (Re.obj W)).hom ≫ f)
      (((symmetry (ModuleCat.{u + 1} A) T).hom.app (C.obj K)).naturality
        (b.app W)).symm
  have h0 :
      C.map (((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) q).app
          W).app K) ≫
        b.app (((Etale.derivedTensor (ModuleCat.{u + 1} A) P).obj W).obj V) ≫
        R.map ((tensorComparison A P W V).hom ≫
          ((derivedTensor (ModuleCat.{u + 1} A) P).obj (D.obj W)).map a) =
      (tensorComparison A T (Re.obj W) K).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} A) T).map (b.app W)).app (C.obj K) ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) q).app
          (D.obj W)).app (C.obj K) := by
    simpa only [C, D, R, Re, V, a, b, tensorComparison, pullback,
      pullComparison_eq, Iso.app_hom, Iso.symm_hom, comparison, geoP1Comparison,
      Etale.ordinaryFinitePushforward] using h
  have hfinal := paste_projection_symmetry R hn hfiber h0 hbase
  simp only [C, D, R, Re, V, b, comparison, geoP1Comparison,
    BoundaryComparison.comparison, BoundaryComparison.etaleImage,
    BoundaryComparison.proetaleImage, Etale.ordinaryFiniteProjection, properProjection,
    pushComparison_mate, Etale.ordinaryFinitePushforward, Etale.ordinaryFinitePullback,
    Etale.ordinaryFiniteTensor, Functor.map_comp,
    Functor.comp_obj, Functor.flip_obj_obj, id_eq, Category.assoc] at hfinal ⊢
  -- The comparison image of the composite is split by `Functor.map_comp` up to instances.
  refine Eq.trans ?_ hfinal
  first
    | rfl
    | exact congrArg (CategoryStruct.comp _) (Functor.map_comp_assoc _ _ _ _)

/-- The canonical projection square for the projective-line counit calculation:
the comparison image of the ordinary ordered projection, followed by the canonical
direct-image mate and the coefficient-first right comparison, is the comparison
tensorator, followed by the tensor of the mate of the Tate line with the identity
and the coefficient-first pro-etale proper projection,
`R_p(ρ^0_K) ∘ β_{M_K} ∘ C_T(π_e) = π_p ∘ (1 ⊗ β_{W_e}) ∘ t_T(K, R_e W_e)`.

Source: the displayed projection square of
`lem-sfb-projection-comparison-etale-proetale` (Stacks 09A6, 07A4 and 0E48),
specialized to `p = q`, `K := W_e`, `N := K` and conjugated by the signed
symmetries; used in `lem-amb-affine-space-top-trace.proof.md`, first paragraph,
lines 19--24 (blueprint: lem-route-line-proper-counit-mate-square).

Proof: specialize the unbounded projection/exchange identity `sp_projection_square`
to the projective-line map, the shifted ordinary Tate line, and `K.obj`. This is the
same canonical projection square, before passing to bounded-below comparison
isomorphisms; only its mate morphisms are needed. Identify the direct-image mate
with `geoP1PushComparison` and its pullback square with `geoP1PullComparison`.
Both ordered projection maps are the usual projection maps conjugated by the
signed symmetries. Naturality of the direct-image mate moves the fiber symmetry
past that mate. The identity `comparisonTensorator_signedSymmetry`, followed by
naturality of the symmetry, moves the fiber symmetry through the tensor-pullback
comparison and the base symmetry through the tensor of the direct-image mate.
Functoriality of the direct image and associativity then give the stated square.
No boundedness or invertibility of a comparison component is required for this
identity of morphisms.
-/
theorem proper_counit_mate_square
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (T : Scheme.{u}) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    let A := Scheme.finiteTateCoefficient l E n
    let P := ProjectiveLine T
    let q : P ⟶ T := P ↘ T
    let W := (Etale.ordinaryFiniteLine A (l ^ (r + 1)) hA P)⟦(2 : ℤ)⟧
    let L := (Etale.ordinaryFinitePushforward A q).obj W
    let M := (Etale.ordinaryFiniteP1Right A (l ^ (r + 1)) hA T).obj K.obj
    (comparison A T).map (Etale.ordinaryFiniteProjection A q W K.obj) ≫
        geoP1PushComparison A q M ≫
        (lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctor.map
          (projectiveRightComparison l E n r hA T K.obj).hom =
      (tensorComparison A T K.obj L).hom ≫
        ((-⊗ᴸ-(T)[ModuleCat.{u + 1} A].obj ((comparison A T).obj K.obj)).map
          (id (geoP1PushComparison A q W))) ≫
        properProjection (ModuleCat.{u + 1} A) q (line l E n r hA P)
          ((comparison A T).obj K.obj) := by
  dsimp only
  simpa only [projectiveRightComparison, projectiveRightComparisonGeneric,
    Etale.ordinaryFiniteP1Right, Etale.ordinaryFiniteTwistedPullback,
    Etale.derivedTensorRight, Functor.comp_obj, Functor.flip_obj_obj, id_eq, line] using
    ordered_projection_comparison (Scheme.finiteTateCoefficient l E n)
      (ProjectiveLine T ↘ T)
      ((Etale.ordinaryFiniteLine (Scheme.finiteTateCoefficient l E n)
        (l ^ (r + 1)) hA (ProjectiveLine T))⟦(2 : ℤ)⟧) K.obj

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
