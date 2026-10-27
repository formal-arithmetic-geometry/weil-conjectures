/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-! # A finite closed image near a geometric fibre

Source: Stacks Project, More on Morphisms of Spaces, Tag 0AEJ,
lemma-flat-proper-family-cannot-collapse-fibre, case (3)(a); Tag 0A4Y;
Morphisms of Spaces, Tag 03ZP (blueprint: lem-sfb-proper-space-finite-image-neighbourhood).

The auxiliary map is the actual sheaf pullback map. The conclusion uses a scheme
representing the finite closed subspace, retaining both projections and the factorization.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The base change of the specified map in a commuting triangle, on actual presheaf
fibre products. Source: Stacks, Tag 0AEJ, notation `h` after base change
(blueprint: lem-sfb-proper-space-finite-image-neighbourhood). -/
def finiteImageBaseChangeMap {S : Scheme.{u}} {T U : Over S}
    {X Y : AlgebraicSpace S} (p : X ⟶ schemeSpace T) (q : Y ⟶ schemeSpace T)
    (h : X ⟶ Y) (w : h ≫ q = p) (b : U ⟶ T) :
    Limits.pullback p.hom.hom (yoneda.map b) ⟶ Limits.pullback q.hom.hom (yoneda.map b) :=
  pullback.map p.hom.hom (yoneda.map b) q.hom.hom (yoneda.map b)
    h.hom.hom (𝟙 _) (𝟙 _)
    (by simpa using (congrArg (fun f ↦ f.hom.hom) w).symm) (by simp)

/-- A finite geometric fibre image of a proper space has a finite closed image over an
 affine neighbourhood. Closed and finite are representable scheme-test properties.
Source: Stacks, Tag 0AEJ, lemma-flat-proper-family-cannot-collapse-fibre, (3)(a),
affine shrink using Tag 01IT; finite convention Tag 03ZP
(blueprint: lem-sfb-proper-space-finite-image-neighbourhood).

Proof:
1. By lem-sfb-space-proper-schematic-image factor `h` through its closed schematic
   image, proper over `T`, with surjective map from `X`.
2. The fibre-product point-image formula of lem-a1-space-point-open-calculus makes
   that map surjective on the geometric fibre. The closed inclusion is injective on
   points by def-weil-closed-immersion. Thus the image's geometric fibre is finite,
   also when empty.
3. Apply lem-sfb-space-finite-fibre-quasifinite-criterion to the proper image: it is
   quasi-finite at every point over `t`.
4. By lem-sfb-space-quasifinite-locus-open its non-quasi-finite locus is closed.
   Properness makes its image closed in `T`, missing `t`. Choose an affine open
   neighbourhood in the complement using lem-weil-pbc-affine-opens-basis.
5. Properness persists by lem-sfb-space-proper-base-change. Every point over this
   open is quasi-finite. Use pqf-def-quasifinite and
   lem-a1-separated-locally-qf-space-representable to represent the image by a scheme;
   pqf-lem-proper-lqf-finite then makes its structure map finite.
6. Base change the original factorization. Its closed inclusion stays closed on scheme
   tests. By lem-trf-finite-radicial-basechange the finite map is finite on every scheme
   base change. Over the affine neighbourhood, def-weil-finite-integral-morphism gives
   an affine scheme with a finite coordinate-ring map. -/
theorem exists_finite_closed_image_affine_neighbourhood
    (T : Scheme.{u}) (X Y : AlgebraicSpace T)
    (p : X ⟶ schemeSpace (Over.mk (𝟙 T)))
    (q : Y ⟶ schemeSpace (Over.mk (𝟙 T))) (h : X ⟶ Y) (w : h ≫ q = p)
    (hp : MapIsProper p) (hq : MapIsSeparated q)
    (hqlft : MapIsLocally (@LocallyOfFiniteType) q)
    (t : T) (Ω : Type u) [Field Ω] [Algebra (T.residueField t) Ω]
    [IsAlgClosure (T.residueField t) Ω]
    (hfinite : (pointImage (finiteImageBaseChangeMap p q h w
      (Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap (T.residueField t) Ω)) ≫ T.fromSpecResidueField t))
        (V := Over.mk (𝟙 T))
        (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
          T.fromSpecResidueField t)))).Finite) :
    ∃ (V : T.Opens), t ∈ V ∧ IsAffineOpen V ∧
      ∃ (Z : Over T) (g : Z ⟶ Over.mk V.ι)
        (j : yoneda.obj Z ⟶ Limits.pullback q.hom.hom
          (yoneda.map (Over.homMk (U := Over.mk V.ι) (V := Over.mk (𝟙 T)) V.ι)))
        (a : Limits.pullback p.hom.hom
          (yoneda.map (Over.homMk (U := Over.mk V.ι) (V := Over.mk (𝟙 T)) V.ι)) ⟶
            yoneda.obj Z),
        IsRepresentableWith (fun _ _ f ↦ IsClosedImmersion f.left) j ∧
        a ≫ j = finiteImageBaseChangeMap p q h w
          (Over.homMk (U := Over.mk V.ι) (V := Over.mk (𝟙 T)) V.ι) ∧
        j ≫ pullback.snd q.hom.hom
          (yoneda.map (Over.homMk (U := Over.mk V.ι) (V := Over.mk (𝟙 T)) V.ι)) =
            yoneda.map g ∧
        a ≫ yoneda.map g = pullback.snd p.hom.hom
          (yoneda.map (Over.homMk (U := Over.mk V.ι) (V := Over.mk (𝟙 T)) V.ι)) ∧
        IsRepresentableWith (fun _ _ f ↦ IsFinite f.left) (yoneda.map g) ∧
        IsAffine Z.left ∧ (g.left.appTop).hom.Finite := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
