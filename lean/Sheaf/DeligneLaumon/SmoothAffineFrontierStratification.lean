/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.LimitsOver
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.DescendClosedImmersion
import Sheaf.AlgebraicGeometry.DescendSmoothQcqs
import Sheaf.AlgebraicGeometry.FiniteFieldClosedSubschemeDescent
import Sheaf.AlgebraicGeometry.GeometricReducedFiniteTypePerfectField
import Sheaf.AlgebraicGeometry.OpenImmersionInverseLimitDescent
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.DeligneLaumon.AffineGeometricComponentsFiniteExtension
import Sheaf.Topology.NoetherianGoodStratificationRefinement
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smooth affine frontier stratification over a finite subfield

Source: Stacks Project, Tags 0B8X, 06LH and 01ZM; `thm-zl-real-mixed-by-curves`
(blueprint: lem-zl-smooth-affine-frontier-stratification).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures

/-- A finite frontier refinement by smooth affine geometrically connected pieces, together
with one finite-field model for all objects and maps.

Source: Stacks Project, Tags 0B8X, 06LH and 01ZM; `thm-zl-real-mixed-by-curves`,
proof paragraphs 6--7 (blueprint: lem-zl-smooth-affine-frontier-stratification).

Proof: If the geometric fibre is empty, use the length-zero chain. Otherwise apply the
Noetherian frontier refinement and choose, on each irreducible component, a nonempty affine
open in the smooth locus. Noetherian induction gives the closed chain and its finite
disjoint open-and-closed pieces. The pieces have constant smooth relative dimension and
are geometrically connected. Finite presentation spreads the whole finite diagram,
including the maps and the containment in the prescribed strata, to one finite subfield;
enlarging that field makes every descended affine piece geometrically connected. The
zero-dimensional case is a finite smooth geometrically connected scheme over the finite
field and hence is `Spec` of that field. The empty case and all inclusions are included.
-/
theorem smooth_affine_frontier_stratification
    (D : FiniteFieldDatum.{u})
    (X₀ : Scheme.{u})
    (a₀ : X₀ ⟶ Spec (CommRingCat.of D.k₀))
    [IsSeparated a₀] [LocallyOfFiniteType (Over.mk a₀).hom] [QuasiCompact (Over.mk a₀).hom]
    (T : Scheme.FiniteLocallyClosedStratification
      (D.geometricFiber (Over.mk a₀)).left.nilradical.subscheme)
    (hTred : ∀ i : Fin T.n, IsReduced (T.domain i)) :
    ∃ (m : ℕ) (hm : 1 ≤ m),
      let km := D.extensionSubfield m hm
      let Sm := Spec (CommRingCat.of km)
      let Xm := (Over.pullback
        (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))).obj (Over.mk a₀)
      let X := D.geometricFiber (Over.mk a₀)
      let Sbase := Spec (CommRingCat.of D.k)
      let BC : Over Sm ⥤ Over Sbase := Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap km D.k)))
      ∃ (χ : BC.obj Xm ≅ X),
        ∃ (t : ℕ) (Z : Fin (t + 1) → Over Sm),
          (∀ a : Fin (t + 1), IsReduced (Z a).left) ∧
          ∃ (hZ0 : Z 0 = Over.mk (Xm.left.nilradical.subschemeι ≫ Xm.hom))
            (hZt : Z (Fin.last t) = Over.mk (Scheme.emptyTo Sm))
            (ι : ∀ a : Fin t, Z a.succ ⟶ Z a.castSucc)
            (z : ∀ a : Fin (t + 1), Z a ⟶ Xm),
            (∀ a : Fin t, IsClosedImmersion (ι a).left) ∧
            (z 0 = eqToHom hZ0 ≫ Over.homMk Xm.left.nilradical.subschemeι (by simp)) ∧
            (∀ a : Fin t, z a.succ = ι a ≫ z a.castSucc) ∧
            ∃ (U : Fin t → Over Sm) (u : ∀ a : Fin t, U a ⟶ Z a.castSucc),
              (∀ a : Fin t, IsOpenImmersion (u a).left) ∧
              (∀ a : Fin t, Set.range (u a).left = (Set.range (ι a).left)ᶜ) ∧
              ∃ (r : Fin t → ℕ) (V : ∀ a : Fin t, Fin (r a) → Over Sm)
                (d : ∀ a : Fin t, Fin (r a) → ℕ)
                (v : ∀ (a : Fin t) (b : Fin (r a)), V a b ⟶ U a),
                (∀ (a : Fin t) (b : Fin (r a)), Nonempty (V a b).left) ∧
                (∀ (a : Fin t) (b : Fin (r a)), IsReduced (V a b).left) ∧
                (∀ (a : Fin t) (b : Fin (r a)), IsAffine (V a b).left) ∧
                (∀ (a : Fin t) (b : Fin (r a)), GeometricallyConnected (V a b).hom) ∧
                (∀ (a : Fin t) (b : Fin (r a)), SmoothOfRelativeDimension (d a b) (V a b).hom) ∧
                (∀ (a : Fin t) (b : Fin (r a)),
                  IsOpenImmersion (v a b).left ∧ IsClosedImmersion (v a b).left) ∧
                (∀ (a : Fin t) (b : Fin (r a)), d a b = 0 → Nonempty (V a b ≅ Over.mk (𝟙 Sm))) ∧
                (∀ (a : Fin t), ⋃ b : Fin (r a), Set.range (v a b).left =
                  Set.univ) ∧
                (∀ (a : Fin t) (b₁ b₂ : Fin (r a)), b₁ ≠ b₂ →
                  Disjoint (Set.range (v a b₁).left) (Set.range (v a b₂).left)) ∧
                (∀ (a : Fin t) (b : Fin (r a)),
                  ∃ (ν : Fin T.n) (j : (BC.obj (V a b)).left ⟶ T.domain ν),
                  IsImmersion j ∧
                  j ≫ T.immersion ν ≫
                      (D.geometricFiber (Over.mk a₀)).left.nilradical.subschemeι =
                    (BC.map (v a b ≫ u a ≫ z a.castSucc) ≫ χ.hom).left)
      := by sorry

end WeilConjectures
