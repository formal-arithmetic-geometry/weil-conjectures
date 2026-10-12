/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedDirectImageInternalHom
public import Sheaf.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint
public import Sheaf.AlgebraicGeometry.DQCoheratorAdjunction
import Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction
import Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

/-! # Coherated sheaf derived Hom adjunction

Source: Stacks Project, Duality for Schemes, Lemma 48.3.6 (Tag 0A9Q), with
equation-sheafy-trace (48.3.5.1) defining the sheafy trace
(blueprint: lem-pc-qcqs-sheaf-rhom-adjunction).
-/

@[expose] public section

universe u₁ w₁

open CategoryTheory MonoidalCategory Opposite
open scoped CategoryTheory.Prod

namespace AlgebraicGeometry

set_option autoImplicit false

/-- For qcqs schemes and a qcqs morphism `f`, let `adj : Rf_* ⊣ a` be the restricted
adjunction on `D_QCoh` and let `c` be the internal-Hom comparison
`Rf_* RHom_X(L, M) ⟶ RHom_Y(Rf_* L, Rf_* M)`, tied by the mate equation `hc` of
`exists_derivedDirectImage_internalHom_comparison` (lem-pc-sheaf-rhom-projection-formula).
The sheafy trace `c(L, aK) ≫ RHom_Y(Rf_* L, ε_K)` is natural in `L` and `K`, and it becomes
invertible after applying the coherator `DQ`.
Source: Stacks Project, Tag 0A9Q and equation 48.3.5.1
(blueprint: lem-pc-qcqs-sheaf-rhom-adjunction).

Proof:
1. The comparison of `lem-pc-sheaf-rhom-projection-formula` at `(L, aK)`, followed by
internal Hom applied to the counit of `lem-pc-qcqs-derived-direct-image-right-adjoint`, is the
map of the statement. Naturality of the comparison, internal Hom and the counit proves
naturality.
2. By `lem-pc-dq-coherator-adjunction`, test the map on Hom from every quasi-coherent M.
3. The adjunction `lem-pc-ringed-spaces-derived-adjoint-general` and
`lem-sc-derived-internal-hom-adjunction` identify its source Hom with
Hom_X(Lf*M ⊗ L, aK). This tensor is quasi-coherent by
`lem-pc-derived-pullback-tensor-qcoh`. The restricted adjunction identifies it with
Hom_Y(Rf*(Lf*M ⊗ L), K). By `lem-pc-projection-formula` and tensor symmetry this is
Hom_Y(M ⊗ Rf*L, K), hence Hom_Y(M, RHom(Rf*L, K)) by tensor-Hom adjunction again.
4. Naturality and the triangle identities identify the map with the identity under
these bijections. Yoneda in the coherator adjunction proves invertibility. -/
theorem qcqsSheafRHomAdjunction (X Y : Scheme.{u₁})
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hpres : ∀ E : schemeDerivedCategory X, schemeDerivedQCohProperty X E →
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E))
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ hpres E.obj E.property) ⊣ a)
    (DQ : schemeDerivedCategory Y ⥤ schemeDerivedQCohCategory Y)
    (coh : (schemeDerivedQCohProperty Y).ι ⊣ DQ)
    (p : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (bX : ∀ L : schemeDerivedCategory X, tensorRight L ⊣
      (Functor.curry.obj
        (derivedInternalHom (Opens.grothendieckTopology X) X.toRingedSpace.sheaf)).obj
          (op L))
    (bY : ∀ L : schemeDerivedCategory Y, tensorRight L ⊣
      (Functor.curry.obj
        (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)).obj
          (op L))
    (t : tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X))
    (c : derivedInternalHom (Opens.grothendieckTopology X) X.toRingedSpace.sheaf ⋙
        schemeDerivedDirectImage f ⟶
      (schemeDerivedDirectImage f).op.prod (schemeDerivedDirectImage f) ⋙
        derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)
    (hc : ∀ (L M : schemeDerivedCategory X) (A : schemeDerivedCategory Y)
      (α : A ⟶ (schemeDerivedDirectImage f).obj
        ((derivedInternalHom (Opens.grothendieckTopology X) X.toRingedSpace.sheaf).obj
          (op L, M))),
      ((bY ((schemeDerivedDirectImage f).obj L)).homEquiv A
        ((schemeDerivedDirectImage f).obj M)).symm (α ≫ c.app (op L, M)) =
      p.homEquiv (A ⊗ (schemeDerivedDirectImage f).obj L) M
        (t.hom.app (A, (schemeDerivedDirectImage f).obj L) ≫
          (𝟙 ((derivedPullback f).obj A) ⊗ₘ p.counit.app L) ≫
          ((bX L).homEquiv ((derivedPullback f).obj A) M).symm
            ((p.homEquiv A
              ((derivedInternalHom (Opens.grothendieckTopology X)
                X.toRingedSpace.sheaf).obj (op L, M))).symm α))) :
    (∀ (L L' : schemeDerivedQCohCategory X) (K K' : schemeDerivedQCohCategory Y)
        (g : L' ⟶ L) (h : K ⟶ K'),
        (schemeDerivedDirectImage f).map
            ((derivedInternalHom (Opens.grothendieckTopology X) X.toRingedSpace.sheaf).map
              (g.hom.op ×ₘ (a.map h).hom)) ≫
          c.app (op L'.obj, (a.obj K').obj) ≫
            (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).map
              (𝟙 _ ×ₘ (adj.counit.app K').hom) =
        (c.app (op L.obj, (a.obj K).obj) ≫
            (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).map
              (𝟙 _ ×ₘ (adj.counit.app K).hom)) ≫
          (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).map
            (((schemeDerivedDirectImage f).map g.hom).op ×ₘ h.hom)) ∧
      (∀ (L : schemeDerivedQCohCategory X) (K : schemeDerivedQCohCategory Y),
        IsIso (DQ.map (c.app (op L.obj, (a.obj K).obj) ≫
          (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).map
            (𝟙 _ ×ₘ (adj.counit.app K).hom)))) := by
  sorry

end AlgebraicGeometry
