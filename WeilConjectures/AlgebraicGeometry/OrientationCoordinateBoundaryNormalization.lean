/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityAffineLineOrientationData

/-! # Uniqueness of the normalized affine-line support boundary

The snake-normalized boundary is independent of the chosen presentation of the
support sequence. (blueprint: lem-pur-orientation-coordinate-boundary-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

/-- The pro-etale support boundaries carried by an orientation chart and by a
coordinate model coincide after injective-resolution normalization.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-affine-line-orientation.proof.md, support-boundary normalization.
Proof: evaluate both normalization predicates on a common bounded-below injective
resolution. Their model boundaries are the same snake connecting morphism of the same
kernel/restriction short exact complex; proof irrelevance identifies the exactness
witnesses. The canonical model comparison isomorphisms then cancel, and naturality
of injective resolutions transports equality back to the derived support functor.
(blueprint: lem-pur-orientation-coordinate-boundary-normalization). -/
theorem orientation_coordinate_boundary_normalization (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (D : OrientationSupportData P h Y) (M : CoordinateBoundaryModel P Y) :
    (D.boundary 1).app ⟨P.gysinInput h Y, trivial⟩ =
      (M.boundaryPro 1).app ⟨P.gysinInput h Y, trivial⟩ := by
  classical
  let C := Sheaf (Scheme.ProEt.topology (Line Y)) (Modules P)
  let Q := (InjectiveObject.ι C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh
  let N := Q.objPreimage (P.gysinInput h Y)
  obtain ⟨L, hL⟩ := HomotopyCategory.Plus.quotient_obj_surjective N
  let I := (InjectiveObject.ι C).mapCochainComplexPlus.obj L
  have (r : ℤ) : Injective (I.obj.X r) :=
    inferInstanceAs (Injective (L.obj.X r).obj)
  let e : DerivedCategory.Plus.Q.obj I ≅ P.gysinInput h Y :=
    Q.mapIso (eqToIso hL) ≪≫ Q.objObjPreimageIso (P.gysinInput h Y)
  obtain ⟨wD, hD, hwD⟩ := D.boundary_normalized I
  obtain ⟨wM, hM, hwM⟩ := M.pro_normalized I
  have hmodel := (hwD 1).trans (hwM 1).symm
  have hb : (D.boundary 1).app ⟨DerivedCategory.Plus.Q.obj I, trivial⟩ =
      (M.boundaryPro 1).app ⟨DerivedCategory.Plus.Q.obj I, trivial⟩ := by
    dsimp only [Sheaf.supportSequenceModelBoundary] at hmodel
    simp only [← Category.assoc] at hmodel
    exact (cancel_epi _).1 ((cancel_mono _).1 hmodel)
  let e' := (⊤ : ObjectProperty (DerivedCategory.Plus C)).isoMk
    (X := ⟨DerivedCategory.Plus.Q.obj I, trivial⟩)
    (Y := ⟨P.gysinInput h Y, trivial⟩) e
  have hd := (D.boundary 1).naturality e'.hom
  have hm := (M.boundaryPro 1).naturality e'.hom
  have hb' : (D.boundary 1).app ⟨P.gysinInput h Y, trivial⟩ =
      (M.boundaryPro 1).app ⟨P.gysinInput h Y, trivial⟩ := by
    rw [hb] at hd
    exact (cancel_epi _).1 (hd.trans hm.symm)
  exact hb'

end WeilConjectures.PurityFiniteSetting
