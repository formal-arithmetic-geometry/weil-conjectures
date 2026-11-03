/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FinitePullbackTensorFixedCoordinates

/-! Core scalar naturality equation after fixed pullback-coordinate naturality.
(blueprint: lem-sf-finite-partial-tensor-identity-naturality-coordinates-expanded-core) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open CompactSupportFiniteProjection

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

attribute [local irreducible] realization AlgebraicGeometry.ProEtale.derivedTensor

private theorem tensorCoordinates_naturality_both
    (S : SixFunctorFiniteOperations D C E n hn) (X : SixFunctorSpace D)
    {M M' : sixFunctorFiniteCategory D C E n hn X}
    {L L' : finiteTorConstructibleCategory C.l E n hn X.obj.left}
    (f : M ⟶ M') (g : L ⟶ L') :
    let R := realization (C := C) (E := E) (n := n) (hn := hn) X
    let F := coordinates (C := C) (E := E) (n := n) (hn := hn) X
    let Q := (finiteTorConstructible C.l E n hn X.obj.left).ι ⋙ R.inverse
    let T := Functor.uncurry.obj (partialTensor S X)
    let W := Functor.uncurry.obj (fixedTensor (C := C) (E := E) (n := n) X)
    F.map (T.map (Prod.mkHom f g)) ≫ (tensorCoordinates S X M' L').hom =
      (tensorCoordinates S X M L).hom ≫ W.map (Prod.mkHom (F.map f) (Q.map g)) := by
  dsimp only
  let R := realization (C := C) (E := E) (n := n) (hn := hn) X
  let W := fixedTensor (C := C) (E := E) (n := n) X
  let t := (W.map (R.inverse.map f.hom)).app (R.inverse.obj L.obj) ≫
    (W.obj (R.inverse.obj M'.obj)).map (R.inverse.map g.hom)
  have h : ((Functor.uncurry.obj (partialTensor S X)).map
      (Prod.mkHom f g)).hom = R.functor.map t := by
    change (R.functor.map ((W.map (R.inverse.map f.hom)).app _) ≫
      R.functor.map ((W.obj _).map (R.inverse.map (𝟙 L.obj)))) ≫
      (R.functor.map ((W.map (R.inverse.map (𝟙 M'.obj))).app _) ≫
        R.functor.map ((W.obj _).map (R.inverse.map g.hom))) = R.functor.map t
    simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id,
      t, Functor.map_comp]
  exact (congrArg (fun z ↦ R.inverse.map z ≫ R.unitIso.inv.app _) h).trans
    (R.unitInv_naturality t)

attribute [local irreducible] partialTensor tensorCoordinates fixedPullRealization
  pullbackTensorComparison targetCoordinates

set_option maxHeartbeats 800000 in
-- The product-category comparison needs extra heartbeats for its component expansions.
/-- The scalar naturality calculation after applying naturality of the fixed-coordinate
pullback comparison. This is the remaining tensor-coordinate and upper-star square.
Source: Stacks Project, sites-cohomology.tex, Tag 07A4, and the fixed-coordinate
expansion in `pullbackTensor_fixed_coordinates`.
(blueprint: lem-sf-finite-partial-tensor-identity-naturality-coordinates-expanded-core) -/
theorem finitePartialTensor_identityNaturality_coordinates_expanded_core
    (S : SixFunctorFiniteOperations D C E n hn) (X : SixFunctorSpace D) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let U := S.finite.pull (𝟙 X)
    let V := CompactSupportFiniteProjection.torPull S (𝟙 X)
    let T := Functor.uncurry.obj (CompactSupportFiniteProjection.partialTensor S X)
    ∀ (M M' : sixFunctorFiniteCategory D C E n hn X)
      (L L' : finiteTorConstructibleCategory C.l E n hn X.obj.left)
      (f : M ⟶ M') (g : L ⟶ L'),
      (CompactSupportFiniteProjection.fixedPullRealization S (𝟙 X)
          (T.obj (M, L))).hom ≫
        (CompactSupportFiniteProjection.fixedDerivedPull
          (C := C) (E := E) (n := n) (𝟙 X)).map
          ((CompactSupportFiniteProjection.coordinates (C := C) (E := E) (n := n)
            (hn := hn) X).map (T.map (Prod.mkHom f g))) ≫
        (CompactSupportFiniteProjection.fixedDerivedPull
          (C := C) (E := E) (n := n) (𝟙 X)).map
          (CompactSupportFiniteProjection.tensorCoordinates S X M' L').hom ≫
        ((AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison
          (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing C.l E n))) ((𝟙 X : X ⟶ X).hom.left)).app
          ((CompactSupportFiniteProjection.coordinates (C := C) (E := E) (n := n)
            (hn := hn) X).obj M')).app
          ((realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj L'.obj) ≫
        ((CompactSupportFiniteProjection.fixedTensor (C := C) (E := E) (n := n) X).map
          (CompactSupportFiniteProjection.fixedPullRealization S (𝟙 X) M').inv).app
          ((CompactSupportFiniteProjection.fixedDerivedPull
            (C := C) (E := E) (n := n) (𝟙 X)).obj
            ((realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj L'.obj)) =
      (CompactSupportFiniteProjection.coordinates (C := C) (E := E) (n := n)
          (hn := hn) X).map
          (CompactSupportFiniteProjection.pullbackTensorComparison S (𝟙 X) M L).hom ≫
        (CompactSupportFiniteProjection.coordinates (C := C) (E := E) (n := n)
          (hn := hn) X).map (T.map (Prod.mkHom (U.map f) (V.map g))) ≫
        (CompactSupportFiniteProjection.targetCoordinates S (𝟙 X) (U.obj M') L').hom := by
  dsimp only
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let R := realization (C := C) (E := E) (n := n) (hn := hn) X
  let F := coordinates (C := C) (E := E) (n := n) (hn := hn) X
  let Q := (finiteTorConstructible C.l E n hn X.obj.left).ι ⋙ R.inverse
  let T := Functor.uncurry.obj (partialTensor S X)
  let W := Functor.uncurry.obj (fixedTensor (C := C) (E := E) (n := n) X)
  let P := fixedDerivedPull (C := C) (E := E) (n := n) (𝟙 X)
  let U := S.finite.pull (𝟙 X)
  let V := torPull S (𝟙 X)
  let J := ObjectProperty.ιOfLE
    (show finiteTorConstructible C.l E n hn X.obj.left ≤
      intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left from fun _ h ↦ h.1)
  let a : U ⋙ F ≅ F ⋙ P := pullCoordinatesIso S (𝟙 X)
  let c : V ⋙ Q ≅ Q ⋙ P := Functor.isoWhiskerLeft J a
  have ha (K : sixFunctorFiniteCategory D C E n hn X) :
      a.app K = fixedPullRealization S (𝟙 X) K := by
    apply Iso.ext
    exact pullCoordinatesIso_hom_app S (𝟙 X) K
  have hah (K : sixFunctorFiniteCategory D C E n hn X) :
      a.hom.app K = (fixedPullRealization S (𝟙 X) K).hom := congrArg Iso.hom (ha K)
  have hai (K : sixFunctorFiniteCategory D C E n hn X) :
      a.inv.app K = (fixedPullRealization S (𝟙 X) K).inv := congrArg Iso.inv (ha K)
  let q : T ⋙ F ≅ F.prod Q ⋙ W := NatIso.ofComponents
    (fun KL ↦ tensorCoordinates S X KL.1 KL.2) (by
      rintro ⟨M, L⟩ ⟨M', L'⟩ ⟨f, g⟩
      exact tensorCoordinates_naturality_both S X f g)
  let μ := AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
      ((𝟙 X : X ⟶ X).hom.left)
  -- Uncurrying postcomposition preserves maps propositionally via map_comp.
  let β : (F.prod Q ⋙ W) ⋙ P ⟶ (F ⋙ P).prod (Q ⋙ P) ⋙ W :=
    { app := fun KL ↦ (μ.app (F.obj KL.1)).app (Q.obj KL.2)
      naturality := by
        intro A B k
        have h := (Functor.uncurry.map μ).naturality
          (Prod.mkHom (F.map k.1) (Q.map k.2))
        change
          (P.map (((fixedTensor (C := C) (E := E) (n := n) X).map
            (F.map k.1)).app (Q.obj A.2)) ≫
            P.map (((fixedTensor (C := C) (E := E) (n := n) X).obj
              (F.obj B.1)).map (Q.map k.2))) ≫
            (μ.app (F.obj B.1)).app (Q.obj B.2) =
          (μ.app (F.obj A.1)).app (Q.obj A.2) ≫
            W.map (Prod.mkHom (P.map (F.map k.1)) (P.map (Q.map k.2))) at h
        simpa only [Functor.comp_map, Functor.prod_map, Functor.comp_obj,
          Functor.prod_obj, W, Functor.uncurry_obj_map,
          CategoryTheory.Functor.map_comp] using h }
  -- Both sides now arise from natural transformations on the product category.
  let η : T ⋙ F ⋙ P ⟶ (U ⋙ F).prod (Q ⋙ P) ⋙ W :=
    Functor.whiskerRight q.hom P ≫
      β ≫
      Functor.whiskerRight (a.inv.prod (𝟙 (Q ⋙ P))) W
  let τ : U.prod V ⋙ T ⋙ F ⟶ (U ⋙ F).prod (Q ⋙ P) ⋙ W :=
    Functor.whiskerLeft (U.prod V) q.hom ≫
      Functor.whiskerRight (NatTrans.prod (𝟙 (U ⋙ F)) c.hom) W
  intro M M' L L' f g
  have hη := η.naturality (Prod.mkHom f g)
  have hτ := τ.naturality (Prod.mkHom f g)
  -- The existing expansion fixes the component, including both coefficient units.
  have hformula : F.map (pullbackTensorComparison S (𝟙 X) M L).hom ≫
      τ.app (M, L) = (fixedPullRealization S (𝟙 X) (T.obj (M, L))).hom ≫
        η.app (M, L) := by
    simpa only [τ, η, β, q, c, W, NatTrans.prod, hah, hai, F, Q, T, P, U, V, J, μ, R,
    ObjectProperty.ι_obj, ObjectProperty.ιOfLE, Functor.uncurry_obj_obj,
      Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, NatIso.ofComponents_hom_app, NatTrans.prod_app_fst,
      NatTrans.prod_app_snd, NatTrans.id_app, Functor.uncurry_obj_map,
      Functor.uncurry_map_app, Functor.prod_obj, Functor.comp_obj,
      CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id,
      Category.assoc,
      targetCoordinates, Iso.trans_hom, Functor.mapIso_hom]
      using pullbackTensor_fixed_coordinates S (𝟙 X) M L
  have h : (fixedPullRealization S (𝟙 X) (T.obj (M, L))).hom ≫
      (T ⋙ F ⋙ P).map (Prod.mkHom f g) ≫ η.app (M', L') =
      F.map (pullbackTensorComparison S (𝟙 X) M L).hom ≫
        (U.prod V ⋙ T ⋙ F).map (Prod.mkHom f g) ≫ τ.app (M', L') := by
    rw [hη, ← Category.assoc, ← hformula, Category.assoc, ← hτ]
  simpa only [τ, η, β, q, c, W, NatTrans.prod, hah, hai, F, Q, T, P, U, V, J, μ, R,
    ObjectProperty.ι_obj, ObjectProperty.ιOfLE, Functor.uncurry_obj_obj,
      Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatIso.ofComponents_hom_app, NatTrans.prod_app_fst,
    NatTrans.prod_app_snd, NatTrans.id_app, Functor.uncurry_obj_map,
    Functor.uncurry_map_app, Functor.prod_obj, Functor.prod_map, Functor.comp_obj,
    Functor.comp_map, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    Category.comp_id, Category.assoc,
    targetCoordinates, Iso.trans_hom, Functor.mapIso_hom] using h

end WeilConjectures
