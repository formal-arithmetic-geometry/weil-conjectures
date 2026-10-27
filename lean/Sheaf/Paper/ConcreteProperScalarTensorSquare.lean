/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import Sheaf.Paper.ConcreteProjectionFactorizationData
import all Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.SixFunctors.ScalarPullbackTensorCoherence
import Sheaf.SecSmoothPurity.ProperScalarCounitSquare

/-! # The proper scalar and tensor square

Source: Stacks Project, Cohomology on Sites.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.ConcreteProjectionReduction
open AlgebraicGeometry.ProEtale.OpenScalarTensor
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Scheme.proEtaleRingDerivedAdjunction Scheme.proEtaleRingModulePullback

private theorem inverse_mate_eq
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {U : D ⥤ C} {M : E ⥤ F} {V : F ⥤ E}
    (a : L ⊣ U) (b : M ⊣ V) {G : C ⥤ E} {H : D ⥤ F}
    (d : U ⋙ G ⟶ H ⋙ V) (c : G ⋙ M ⟶ L ⋙ H)
    (hc : ∀ N, M.map (d.app N) ≫ b.counit.app (H.obj N) =
      c.app (U.obj N) ≫ H.map (a.counit.app N)) :
    ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ d)).natTrans = c := by
  have he : mateEquiv a b (TwoSquare.mk _ _ _ _ c) = TwoSquare.mk _ _ _ _ d := by
    ext N
    apply (b.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
      mateEquiv_counit]
    exact (hc N).symm
  have h := congrArg (fun z ↦ ((mateEquiv a b).symm z).natTrans) he
  simpa only [Equiv.symm_apply_apply] using h.symm

private theorem proper_published {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    PurCompactSupport.properComparison (coefficientChange φ) g =
      directImageScalarComparison φ g := by
  exact inverse_mate_eq (directImageScalarAdjunction φ Z)
    (directImageScalarAdjunction φ Y) (directImageScalarRestrictionIso φ g).hom
    (directImageScalarComparison φ g)
    (fun H ↦ (properScalarCounitSquare φ g).2.2.1 H |>.2)

variable (m : Models.{u}) (choices : Choices m)

/-- Scalar change commutes with the counit-defined proper projection.
Source: Stacks Tag 0E48, remark-compatible-with-diagram; Tag 0B56.
(blueprint: lem-sf-concrete-proper-scalar-tensor-square).

Proof: use the normalized scalar/pullback isomorphism lambda for the geometric
coefficient square. The normalized tensor comparisons commute with lambda: on
flat K-flat representatives both maps split the same balanced tensor into its
first and second factors. The scalar mate normalization identifies properScalar
with the proper-adjunction mate of lambda. Transpose the displayed equation under
the B-coefficient geometric adjunction. Expand properProjection by its counit
formula. Naturality of lambda and the counit moves the scalar comparison through
the proper projection. The tensor compatibility just described identifies the
two resulting arrows. Injectivity of the adjunction bijection proves the equation.
No coefficient-flatness, boundedness, geometric properness, or invertibility of
properScalar or properProjection is used. Zero inputs, empty schemes, and identity
coefficient maps satisfy the same counit equations. -/
theorem proper_scalar_tensor_square
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (M : proEtaleDerivedCategory Z A) (L : proEtaleDerivedCategory Y A) :
    (scalar m φ Y).map (properProjection m A g M L) ≫
      (properScalar m φ g).app (input m A g M L) ≫
      (properImage B g).map (inputComparison m choices φ g M L).hom =
    (choices.scalarTensor φ Y).iso.hom.app ((properImage A g).obj M, L) ≫
      (tensor m B Y).map (Prod.mkHom ((properScalar m φ g).app M) (𝟙 _)) ≫
      properProjection m B g ((scalar m φ Z).obj M) ((scalar m φ Y).obj L) := by
  have he : properScalar m φ g =
      (mateEquiv (directImageConstantAdjunction A g)
        (directImageConstantAdjunction B g) (lambda m φ g).hom).natTrans := by
    ext N
    simp only [properScalar, proper_published, lambda, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      directImageScalarComparison, mateEquiv_apply, TwoSquare.mk, TwoSquare.natTrans,
      Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.map_comp, Functor.comp_map, Functor.comp_obj, Category.id_comp,
      Category.assoc]
    dsimp only [Functor.comp_obj, Functor.id_obj]
    simp only [Category.comp_id]
    have hy := (directImageConstantAdjunction B g).unit.naturality
      ((scalarIso m φ Y).hom.app ((directImageConstantPush A g).obj N))
    dsimp only [Functor.comp_map, Functor.id_map] at hy
    rw [← reassoc_of% hy]
    have hz := (scalarIso m φ Z).inv.naturality
      ((directImageConstantAdjunction A g).counit.app N)
    dsimp only [Functor.comp_obj, Functor.id_obj] at hz
    simp only [← (directImageConstantPush B g).map_comp]
    erw [← hz]
    simp only [Functor.map_comp]
    erw [Category.id_comp]
    rfl
  rw [he]
  exact tensor_mate_coherence
    (directImageConstantAdjunction A g) (directImageConstantAdjunction B g)
    (tensor m A Y) (tensor m A Z) (tensor m B Y) (tensor m B Z)
    (restrictionTensor m A g).hom (choices.scalarTensor φ Y).iso.hom
    (choices.scalarTensor φ Z).iso.hom (restrictionTensor m B g).hom
    (lambda m φ g) (scalarPullbackTensorCoherence m choices φ g) M L


end WeilConjectures.ConcreteProjectionReduction
