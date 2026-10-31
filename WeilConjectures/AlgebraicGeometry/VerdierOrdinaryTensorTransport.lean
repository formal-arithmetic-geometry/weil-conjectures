/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VerdierHomChainCompositionData

/-! # Ordinary and tensor transpose transport for the Verdier composition

Source: current blueprint, fix-prop-coherence.proof.md, adjoint-mate sentence;
proof step 3 of lem-sf-verdier-hom-chain-composition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

namespace WeilConjectures.VerdierHomChainComposition
open TensorHomCoefficientTransposes

variable {D : FiniteFieldDatum.{u}} {B : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic B.l) E]
  [FiniteDimensional (Padic B.l) E] {n : ℕ} {hn : 1 ≤ n}
  (S : SixFunctorOperationDatum D B E n hn) (s : PodCoefficientStage)

variable {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
  (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
  (cx : Compactification (f ≫ g).hom.left)
  (Rf : Domain S s f cf) (Rg : Domain S s g cg) (Rx : Domain S s (f ≫ g) cx)


private theorem inverse_right_uniq
    {A B : Type*} [Category A] [Category B] {L : A ⥤ B}
    {R R' : B ⥤ A} (adj : L ⊣ R) (adj' : L ⊣ R')
    (T : A) (N : B) (v : T ⟶ R.obj N) :
    (adj'.homEquiv T N).symm (v ≫ (adj.rightAdjointUniq adj').hom.app N) =
      (adj.homEquiv T N).symm v := by
  rw [adj'.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_symm_rightAdjointUniq_hom_app, Adjunction.homEquiv_counit]

private theorem inverse_tensor_coordinate
    {W : SixFunctorSpace D}
    {C C' : SixFunctorClosedDomain (PodCoefficientStage.domain S s W)
      (PodCoefficientStage.homPairs (S := S) s W)
      (PodCoefficientStage.internalHom (S := S) s W)}
    (h : C = C') (M T N : (PodCoefficientStage.domain S s W).FullSubcategory)
    (v : T ⟶ (sixFunctorDomainHom _ _ _ C.homPermitted C.homDomain).obj (op M, N)) :
    (tensorCoordinate S s h M T).hom ≫
        (((C'.closed.adjunction M).ofNatIsoLeft
          (@BraidedCategory.tensorLeftIsoTensorRight _ _ C'.closed.monoidal
            C'.symmetric.toBraidedCategory M).symm).homEquiv T N).symm v =
      (((C.closed.adjunction M).ofNatIsoLeft
          (@BraidedCategory.tensorLeftIsoTensorRight _ _ C.closed.monoidal
            C.symmetric.toBraidedCategory M).symm).homEquiv T N).symm v := by
  subst C'
  simp only [tensorCoordinate, eqToIso_refl, Iso.refl_hom, Category.id_comp]

/-- The first two inverse transposes respect the ordinary compositor and
postcomposition by the exceptional compositor. Only these transposes occur here;
there is no projection, exceptional transpose, or final tensor transpose.
Source: fix-prop-coherence.proof.md, adjoint-mate sentence, expanded in step 3
(blueprint: lem-sf-verdier-ordinary-tensor-transport).
Proof: the direct compositor is rightAdjointUniq for the composite ordinary
adjunction transported along pullComposition. Applying the inverse Hom equivalence
therefore sends z followed by this compositor to pullComposition inverse followed
by the two successive inverse ordinary transposes. Target naturality moves the
exceptional compositor through the inverse ordinary and tensor transposes.
Identify the closed data on X by hX; source naturality of its tensor adjunction
moves pullComposition across the inverse tensor transpose. This gives the formula.
Every morphism lies in the displayed full subcategories, including zero objects,
and the argument applies to every coefficient stage without a faithfulness claim. -/
theorem ordinary_tensor_transport
    (hX : Rf.closedX = Rx.closedX)
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (N T : (PodCoefficientStage.domain S s Z).FullSubcategory)
    (z : T ⟶ (PodHomChain.sourceFunctor S s (f ≫ g) cx Rx M).obj N) :
    (tensorCoordinate S s hX M (Rx.pull.obj T)).hom ≫
        ((Rx.tensorAdjunctionX M).homEquiv _ _).symm
          ((Rx.ordinaryAdjunction.homEquiv T _).symm z) ≫
        (exceptionalComposition S s f g cf cg cx Rf Rg Rx).hom.app N =
      (tensorLeft Rf.closedX.closed.monoidal M).map
          ((pullComposition S s f g cf cg cx Rf Rg Rx).hom.app T) ≫
        ((Rf.tensorAdjunctionX M).homEquiv _ _).symm
          ((Rf.ordinaryAdjunction.homEquiv _ _).symm
            ((Rg.ordinaryAdjunction.homEquiv T _).symm
              (z ≫ (sourceCoordinate S s f g cf cg cx Rf Rg Rx M N).hom))) := by
  let H := PodCtfPairing.homX S s f cf Rf M
  let e := exceptionalComposition S s f g cf cg cx Rf Rg Rx
  let p := pullComposition S s f g cf cg cx Rf Rg Rx
  let K := H.obj (Rf.exceptional.obj (Rg.exceptional.obj N))
  let w := (Rg.ordinaryAdjunction.homEquiv T (Rf.direct.obj K)).symm
    (z ≫ (sourceCoordinate S s f g cf cg cx Rf Rg Rx M N).hom)
  have ho : (Rx.ordinaryAdjunction.homEquiv T _).symm z ≫ H.map (e.hom.app N) =
      p.hom.app T ≫ (Rf.ordinaryAdjunction.homEquiv _ K).symm w := by
    let adj := (Rg.ordinaryAdjunction.comp Rf.ordinaryAdjunction).ofNatIsoLeft p.symm
    have hu := inverse_right_uniq Rx.ordinaryAdjunction adj T K
      (z ≫ Rx.direct.map (H.map (e.hom.app N)))
    rw [Rx.ordinaryAdjunction.homEquiv_naturality_right_symm] at hu
    rw [Adjunction.homEquiv_ofNatIsoLeft_symm_apply,
      Adjunction.comp_homEquiv] at hu
    simpa only [w, sourceCoordinate, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, directComposition, adj, e, p, Equiv.symm_trans_apply,
      Iso.symm_inv, Category.assoc, H, K, PodCtfPairing.homX,
      Functor.comp_obj] using hu.symm
  have ht := inverse_tensor_coordinate S s hX M (Rx.pull.obj T)
    (Rx.exceptional.obj N) ((Rx.ordinaryAdjunction.homEquiv T _).symm z)
  change (tensorCoordinate S s hX M (Rx.pull.obj T)).hom ≫
      ((Rx.tensorAdjunctionX M).homEquiv _ _).symm
        ((Rx.ordinaryAdjunction.homEquiv T _).symm z) =
    ((Rf.tensorAdjunctionX M).homEquiv _ _).symm
      ((Rx.ordinaryAdjunction.homEquiv T _).symm z) at ht
  rw [← Category.assoc, ht]
  change ((Rf.tensorAdjunctionX M).homEquiv _ _).symm
      ((Rx.ordinaryAdjunction.homEquiv T _).symm z) ≫ e.hom.app N = _
  exact ((Rf.tensorAdjunctionX M).homEquiv_naturality_right_symm
    ((Rx.ordinaryAdjunction.homEquiv T _).symm z) (e.hom.app N)).symm.trans
      ((congrArg ((Rf.tensorAdjunctionX M).homEquiv (Rx.pull.obj T) _).symm ho).trans
        ((Rf.tensorAdjunctionX M).homEquiv_naturality_left_symm
          (p.hom.app T) ((Rf.ordinaryAdjunction.homEquiv _ K).symm w)))

end WeilConjectures.VerdierHomChainComposition
