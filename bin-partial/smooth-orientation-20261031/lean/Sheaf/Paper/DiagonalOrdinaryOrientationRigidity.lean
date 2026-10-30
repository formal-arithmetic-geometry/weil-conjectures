/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.Paper.PurityDiagonalDualizingData
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import Sheaf.AlgebraicGeometry.AffineTraceRightNormalForm
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.SixFunctors.OpenClosed.Conservative
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Rigidity of coordinate-normalized diagonal orientations

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-orientation,
thm-pur-diagonal-dualizing-object.proof.md, canonicity paragraph;
Stacks Tags 06XS, 03EM and 04TQ.
(blueprint: lem-pur-diagonal-ordinary-orientation-rigidity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

attribute [local instance] Sheaf.monoidalCategory

private theorem base_normal_form (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    Nonempty (Etale.affineLinearBaseCoefficient A N hA S d ≅
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf A N S hA (d : ℤ)))⟦2 * (d : ℤ)⟧) := by
  let E := fun d : ℕ ↦ Scheme.finiteEtaleTateSheaf A N S hA (d : ℤ)
  have hflat (d : ℕ) : ObjectProperty.flat (E d) := by
    apply (ObjectProperty.flat_iff_preservesFiniteLimits _).2
    exact (Scheme.finite_etale_torsion_twist_line S N hN
      (fun x ↦ by
        simpa only [map_natCast] using hS.map (S.presheaf.germ ⊤ x (by trivial)).hom)
      A hA d).2.2.1
  let t := Scheme.finiteEtaleTwistPullbackData A N hN hA
  induction d with
  | zero =>
    exact ⟨(Iso.refl _) ≪≫ (shiftFunctorZero _ ℤ).symm.app _⟩
  | succ d ih =>
    obtain ⟨e⟩ := ih
    let prod : E d ⊗ E 1 ≅ E (d + 1) :=
      t.p S hS d 1 ≪≫ eqToIso (congrArg (Scheme.finiteEtaleTateSheaf A N S hA)
        (by omega))
    refine ⟨((Etale.derivedTensorRight (ModuleCat.{u + 1} A) S
      ((Etale.ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).mapIso e) ≪≫ ?_⟩
    exact Etale.derivedTensorShiftIso (ModuleCat.{u + 1} A) _ _ (2 * (d : ℤ)) 2 ≪≫
      (shiftFunctor _ (2 * (d : ℤ) + 2)).mapIso
        (Etale.singleProductGeneral (ModuleCat.{u + 1} A) S (E d) (E 1) (E (d + 1))
          (hflat d) prod) ≪≫
      eqToIso (congrArg (fun a : ℤ ↦
        ((_root_.DerivedCategory.singleFunctor _ 0).obj (E (d + 1)))⟦a⟧) (by omega))

private theorem map_eq_of_cover (A : Type (u + 1)) [CommRing A]
    {S : Scheme.{u}} {I : Type u} (U : I → S.Opens)
    (hU : ∀ x : S, ∃ i : I, x ∈ U i)
    {K L : Etale.DerivedCategoryModule A S} (n : ℤ)
    [K.IsLE n] [L.IsGE n] (f g : K ⟶ L)
    (h : ∀ i, (Etale.ordinaryFinitePullback A (U i).ι).map f =
      (Etale.ordinaryFinitePullback A (U i).ι).map g) : f = g := by
  apply (_root_.DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE n).injective
  have hf : JointlyFaithful (fun i ↦ Etale.upperStar (ModuleCat.{u + 1} A) (U i).ι) := by
    apply JointlyReflectIsomorphisms.jointlyFaithful
    constructor
    intro M N z hz
    apply Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective
      (ModuleCat.{u + 1} A) (fun i ↦ (U i).ι) ?_ z hz
    intro x
    obtain ⟨i, hi⟩ := hU x
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  apply hf.map_injective
  intro i
  have hh : (Etale.upperStar (ModuleCat.{u + 1} A) (U i).ι).mapDerivedCategory.map f =
      (Etale.upperStar (ModuleCat.{u + 1} A) (U i).ι).mapDerivedCategory.map g := by
    let c := Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (U i).ι
    exact (NatIso.naturality_1 c f).symm.trans
      ((congrArg (fun z ↦ c.inv.app K ≫ z ≫ c.hom.app L) (h i)).trans
        (NatIso.naturality_1 c g))
  let e := (Etale.upperStar (ModuleCat.{u + 1} A) (U i).ι).mapDerivedCategoryHomologyFunctorIso n
  exact (NatIso.naturality_2 e f).symm.trans
    ((congrArg (fun z ↦ e.hom.app K ≫ z ≫ e.inv.app L)
      ((_root_.DerivedCategory.homologyFunctor _ n).congr_map hh)).trans
        (NatIso.naturality_2 e g))

/-- The affine-counit normalization determines an ordinary orientation uniquely.
This is only an equality test; no orientation is constructed by this assertion.
Source: blueprint diagonal-dualizing proof, canonicity paragraph, and the local
normalization in thm-pur-diagonal-dualizing-object, Step 6
(blueprint: lem-pur-diagonal-ordinary-orientation-rigidity).

Proof:
1. Smooth relative dimension d gives etale coordinate neighbourhoods U mapping
   etale to affine d-space over Y. Choose affine neighbourhoods so these maps are
   quasi-compact and separated. Noetherianity gives the compactifications used in
   the normalization equations. These U cover X, also when X is empty.
2. Choose t and D by exists_ordinaryFiniteP1Adjunction and N by
   nonempty_etaleCompactSupportNormalization; without them both predicates would
   be vacuous. Evaluate the two normalization predicates at these same t, D and N.
   Their right sides are identical.
3. Cancel the invertible source-etale locality map. Thus the pullbacks of e.inv
   and e'.inv agree on each coordinate neighbourhood.
4. The common Tate source becomes a sheaf in degree zero after shifting by -2d.
   Either isomorphism gives the same concentration for the dualizing target.
   Fully faithful single-complex embedding identifies the shifted maps with
   sheaf maps. Etale sheaf-Hom gluing tests their equality on this cover.
5. Undo the shift to obtain e.inv=e'.inv, hence e=e'. This uses no full
   faithfulness claim for restriction on arbitrary derived complexes, and works
   without absolute separatedness, for d=0, and for the empty scheme. -/
theorem diagonalOrdinaryOrientationRigidity (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    [IsNoetherian X] [IsNoetherian Y] [HasCompactification f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e e' : P.diagonalOrdinaryDualizing f ≅ P.diagonalTwistEtale X d)
    (he : P.DiagonalOrientationNormalization d f aY e)
    (he' : P.DiagonalOrientationNormalization d f aY e') : e = e' := by
  classical
  have hN : 0 < P.diagonalExponent := pow_pos P.coefficients.prime.out.pos P.level
  obtain ⟨t, D, _⟩ := Etale.exists_ordinaryFiniteP1Adjunction P.diagonalExponent hN
    P.Coefficient P.diagonalExponent_annihilates
  obtain ⟨N⟩ := Etale.nonempty_etaleCompactSupportNormalization P.Coefficient
  obtain ⟨c⟩ := base_normal_form P.diagonalExponent hN P.Coefficient
    P.diagonalExponent_annihilates X (P.diagonalExponent_isUnit (f ≫ aY)) d
  let L := (_root_.DerivedCategory.singleFunctor _ 0).obj
    (Scheme.finiteEtaleTateSheaf P.Coefficient P.diagonalExponent X
      P.diagonalExponent_annihilates (d : ℤ))
  have hle : _root_.DerivedCategory.TStructure.t.IsLE (L⟦2 * (d : ℤ)⟧)
      (-(2 * (d : ℤ))) :=
    _root_.DerivedCategory.TStructure.t.isLE_shift L 0 (2 * (d : ℤ)) _ (by omega)
  have hge : _root_.DerivedCategory.TStructure.t.IsGE (L⟦2 * (d : ℤ)⟧)
      (-(2 * (d : ℤ))) :=
    _root_.DerivedCategory.TStructure.t.isGE_shift L 0 (2 * (d : ℤ)) _ (by omega)
  have : (P.diagonalTwistEtale X d).IsLE (-(2 * (d : ℤ))) :=
    _root_.DerivedCategory.TStructure.t.isLE_of_iso c.symm _
  have : (P.diagonalOrdinaryDualizing f).IsGE (-(2 * (d : ℤ))) :=
    _root_.DerivedCategory.TStructure.t.isGE_of_iso (c.symm ≪≫ e.symm) _
  choose V U hV hU _ hx hUV v hv hw using
    fun x : X ↦ Smooth.exists_etale_to_affineSpace f d x
  suffices h : e.inv = e'.inv by
    have hs : e.symm = e'.symm := Iso.ext h
    exact congrArg Iso.symm hs
  apply map_eq_of_cover P.Coefficient U (fun x ↦ ⟨x, hx x⟩) (-(2 * (d : ℤ)))
  intro x
  have : IsAffine (U x).toScheme := hU x
  have : IsNoetherian (U x).toScheme := isNoetherian_of_locallyOfFiniteType (U x).ι
  have : Etale (v x) := hv x
  have : IsOpenImmersion (AffineSpace.map (ULift.{u} (Fin d)) (V x).ι) :=
    MorphismProperty.of_isPullback
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin d)) (V x).ι).flip
      (inferInstance : IsOpenImmersion (V x).ι)
  let q := v x ≫ AffineSpace.map (ULift.{u} (Fin d)) (V x).ι ≫
    (affineTraceAffineSpaceIso Y d).inv
  have : Etale q := inferInstance
  have : IsSeparated q := inferInstance
  have : LocallyOfFiniteType q := inferInstance
  have : QuasiCompact q := inferInstance
  have hp : (affineTraceAffineSpaceIso Y d).inv ≫ affineTraceProjection Y d =
      AffineSpace (ULift.{u} (Fin d)) Y ↘ Y := by
    apply (cancel_epi (affineTraceAffineSpaceIso Y d).hom).mp
    simp only [Iso.hom_inv_id_assoc]
    exact (AffineSpace.homOfVector_over _ _).symm
  have w : q ≫ affineTraceProjection Y d = (U x).ι ≫ f := by
    dsimp only [q]
    simp only [Category.assoc, hp, AffineSpace.map_over]
    rw [← Category.assoc, hw x, Scheme.Hom.resLE_comp_ι]
  have : HasCompactification ((U x).ι ≫ f) := inferInstance
  have : HasCompactification (q ≫ affineTraceProjection Y d) := by
    rw [w]
    infer_instance
  apply (cancel_mono (P.diagonalEtaleLocality N (U x).ι f).hom).mp
  exact (he t D N (U x).toScheme (U x).ι q w).trans
    (he' t D N (U x).toScheme (U x).ι q w).symm

end WeilConjectures.PurityFiniteSetting
