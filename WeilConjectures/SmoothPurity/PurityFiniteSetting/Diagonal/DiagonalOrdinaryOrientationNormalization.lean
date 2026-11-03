/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalOrientationRefinement
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalAffineCounitRestriction
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.SixFunctors.OpenClosed.Conservative
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

/-! # Coordinate normalization of the glued diagonal orientation

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-orientation,
thm-pur-diagonal-dualizing-object.proof.md, Steps 1--2 and canonicity paragraph.
(blueprint: lem-pur-diagonal-ordinary-orientation-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

open AlgebraicGeometry.Etale

attribute [local irreducible] derivedTensor

private theorem mapped_inverse_factor
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) {W X Y : C} {Z : E}
    (a : W ≅ X) (b : X ≅ Y) (c : G.obj (F.obj Y) ≅ Z)
    (q : G.obj (F.obj W) ≅ Z)
    (h : G.mapIso (F.mapIso (a ≪≫ b)) ≪≫ c = q) :
    G.map (F.map b.inv) = c.hom ≫ q.inv ≫ G.map (F.map a.hom) := by
  have h' : G.mapIso (F.mapIso a) ≪≫ G.mapIso (F.mapIso b) ≪≫ c = q := by
    simpa only [Functor.mapIso_trans, Iso.trans_assoc] using h
  rw [← h']
  simp only [Iso.trans_inv, Functor.mapIso_inv, Category.assoc, Iso.hom_inv_id_assoc,
    ← Functor.map_comp, Iso.inv_hom_id, Category.comp_id]

private theorem tensor_shift_right
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (X : Scheme.{u})
    (L M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B)) (a b : ℤ) :
    Nonempty ((derivedTensorRight B X (M⟦b⟧)).obj (L⟦a⟧) ≅
      ((derivedTensorRight B X M).obj L)⟦a + b⟧) :=
  ⟨derivedTensorShiftIso B L M a b⟩

private theorem tensor_single_right
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (X : Scheme.{u})
    (L M R : Sheaf X.smallEtaleTopology B) (hL : ObjectProperty.flat L)
    (e : L ⊗ M ≅ R) :
    Nonempty ((derivedTensorRight B X ((_root_.DerivedCategory.singleFunctor _ 0).obj M)).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj L) ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj R) :=
  ⟨singleProductGeneral B X L M R hL e⟩

private theorem base_normal_form (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    Nonempty (affineLinearBaseCoefficient A N hA S d ≅
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf A N S hA (d : ℤ)))⟦2 * (d : ℤ)⟧) := by
  let E := fun d : ℕ ↦ Scheme.finiteEtaleTateSheaf A N S hA (d : ℤ)
  have hflat (d : ℕ) : ObjectProperty.flat (E d) := by
    apply (ObjectProperty.flat_iff_preservesFiniteLimits _).2
    exact (Scheme.finite_etale_torsion_twist_line S N hN
      (fun x ↦ by
        simpa only [map_natCast] using hS.map (S.presheaf.germ ⊤ x (by trivial)).hom)
      A hA d).2.2.1
  induction d with
  | zero =>
    exact ⟨(Iso.refl _) ≪≫ (shiftFunctorZero _ ℤ).symm.app _⟩
  | succ d ih =>
    obtain ⟨e⟩ := ih
    let prod : E d ⊗ E 1 ≅ E (d + 1) := by
      cases d with
      | zero => exact λ_ (E 1)
      | succ d => exact Iso.refl _
    obtain ⟨shift⟩ := tensor_shift_right (ModuleCat.{u + 1} A) S
      ((_root_.DerivedCategory.singleFunctor _ 0).obj (E d))
      ((_root_.DerivedCategory.singleFunctor _ 0).obj (E 1)) (2 * (d : ℤ)) 2
    obtain ⟨single⟩ := tensor_single_right (ModuleCat.{u + 1} A) S
      (E d) (E 1) (E (d + 1)) (hflat d) prod
    exact ⟨((derivedTensorRight (ModuleCat.{u + 1} A) S
      ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).mapIso e) ≪≫
      shift ≪≫ (shiftFunctor _ (2 * (d : ℤ) + 2)).mapIso single ≪≫
      eqToIso (congrArg (fun a : ℤ ↦
        ((_root_.DerivedCategory.singleFunctor _ 0).obj (E (d + 1)))⟦a⟧) (by omega))⟩

private theorem map_eq_of_cover (A : Type (u + 1)) [CommRing A]
    {S : Scheme.{u}} {I : Type u} (U : I → S.Opens)
    (hU : ∀ x : S, ∃ i : I, x ∈ U i)
    {K L : DerivedCategoryModule A S} (n : ℤ)
    [K.IsLE n] [L.IsGE n] (f g : K ⟶ L)
    (h : ∀ i, (ordinaryFinitePullback A (U i).ι).map f =
      (ordinaryFinitePullback A (U i).ι).map g) : f = g := by
  apply (_root_.DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE n).injective
  have hf : JointlyFaithful (fun i ↦ upperStar (ModuleCat.{u + 1} A) (U i).ι) := by
    apply JointlyReflectIsomorphisms.jointlyFaithful
    constructor
    intro M N z hz
    apply isIso_of_isIso_upperStar_map_of_jointlySurjective
      (ModuleCat.{u + 1} A) (fun i ↦ (U i).ι) ?_ z hz
    intro x
    obtain ⟨i, hi⟩ := hU x
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  apply hf.map_injective
  intro i
  have hh : (upperStar (ModuleCat.{u + 1} A) (U i).ι).mapDerivedCategory.map f =
      (upperStar (ModuleCat.{u + 1} A) (U i).ι).mapDerivedCategory.map g := by
    let c := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (U i).ι
    exact (NatIso.naturality_1 c f).symm.trans
      ((congrArg (fun z ↦ c.inv.app K ≫ z ≫ c.hom.app L) (h i)).trans
        (NatIso.naturality_1 c g))
  let e := (upperStar (ModuleCat.{u + 1} A) (U i).ι).mapDerivedCategoryHomologyFunctorIso n
  exact (NatIso.naturality_2 e f).symm.trans
    ((congrArg (fun z ↦ e.hom.app K ≫ z ≫ e.inv.app L)
      ((_root_.DerivedCategory.homologyFunctor _ n).congr_map hh)).trans
        (NatIso.naturality_2 e g))

/-- A realization of the affine-target DNC composites has the prescribed counit on
all etale coordinate charts. This is a compatibility assertion for a given e, not
an existence assertion.
Source: blueprint diagonal-dualizing proof, Steps 1--2 and canonicity paragraph
(blueprint: lem-pur-diagonal-ordinary-orientation-normalization).

Proof:
1. Restrict an etale coordinate diagram to inverse images of finite-type affine
   opens of Y. The assumed equation replaces e there by rho, alpha inverse,
   delta, beta, in the canonical comparison coordinates.
2. The diagonal is the closed section of its smooth self-product projection.
   Etale base change identifies its conormal generators with coordinate differences.
   The normalized DNC comparison is the identity on the corresponding standard
   section invariant, by its family equation at one and zero.
3. BetaNormalized identifies the last factor with the zero restriction of vector
   integration in every bundle model. On the coordinate model the ordered affine
   integration counit is the tensor product of the rank-one Kummer-normalized
   counits, with the identity for the empty tensor power.
4. Transpose that counit equality under the exceptional adjunction. Pasting source
   etale locality identifies its two sides with diagonalEtaleLocality and
   diagonalAffineMate. The root-tensor pullback comparisons give exactly the two
   displayed coefficient maps in DiagonalOrientationNormalization; the equality
   of composites is diagonalDualizingCongr.
5. Shift both objects by -2d and test equality of the resulting sheaf maps on the
   inverse-image affine cover. Degree-zero derived-map gluing identifies the global
   equality. Repeat for each t, D and N: their defining unit, Kummer and counit
   normalizations give the same computation, so no presentation is an assumption.
   Empty schemes, empty overlaps and dimension zero satisfy the same identities. -/
theorem diagonalOrdinaryOrientationNormalization (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    [IsNoetherian X] [IsNoetherian Y] [HasCompactification f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (D : ∀ (V : Y.affineOpens), (V.1.ι ≫ aY).appTop.hom.FiniteType →
      OrientationRefinement.Chart P f aY d V)
    (e : P.diagonalOrdinaryDualizing f ≅ P.diagonalTwistEtale X d)
    (he :
      ∀ (V : Y.affineOpens) (hV : (V.1.ι ≫ aY).appTop.hom.FiniteType),
        (OrientationRefinement.pull P (f ⁻¹ᵁ V.1).ι).mapIso
          ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
            ((Etale.rightDerivedUpperShriek P.Coefficient f).mapIso
              (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) Y).symm ≪≫
                e)) ≪≫
          OrientationRefinement.tate P (f ⁻¹ᵁ V.1).ι (f ≫ aY) d =
        OrientationRefinement.theta P f aY d V (D V hV).geometry (D V hV).betaEtale) :
    P.DiagonalOrientationNormalization d f aY e := by
  classical
  let _ := affineTraceNoetherian Y d
  intro t Dp N U _ j _ _ _ _ v _ _ _ _ w _ _
  let J := Etale.ordinaryFinitePullback P.Coefficient j
  let νX := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  let νU := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory
  let b := OrientationCounit.coordinate P d f aY t Dp N U j v w
  suffices hab : J.map e.inv = b by
    simpa only [b, OrientationCounit.coordinate, Category.assoc,
      Iso.inv_hom_id, Category.comp_id] using
        congrArg (fun z ↦ z ≫ (P.diagonalEtaleLocality N j f).hom) hab
  obtain ⟨q⟩ := base_normal_form P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates X (P.diagonalExponent_isUnit (f ≫ aY)) d
  let L := (_root_.DerivedCategory.singleFunctor _ 0).obj
    (Scheme.finiteEtaleTateSheaf P.Coefficient P.diagonalExponent X
      P.diagonalExponent_annihilates (d : ℤ))
  let n : ℤ := -(2 * (d : ℤ))
  have hle : _root_.DerivedCategory.TStructure.t.IsLE (L⟦2 * (d : ℤ)⟧) n :=
    _root_.DerivedCategory.TStructure.t.isLE_shift L 0 (2 * (d : ℤ)) n (by dsimp [n]; omega)
  have hge : _root_.DerivedCategory.TStructure.t.IsGE (L⟦2 * (d : ℤ)⟧) n :=
    _root_.DerivedCategory.TStructure.t.isGE_shift L 0 (2 * (d : ℤ)) n (by dsimp [n]; omega)
  have hK : (P.diagonalTwistEtale X d).IsLE n :=
    _root_.DerivedCategory.TStructure.t.isLE_of_iso q.symm n
  have hT : (P.diagonalTwistEtale X d).IsGE n :=
    _root_.DerivedCategory.TStructure.t.isGE_of_iso q.symm n
  have hM : (P.diagonalOrdinaryDualizing f).IsGE n :=
    _root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm n
  have hJK : (J.obj (P.diagonalTwistEtale X d)).IsLE n := by
    have := (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) j).isLE_mapDerivedCategory_obj
      (P.diagonalTwistEtale X d) n
    exact _root_.DerivedCategory.TStructure.t.isLE_of_iso
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) j).app _).symm n
  have hJM : (J.obj (P.diagonalOrdinaryDualizing f)).IsGE n := by
    have := (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) j).isGE_mapDerivedCategory_obj
      (P.diagonalOrdinaryDualizing f) n
    exact _root_.DerivedCategory.TStructure.t.isGE_of_iso
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) j).app _).symm n
  obtain ⟨S, hS, hft⟩ := (P.affineTargetDiagonalDnc aY (f ≫ aY) f rfl d).1
  let W : S → U.Opens := fun V ↦ j ⁻¹ᵁ (f ⁻¹ᵁ V.val.1)
  have hW : ∀ x : U, ∃ V : S, x ∈ W V := by
    intro x
    have hx : f (j x) ∈ (⨆ V ∈ S, V.1) := by rw [hS]; trivial
    obtain ⟨V, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨hV, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨⟨V, hV⟩, hx⟩
  apply map_eq_of_cover P.Coefficient W hW n
  intro V
  let W₀ := f ⁻¹ᵁ V.val.1
  let R := OrientationRefinement.pull P W₀.ι
  let T := OrientationRefinement.pull P (j ⁻¹ᵁ W₀).ι
  let Q := OrientationRefinement.pull P (j ∣_ W₀)
  let c := OrientationCounit.restriction P j W₀
  have hr : R.map (νX.map e.inv) =
      (OrientationRefinement.tate P W₀.ι (f ≫ aY) d).hom ≫
        (OrientationRefinement.theta P f aY d V.val
          (D V.val (hft V.val V.property)).geometry
          (D V.val (hft V.val V.property)).betaEtale).inv ≫
        R.map (νX.map (OrientationCounit.unitChange P f).hom) := by
    exact mapped_inverse_factor νX R (OrientationCounit.unitChange P f) e
      (OrientationRefinement.tate P W₀.ι (f ≫ aY) d)
      (OrientationRefinement.theta P f aY d V.val
        (D V.val (hft V.val V.property)).geometry
        (D V.val (hft V.val V.property)).betaEtale)
      (he V.val (hft V.val V.property))
  have hc : T.map (νU.map (J.map e.inv)) = T.map (νU.map b) := by
    rw [show T.map (νU.map (J.map e.inv)) =
      (c.app (P.diagonalTwistEtale X d)).inv ≫
        Q.map (R.map (νX.map e.inv)) ≫
        (c.app (P.diagonalOrdinaryDualizing f)).hom from (NatIso.naturality_1 c e.inv).symm]
    rw [hr]
    exact (P.diagonalAffineCounitRestriction d f aY V.val
      (D V.val (hft V.val V.property)) t Dp N U j v w).symm
  let νW := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) (W V).toScheme).mapDerivedCategory
  let k := OrientationCounit.comparisonPull P (W V).ι
  have hk : νW.map ((Etale.ordinaryFinitePullback P.Coefficient (W V).ι).map
      (J.map e.inv)) =
      νW.map ((Etale.ordinaryFinitePullback P.Coefficient (W V).ι).map b) := by
    exact (NatIso.naturality_1 k (J.map e.inv)).symm.trans
      ((congrArg (fun z ↦ k.inv.app _ ≫ z ≫ k.hom.app _) hc).trans
        (NatIso.naturality_1 k b))
  apply (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map _ _ ?_).injective hk
  have hbound := (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
    (W V).ι).isGE_mapDerivedCategory_obj (J.obj (P.diagonalOrdinaryDualizing f)) n
  have : ((Etale.ordinaryFinitePullback P.Coefficient (W V).ι).obj
      (J.obj (P.diagonalOrdinaryDualizing f))).IsGE n :=
    _root_.DerivedCategory.TStructure.t.isGE_of_iso
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) (W V).ι).app _).symm n
  exact ⟨n, this⟩

end WeilConjectures.PurityFiniteSetting
