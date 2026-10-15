/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Sheaf.Paper.ModuleCupResolutionData
import Mathlib.Algebra.Homology.Embedding.Restriction
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-! # Positive-degree scalar cup on resolution classes

Source: Stacks Project, Cohomology, Tags 01F7 and 0FKV.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
attribute [local instance] Sheaf.monoidalCategory HasExt.standard

private instance {X : Scheme.{w}} : EnoughInjectives X.Modules :=
  (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
private instance {X : Scheme.{w}} : HasExt.{w} X.Modules :=
  hasExt_of_enoughInjectives.{w, w, w + 1} X.Modules
private instance {X : Scheme.{w}} :
    EnoughInjectives (SheafOfModules.{w} X.ringCatSheaf) :=
  (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
private instance {X : Scheme.{w}} : HasExt.{w} (SheafOfModules.{w} X.ringCatSheaf) :=
  hasExt_of_enoughInjectives.{w, w, w + 1} (SheafOfModules.{w} X.ringCatSheaf)

-- The first part of the comparison is constructive: pair with a fixed right cycle.
private abbrev RCycles {X : Scheme.{w}} {F : X.Modules}
    (D : CupAcyclicResolution F) (n : ℕ) :=
  ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj D.K).sc n).moduleCatLeftHomologyData.K
private def pairRightComponent {X : Scheme.{w}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (q : ℕ) (b : RCycles D.right q) (n : ℕ) :
    D.left.K.X n ⟶ D.target.K.X (n + q) where
  val := {
    app := fun V ↦ ModuleCat.ofHom ((D.pair n q V.unop).flip
      ((D.right.K.X q).presheaf.map (homOfLE le_top).op b.val))
    naturality := by
      intro V W u
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      change D.pair n q W.unop ((D.left.K.X n).val.map u a)
          ((D.right.K.X q).presheaf.map (homOfLE le_top).op b.val) =
        (D.target.K.X (n + q)).val.map u
          (D.pair n q V.unop a
            ((D.right.K.X q).presheaf.map (homOfLE le_top).op b.val))
      have h := D.restriction n q V.unop W.unop (leOfHom u.unop) a
        ((D.right.K.X q).presheaf.map (homOfLE le_top).op b.val)
      refine Eq.trans ?_ h.symm
      apply congrArg (fun t ↦ D.pair n q W.unop ((D.left.K.X n).val.map u a) t)
      exact ((presheaf_map_map_apply (M := D.right.K.X q)
        (homOfLE le_top) u.unop b.val).trans rfl).symm }
private theorem pairRightComponent_comm {X : Scheme.{w}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (q : ℕ) (b : RCycles D.right q) (n : ℕ) :
    pairRightComponent D q b n ≫ D.target.K.d (n + q) (n + q + 1) =
      D.left.K.d n (n + 1) ≫ pairRightComponent D q b (n + 1) ≫
        eqToHom (congrArg D.target.K.X (by omega : n + 1 + q = n + q + 1)) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  have hb : (D.right.K.d q (q + 1)).val.app V
      ((D.right.K.X q).presheaf.map (homOfLE le_top).op b.val) = 0 := by
    have h := Hom.app_presheaf_map (D.right.K.d q (q + 1))
      (homOfLE (le_top : V.unop ≤ ⊤)) b.val
    have hb' : (D.right.K.d q (q + 1)).val.app (op ⊤) b.val = 0 := by
      have h := b.property
      change (D.right.K.d q ((ComplexShape.up ℕ).next q)).val.app (op ⊤) b.val = 0 at h
      rw [ComplexShape.next_eq' (ComplexShape.up ℕ) (by simp :
        (ComplexShape.up ℕ).Rel q (q + 1))] at h
      exact h
    have he : (D.right.K.d q (q + 1)).app ⊤ b.val = 0 := hb'
    exact h.trans ((congrArg
      ((D.right.K.X (q + 1)).presheaf.map (homOfLE le_top).op) he).trans (map_zero _))
  have h := D.leibniz n q V.unop a
    ((D.right.K.X q).presheaf.map (homOfLE le_top).op b.val)
  simp only [hb, map_zero, smul_zero, add_zero] at h
  exact h
private def pairRightMap {X : Scheme.{w}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (q : ℕ) (b : RCycles D.right q) :
    D.left.K ⟶ D.target.K.restriction (ComplexShape.embeddingUp'Add 1 q) where
  f n := pairRightComponent D q b n
  comm' n m hnm := by
    change n + 1 = m at hnm
    subst m
    change pairRightComponent D q b n ≫ D.target.K.d (n + q) (n + 1 + q) =
      D.left.K.d n (n + 1) ≫ pairRightComponent D q b (n + 1)
    let h : n + 1 + q = n + q + 1 := by omega
    apply (cancel_mono (eqToHom (congrArg D.target.K.X h))).mp
    rw [Category.assoc]
    rw [HomologicalComplex.d_comp_eqToHom D.target.K
      (by simp : (ComplexShape.up ℕ).Rel (n + q) (n + q + 1))
      (by change n + q + 1 = n + 1 + q; omega)]
    exact pairRightComponent_comm D q b n
open CochainComplex.HomComplex
private def pairRightCochain {X : Scheme.{w}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (q : ℕ) (b : RCycles D.right q) :
    Cochain (D.left.K.extend ComplexShape.embeddingUpNat)
      (D.target.K.extend ComplexShape.embeddingUpNat) (q : ℤ) :=
  Cochain.mk fun i j hij ↦
    if hi : 0 ≤ i then
      (D.left.K.extendXIso ComplexShape.embeddingUpNat (by simpa using hi)).hom ≫
        ((-1 : ℤ) ^ (i.toNat * q) • pairRightComponent D q b i.toNat) ≫
          (D.target.K.extendXIso ComplexShape.embeddingUpNat (by
            omega : ((i.toNat + q : ℕ) : ℤ) = j)).inv
    else 0
private theorem pairRightCochain_v_nat {X : Scheme.{w}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (q : ℕ) (b : RCycles D.right q) (n : ℕ)
    (j : ℤ) (h : (n : ℤ) + q = j) :
    (pairRightCochain D q b).v n j h =
      (D.left.K.extendXIso ComplexShape.embeddingUpNat rfl).hom ≫
        ((-1 : ℤ) ^ (n * q) • pairRightComponent D q b n) ≫
          (D.target.K.extendXIso ComplexShape.embeddingUpNat (by omega :
            ((n + q : ℕ) : ℤ) = j)).inv := by
  simp only [pairRightCochain, Cochain.mk_v, Int.natCast_nonneg, dif_pos, Int.toNat_natCast]
private theorem pairRightCochain_v {X : Scheme.{w}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (q : ℕ) (b : RCycles D.right q) (n : ℕ)
    (i j : ℤ) (hi : ComplexShape.embeddingUpNat.f n = i) (h : i + q = j) :
    (pairRightCochain D q b).v i j h =
      (D.left.K.extendXIso ComplexShape.embeddingUpNat hi).hom ≫
        ((-1 : ℤ) ^ (n * q) • pairRightComponent D q b n) ≫
          (D.target.K.extendXIso ComplexShape.embeddingUpNat (by
            have hh : (n : ℤ) = i := hi
            change ((n + q : ℕ) : ℤ) = j
            omega)).inv := by
  subst i
  exact pairRightCochain_v_nat D q b n j h
private theorem pairRightCochain_closed {X : Scheme.{w}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (q : ℕ) (b : RCycles D.right q) :
    δ (q : ℤ) ((q : ℤ) + 1) (pairRightCochain D q b) = 0 := by
  apply Cochain.ext
  intro i j hij
  rw [δ_v _ _ rfl _ i j hij (i + q) (i + 1) (by omega) rfl]
  by_cases hi : 0 ≤ i
  · lift i to ℕ using hi with n hn
    subst i
    erw [pairRightCochain_v D q b n (n : ℤ) ((n : ℤ) + q) rfl rfl]
    erw [pairRightCochain_v D q b (n + 1) ((n : ℤ) + 1) j (by simp) (by omega)]
    erw [D.target.K.extend_d_eq ComplexShape.embeddingUpNat
      (i' := (n : ℤ) + q) (j' := j) (i := n + q) (j := n + 1 + q)
      (by change ((n + q : ℕ) : ℤ) = (n : ℤ) + q; omega)
      (by change ((n + 1 + q : ℕ) : ℤ) = j; omega)]
    erw [D.left.K.extend_d_eq ComplexShape.embeddingUpNat
      (i' := (n : ℤ)) (j' := (n : ℤ) + 1) (i := n) (j := n + 1) rfl
      (by change ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1; omega)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have hcomm : pairRightComponent D q b n ≫ D.target.K.d (n + q) (n + 1 + q) =
        D.left.K.d n (n + 1) ≫ pairRightComponent D q b (n + 1) :=
      (pairRightMap D q b).comm n (n + 1)
    simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp,
      Cochain.zero_v]
    let L := (D.left.K.extendXIso ComplexShape.embeddingUpNat
      (i := n) (i' := (n : ℤ)) rfl).hom
    let R := (D.target.K.extendXIso ComplexShape.embeddingUpNat
      (i := n + 1 + q) (i' := j) (by
        change ((n + 1 + q : ℕ) : ℤ) = j
        omega)).inv
    change (-1 : ℤ) ^ (n * q) •
        (L ≫ pairRightComponent D q b n ≫ D.target.K.d (n + q) (n + 1 + q) ≫ R) +
      ((q : ℤ) + 1).negOnePow • ((-1 : ℤ) ^ ((n + 1) * q) •
        (L ≫ D.left.K.d n (n + 1) ≫ pairRightComponent D q b (n + 1) ≫ R)) = 0
    have ht := congrArg (fun u ↦ L ≫ u ≫ R) hcomm
    simp only [Category.assoc] at ht
    erw [ht]
    have hsign : (q : ℤ).negOnePow • ((-1 : ℤ) ^ ((n + 1) * q)) =
        (-1 : ℤ) ^ (n * q) := by
      change ((q : ℤ).negOnePow : ℤ) * (-1 : ℤ) ^ ((n + 1) * q) = _
      rw [Int.coe_negOnePow_natCast, add_mul, one_mul, pow_add]
      calc
        (-1 : ℤ) ^ q * ((-1) ^ (n * q) * (-1) ^ q) =
            (-1) ^ (n * q) * ((-1) ^ q * (-1) ^ q) := by ring
        _ = _ := by rw [← mul_pow]; simp
    rw [Int.negOnePow_succ, Units.neg_smul]
    simp only [Units.smul_def, smul_smul]
    change _ + -((((q : ℤ).negOnePow : ℤ) * (-1 : ℤ) ^ ((n + 1) * q)) • _) = 0
    rw [show ((q : ℤ).negOnePow : ℤ) * (-1 : ℤ) ^ ((n + 1) * q) =
      (-1 : ℤ) ^ (n * q) from hsign]
    exact add_neg_cancel _
  · have hzero := D.left.K.isZero_extend_X ComplexShape.embeddingUpNat i (by
      intro n h
      have hn : (n : ℤ) = i := h
      omega)
    exact hzero.eq_of_src _ _

-- The class comparison used for the remaining Yoneda calculation, in every degree.
private theorem class_ext_formula {X : Scheme.{w}} {F : X.Modules}
    (D : CupAcyclicResolution F) (n : ℕ) (a : RCycles D n)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ D.I.cocomplex.X n)
    (hs : s ≫ D.I.cocomplex.d n (n + 1) = 0)
    (heval : s.val.app (op ⊤) (1 : Γ(X, ⊤)) =
      (D.comparison.f n).val.app (op ⊤) a.val) :
    moduleExtEquiv F n (D.class n a) =
      InjectiveResolution.extMk.{w, w, w + 1} D.I s (n + 1) rfl hs := by
  let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let : S.Additive := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let K := (S.mapHomologicalComplex (.up ℕ)).obj D.K
  let L := RingedSpace.globalSectionsComplex D.I
  let φ := (S.mapHomologicalComplex (.up ℕ)).map D.comparison
  let a' : K.cycles n := (K.sc n).moduleCatCyclesIso.inv a
  let z : L.cycles n := HomologicalComplex.cyclesMap φ n a'
  have hi : K.iCycles n a' = a.val :=
    ConcreteCategory.congr_hom (ShortComplex.moduleCatCyclesIso_inv_iCycles (K.sc n)) a
  have hz : s.val.app (op ⊤) (1 : Γ(X, ⊤)) = L.iCycles n z := by
    have h := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φ n) a'
    simp only [ConcreteCategory.comp_apply] at h
    exact heval.trans ((congrArg (φ.f n) hi.symm).trans h.symm)
  have hπ := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality φ n) a'
  simp only [ConcreteCategory.comp_apply] at hπ
  have hclass : D.class n a = (D.I.isoRightDerivedObj S n).inv (L.homologyπ n z) := by
    exact congrArg (D.I.isoRightDerivedObj S n).inv hπ
  rw [hclass]
  unfold moduleExtEquiv
  exact Classical.choose_spec (exists_moduleExtEquiv F n) D.I z s hs hz
private theorem scalar_class_ext_formula {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) {F : X.Modules}
    (D : CupAcyclicResolution F) (n : ℕ) (a : RCycles D n)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ D.I.cocomplex.X n)
    (hs : s ≫ D.I.cocomplex.d n (n + 1) = 0)
    (heval : s.val.app (op ⊤) (1 : Γ(X, ⊤)) =
      (D.comparison.f n).val.app (op ⊤) a.val) :
    scalarCohomologyExtEquiv f F n (D.class n a) =
      (Abelian.Ext.mk₀ (scalarUnitMorphism f)).comp
        ((InjectiveResolution.extMk.{w, w, w + 1} D.I s (n + 1) rfl hs).mapExactFunctor.{w, w + 1}
          (scalarFunctor f)) (zero_add n) := by
  unfold scalarCohomologyExtEquiv scalarCohomologyExtMap scalarExtMap
  change (Abelian.Ext.mk₀ (scalarUnitMorphism f)).comp
    ((moduleExtEquiv F n (D.class n a)).mapExactFunctor.{w, w + 1}
      (scalarFunctor f)) (zero_add n) = _
  rw [class_ext_formula D n a s hs heval]


/-- Positive-degree part of the signed resolution comparison.
Source: Stacks Project, Cohomology, Tags 01F7 and 0FKV; Mathlib,
Algebra.Homology.BifunctorShift, shift interchange formula.
(blueprint: new-sc-scalar-cup-positive-resolution-class-compatibility).

Proof: Apply the exact restriction-of-scalars functor to the three nonnegative
resolutions and extend them by zero to integer cochain complexes. Linearize the
sectionwise O-bilinear pairing over k and assemble its components with the
coproduct universal property of the total tensor. Restriction compatibility
makes this a sheaf morphism, and the stated Leibniz equation makes it a cochain
map. Its composite with the tensor of the two augmentations is the scalar tensor
coefficient map followed by the target augmentation. Tensoring sheaves of vector
spaces preserves quasi-isomorphisms, so localization identifies this map with
the coefficient map between the two resolved objects.

Represent the two global cycles by cochain maps from the scalar unit concentrated
in degrees p and q. After localization and inverse augmentation these maps are
the Ext classes of the two resolution classes: use the defining injective-cocycle
formula for moduleExtEquiv and the comparison maps in D. Restriction of scalars
and precomposition with scalarUnitMorphism preserve this formula. Tensor the two
representing maps. The left-then-right order defining scalarExtCup moves the left
shift out before the right shift; the two shift comparisons differ by
(-1)^(p*q), by mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso. Evaluation on the
(p,q) summand therefore gives (-1)^(p*q) times the paired target cycle c. The
coefficient map and target comparison identify this with the Ext image of the
signed target class. Additivity of the Ext equivalence transports the integer
scalar, and injectivity gives the asserted equality. The same maps cover zero
cycles, characteristic two, and the empty scheme.
The private pairRightCochain constructs the signed degree-q cochain by pairing
with the fixed right cycle. The theorem pairRightCochain_closed proves its
closedness, including its negative-degree components, and scalar_class_ext_formula
proves the injective-cocycle formula for any resolution class in every degree.
The remaining identification is that this cochain represents tensor transport of
the right class, followed by the coefficient map; composing with the left class
then evaluates its degree-p component. These constructions give a route that can
avoid assembling the full tensor, but that Yoneda identification remains open.
Only p,q>0 remain here: both degree-zero axes have separate proofs using actual
maps of resolutions and the appropriate unitor.
-/
theorem scalarCup_positive_resolution_class_compatibility
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F G : X.Modules) (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (D : CupResolutionPairing F G)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
    (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K)
    (hc : c.val = D.pair p q ⊤ a.val b.val) :
    scalarCohomologyCup f F G p q (D.left.class p a) (D.right.class q b) =
      (-1 : ℤ) ^ (p * q) • D.target.class (p + q) c := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
