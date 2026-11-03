/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedWeil.NativeCondensedWeilReality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackConstantModelConstructible
import WeilConjectures.AlgebraicGeometry.Closed.ClosedPointField
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Roots
import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import WeilConjectures.Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Trace
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.FieldPointFactorsThroughImmersion
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.DeligneLaumon.AffineLine.Defs
public import WeilConjectures.PointCount
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeil.CondensedStrictWeilComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-! # Exact condensed Weil pullback and residue-degree Frobenius

Source: latest blueprint, sec-deligne-laumon-general/sk-i-dl-general-real/
thm-zl-real-mixed-by-curves.proof.md, paragraphs 1--4 and 7
(blueprint: lem-zl-condensed-pullback-frobenius).

## Main statements

* `condensed_pullback_frobenius`: exactness, fixed rank and finite Weil filtrations.
* `local_frobenius`: the natural canonical comparison, residue powers and full spectrum.
* `preserves_weights`: reality, punctual purity and mixed upper bounds for any embedding.

All fibres and predicates are the current native condensed ones. The only scalar lift
is the standard universe lift already used by those predicates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.Endofunctor
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeCondensedPullback
open NativeL2 NativeCondensedWeil NativeCondensedModule

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)

/-- The fixed subfield k_m has q^m elements and the same algebraic closure k.
Source: Deligne, Weil II, p. 152, change of finite base field
(blueprint: lem-zl-condensed-pullback-frobenius).
Proof: the unique-subfield theorem gives cardinality q^m, which is nonzero,
so the subfield is finite. The closure k is algebraically closed and algebraic
also over this intermediate finite field, hence is its algebraic closure. -/
theorem constantExtensionField_properties :
    Finite (D.extensionSubfield m hm) ∧
      Nat.card (D.extensionSubfield m hm) = D.q ^ m ∧
      IsAlgClosure (D.extensionSubfield m hm) D.k := by
  have hc : Nat.card (D.extensionSubfield m hm) = D.q ^ m :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.2.1
  have hf : Finite (D.extensionSubfield m hm) := Nat.finite_of_card_ne_zero
    (hc ▸ pow_ne_zero m (D.cardinality_eq ▸ pow_ne_zero D.a D.prime.ne_zero))
  let := (D.extensionEmbedding m hm).toAlgebra
  have hcomp : (D.extensionSubfield m hm).subtype.comp (D.extensionEmbedding m hm) =
      algebraMap D.k₀ D.k :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.2.2.2.2.2.2.choose_spec
  let : IsScalarTower D.k₀ (D.extensionSubfield m hm) D.k :=
    IsScalarTower.of_algebraMap_eq' hcomp.symm
  exact ⟨hf, hc, ⟨IsAlgClosure.isAlgClosed D.k₀,
    Algebra.IsAlgebraic.tower_top (K := D.k₀) (D.extensionSubfield m hm)⟩⟩

/-- The new finite base remains the actual subfield of the fixed closure.
Source: Deligne, Weil II, p. 152
(blueprint: lem-zl-condensed-pullback-frobenius). -/
def constantExtensionDatum : FiniteFieldDatum.{u} where
  p := D.p
  a := D.a * m
  q := D.q ^ m
  prime := D.prime
  exponent_pos := le_trans hm (Nat.le_mul_of_pos_left m D.exponent_pos)
  cardinality_eq := D.cardinality_eq ▸ (pow_mul D.p D.a m).symm
  k₀ := D.extensionSubfield m hm
  finite_base := (constantExtensionField_properties D m hm).1
  card_base := (constantExtensionField_properties D m hm).2.1
  k := D.k
  isAlgClosure := (constantExtensionField_properties D m hm).2.2

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
  (T₀ : Over (Spec (.of D.k₀))) [hTft : LocallyOfFiniteType T₀.hom] [hTqc : QuasiCompact T₀.hom]
  [hTs : IsSeparated T₀.hom]
  (Y₀ : Over (Spec (.of (constantExtensionDatum D m hm).k₀)))
  [hYft : LocallyOfFiniteType Y₀.hom] [hYqc : QuasiCompact Y₀.hom]
  [hYs : IsSeparated Y₀.hom]
  (f₀ : Over.mk (Y₀.hom ≫
    Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) ⟶ T₀)

set_option linter.unusedSectionVars false in
/-- The two components of the induced geometric map are compatible.
Source: latest blueprint, paragraphs 1--3
(blueprint: lem-zl-condensed-pullback-frobenius).
Proof: compose the source pullback projection equation with Spec(k_m → k₀),
use the defining equation of f₀, and use that k₀ → k_m → k is its fixed inclusion. -/
theorem geometricMap_compatible :
    (pullback.fst Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap
        (constantExtensionDatum D m hm).k₀ (constantExtensionDatum D m hm).k))) ≫
      f₀.left) ≫ T₀.hom =
    ((constantExtensionDatum D m hm).geometricFiber Y₀).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
  have hcomp : (D.extensionSubfield m hm).subtype.comp (D.extensionEmbedding m hm) =
      algebraMap D.k₀ D.k :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.2.2.2.2.2.2.choose_spec
  rw [Category.assoc, Over.w f₀]
  change pullback.fst _ _ ≫ (Y₀.hom ≫ _) = pullback.snd _ _ ≫ _
  have hcomp' : (algebraMap (constantExtensionDatum D m hm).k₀
      (constantExtensionDatum D m hm).k).comp (D.extensionEmbedding m hm) =
      algebraMap D.k₀ D.k := hcomp
  rw [← Category.assoc, pullback.condition, Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp']

/-- The induced f:Y → T, using the fixed inclusion k_m ⊂ k.
Source: latest blueprint, paragraphs 1--3
(blueprint: lem-zl-condensed-pullback-frobenius). -/
def geometricMap : ((constantExtensionDatum D m hm).geometricFiber Y₀).left ⟶
    (D.geometricFiber T₀).left :=
  pullback.lift
    (pullback.fst Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap
        (constantExtensionDatum D m hm).k₀ (constantExtensionDatum D m hm).k))) ≫ f₀.left)
    ((constantExtensionDatum D m hm).geometricFiber Y₀).hom
    (geometricMap_compatible D m hm T₀ Y₀ f₀)

/-- The source q^m-Frobenius commutes with f and the mth target Frobenius power.
Source: latest blueprint, paragraphs 1--3
(blueprint: lem-zl-condensed-pullback-frobenius).
Proof: the two composites have the same model projection, since Frobenius fixes the
models. Their closure projection is Spec(z ↦ z^(1/q^m)) on both sides. The mth
geometric field Frobenius fixes k_m. Pullback uniqueness gives the square. -/
theorem geometricMap_frobenius :
    CommSq ((constantExtensionDatum D m hm).geometricFrobenius Y₀).hom
      (geometricMap D m hm T₀ Y₀ f₀) (geometricMap D m hm T₀ Y₀ f₀)
      (localPositivePower (D.geometricFrobenius T₀).hom (m - 1))  := by
  let := Fintype.ofFinite D.k₀
  let : Algebra (constantExtensionDatum D m hm).k₀ D.k :=
    (constantExtensionDatum D m hm).algebra_closure
  let : IsAlgClosure (constantExtensionDatum D m hm).k₀ D.k :=
    (constantExtensionDatum D m hm).isAlgClosure
  let := Fintype.ofFinite (constantExtensionDatum D m hm).k₀
  have hn := (constantExtensionDatum D m hm).galoisMap_projections Y₀.hom
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic
      (constantExtensionDatum D m hm).k₀ D.k)
  have ho := frobeniusPower_projections D T₀ (m - 1)
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have he := extensionFrobenius_power D m hm
  refine ⟨?_⟩
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [ho.1]
    simp only [geometricMap, pullback.lift_fst]
    exact hn.1 =≫ f₀.left
  · simp only [Category.assoc]
    rw [ho.2, hm']
    simp only [geometricMap, pullback.lift_snd, pullback.lift_snd_assoc]
    rw [← he]
    exact hn.2

variable (l : ℕ) [Fact l.Prime]

/-- Pullback of a Weil object: canonical square comparison followed by f*theta^[m].
Source: latest blueprint, paragraphs 1--3
(blueprint: lem-zl-condensed-pullback-frobenius). -/
def object (M : WeilModule D l T₀) : WeilModule (constantExtensionDatum D m hm) l Y₀ :=
  IsoAlgebra.mk
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (geometricMap D m hm T₀ Y₀ f₀)).obj M.carrier)
    (((CondensedRing.upperStarSquareComparison (Profinite.padicAlgClRingObj l)
      (geometricMap_frobenius D m hm T₀ Y₀ f₀)).symm.app M.carrier) ≪≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (geometricMap D m hm T₀ Y₀ f₀)).mapIso
          (NativeCondensedModule.iterate l (D.geometricFrobenius T₀).hom
            M.carrier M.str (m - 1)))

private theorem chain_naturality {C : Type*} [Category* C]
    (A B : ℕ → C) (M N : C) (f : M ⟶ N)
    (iA : A 0 ≅ M) (iB : B 0 ≅ N)
    (sA : ∀ n, A (n + 1) ≅ A n) (sB : ∀ n, B (n + 1) ≅ B n)
    (v : ∀ n, A n ⟶ B n) (hi : v 0 ≫ iB.hom = iA.hom ≫ f)
    (hs : ∀ n, v (n + 1) ≫ (sB n).hom = (sA n).hom ≫ v n) (n : ℕ) :
    v n ≫ (isoChain B N iB sB n).hom = (isoChain A M iA sA n).hom ≫ f := by
  induction n with
  | zero => exact hi
  | succ n ih =>
    change v (n + 1) ≫ ((sB n).hom ≫ (isoChain B N iB sB n).hom) =
      ((sA n).hom ≫ (isoChain A M iA sA n).hom) ≫ f
    rw [← Category.assoc, hs, Category.assoc, ih, Category.assoc]

private theorem initial_naturality {C : Type*} [Category* C]
    (F G : C ⥤ C) (c : F ≅ G) (M N : C)
    (θ : G.obj M ≅ M) (η : G.obj N ≅ N) (f : M ⟶ N)
    (hf : G.map f ≫ η.hom = θ.hom ≫ f) :
    F.map f ≫ (evaluateInitial F G c N η).hom =
      (evaluateInitial F G c M θ).hom ≫ f := by
  dsimp only [evaluateInitial, Iso.trans_hom, Iso.app_hom]
  rw [NatTrans.naturality_assoc, hf, Category.assoc]

private theorem step_naturality {C : Type*} [Category* C]
    (F G H : C ⥤ C) (c : H ≅ G ⋙ F) (M N : C)
    (θ : G.obj M ≅ M) (η : G.obj N ≅ N) (f : M ⟶ N)
    (hf : G.map f ≫ η.hom = θ.hom ≫ f) :
    H.map f ≫ (evaluateStep F G H c N η).hom =
      (evaluateStep F G H c M θ).hom ≫ F.map f := by
  dsimp only [evaluateStep, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [NatTrans.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp, hf, Functor.map_comp, Category.assoc]

private theorem iterate_naturality (l : ℕ) [Fact l.Prime] {T : Scheme.{u}}
    (a : T ⟶ T) (M N : Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (η : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj N ≅ N)
    (f : M ⟶ N)
    (hf : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).map f ≫ η.hom =
      θ.hom ≫ f) (n : ℕ) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (localPositivePower a n)).map f ≫ (iterate l a N η n).hom =
      (iterate l a M θ n).hom ≫ f := by
  unfold iterate
  refine chain_naturality
    (fun k ↦ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (localPositivePower a k)).obj M)
    (fun k ↦ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (localPositivePower a k)).obj N) M N f _ _ _ _
    (fun k ↦ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (localPositivePower a k)).map f) ?_ ?_ n
  · exact initial_naturality _ _ _ M N θ η f hf
  · intro k
    unfold iterateStep
    exact step_naturality _ _ _ _ M N θ η f hf

private theorem square_naturality {C : Type*} [Category* C]
    {E : Type*} [Category* E] (L : C ⥤ E) (G : C ⥤ C) (H : E ⥤ E)
    (c : G ⋙ L ≅ L ⋙ H) (M N : C)
    (θ : G.obj M ≅ M) (η : G.obj N ≅ N) (f : M ⟶ N)
    (hf : G.map f ≫ η.hom = θ.hom ≫ f) :
    H.map (L.map f) ≫ (c.symm.app N ≪≫ L.mapIso η).hom =
      (c.symm.app M ≪≫ L.mapIso θ).hom ≫ L.map f := by
  dsimp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom]
  change (L ⋙ H).map f ≫ c.inv.app N ≫ _ = _
  rw [NatTrans.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp, hf, Functor.map_comp, Category.assoc]

/-- Pullback of a Weil arrow commutes with the induced source Weil structures.
Source: latest blueprint, paragraph 2
(blueprint: lem-zl-condensed-pullback-frobenius).
Proof: induction on the ordered iterate gives the equivariance equation for theta^[m].
Apply f* and naturality of the canonical square comparison to this equation. -/
theorem map_equivariance {M N : WeilModule D l T₀} (a : M ⟶ N) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      ((constantExtensionDatum D m hm).geometricFrobenius Y₀).hom).map
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (geometricMap D m hm T₀ Y₀ f₀)).map a.hom.f) ≫
        (object D m hm T₀ Y₀ f₀ l N).str.hom =
      (object D m hm T₀ Y₀ f₀ l M).str.hom ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (geometricMap D m hm T₀ Y₀ f₀)).map a.hom.f  := by
  exact square_naturality _ _ _
    (CondensedRing.upperStarSquareComparison (Profinite.padicAlgClRingObj l)
      (geometricMap_frobenius D m hm T₀ Y₀ f₀)) M.carrier N.carrier _ _ a.hom.f
    (iterate_naturality l (D.geometricFrobenius T₀).hom M.carrier N.carrier
      M.str N.str a.hom.f a.hom.h (m - 1))

/-- The actual module inverse-image map, with its Weil equivariance.
Source: latest blueprint, paragraph 2
(blueprint: lem-zl-condensed-pullback-frobenius). -/
def map {M N : WeilModule D l T₀} (a : M ⟶ N) :
    object D m hm T₀ Y₀ f₀ l M ⟶ object D m hm T₀ Y₀ f₀ l N :=
  ObjectProperty.homMk
    { f := (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (geometricMap D m hm T₀ Y₀ f₀)).map a.hom.f
      h := map_equivariance D m hm T₀ Y₀ f₀ l a }

/-- The induced arrow construction preserves identities.
Source: latest blueprint, paragraph 2
(blueprint: lem-zl-condensed-pullback-frobenius).
Proof: forgetting the Weil structure is faithful; the underlying arrow is f*(id)=id. -/
theorem map_identity (M : WeilModule D l T₀) :
    map D m hm T₀ Y₀ f₀ l (𝟙 M) = 𝟙 (object D m hm T₀ Y₀ f₀ l M) := by
  apply ObjectProperty.hom_ext _
  apply CategoryTheory.Endofunctor.Algebra.Hom.ext
  simp [map, object]

/-- The induced arrow construction preserves composites.
Source: latest blueprint, paragraph 2
(blueprint: lem-zl-condensed-pullback-frobenius).
Proof: forgetting the Weil structure is faithful; the underlying equation is functoriality
of module inverse image on a composable pair of arrows. -/
theorem map_composition {M N P : WeilModule D l T₀} (a : M ⟶ N) (b : N ⟶ P) :
    map D m hm T₀ Y₀ f₀ l (a ≫ b) =
      map D m hm T₀ Y₀ f₀ l a ≫ map D m hm T₀ Y₀ f₀ l b := by
  apply ObjectProperty.hom_ext _
  apply CategoryTheory.Endofunctor.Algebra.Hom.ext
  simp [map]

/-- The canonical ambient Weil pullback functor, including its arrow action.
Source: latest blueprint, paragraphs 1--3
(blueprint: lem-zl-condensed-pullback-frobenius). -/
@[irreducible] def functor :
    WeilModule D l T₀ ⥤ WeilModule (constantExtensionDatum D m hm) l Y₀ where
  obj := object D m hm T₀ Y₀ f₀ l
  map := map D m hm T₀ Y₀ f₀ l
  map_id := map_identity D m hm T₀ Y₀ f₀ l
  map_comp := map_composition D m hm T₀ Y₀ f₀ l

/-- The explicit Weil functor has exactly the module inverse-image carrier.
Source: latest blueprint, paragraphs 1--2
(blueprint: lem-zl-condensed-pullback-frobenius).
Proof: expand functor, object and IsoAlgebra.mk; its carrier is the specified module
pullback. This named equality keeps the kernel from unfolding the full Weil functor
inside the scalar-fibre comparison. -/
theorem carrier_eq (M : WeilModule D l T₀) :
    ((functor D m hm T₀ Y₀ f₀ l).obj M).carrier =
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (geometricMap D m hm T₀ Y₀ f₀)).obj M.carrier := by
  unfold functor
  rfl

end WeilConjectures.NativeCondensedPullback

namespace WeilConjectures.NativeCondensedPullback
open NativeL2 NativeCondensedWeil NativeCondensedModule

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
  (T₀ : Over (Spec (.of D.k₀))) [hTft : LocallyOfFiniteType T₀.hom] [hTqc : QuasiCompact T₀.hom]
  [hTs : IsSeparated T₀.hom]
  (Y₀ : Over (Spec (.of (constantExtensionDatum D m hm).k₀)))
  [hYft : LocallyOfFiniteType Y₀.hom] [hYqc : QuasiCompact Y₀.hom]
  [hYs : IsSeparated Y₀.hom]
  (f₀ : Over.mk (Y₀.hom ≫
    Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) ⟶ T₀)
  (l : ℕ) [Fact l.Prime]

set_option linter.unusedSectionVars false in
include hTft hTqc hYft hYqc in
set_option linter.unusedSectionVars false in
include hTs hYs in
set_option linter.unusedSectionVars false in
include hTs hYs in
set_option linter.unusedSectionVars false in
include hTs hYs in
end WeilConjectures.NativeCondensedPullback
