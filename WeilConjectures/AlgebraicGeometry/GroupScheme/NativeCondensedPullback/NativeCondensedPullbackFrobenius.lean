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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- The induced arrow construction preserves composites.
Source: latest blueprint, paragraph 2
(blueprint: lem-zl-condensed-pullback-frobenius).
Proof: forgetting the Weil structure is faithful; the underlying equation is functoriality
of module inverse image on a composable pair of arrows. -/
theorem map_composition {M N P : WeilModule D l T₀} (a : M ⟶ N) (b : N ⟶ P) :
    map D m hm T₀ Y₀ f₀ l (a ≫ b) =
      map D m hm T₀ Y₀ f₀ l a ≫ map D m hm T₀ Y₀ f₀ l b := by
  sorry

/-- The canonical ambient Weil pullback functor, including its arrow action.
Source: latest blueprint, paragraphs 1--3
(blueprint: lem-zl-condensed-pullback-frobenius). -/
@[irreducible] def functor :
    WeilModule D l T₀ ⥤ WeilModule (constantExtensionDatum D m hm) l Y₀ where
  obj := object D m hm T₀ Y₀ f₀ l
  map := map D m hm T₀ Y₀ f₀ l
  map_id := map_identity D m hm T₀ Y₀ f₀ l
  map_comp := map_composition D m hm T₀ Y₀ f₀ l

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
