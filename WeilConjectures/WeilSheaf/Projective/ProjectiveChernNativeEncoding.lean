/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Projective.ProjectiveLineRestriction
public import WeilConjectures.AlgebraicGeometry.NativeCartier.NativeCartierRealization
public import WeilConjectures.AlgebraicGeometry.NativeEncoding.NativeAdicEncodingCore
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraFullyFaithful
import WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobenius

/-! # The specified coefficient encoding on native Weil sheaves

Source: the exact continuous-coefficient encoding and geometric Frobenius inverse image.
(blueprint: def-pur-v5-projective-chern-native-encoding).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The Frobenius exchange of the actual coefficient encoding.
Source: the mate-normalized encoding pullback comparison and inverse image of an isomorphism.
(blueprint: def-pur-v5-projective-chern-native-encoding). -/
def projectiveChernFrobeniusEncoding :
    ProEtale.NativeEncoding.encoding l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ⋙
        ProEtale.NativeCartier.frobenius k₀ l X ≅
      WeilSheaf.frobeniusPullback k₀ l X ⋙
        ProEtale.NativeEncoding.encoding l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  (ProEtale.NativeEncoding.pullComparison l
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom).symm ≪≫
      Functor.isoWhiskerRight (ProEtale.adicUpperStarIsoLowerStarInv l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius) _

/-- Encode the native fixed pairs before deriving.
Source: fixed-pair transport of the specified Frobenius exchange.
(blueprint: def-pur-v5-projective-chern-native-encoding). -/
def projectiveChernNativeEncoding :
    ProEtaleWeilSheaf k₀ l X ⥤ ProEtale.NativeCartier.WeilModules k₀ l X :=
  Endofunctor.IsoAlgebra.mapOfNatIso (projectiveChernFrobeniusEncoding (l := l) X)

/-- The native encoding preserves addition on the actual underlying maps.
Source: additive fixed-pair transport of the additive coefficient encoding.
(blueprint: def-pur-v5-projective-chern-native-encoding). -/
instance projectiveChernNativeEncoding_additive :
    (projectiveChernNativeEncoding (k₀ := k₀) (l := l) X).Additive :=
  Endofunctor.IsoAlgebra.additive_mapOfNatIso _

/-- This encoding is an equivalence on native sheaves, without a separatedness hypothesis.
Source: fully faithful fixed-pair transport and the continuous-coefficient equivalence.
(blueprint: def-pur-v5-projective-chern-native-encoding).
Proof: fullness and faithfulness lift along the Frobenius exchange. For a target fixed
pair M, use the inverse coefficient encoding for its carrier; transport its structure
map across the counit and the exchange. Full faithfulness lifts this isomorphism, and
the counit itself is an isomorphism of fixed pairs. -/
instance projectiveChernNativeEncoding_isEquivalence :
    (projectiveChernNativeEncoding (k₀ := k₀) (l := l) X).IsEquivalence := by
  let E := ProEtale.NativeEncoding.equivalence l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let c := projectiveChernFrobeniusEncoding (k₀ := k₀) (l := l) X
  let T := projectiveChernNativeEncoding (k₀ := k₀) (l := l) X
  let ff : T.FullyFaithful :=
    Endofunctor.IsoAlgebra.fullyFaithfulMapOfNatIso c E.fullyFaithfulFunctor
  let : T.Full := ff.full
  let : T.Faithful := ff.faithful
  let : T.EssSurj := ⟨fun M ↦ by
    let B := E.inverse.obj M.carrier
    let b : E.functor.obj B ≅ M.carrier := E.counitIso.app M.carrier
    let t : (WeilSheaf.frobeniusPullback k₀ l X).obj B ≅ B := E.functor.preimageIso
      ((c.app B).symm ≪≫ (ProEtale.NativeCartier.frobenius k₀ l X).mapIso b ≪≫
        M.str ≪≫ b.symm)
    refine ⟨Endofunctor.IsoAlgebra.mk B t,
      ⟨ObjectProperty.isoMk _ (Endofunctor.Algebra.isoMk b ?_)⟩⟩
    change (ProEtale.NativeCartier.frobenius k₀ l X).map b.hom ≫ M.str.hom =
      (c.hom.app B ≫ E.functor.map t.hom) ≫ b.hom
    simp [t, Category.assoc]⟩
  exact { }

/-- The equivalence with the specified forward encoding; its inverse is determined by it.
Source: the exact continuous-coefficient encoding.
(blueprint: def-pur-v5-projective-chern-native-encoding). -/
def projectiveChernNativeEquivalence :
    ProEtaleWeilSheaf k₀ l X ≌ ProEtale.NativeCartier.WeilModules k₀ l X :=
  (projectiveChernNativeEncoding (k₀ := k₀) (l := l) X).asEquivalence

/-- The forward functor of the specified native equivalence is additive. -/
instance projectiveChernNativeEquivalence_additive :
    (projectiveChernNativeEquivalence (k₀ := k₀) (l := l) X).functor.Additive :=
  projectiveChernNativeEncoding_additive (k₀ := k₀) (l := l) X

/-- The specified inverse encoding is additive, so acts on complexes and derived arrows.
Source: additivity of the inverse of an additive equivalence.
(blueprint: def-pur-v5-projective-chern-native-encoding). -/
instance projectiveChernNativeEquivalence_inverse_additive :
    (projectiveChernNativeEquivalence (k₀ := k₀) (l := l) X).inverse.Additive :=
  (projectiveChernNativeEquivalence (k₀ := k₀) (l := l) X).inverse_additive

end AlgebraicGeometry.WeilComplex
