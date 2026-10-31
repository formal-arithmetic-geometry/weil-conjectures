/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic
import WeilConjectures.SixFunctors.ProEtale.Adic.ConstructibleHeart
import WeilConjectures.AlgebraicGeometry.Native.NativeAdicConstructibilityEncoding
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback

/-!
# Adic finiteness for projection from relative projective space

This is the proper input for the affine compactification reduction of
`sk-prop-sf-finiteness`. Its source is a constructible sheaf in degree zero; the existing
truncation dévissage extends the result to bounded constructible complexes.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {K : Type u} [Field K] [IsAlgClosed K]

open Scheme
open Limits
open scoped CategoryTheory.Obj

-- Retain the original algebraic-closedness hypothesis in the public statement.
set_option linter.unusedSectionVars false in
/-- Projection from finite-dimensional projective space over an affine finite-type base
has bounded constructible direct image on constructible adic sheaves.

Source: the proper-case paragraph of `sk-prop-sf-finiteness`, SGA 4½, *Théorème de finitude*,
Theorem 1.1; Bhatt--Scholze, Lemma 6.7.2, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-adic-projective-space-direct-image-finiteness)

Proof: the base is Noetherian since it is affine and locally of finite type over K;
the projective-space projection is proper and locally of finite type, so its source
is Noetherian as well. The normalized native-to-condensed encoding is an exact
faithful equivalence. On both schemes it preserves and detects constructibility:
local finite-free trivializations correspond under the pullback comparison, and
local finite presentation over these field coefficients is local finite freeness.
Thus F[0] encodes to a bounded constructible complex. Apply the existing proper
finiteness theorem for condensed algebraic-closure coefficients. The derived
pushforward comparison identifies its image with the encoding of Rp_* F[0].
Exactness and faithfulness reflect boundedness, and the homology comparison and
the constructibility equivalence reflect constructible cohomology. The construction
includes the empty base and the case n empty (projective zero-space). -/
theorem bounded_constructible_rightDerivedFunctor_adicLowerStar_projectiveSpace
    (hK : ringChar K ≠ l) {W : Scheme.{u}} [IsAffine W]
    (t : W ⟶ Spec (.of K)) [LocallyOfFiniteType t] (n : Type u) [Finite n]
    (F : AdicSheaf l ℙ(Option n; W)) (hF : IsAdicConstructibleSheaf F) :
    (_root_.DerivedCategory.TStructure.t.bounded ⊓
      _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l W))
      ((ℙ(Option n; W) ↘ W)_*ᵃ[l].rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by
  classical
  have : Fact (ringChar K ≠ l) := ⟨hK⟩
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian t
  have : IsNoetherian W := {}
  have : IsNoetherian ℙ(Option n; W) :=
    isNoetherian_of_locallyOfFiniteType (ℙ(Option n; W) ↘ W)
  let A := (_root_.DerivedCategory.singleFunctor _ 0).obj F
  let p := ℙ(Option n; W) ↘ W
  have hA := (DerivedCategory.adicConstructibleHeart_singleFunctor_obj hF).1.1
  have hX := NativeEncoding.encoding_exact_derived l ℙ(Option n; W)
  have hY := NativeEncoding.encoding_exact_derived l W
  let := hX.1
  let := hX.2.1
  let := hY.1
  let := hY.2.1
  have hencoded : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj l) ℙ(Option n; W))
      ((NativeEncoding.derivedEncoding l ℙ(Option n; W)).obj A) := by
    refine ⟨(NativeEncoding.encoding l _).bounded_mapDerivedCategory_obj hA.1, ?_⟩
    intro q
    exact constructible_of_iso
      (((NativeEncoding.encoding l _).mapDerivedCategoryHomologyFunctorIso q).app A)
      ((encoding_constructible_iff _).mp (hA.2 q))
  have hp :=
    CondensedRing.boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicAlgClRingObj
      l t p _ hencoded
  have himage : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj l) W)
      ((NativeEncoding.derivedEncoding l W).obj ((adicLowerStar l p).rightDerivedFunctor.obj A)) :=
    ⟨(_root_.DerivedCategory.TStructure.t.bounded).prop_of_iso
      ((NativeEncoding.derivedPushComparison l p).app A).symm hp.1,
      fun q ↦ constructible_of_iso
        ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
          ((NativeEncoding.derivedPushComparison l p).app A).symm) (hp.2 q)⟩
  refine ⟨(NativeEncoding.encoding l W).bounded_of_bounded_mapDerivedCategory_obj himage.1,
    fun q ↦ ?_⟩
  apply (encoding_constructible_iff _).mpr
  exact constructible_of_iso
    (((NativeEncoding.encoding l W).mapDerivedCategoryHomologyFunctorIso q).app
      ((adicLowerStar l p).rightDerivedFunctor.obj A)).symm (himage.2 q)

end AlgebraicGeometry.ProEtale
