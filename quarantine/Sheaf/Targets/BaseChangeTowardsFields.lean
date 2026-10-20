/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import Sheaf.AlgebraicGeometry.InvertibleTorsionOrders
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import Sheaf.AlgebraicGeometry.UnboundedExchangeAgrees
import Sheaf.AlgebraicGeometry.KunnethBaseChangeFailure
import Sheaf.AlgebraicGeometry.NTorsionModuleLift
import Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison
import Sheaf.AlgebraicGeometry.ConstantHigherDirectImageSquareIso
import Sheaf.AlgebraicGeometry.NormalGenericFibreVanishing
import Sheaf.AlgebraicGeometry.DegreeZeroFieldBaseChange
import Sheaf.AlgebraicGeometry.TorsionExchangeFilteredPassage

/-!
# Base change towards spectra of fields

Source: Stacks Project, Tag 0F1I (blueprint: lem-kun-0f1i).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

private theorem genericFibre_vanishes_in_cartesian_diagram
    {K : Type u} [Field K] {X S' X' Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f]
    (a : S' ⟶ Spec (.of K)) (b : X' ⟶ X) (f' : X' ⟶ S')
    (sq₁ : ChosenCartesianSquare b f' f a)
    [IsAffine S'] [IsIntegral S'] (hnormal : ∀ x : S',
      IsIntegrallyClosed (S'.presheaf.stalk x)) [IsAlgClosed S'.functionField]
    (e : Y ⟶ Spec S'.functionField) (h : Y ⟶ X')
    (sq₂ : ChosenCartesianSquare h e f' (S'.fromSpecStalk (genericPoint S')))
    (n : invertibleTorsionOrders K) (q : ℤ) (hq : 0 < q) (d : ℕ) (hd : d ∣ n.val) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod d))))))) := by
  let : X.Over (Spec (.of K)) := ⟨f⟩
  let : S'.Over (Spec (.of K)) := ⟨a⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of K)) := ‹LocallyOfFiniteType f›
  have : QuasiCompact (X ↘ Spec (.of K)) := ‹QuasiCompact f›
  let j := S'.fromSpecStalk (genericPoint S')
  let c := pullback.map f' j (pullback.snd f a) j sq₁.isoPullback.hom
    (𝟙 _) (𝟙 _) (by simpa using sq₁.hom_snd.symm) (by simp)
  have : IsIso c := by dsimp [c]; infer_instance
  let cY := sq₂.isoPullback.hom ≫ c
  have hc : cY ≫ pullback.fst (pullback.snd f a) j = h ≫ sq₁.isoPullback.hom := by
    simp only [cY, c, pullback.map, Category.assoc, pullback.lift_fst]
    rw [← Category.assoc, sq₂.hom_fst]
  let sq : IsPullback (inv cY) (pullback.fst (pullback.snd f a) j)
      h sq₁.isoPullback.inv := IsPullback.of_horiz_isIso ⟨by
    rw [IsIso.inv_comp_eq, ← Category.assoc, hc, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]⟩
  have hn : IsNormalScheme S' :=
    ⟨inferInstance, fun x ↦ ⟨inferInstance, hnormal x⟩⟩
  exact isZero_constantHigherDirectImage_of_isomorphic_square sq
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod d))) q
    (isZero_higherDirectImage_constant_genericFibre n X S' hn q hq d hd)

private theorem cumulativeFieldBaseChange_of_zero
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f]
    (n : invertibleTorsionOrders K)
    (hinv : IsUnit (n.val : Γ(Spec (.of K), ⊤)))
    (hzero : UnboundedCumulativeUniversalBaseChangeProperty f n.val n.property.1 0) :
    ∀ q : ℕ, UnboundedCumulativeUniversalBaseChangeProperty f n.val n.property.1 q := by
  intro q
  induction q with
  | zero => exact hzero
  | succ q ih =>
    by_contra hfail
    obtain ⟨S', X', a, b, f', sq₁, hAffine, hIntegral, hnormal, hclosed,
      Y, e, h, sq₂, d, hd, hne⟩ :=
      exists_kunnethBaseChangeFailure_functionField f n.val n.property.1 hinv (q + 1)
        (by omega) (by simpa using ih) hfail
    exact hne (genericFibre_vanishes_in_cartesian_diagram f a b f' sq₁ hnormal
      e h sq₂ n ((q + 1 : ℕ) : ℤ) (by omega) d hd)

private theorem isIso_exact_exchange_iff_abelian
    (Λ : Type (u + 1)) [CommRing Λ]
    {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : ChosenCartesianSquare g' f' f g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) ↔
      IsIso ((exactDerivedBaseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app
        ((moduleAbelianForget Λ X).mapDerivedCategory.obj K)) := by
  obtain ⟨hU, hR, hEx⟩ := unbounded_abelian_exchange_comparison Λ sq
  have := (hU Y').2.2.2.1
  have := (hR f).1
  have := (hR f').1
  rw [← isIso_iff_of_reflects_iso _ (moduleAbelianForget Λ Y').mapDerivedCategory]
  have hi := congrArg IsIso (hEx K)
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using hi.to_iff

private theorem boundedExponentFieldBaseChange_of_zero
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f]
    (n : invertibleTorsionOrders K)
    (hzero : UnboundedCumulativeUniversalBaseChangeProperty f n.val n.property.1 0)
    (S' : Scheme.{u}) (a : S' ⟶ Spec (.of K)) (T : Scheme.{u}) (g : T ⟶ S')
    [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : n.val • 𝟙 F = 0) :
    IsIso ((exactDerivedBaseChangeMap AddCommGrpCat.{u + 1}
      (IsPullback.of_hasPullback (pullback.snd f a) g).flip.toCommSq).app
        ((DerivedCategory.singleFunctor _ 0).obj F)) := by
  have hinv : IsUnit (n.val : Γ(Spec (.of K), ⊤)) := by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr n.property.2).map ((Scheme.ΓSpecIso (.of K)).inv.hom)
  obtain ⟨G, ⟨e⟩⟩ := exists_moduleLift_of_nsmul_eq_zero n.val F hF
  let Λ := ULift.{u + 1} (ZMod n.val)
  have hmod : IsIso ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ)
      (IsPullback.of_hasPullback (pullback.snd f a) g).flip.toCommSq).app
        ((DerivedCategory.singleFunctor _ 0).obj G)) := by
    apply (DerivedCategory.isIso_iff _ _).mpr
    intro q
    exact cumulativeFieldBaseChange_of_zero f n hinv hzero q.toNat S' a T g G q
      (by omega)
  let c : ChosenCartesianSquare (pullback.snd (pullback.snd f a) g)
      (pullback.fst (pullback.snd f a) g) g (pullback.snd f a) :=
    { toCommSq := (IsPullback.of_hasPullback (pullback.snd f a) g).flip.toCommSq
      isoPullback := (IsPullback.of_hasPullback (pullback.snd f a) g).flip.isoPullback
      hom_fst := (IsPullback.of_hasPullback (pullback.snd f a) g).flip.isoPullback_hom_fst
      hom_snd := (IsPullback.of_hasPullback (pullback.snd f a) g).flip.isoPullback_hom_snd }
  have hab := (isIso_exact_exchange_iff_abelian Λ c _).mp hmod
  exact (NatTrans.isIso_app_iff_of_iso
    (exactDerivedBaseChangeMap AddCommGrpCat.{u + 1} c.toCommSq)
    (((moduleAbelianForget Λ T).mapDerivedCategorySingleFunctor 0).app G ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso e)).mp hab

/-- Base change for torsion étale sheaves along a finite-type scheme over a field.
Source: Stacks Project, Tag 0F1I (blueprint: lem-kun-0f1i).

Proof:
1. Degree-zero exchange holds universally over any field. Pass to its perfect closure
and reduce the scheme. The two comparison maps are universal homeomorphisms. Flat
base change applies after reduction; pasting and cancelling the comparison exchanges
descends the degree-zero result. Negative cohomology vanishes.
2. Induct on the cumulative universal degree bound. Failure in the successor degree
produces a normal integral affine scheme with algebraically closed function field and
a nonzero constant higher direct image. The normal generic-fibre vanishing theorem
contradicts this, after transporting through the canonical Cartesian isomorphisms.
3. A sheaf killed by n has the canonical Z/nZ-module structure on its sections.
The module-to-abelian comparison reflects invertibility of the exact derived exchange.
Thus all sheaves killed by a positive invertible n have invertible exchange.
4. Express F as the filtered colimit of its invertible-order torsion kernels. Both
cohomology endpoint functors preserve this colimit, by exactness of inverse image and
filtered-colimit preservation of qcqs higher direct image. Naturality identifies its
exchange with the colimit of the exchanges of the kernels. Each kernel is killed by
its index, so step 3 applies. Cohomology detects invertibility. -/
theorem baseChange_towardsSpecField
    {K : Type u} [Field K]
    {X S' T : Scheme.{u}}
    (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [QuasiCompact f]
    [S'.Over (Spec (.of K))] [T.Over (Spec (.of K))]
    (g : T ⟶ S') [g.IsOver (Spec (.of K))]
    [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsTorsionOfInvertibleOrder K (Over.mk (T ↘ Spec (.of K))) F) :
    IsIso (((exactDerivedBaseChangeMap AddCommGrpCat.{u + 1}
      (CommSq.mk (pullback.condition (f := pullback.snd f (S' ↘ Spec (.of K)))
        (g := g)).symm)).app
      ((DerivedCategory.singleFunctor
        (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) := by
  apply isIso_exchange_of_isIso_torsion_pieces f g F hF
  intro n hn
  apply boundedExponentFieldBaseChange_of_zero f ⟨n, hn⟩
    (unboundedCumulativeFieldBaseChange_zero f n hn.1) S'
      (S' ↘ Spec (.of K)) T g (etaleNTorsion F n)
  change n • 𝟙 (kernel (n • 𝟙 F)) = 0
  apply (cancel_mono (kernel.ι (n • 𝟙 F))).1
  simp only [Preadditive.nsmul_comp, Category.id_comp, zero_comp]
  exact kernel.condition (n • 𝟙 F)

end AlgebraicGeometry.Etale
