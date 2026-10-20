/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups B2, C4
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FinitenessCoefficient
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor

import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Sheaf.AlgebraicGeometry.LfpTensorSingle
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import all Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal


/-! # BoundedConstructibleTensorSingle

The remaining local tensor calculation on constructible sheaves in degree zero.
-/

@[expose] public section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

open scoped CategoryTheory.Obj
open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ] {k : Type u} [Field k]
variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The tensor calculation for two constructible sheaves in degree zero.

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3);
blueprint `lem-sfb-dc-tensor-preserves`, steps 1--9. The finite-type scheme is noetherian.
Refine the finite constructible stratifications of F and G. On each stratum the two
restrictions are locally finitely presented. In the field cases local triviality reduces
tensoring to a finite sum of the second factor in degree zero. In the integral cases use
the existing two-term locally finite free resolution of the first factor. Tensor its
short exact sequence triangle with the second factor: rotation gives the lower bound -1,
and the weak Serre closure of locally finitely presented integral modules gives finite
presentation of all homology. The general derived tensor upper bound is zero. Exact
monoidal inverse image identifies these local computations with the restrictions of the
global tensor. Finite quasi-compact stratum detection descends the lower vanishing bound,
and the common stratification exhibits constructibility of every homology sheaf.
The zero module, rank zero and empty strata are included.
(blueprint: lem-sfb-dc-tensor-single) -/
theorem boundedConstructible_tensor_single
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))
    (hF : IsConstructibleModuleObject (condensedRingObj Λ X.left) F)
    (hG : IsConstructibleModuleObject (condensedRingObj Λ X.left) G) :
    boundedConstructible (condensedRingObj Λ X.left)
      ((DerivedCategory.singleFunctor _ 0).obj F ⊗
        (DerivedCategory.singleFunctor _ 0).obj G) := by
  classical
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  let R := condensedRingObj Λ X.left
  let K := (DerivedCategory.singleFunctor _ 0).obj F ⊗
    (DerivedCategory.singleFunctor _ 0).obj G
  obtain ⟨S, hS⟩ := common_lfp_stratification hF hG
  let H (a : Fin S.n) := upperStar Λ (S.immersion a)
  have lfp (a : Fin S.n)
      (M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) R)
      (hM : IsLocallyFinitelyPresented
        ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).obj R)
        (((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).mapMod R).obj M)) :
      IsLocallyFinitelyPresented (condensedRingObj Λ (S.domain a)) ((H a).obj M) := by
    exact localFinitePresentation_of_iso
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ (S.immersion a))).app _).symm
      (localFinitePresentation_comap _ hM)
  let e (a : Fin S.n) : (H a).leftDerivedFunctor.obj K ≅
      (DerivedCategory.singleFunctor _ 0).obj ((H a).obj F) ⊗
        (DerivedCategory.singleFunctor _ 0).obj ((H a).obj G) :=
    (Functor.Monoidal.μIso (H a).leftDerivedFunctor _ _).symm ≪≫
      tensorIso ((H a).singleFunctorCompLeftDerivedFunctorIso.app F)
        ((H a).singleFunctorCompLeftDerivedFunctorIso.app G)
  have hlocal (a : Fin S.n) :
      TopologicalSpace.NoetherianSpace (S.domain a) :=
    (S.immersion a).isEmbedding.noetherianSpace
  have hom_lfp (a : Fin S.n) (n : ℤ) :
      IsLocallyFinitelyPresented (condensedRingObj Λ (S.domain a))
        ((H a).obj ((DerivedCategory.homologyFunctor _ n).obj K)) := by
    apply localFinitePresentation_of_iso
      ((H a).leftDerivedFunctorHomologyFunctorIso n |>.app K).symm
    apply localFinitePresentation_of_iso ((DerivedCategory.homologyFunctor _ n).mapIso (e a)).symm
    exact (lfp_tensor_single Λ (S.domain a) ((H a).obj F) ((H a).obj G)
      (lfp a F (hS a).1) (lfp a G (hS a).2)).2 n
  have detect
      (M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) R)
      (hM : ∀ a : Fin S.n, IsZero ((H a).obj M)) : IsZero M := by
    rw [IsZero.iff_id_eq_zero]
    apply Mod.hom_ext
    apply abDetectMaps S.immersion
    · intro x
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
      exact ⟨a, S.range_immersion a |>.symm ▸ ha⟩
    · intro a
      let e' := (Mod.extendScalarsIsoComapInv
        (condensedPullbackHom Λ (S.immersion a))).app
        (((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).mapMod R).obj M)
      have hz := (Mod.forget _).map_isZero ((hM a).of_iso e'.symm)
      change IsZero ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).obj M.X) at hz
      simpa using hz.eq_of_src
        ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).map (𝟙 M.X)) 0
  have hupper := DerivedCategory.isLE_tensor
    ((DerivedCategory.singleFunctor _ 0).obj F)
    ((DerivedCategory.singleFunctor _ 0).obj G) 0 0
  rw [add_zero] at hupper
  apply (mem_boundedConstructible_iff R K).2
  constructor
  · refine ⟨-1, 0, fun n hn ↦ ?_⟩
    rcases hn with hn | hn
    · apply detect
      intro a
      have hb := (lfp_tensor_single Λ (S.domain a) ((H a).obj F) ((H a).obj G)
        (lfp a F (hS a).1) (lfp a G (hS a).2)).1
      have hz := (DerivedCategory.isGE_iff _ (-1)).1 hb n hn
      exact hz.of_iso
        (((H a).leftDerivedFunctorHomologyFunctorIso n).app K ≪≫
          (DerivedCategory.homologyFunctor _ n).mapIso (e a))
    · exact (DerivedCategory.isLE_iff K 0).1 hupper n hn
  · intro n
    refine ⟨S, fun a ↦ ?_⟩
    apply localFinitePresentation_of_comap (inv (condensedPullbackHom Λ (S.immersion a)))
    apply localFinitePresentation_of_iso
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ (S.immersion a))).app _)
    exact hom_lfp a n

end AlgebraicGeometry.ProEtale.CondensedRing
