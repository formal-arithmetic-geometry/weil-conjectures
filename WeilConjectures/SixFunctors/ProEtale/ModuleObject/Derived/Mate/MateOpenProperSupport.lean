/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenBoundaryZero
import WeilConjectures.AlgebraicGeometry.SixFunctors.QcqsProperConstructibleClosedBaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Support of proper image of extension by zero in a Cartesian open square

Source: blueprint det-sf-comp-composition-interchange, proof (3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Proper image of open extension has no boundary cohomology on the localizing hull.
Source: blueprint det-sf-comp-composition-interchange, proof (3)
(blueprint: lem-sfb-mate-open-proper-support).

Proof: On a bounded constructible finite-Tor generator, apply closed proper base
change to the complementary closed square. Mixed open/closed restriction kills its
source. The usual coefficient cases use proper_open_boundary_zero; the continuous
algebraic-closure case uses the norm-topological closed base-change theorem. Proper
compact-support image preserves coproducts on the localizing hull. Exact closed
restriction preserves coproducts as a left adjoint, so the kernel of their composite
is replete, triangulated and sum-closed. Minimality of the hull extends the vanishing
from the generators to every object, including unbounded ones. -/
theorem mateOpenProperSupport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {W V Y : Over (Spec (.of k))}
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (r : W ⟶ Y) [IsProper r.left]
    (i : V ⟶ Y) [IsOpenImmersion i.left] [QuasiCompact i.left]
    (K : DerivedCategory
      (Mod (Sheaf (ProEt.topology (pullback r.left i.left)) Ab.{u + 1})
        (condensedRingObj Λ (pullback r.left i.left))))
    (hK : localizingClosureProEtale Λ (pullback r.left i.left) K) :
    IsZero ((upperStar Λ i.left.closedComplement).mapDerivedCategory.obj
      ((lowerStar Λ r.left).rightDerivedFunctor.obj
        ((openImmersionLowerShriek Λ (pullback.fst r.left i.left)).mapDerivedCategory.obj K))) := by
  let b := pullback.fst r.left i.left
  let c := i.left.closedComplement
  let : W.left.Over (Spec (.of k)) := ⟨W.hom⟩
  let : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  let : (pullback r.left i.left).Over (Spec (.of k)) := ⟨b ≫ W.hom⟩
  have : b.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : r.left.IsOver (Spec (.of k)) := ⟨Over.w r⟩
  have : LocallyOfFiniteType (W.left ↘ Spec (.of k)) := inferInstanceAs
    (LocallyOfFiniteType W.hom)
  have : QuasiCompact (W.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact W.hom)
  have : IsSeparated (W.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated W.hom)
  have : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) := inferInstanceAs
    (LocallyOfFiniteType Y.hom)
  have : QuasiCompact (Y.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact Y.hom)
  have : IsSeparated (Y.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated Y.hom)
  have : LocallyOfFiniteType (pullback r.left i.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (b ≫ W.hom))
  have : QuasiCompact (pullback r.left i.left ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (b ≫ W.hom))
  have : IsSeparated (pullback r.left i.left ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (b ≫ W.hom))
  let J := (openImmersionLowerShriek Λ b).mapDerivedCategory
  let R := (lowerStar Λ r.left).rightDerivedFunctor
  let C := (upperStar Λ c).mapDerivedCategory
  let F := J ⋙ R ⋙ C
  let cr : Compactification (b ≫ r.left) :=
    { Z := W.left
      i := b
      g := r.left
      comm := rfl
      isProper := inferInstance
      isOpenImmersion := inferInstance }
  let bc : Compactification.BoundaryCompactification (b ≫ r.left) :=
    ⟨⟨cr, inferInstance⟩⟩
  have : IsLocallyNoetherian Y.left :=
    LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsNoetherian Y.left := ⟨⟩
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have hsums := (compactification_localizing Λ ℓ k (b ≫ r.left) bc hΛ).2.2.1
  let : C.IsLeftAdjoint :=
    ((derivedUpperStarLowerStarAdjunction Λ c).ofNatIsoLeft
      (leftDerivedUpperStarIsoMapDerivedCategory Λ c)).isLeftAdjoint
  let S := constantModelBoundedConstructible Λ (pullback r.left i.left) ⊓
    fun L ↦ DerivedCategory.finiteTorAmplitude _ L
  apply CategoryTheory.extend_zero S
    (ProEtale.localizingClosure_exists Λ _ S).2.2.2.1 F _ _ K hK
  · intro I L hL
    have : PreservesColimit L (J ⋙ R) := hsums I L hL
    change PreservesColimit L ((J ⋙ R) ⋙ C)
    infer_instance
  · intro A hA
    have hc : Set.range c.base = (Set.range i.left.base)ᶜ :=
      Scheme.Hom.range_closedComplement i.left
    have hstandard (hstd : IsFiniteSubextensionLocalizingAdmissibleCoefficient ℓ Λ) :
        IsZero (F.obj A) := by
      let Z : Over (Spec (.of k)) := Over.mk (c ≫ Y.hom)
      have : LocallyOfFiniteType Z.hom :=
        inferInstanceAs (LocallyOfFiniteType (c ≫ Y.hom))
      have : QuasiCompact Z.hom := inferInstanceAs (QuasiCompact (c ≫ Y.hom))
      have : IsSeparated Z.hom := inferInstanceAs (IsSeparated (c ≫ Y.hom))
      let cc : Z ⟶ Y := Over.homMk c
      have : IsClosedImmersion cc.left := inferInstanceAs (IsClosedImmersion c)
      have : IsReduced Z.left := by
        change IsReduced (Scheme.IdealSheafData.vanishingIdeal
          ⟨(i.left.opensRange : Set Y.left)ᶜ, i.left.opensRange.isOpen.isClosed_compl⟩).subscheme
        infer_instance
      have hzero := proper_open_boundary_zero ℓ Λ hstd k W Y V Z r i cc hc ⟨A, hA⟩
      exact hzero.of_iso ((leftDerivedUpperStarIsoMapDerivedCategory Λ c).symm.app _)
    rcases hΛ with hf | hz | hq | he | ho | hfbar
    · exact hstandard (Or.inl hf)
    · exact hstandard (Or.inr (Or.inl hz))
    · exact hstandard (Or.inr (Or.inr (Or.inl hq)))
    · exact hstandard (Or.inr (Or.inr (Or.inr (Or.inl he))))
    · exact hstandard (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ho)))))
    · exact hstandard (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hfbar)))))

end AlgebraicGeometry.ProEtale.CondensedRing
