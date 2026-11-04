/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartFiltration
import all WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedReconstruction
import all WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # Closed-then-open extension by zero on a topologically Noetherian scheme

For a closed immersion `t : S ⟶ V` followed by an open immersion `v : V ⟶ X`, the extension
by zero `v_! t_* M` restricts to `M` along `t ≫ v` and to zero away from its range. When `X`
is topologically Noetherian it agrees with the open-then-closed extension
`coefficientHeartLocallyClosedExtension` through the scheme-theoretic closure.

Source: Bhatt--Scholze, Lemma 6.8.13; Stacks Project, Tags 03DI, 03DJ and 09BM
(blueprint: lem-sfb-topological-locally-closed-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The closed-then-open extension by zero `v_! t_* M` restricts to zero along any morphism
whose range is disjoint from the range of `t ≫ v`.

Source: Stacks Project, Tags 03DI and 03DJ
(blueprint: lem-sfb-topological-locally-closed-extension). -/
theorem isZero_upperStar_openImmersionLowerShriek_lowerStar_of_disjoint
    {S V X Y : Scheme.{u}} (t : S ⟶ V) [IsClosedImmersion t] (v : V ⟶ X) [IsOpenImmersion v]
    (g : Y ⟶ X) (hg : Disjoint (Set.range g) (Set.range (t ≫ v)))
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    IsZero ((upperStar Λ g).obj
      ((openImmersionLowerShriek Λ v).obj ((lowerStar Λ t).obj M))) := by
  have hdis : Disjoint (Set.range (pullback.snd g v)) (Set.range t) := by
    rw [Set.disjoint_left]
    rintro x ⟨y, rfl⟩ ⟨z, hz⟩
    apply Set.disjoint_left.mp hg
      (show v (pullback.snd g v y) ∈ Set.range g from
        ⟨pullback.fst g v y, by
          exact congrArg (fun f : pullback g v ⟶ X ↦ f y) pullback.condition⟩)
    exact ⟨z, congrArg v hz⟩
  let O : V.Opens := ⟨(Set.range t)ᶜ, t.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hO : Set.range O.ι = (Set.range t)ᶜ := O.range_ι
  have hfactor : Set.range (pullback.snd g v) ⊆ Set.range O.ι := by
    rw [hO]
    exact hdis.subset_compl_right
  let f := IsOpenImmersion.lift O.ι (pullback.snd g v) hfactor
  have hf : f ≫ O.ι = pullback.snd g v := IsOpenImmersion.lift_fac _ _ hfactor
  have hz := ((upperStar Λ f).map_isZero
    (openRestrictionPushforwardZero Λ t O.ι hO M)).of_iso
      ((upperStarCongr Λ hf.symm).app _ ≪≫ (upperStarComp Λ f O.ι).app _)
  have hz' := ((Mod.forget _).map_isZero hz).of_iso
    (upperStarObjXIso Λ (pullback.snd g v) _).symm
  have ebc := (ProEtale.openImmersionLowerShriekBaseChangeIso Ab.{u + 1}
    (IsPullback.of_hasPullback g v).flip).app ((lowerStar Λ t).obj M).X
  exact isZero_of_isZero_X Λ
    (((ProEtale.openImmersionLowerShriek Ab.{u + 1} (pullback.fst g v)).map_isZero
      hz').of_iso (upperStarObjXIso Λ g _ ≪≫ ebc.symm))

/-- The closed-then-open extension by zero `v_! t_* M` restricts to `M` along `t ≫ v`: the
unit of `v_! ⊣ v^*` and the counit of `t^* ⊣ t_*` are isomorphisms.

Source: Stacks Project, Tags 03DI and 03DJ
(blueprint: lem-sfb-topological-locally-closed-extension). -/
theorem nonempty_upperStar_openImmersionLowerShriek_lowerStar_iso
    {S V X : Scheme.{u}} (t : S ⟶ V) [IsClosedImmersion t] (v : V ⟶ X) [IsOpenImmersion v]
    (a : S ⟶ X) (htv : t ≫ v = a)
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    Nonempty ((upperStar Λ a).obj
      ((openImmersionLowerShriek Λ v).obj ((lowerStar Λ t).obj M)) ≅ M) := by
  have hc : IsIso (upperStarLowerStarAdjunction Λ t).counit :=
    moduleCounitOfAbelian Λ t (ProEtale.abelian_closed_counit t)
  have hu : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ v).unit :=
    openUnitIsIso Λ v
  exact ⟨(upperStarCongr Λ htv.symm).app _ ≪≫ (upperStarComp Λ t v).app _ ≪≫
    (upperStar Λ t).mapIso
      (asIso ((openImmersionLowerShriekUpperStarAdjunction Λ v).unit.app
        ((lowerStar Λ t).obj M))).symm ≪≫
    asIso ((upperStarLowerStarAdjunction Λ t).counit.app M)⟩

/-- On a topologically Noetherian scheme, the closed-then-open extension by zero `v_! t_* M`
along a factorization `a = t ≫ v` agrees with the open-then-closed extension
`coefficientHeartLocallyClosedExtension` through the scheme-theoretic closure of `a`.

Source: Stacks Project, Tags 03DI, 03DJ and 09BM
(blueprint: lem-sfb-topological-locally-closed-extension).

Proof. The module `N = v_! t_* M` restricts to zero away from the range of `a` and to `M`
along `a`. Hence the closed unit along the closure and the open counit along `a.toImage`
are isomorphisms, which identifies `N` with `i_* u_! a^* N ≅ i_* u_! M`. All opens involved
are quasi-compact since every subspace of a Noetherian space is Noetherian. -/
theorem nonempty_openImmersionLowerShriek_lowerStar_iso_coefficientHeartLocallyClosedExtension
    {S V X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    (a : S ⟶ X) [IsImmersion a]
    (t : S ⟶ V) [IsClosedImmersion t] (v : V ⟶ X) [IsOpenImmersion v]
    (htv : t ≫ v = a)
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    Nonempty ((openImmersionLowerShriek Λ v).obj ((lowerStar Λ t).obj M) ≅
      (coefficientHeartLocallyClosedExtension Λ a inferInstance).obj M) := by
  have : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  let N := (openImmersionLowerShriek Λ v).obj ((lowerStar Λ t).obj M)
  have hs {Y : Scheme.{u}} (g : Y ⟶ X) (hg : Disjoint (Set.range g) (Set.range a)) :
      IsZero ((upperStar Λ g).obj N) :=
    isZero_upperStar_openImmersionLowerShriek_lowerStar_of_disjoint Λ t v g
      (by rwa [htv]) M
  obtain ⟨e⟩ := nonempty_upperStar_openImmersionLowerShriek_lowerStar_iso Λ t v a htv M
  let U : X.Opens :=
    ⟨(Set.range a.imageι)ᶜ, a.imageι.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hU : Set.range U.ι = (Set.range a.imageι)ᶜ := U.range_ι
  have : TopologicalSpace.NoetherianSpace U.toScheme :=
    U.ι.isEmbedding.isInducing.noetherianSpace
  have houter : Disjoint (Set.range U.ι) (Set.range a) := by
    rw [hU, Set.disjoint_left]
    rintro x hx ⟨z, rfl⟩
    apply hx
    exact ⟨a.toImage z, (congrArg (fun f : S ⟶ X ↦ f z) a.toImage_imageι).symm⟩
  have houterAb := ((Mod.forget _).map_isZero (hs U.ι houter)).of_iso
    (upperStarObjXIso Λ U.ι N).symm
  have ho := moduleUnitOfAbelian Λ a.imageι N
    ((ProEtale.abelian_closed_support_counit_and_unit a.imageι U.ι hU).2 N.X houterAb)
  have hd : Disjoint (Set.range (a.toImage.closedComplement ≫ a.imageι))
      (Set.range a) := by
    rw [Set.disjoint_left]
    rintro x ⟨y, rfl⟩ ⟨z, hz⟩
    have he : a.toImage z = a.toImage.closedComplement y :=
      a.imageι.isEmbedding.injective
        ((congrArg (fun f : S ⟶ X ↦ f z) a.toImage_imageι).trans hz)
    have hy : a.toImage.closedComplement y ∈ (Set.range a.toImage)ᶜ := by
      rw [← a.toImage.range_closedComplement]
      exact ⟨y, rfl⟩
    exact hy ⟨z, he⟩
  have hz := (hs (a.toImage.closedComplement ≫ a.imageι) hd).of_iso
    ((upperStarComp Λ a.toImage.closedComplement a.imageι).app N).symm
  have hzAb := ((Mod.forget _).map_isZero hz).of_iso
    (upperStarObjXIso Λ a.toImage.closedComplement _).symm
  have hopenAb := ProEtale.abelian_open_supported_counit
    a.toImage.closedComplement a.toImage
    (by rw [a.toImage.range_closedComplement, compl_compl])
    ((upperStar Λ a.imageι).obj N).X hzAb
  have hi : IsIso ((openImmersionLowerShriekUpperStarAdjunction Λ a.toImage).counit.app
      ((upperStar Λ a.imageι).obj N)) := by
    apply (Adjunction.isIso_counit_app_iff_mem_essImage _).2
    apply mem_essImage_openImmersionLowerShriek_of_mem_essImage Λ a.toImage
    exact (Adjunction.isIso_counit_app_iff_mem_essImage _).1 hopenAb
  refine ⟨asIso ((upperStarLowerStarAdjunction Λ a.imageι).unit.app N) ≪≫
    (lowerStar Λ a.imageι).mapIso
      (asIso ((openImmersionLowerShriekUpperStarAdjunction Λ a.toImage).counit.app
        ((upperStar Λ a.imageι).obj N))).symm ≪≫ ?_⟩
  exact (lowerStar Λ a.imageι).mapIso ((openImmersionLowerShriek Λ a.toImage).mapIso
    (((upperStarComp Λ a.toImage a.imageι).symm ≪≫
      upperStarCongr Λ a.toImage_imageι).app N ≪≫ e))

end AlgebraicGeometry.ProEtale.CondensedRing
