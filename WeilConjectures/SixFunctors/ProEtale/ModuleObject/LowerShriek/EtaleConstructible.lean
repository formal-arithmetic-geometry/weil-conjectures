/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleImageNowhereDense
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleOpenCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstructibleOfStratification
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFinitelyPresentedDenseOpen
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.WeaklyEtaleBaseChange

/-!
# Extension by zero along an étale morphism preserves constructibility

Let `f : X ⟶ Y` be an étale morphism of Noetherian schemes and `Λ` a commutative condensed ring.
The extension by zero `f_!` of module objects over `Λ` maps constructible module objects to
constructible module objects
(`ProEtale.CondensedRing.isConstructibleModuleObject_weaklyEtaleLowerShriek_of_etale`).

* If `f` is finite étale and `M` is pro-étale locally finitely presented (lisse), so is `f_! M`
  (`ProEtale.CondensedRing.isLocallyFinitelyPresented_weaklyEtaleLowerShriek_of_isFinite`):
  étale locally on `Y`, `f` splits into a disjoint union of copies of the base, over which `f_! M`
  is a finite direct sum of restrictions of `M`.
* If `f` is finite étale and `M` constructible, `f_! M` is constructible, by Noetherian induction
  on `Y`: `M` is lisse on a dense open `U ⊆ X`, so `f_! M` is lisse over the dense open complement
  of `f(X ∖ U)`, and the closed complement is treated by induction and base change.
* In general, `Y` has a stratification over whose strata `f` is finite étale (Stacks, Tag 03S0),
  and constructibility can be checked on the strata.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- If the base change of `f` along `g` is a disjoint union of copies of `U`, through sections `s`,
then the restriction along `g` of `f_! M` is a finite direct sum of restrictions of `M`, hence lisse
as soon as `M` is. -/
theorem isLocallyFinitelyPresented_upperStar_weaklyEtaleLowerShriek_of_isColimit
    {X Y U : Scheme.{u}} (f : X ⟶ Y) [WeaklyEtale f] (g : U ⟶ Y) {J : Type u} [Finite J]
    (s : J → (U ⟶ pullback f g))
    (hs : ∀ j, s j ≫ pullback.snd f g = 𝟙 U) (hP : IsColimit (Cofan.mk (pullback f g) s))
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsLocallyFinitelyPresented (condensedRingObj Λ X) M) :
    IsLocallyFinitelyPresented (condensedRingObj Λ U)
      ((g)^*⟦Λ⟧.obj ((weaklyEtaleLowerShriek Λ f).obj M)) := by
  have hlisse (j : J) : IsLocallyFinitelyPresented (condensedRingObj Λ U)
      ((s j)^*⟦Λ⟧.obj ((pullback.fst f g)^*⟦Λ⟧.obj M)) :=
    IsLocallyFinitelyPresented.upperStar Λ _ (IsLocallyFinitelyPresented.upperStar Λ _ hM)
  exact (isLocallyFinitelyPresented_biproduct _ hlisse).of_iso
    ((weaklyEtaleLowerShriekObjIsoBiproduct Λ hs hP _).symm ≪≫
      (weaklyEtaleLowerShriekBaseChangeIso Λ (IsPullback.of_hasPullback f g)).app M)

/-- **Extension by zero along a finite étale morphism preserves lisse module objects.** -/
theorem isLocallyFinitelyPresented_weaklyEtaleLowerShriek_of_isFinite {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [Etale f]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsLocallyFinitelyPresented (condensedRingObj Λ X) M) :
    IsLocallyFinitelyPresented (condensedRingObj Λ Y) ((weaklyEtaleLowerShriek Λ f).obj M) := by
  choose U g u hg hu J V ι hJ hc hι he using fun y ↦ finite_etale_etale_local_split f y
  let 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage Y :=
    { I₀ := Y
      X := U
      f := g
      mem₀ := Scheme.etalePrecoverage_le_proetalePrecoverage _
        ((Scheme.ofArrows_mem_precoverage_iff _).mpr
          ⟨fun y ↦ ⟨y, u y, hu y⟩, fun y ↦ hg y⟩) }
  refine isLocallyFinitelyPresented_of_cover 𝒰 fun y ↦ ?_
  have : Finite (J y) := hJ y
  choose e he using he y
  -- The sections are typed through `𝒰`, so that the conclusion matches the goal syntactically.
  let s (j : J y) : 𝒰.X y ⟶ pullback f (𝒰.f y) := (e j).inv ≫ ι y j
  have hs (j : J y) : s j ≫ pullback.snd f (𝒰.f y) = 𝟙 (𝒰.X y) := by
    change ((e j).inv ≫ ι y j) ≫ pullback.snd f (g y) = 𝟙 (U y)
    rw [Category.assoc, ← he j, Iso.inv_hom_id]
  have hP : IsColimit (Cofan.mk (pullback f (𝒰.f y)) s) := by
    let α : Discrete.functor (V y) ≅ Discrete.functor (fun _ : J y ↦ U y) :=
      Discrete.natIso fun j ↦ e j.as
    refine (IsColimit.precomposeHomEquiv α _) (IsColimit.ofIsoColimit (hc y).some
      (Cocone.ext (Iso.refl _) ?_))
    rintro ⟨j⟩
    simp [α, s]
  exact isLocallyFinitelyPresented_upperStar_weaklyEtaleLowerShriek_of_isColimit Λ f (𝒰.f y) s
    hs hP hM

/-- The Noetherian induction behind
`isConstructibleModuleObject_weaklyEtaleLowerShriek_of_isFinite`, over the closed subschemes of a
fixed Noetherian scheme `Y₀`, indexed by their supports. -/
private theorem isConstructibleModuleObject_weaklyEtaleLowerShriek_of_isFinite_aux
    (Y₀ : Scheme.{u}) [IsNoetherian Y₀] (C : TopologicalSpace.Closeds Y₀) :
    ∀ {Y : Scheme.{u}} (ι : Y ⟶ Y₀) [IsClosedImmersion ι], Set.range ι.base = C →
      ∀ {X : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
        (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
        IsConstructibleModuleObject (condensedRingObj Λ X) M →
          IsConstructibleModuleObject (condensedRingObj Λ Y)
            ((weaklyEtaleLowerShriek Λ f).obj M) := by
  induction C using WellFoundedLT.induction with
  | ind C ih =>
  intro Y ι _ hι X f _ _ M hM
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType ι
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  rcases isEmpty_or_nonempty Y with hY | hY
  · exact ProEtale.isConstructibleModuleObject_of_isZero _ (isZero_mod_of_isEmpty Λ _)
  -- `M` is lisse on a dense open `U`, hence `f_! M` is lisse over the dense open complement `V`
  -- of `f(X ∖ U)`
  obtain ⟨U, hUd, hU⟩ := IsConstructibleModuleObject.exists_dense_isLocallyFinitelyPresented hM
  have hB' : interior ((U : Set X)ᶜ) = ∅ := by
    rw [interior_compl, hUd.closure_eq, Set.compl_univ]
  obtain ⟨hVo, hVd⟩ := dense_compl_image_of_isFinite f U.isOpen.isClosed_compl hB'
  let V : Y.Opens := ⟨_, hVo⟩
  have hfV : f ⁻¹ᵁ V ≤ U := fun x hx ↦ by
    by_contra h
    exact (Set.eq_empty_iff_forall_notMem.1 (preimage_compl_image_inter_eq_empty f)) x ⟨hx, h⟩
  have hVc : IsConstructibleModuleObject (condensedRingObj Λ V)
      ((V.ι)^*⟦Λ⟧.obj ((weaklyEtaleLowerShriek Λ f).obj M)) :=
    isConstructibleModuleObject_of_isLocallyFinitelyPresented
      ((isLocallyFinitelyPresented_weaklyEtaleLowerShriek_of_isFinite Λ (f ∣_ V)
        (isLocallyFinitelyPresented_upperStar_ι_of_le hfV hU)).of_iso
        ((weaklyEtaleLowerShriekBaseChangeIso Λ (isPullback_morphismRestrict f V).flip).app M))
  -- the closed complement of `V` is treated by induction
  let i := V.closedComplement
  let C' : TopologicalSpace.Closeds Y₀ :=
    ⟨Set.range (i ≫ ι).base, (i ≫ ι).isClosedEmbedding.isClosed_range⟩
  have hC' : C' < C := by
    refine lt_of_le_of_ne ?_ fun h ↦ ?_
    · rintro _ ⟨z, rfl⟩
      change _ ∈ (C : Set Y₀)
      rw [← hι]
      exact ⟨i.base z, by simp⟩
    obtain ⟨y, hy⟩ := hVd.nonempty
    have hyC : ι.base y ∈ (C' : Set Y₀) := by
      rw [h, ← hι]
      exact Set.mem_range_self y
    obtain ⟨z, hz⟩ := hyC
    have hzy : i.base z = y := ι.isClosedEmbedding.injective (by simpa using hz)
    have : y ∈ Set.range i.base := ⟨z, hzy⟩
    rw [V.range_closedComplement] at this
    exact this hy
  have hZ := ih C' hC' (i ≫ ι) rfl (pullback.snd f i) _
    (IsConstructibleModuleObject.upperStar Λ (pullback.fst f i) hM)
  exact isConstructibleModuleObject_of_openClosed Λ V.ι i
    (by rw [V.range_closedComplement, Scheme.Opens.range_ι]) _ hVc
    (hZ.of_iso ((weaklyEtaleLowerShriekBaseChangeIso Λ (IsPullback.of_hasPullback f i)).app M))

/-- **Extension by zero along a finite étale morphism preserves constructibility**, over a
Noetherian base. -/
theorem isConstructibleModuleObject_weaklyEtaleLowerShriek_of_isFinite {X Y : Scheme.{u}}
    [IsNoetherian Y] (f : X ⟶ Y) [IsFinite f] [Etale f]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsConstructibleModuleObject (condensedRingObj Λ X) M) :
    IsConstructibleModuleObject (condensedRingObj Λ Y) ((weaklyEtaleLowerShriek Λ f).obj M) :=
  isConstructibleModuleObject_weaklyEtaleLowerShriek_of_isFinite_aux Λ Y ⊤ (𝟙 Y)
    (by simp) f M hM

/-- **Extension by zero along an étale morphism preserves constructibility**: for an étale
morphism `f : X ⟶ Y` of Noetherian schemes, `f_!` maps constructible module objects over `Λ` to
constructible module objects. Over the strata of a stratification of `Y`, `f` is finite étale
(Stacks, Tag 03S0). -/
theorem isConstructibleModuleObject_weaklyEtaleLowerShriek_of_etale {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [Etale f]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsConstructibleModuleObject (condensedRingObj Λ X) M) :
    IsConstructibleModuleObject (condensedRingObj Λ Y) ((weaklyEtaleLowerShriek Λ f).obj M) := by
  obtain ⟨S, -, hS⟩ := Scheme.exists_etale_stratified_finite f
  refine isConstructibleModuleObject_of_stratification Λ S _ fun i ↦ ?_
  have := (hS i).1
  have := (hS i).2
  have : CompactSpace (S.domain i) := by
    rw [← isCompact_univ_iff, (S.immersion i).isEmbedding.isCompact_iff, Set.image_univ]
    exact TopologicalSpace.NoetherianSpace.isCompact _
  have : IsLocallyNoetherian (S.domain i) := LocallyOfFiniteType.isLocallyNoetherian (S.immersion i)
  have : IsNoetherian (S.domain i) := ⟨⟩
  exact (isConstructibleModuleObject_weaklyEtaleLowerShriek_of_isFinite Λ
    (pullback.snd f (S.immersion i))
    (IsConstructibleModuleObject.upperStar Λ (pullback.fst f (S.immersion i)) hM)).of_iso
      ((weaklyEtaleLowerShriekBaseChangeIso Λ (IsPullback.of_hasPullback f (S.immersion i))).app M)

end AlgebraicGeometry.ProEtale.CondensedRing
