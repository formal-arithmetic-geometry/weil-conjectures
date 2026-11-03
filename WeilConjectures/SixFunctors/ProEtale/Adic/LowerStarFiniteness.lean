/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelConstructible
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelDerived
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimitEssSurjGenerators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar

/-!
# Finiteness for the pushforward of constructible `ℓ`-adic sheaves, by comparison of models
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- An `ℓ`-adic complex on a scheme with noetherian underlying space whose module-object
counterpart over `ℚ̲̄_ℓ` (`AlgebraicGeometry.ProEtale.adicSheafDerivedEquivCondensedMod`) is
bounded constructible is bounded with constructible cohomology sheaves. -/
theorem bounded_homologyProperty_of_boundedConstructible {Y : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace Y] {K : DerivedCategory (AdicSheaf l Y)}
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj.{u} l) Y)
      ((adicSheafDerivedEquivCondensedMod l Y).functor.obj K)) :
    DerivedCategory.TStructure.t.bounded K ∧
      _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l Y) K := by
  let E := adicSheafEquivCondensedMod l Y
  have e (n : ℤ) := (homologyFunctorCompAdicSheafEquivCondensedModIso (l := l) (X := Y) n).app K
  have hz (n : ℤ) (h : IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((adicSheafDerivedEquivCondensedMod l Y).functor.obj K))) :
      IsZero ((DerivedCategory.homologyFunctor _ n).obj K) :=
    (E.inverse.map_isZero (h.of_iso (e n))).of_iso (E.unitIso.app _)
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hK
  refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun n ↦ ?_⟩
  · exact (DerivedCategory.isGE_iff K a).2 fun n hn ↦
      hz n ((DerivedCategory.isGE_iff _ a).1 ha n hn)
  · exact (DerivedCategory.isLE_iff K b).2 fun n hn ↦
      hz n ((DerivedCategory.isLE_iff _ b).1 hb n hn)
  · exact isAdicConstructibleSheaf_of_isConstructibleModuleObject
      (IsConstructibleModuleObject.of_iso (e n).symm (hc n))

section Finiteness

variable {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
  (s : Y ⟶ Spec (.of K)) (f : X ⟶ Y)

omit [IsAlgClosed K] in
/-- The positive characteristic case of
`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_isAffine`, by comparison with the
module objects over `ℚ̲̄_ℓ`. -/
theorem finiteLowerStar_singleFunctor_of_isAffine_of_charP [Fact (ringChar K).Prime]
    [Fact (ringChar K ≠ l)] [LocallyOfFiniteType s]
    [IsAffine Y] {T : Scheme.{u}} [IsAffine T] (g : T ⟶ Y) [LocallyOfFiniteType g]
    {F : AdicSheaf l T} (hF : IsAdicConstructibleSheaf F) :
    finiteLowerStar l g ((DerivedCategory.singleFunctor _ 0).obj F) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (g ≫ s)
  have : IsNoetherian Y := {}
  have : IsNoetherian T := {}
  let X' : Over (Spec (.of K)) := Over.mk (g ≫ s)
  let Y' : Over (Spec (.of K)) := Over.mk s
  let f' : X' ⟶ Y' := Over.homMk g
  have : LocallyOfFiniteType X'.hom := inferInstanceAs (LocallyOfFiniteType (g ≫ s))
  have : LocallyOfFiniteType Y'.hom := inferInstanceAs (LocallyOfFiniteType s)
  have : QuasiCompact X'.hom := inferInstanceAs (QuasiCompact (g ≫ s))
  have : QuasiCompact Y'.hom := inferInstanceAs (QuasiCompact s)
  have : IsSeparated X'.hom := inferInstanceAs (IsSeparated (g ≫ s))
  have : IsSeparated Y'.hom := inferInstanceAs (IsSeparated s)
  have hM : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj.{u} l) T)
      ((adicSheafDerivedEquivCondensedMod l T).functor.obj
        ((DerivedCategory.singleFunctor _ 0).obj F)) :=
    (boundedConstructible _).prop_of_iso
      ((singleFunctorCompAdicSheafDerivedEquivCondensedModIso (l := l) (X := T) 0).app F).symm
      (CondensedRing.boundedConstructible_singleFunctor_obj_of_isConstructibleModuleObject _ 0
        hF.isConstructibleModuleObject)
  have h := CondensedRing.boundedConstructible_rightDerivedLowerStar_obj l f' ⟨_, hM⟩
  exact bounded_homologyProperty_of_boundedConstructible
    ((boundedConstructible _).prop_of_iso
      ((adicRightDerivedLowerStarCompIso (l := l) (X := Y) g).app _).symm h)

/-- **Finiteness for the derived pushforward of a constructible `ℓ`-adic sheaf, affine case**
(SGA 4½, *Th. finitude*): over an algebraically closed field of characteristic `≠ ℓ`, the
derived pushforward `Rg_* F` of a constructible `ℓ`-adic sheaf along a morphism `g` locally of
finite type between affine schemes, with target of finite type, is bounded with constructible
cohomology sheaves `Rⁿg_* F`. This is the affine `ℚ̄_ℓ` case of clause (3) of blueprint
`det-thm-sf-ctf-stability-direct-images` (subsection `sk-thm-sf-ctf-stability`: `Rf_*`
preserves `Dᵇc(-, ℚ̄_ℓ)`); blueprint `sk-prop-sf-finiteness` is the finite-coefficient case. -/
theorem finiteLowerStar_singleFunctor_of_isAffine (hK : ringChar K ≠ l) [LocallyOfFiniteType s]
    [IsAffine Y] {T : Scheme.{u}} [IsAffine T] (g : T ⟶ Y) [LocallyOfFiniteType g]
    {F : AdicSheaf l T} (hF : IsAdicConstructibleSheaf F) :
    finiteLowerStar l g ((DerivedCategory.singleFunctor _ 0).obj F) :=
  by
  obtain hp | h0 := CharP.char_is_prime_or_zero K (ringChar K)
  · have : Fact (ringChar K).Prime := ⟨hp⟩
    have : Fact (ringChar K ≠ l) := ⟨hK⟩
    exact finiteLowerStar_singleFunctor_of_isAffine_of_charP s g hF
  · sorry


/-- **Finiteness over an affine target** (SGA 4½, *Th. finitude*): the case of a quasi-compact
quasi-separated source reduces to that of an affine source
(`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_isAffine`) by the Čech argument
of `AlgebraicGeometry.ProEtale.FiniteFor.of_quasiSeparatedSpace`. -/
theorem finiteFor_of_isAffine (hK : ringChar K ≠ l) [LocallyOfFiniteType s] [IsAffine Y]
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f] : FiniteFor l f := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  exact FiniteFor.of_quasiSeparatedSpace (l := l) f fun T' _ g' _ K hb hc ↦
    finiteLowerStar_of_bounded g' (fun F hF ↦ finiteLowerStar_singleFunctor_of_isAffine s hK g' hF)
      K hb hc

/-- **Finiteness for the higher direct images of a constructible `ℓ`-adic sheaf** (SGA 4½,
*Th. finitude*): over an algebraically closed field of characteristic `≠ ℓ`, the higher direct
images `Rⁿf_* F` of a constructible `ℓ`-adic sheaf along a quasi-compact quasi-separated
morphism locally of finite type, with target locally of finite type, are constructible.
Constructibility being local on `Y` and the higher direct images commuting with restriction
to an open subscheme (`AlgebraicGeometry.ProEtale.adicDerivedBaseChangeIso`), this is the case
of an affine target, `AlgebraicGeometry.ProEtale.finiteFor_of_isAffine`. -/
theorem isAdicConstructibleSheaf_homology_rightDerivedFunctor_lowerStar (hK : ringChar K ≠ l)
    [LocallyOfFiniteType s] [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    {F : AdicSheaf l X} (hF : IsAdicConstructibleSheaf F) (n : ℤ) :
    IsAdicConstructibleSheaf ((DerivedCategory.homologyFunctor _ n).obj
      ((f)_*ᵃ[l].rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  refine IsAdicConstructibleSheaf.of_openCover fun y ↦ ?_
  obtain ⟨R, j, hj, v, rfl⟩ := Scheme.exists_Spec_apply_eq y
  have h := finiteFor_of_isAffine (j ≫ s) (pullback.snd f j) hK _
    (bounded_homologyProperty_singleFunctor (hF.upperStar (pullback.fst f j))).1
    (bounded_homologyProperty_singleFunctor (hF.upperStar (pullback.fst f j))).2
  refine ⟨_, j, hj, ⟨v, rfl⟩, (h.2 n).of_iso ?_⟩
  exact (DerivedCategory.homologyFunctor _ n).mapIso
      (mapDerivedCategoryUpperStarRightDerivedFunctorLowerStarIso f j F).symm ≪≫
    (((j)^*ᵃ[l].mapDerivedCategoryHomologyFunctorIso n).app _).symm

/-- **Finiteness for the pushforward of a constructible `ℓ`-adic sheaf** (SGA 4½,
*Th. finitude*): over an algebraically closed field of characteristic `≠ ℓ`, the pushforward
of a constructible `ℓ`-adic sheaf along a quasi-compact quasi-separated morphism locally of
finite type, with target locally of finite type, is constructible: it is the degree `0` case
of `AlgebraicGeometry.ProEtale.isAdicConstructibleSheaf_homology_rightDerivedFunctor_lowerStar`,
`f_*` being left exact. -/
theorem IsAdicConstructibleSheaf.lowerStar (hK : ringChar K ≠ l) [LocallyOfFiniteType s]
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    {F : AdicSheaf l X}
    (hF : IsAdicConstructibleSheaf F) :
    IsAdicConstructibleSheaf ((f)_*ᵃ[l].obj F) :=
  (isAdicConstructibleSheaf_homology_rightDerivedFunctor_lowerStar s f hK hF 0).of_iso
    ((f)_*ᵃ[l].homologyRightDerivedFunctorObjSingleFunctorIso F 0 ≪≫
      (f)_*ᵃ[l].rightDerivedZeroIsoSelf.app F)

/-- **Cohomological dimension of the pushforward of a constructible `ℓ`-adic sheaf**
(SGA 4½, *Th. finitude*; SGA 4, Exp. X): over an algebraically closed field of characteristic
`≠ ℓ`, the higher direct images `Rⁿf_* F` of a constructible `ℓ`-adic sheaf along a
quasi-compact quasi-separated morphism locally of finite type, with target quasi-compact and
locally of finite type, vanish in large degrees. Over each member of a finite affine cover of
`Y` this is `AlgebraicGeometry.ProEtale.finiteFor_of_isAffine`, and restrictions to an open
cover detect vanishing. -/
theorem exists_isLE_rightDerivedFunctor_lowerStar (hK : ringChar K ≠ l) [LocallyOfFiniteType s]
    [QuasiCompact s] [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    {F : AdicSheaf l X}
    (hF : IsAdicConstructibleSheaf F) :
    ∃ b : ℤ, ((f)_*ᵃ[l].rightDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE b := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  obtain ⟨S, hSa, hS⟩ := Scheme.exists_finset_isAffineOpen_sup_eq_top Y
  have hb (O : S) : ∃ b : ℤ, ((O.1.ι)^*ᵃ[l].mapDerivedCategory.obj
      ((f)_*ᵃ[l].rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj F))).IsLE b := by
    have : IsAffine O.1.toScheme := hSa O.1 O.2
    have h := finiteFor_of_isAffine (O.1.ι ≫ s) (pullback.snd f O.1.ι) hK _
      (bounded_homologyProperty_singleFunctor (hF.upperStar (pullback.fst f O.1.ι))).1
      (bounded_homologyProperty_singleFunctor (hF.upperStar (pullback.fst f O.1.ι))).2
    obtain ⟨b, hb⟩ := h.1.2
    exact ⟨b, DerivedCategory.TStructure.t.isLE_of_iso
      (mapDerivedCategoryUpperStarRightDerivedFunctorLowerStarIso f O.1.ι F).symm b⟩
  choose b hb using hb
  refine ⟨∑ O, |b O|, ?_⟩
  rw [DerivedCategory.isLE_iff]
  intro n hn
  refine isZero_of_isZero_adicUpperStar l (W := fun O : S ↦ O.1.toScheme) (fun O ↦ O.1.ι)
    (Scheme.zariskiPrecoverage_le_proetalePrecoverage _
      ((Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨fun y ↦ ?_, fun _ ↦ inferInstance⟩))
    fun O ↦ ?_
  · have hy : y ∈ S.sup id := hS ▸ trivial
    rw [Finset.sup_eq_iSup] at hy
    obtain ⟨O, hO⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨hOS, hy⟩ := TopologicalSpace.Opens.mem_iSup.1 hO
    exact ⟨⟨O, hOS⟩, by rw [Scheme.Opens.range_ι]; exact hy⟩
  · have hO : b O < n := lt_of_le_of_lt ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun O ↦ |b O|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_univ O))) hn
    exact (((DerivedCategory.isLE_iff _ (b O)).1 (hb O) n hO)).of_iso
      (((O.1.ι)^*ᵃ[l].mapDerivedCategoryHomologyFunctorIso n).app _)

/-- **Boundedness of the derived pushforward of a constructible `ℓ`-adic sheaf** (SGA 4½,
*Th. finitude*): over an algebraically closed field of characteristic `≠ ℓ`, the derived
pushforward of a constructible `ℓ`-adic sheaf along a quasi-compact quasi-separated morphism
locally of finite type, with target quasi-compact and locally of finite type, is bounded. -/
theorem bounded_rightDerivedFunctor_lowerStar (hK : ringChar K ≠ l) [LocallyOfFiniteType s]
    [QuasiCompact s] [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    {F : AdicSheaf l X}
    (hF : IsAdicConstructibleSheaf F) :
    DerivedCategory.TStructure.t.bounded
      ((f)_*ᵃ[l].rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj F)) :=
  ⟨⟨0, (f)_*ᵃ[l].isGE_rightDerivedFunctor_obj_singleFunctor F⟩,
    exists_isLE_rightDerivedFunctor_lowerStar s f hK hF⟩

/-- **Finiteness for the derived pushforward of a constructible `ℓ`-adic sheaf** (SGA 4½,
*Th. finitude*): over a quasi-compact target, `Rf_* F` is bounded with constructible cohomology
sheaves. -/
theorem finiteLowerStar_singleFunctor (hK : ringChar K ≠ l) [LocallyOfFiniteType s]
    [QuasiCompact s] [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    {F : AdicSheaf l X} (hF : IsAdicConstructibleSheaf F) :
    finiteLowerStar l f ((DerivedCategory.singleFunctor _ 0).obj F) :=
  ⟨bounded_rightDerivedFunctor_lowerStar s f hK hF,
    isAdicConstructibleSheaf_homology_rightDerivedFunctor_lowerStar s f hK hF⟩

end Finiteness

end AlgebraicGeometry.ProEtale
