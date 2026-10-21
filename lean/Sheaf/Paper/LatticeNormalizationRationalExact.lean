/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U9
-/
module

public import Sheaf.Paper.EtaleMonodromyRealizationData
import Sheaf.Paper.MonodromyLimitRationalExact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.AlgebraicGeometry.FiniteLocalAbelianForget
import WeilConjectures.ConstructibleSheaf.Simple
import WeilConjectures.ConstructibleSheaf.StalkZeroLocus
import WeilConjectures.ConstructibleSheaf.OfForget
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars

/-! # Exact rationalizations of a compatible normalized lattice sequence

Source: Bhatt--Scholze, proof of Corollary 6.8.5, pp. 59--60.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem bigZ_forget_full :
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}).Full := by
  change (ModuleCat.restrictScalars (ULift.ringEquiv.symm.toRingHom :
    ℤ →+* ULift.{u + 1} ℤ) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).Full
  infer_instance

private theorem bigZ_locally_constant {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    (hF : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf _ F)) :
    IsLocallyConstantSheaf F := by
  let K := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}
  have : K.Full := bigZ_forget_full
  have : K.EssSurj := ⟨fun A ↦ by
    let M : ModuleCat.{u + 1} (ULift.{u + 1} ℤ) :=
      letI : Module (ULift.{u + 1} ℤ) A := Module.compHom A ULift.ringEquiv.toRingHom
      ModuleCat.of _ A
    exact ⟨M, ⟨Iso.refl A⟩⟩⟩
  have : K.IsEquivalence := {}
  let G := (sheafCompose T.smallEtaleTopology K).obj F
  have hG : IsLocallyConstantSheaf G :=
    ((finite_local_abelian_forget_iff G).mp hF).1
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := hG.nonempty_locallyConstantDatum
  refine ⟨⟨⟨𝒰, fun i ↦ ?_⟩⟩⟩
  let U := 𝒰.etalePrecoverageToEtale i
  have hU : ((sheafCompose (T.smallEtaleTopology.over U) K).obj (F.over U)).IsConstant
      (T.smallEtaleTopology.over U) := h𝒰 i
  obtain ⟨A, ⟨e⟩⟩ := Sheaf.mem_essImage_of_isConstant _
    ((sheafCompose (T.smallEtaleTopology.over U) K).obj (F.over U))
  let M : ModuleCat.{u + 1} (ULift.{u + 1} ℤ) :=
    letI : Module (ULift.{u + 1} ℤ) A := Module.compHom A ULift.ringEquiv.toRingHom
    ModuleCat.of _ A
  let d : (constantSheaf (T.smallEtaleTopology.over U) (ModuleCat.{u + 1}
      (ULift.{u + 1} ℤ))).obj M ≅ F.over U :=
    (Functor.FullyFaithful.ofFullyFaithful
      (sheafCompose (T.smallEtaleTopology.over U) K)).preimageIso
      ((constantCommuteCompose (T.smallEtaleTopology.over U) K).app M ≪≫ e)
  exact Sheaf.isConstant_of_iso _ d.symm

private theorem bigZ_finite_locally_constant {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    (hF : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf _ F)) :
    IsFiniteLocallyConstantSheaf F :=
  { toIsLocallyConstantSheaf := bigZ_locally_constant F hF
    toIsFiniteSheaf := IsFiniteSheaf.of_forget F hF.2 }

private theorem zero_of_zero_fiber {T : Scheme.{u}} [ConnectedSpace T]
    {R : Type (u + 1)} [Ring R]
    (p : SfMonodromyPoint T)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))
    [IsLocallyConstantSheaf F]
    (h : IsZero (((pointSmallEtale p.point).sheafFiber
      (A := ModuleCat.{u + 1} R)).obj F)) : IsZero F := by
  have hp := Etale.mem_stalkZeroLocus_of_isLocallyConstantSheaf F p.point h
  have hcl := Etale.isClopen_stalkZeroLocus F
  have hall : Etale.stalkZeroLocus F = Set.univ := by
    rcases isClopen_iff.mp hcl with he | he
    · exact False.elim (by simp [he] at hp)
    · exact he
  exact (Etale.isZero_iff_stalkZeroLocus_eq_univ F).mpr hall

private theorem exact_of_exact_fiber {T : Scheme.{u}} [ConnectedSpace T]
    {R : Type (u + 1)} [Ring R] [IsNoetherianRing R]
    (p : SfMonodromyPoint T)
    (S : ShortComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)))
    [IsFiniteLocallyConstantSheaf S.X₁] [IsFiniteLocallyConstantSheaf S.X₂]
    [IsFiniteLocallyConstantSheaf S.X₃]
    (h : (S.map ((pointSmallEtale p.point).sheafFiber
      (A := ModuleCat.{u + 1} R))).Exact) : S.Exact := by
  have := IsFiniteLocallyConstantSheaf.homology S
  rw [ShortComplex.exact_iff_isZero_homology]
  apply zero_of_zero_fiber p
  exact ((ShortComplex.exact_iff_isZero_homology _).mp h).of_iso
    (S.mapHomologyIso ((pointSmallEtale p.point).sheafFiber)).symm

private theorem exact_of_exact_finite_fiber {T : Scheme.{u}}
    (p : SfMonodromyPoint T) {R : Type (u + 1)} [CommRing R]
    (S : ShortComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)))
    (h₁ : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R S.X₁))
    (h₂ : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R S.X₂))
    (h₃ : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R S.X₃))
    (h : (S.map ((pointSmallEtale p.point).sheafFiber
      (A := ModuleCat.{u + 1} R))).Exact) : S.Exact := by
  have : ConnectedSpace T := p.connected
  let r : ULift.{u + 1} ℤ →+* R := (Int.castRingHom R).comp ULift.ringEquiv.toRingHom
  have : (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} r).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} r).isLeftAdjoint
  have : (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} r).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} r).isRightAdjoint
  have : PreservesLimitsOfSize.{u + 1, u + 1}
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} r) :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} r).rightAdjoint_preservesLimits
  have : PreservesLimitsOfSize.{u, u + 1}
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} r) :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} r).rightAdjoint_preservesLimits
  let D := sheafCompose T.smallEtaleTopology
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} r)
  have : IsFiniteLocallyConstantSheaf (S.map D).X₁ := bigZ_finite_locally_constant _ h₁
  have : IsFiniteLocallyConstantSheaf (S.map D).X₂ := bigZ_finite_locally_constant _ h₂
  have : IsFiniteLocallyConstantSheaf (S.map D).X₃ := bigZ_finite_locally_constant _ h₃
  apply (S.exact_map_iff_of_faithful D).mp
  have : IsNoetherianRing (ULift.{u + 1} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  apply exact_of_exact_fiber p
  have : PreservesFilteredColimitsOfSize.{u, u}
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} r) := inferInstance
  exact (ShortComplex.exact_iff_of_iso (S.mapNatIso
    ((pointSmallEtale p.point).sheafFiberCompIso
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} r)))).mpr
        (h.map (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} r))

private theorem short_exact_of_finite_fiber {T : Scheme.{u}}
    (p : SfMonodromyPoint T) {R : Type (u + 1)} [CommRing R]
    (S : ShortComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)))
    (h₁ : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R S.X₁))
    (h₂ : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R S.X₂))
    (h₃ : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R S.X₃))
    (h : (S.map ((pointSmallEtale p.point).sheafFiber
      (A := ModuleCat.{u + 1} R))).ShortExact) : S.ShortExact := by
  let D := (pointSmallEtale p.point).sheafFiber (A := ModuleCat.{u + 1} R)
  refine { exact := exact_of_exact_finite_fiber p S h₁ h₂ h₃ h.exact
           mono_f := ?_
           epi_g := ?_ }
  · let L := ShortComplex.mk (0 : S.X₁ ⟶ S.X₁) S.f zero_comp
    apply (L.exact_iff_mono rfl).mp
    apply exact_of_exact_finite_fiber p L h₁ h₁ h₂
    exact ((L.map D).exact_iff_mono (by simp [L])).mpr h.mono_f
  · let L := ShortComplex.mk S.g (0 : S.X₃ ⟶ S.X₃) comp_zero
    apply (L.exact_iff_epi rfl).mp
    apply exact_of_exact_finite_fiber p L h₂ h₃ h₃
    exact ((L.map D).exact_iff_epi (by simp [L])).mpr h.epi_g

private theorem finite_fiber_faithful {T : Scheme.{u}} (p : SfMonodromyPoint T)
    (c : GaloisLisseFiniteCorrespondence p.point p.group) :
    (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := T)) ⋙
      (pointSmallEtale p.point).sheafFiber (A := Type (u + 1))).Faithful := by
  let K := ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := T)) ⋙
    (pointSmallEtale p.point).sheafFiber (A := Type (u + 1))
  have : ConnectedSpace T := p.connected
  have : (c.Φ.functor ⋙ K).Faithful := Functor.Faithful.of_iso c.η.symm
  let e : c.Φ.inverse ⋙ (c.Φ.functor ⋙ K) ≅ K :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight c.Φ.counitIso K ≪≫ Functor.leftUnitor K
  exact Functor.Faithful.of_iso e

private theorem eq_of_finite_fiber {T : Scheme.{u}}
    (p : SfMonodromyPoint T) (c : GaloisLisseFiniteCorrespondence p.point p.group)
    {R : Type (u + 1)} [CommRing R]
    {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (hF : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R F))
    (hG : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R G))
    (f g : F ⟶ G)
    (h : ((pointSmallEtale p.point).sheafFiber.map f) =
      ((pointSmallEtale p.point).sheafFiber.map g)) : f = g := by
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1} _
  let A : T.FLC := ⟨galoisUnderlyingSetSheaf R F, hF⟩
  let B : T.FLC := ⟨galoisUnderlyingSetSheaf R G, hG⟩
  let D := sheafCompose T.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} R))
  let a : A ⟶ B := ObjectProperty.homMk (D.map f)
  let b : A ⟶ B := ObjectProperty.homMk (D.map g)
  have : (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := T)) ⋙
      (pointSmallEtale p.point).sheafFiber (A := Type (u + 1))).Faithful :=
    finite_fiber_faithful p c
  suffices a = b from D.map_injective (congrArg (fun k : A ⟶ B ↦ k.hom) this)
  apply (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := T)) ⋙
    (pointSmallEtale p.point).sheafFiber (A := Type (u + 1))).map_injective
  change ((pointSmallEtale p.point).sheafFiber.map (D.map f)) =
    ((pointSmallEtale p.point).sheafFiber.map (D.map g))
  let e := (pointSmallEtale p.point).sheafFiberCompIso (CategoryTheory.forget
    (ModuleCat.{u + 1} R))
  apply (cancel_mono (e.hom.app G)).mp
  calc
    _ = e.hom.app F ≫ (CategoryTheory.forget _).map
        ((pointSmallEtale p.point).sheafFiber.map f) := e.hom.naturality f
    _ = e.hom.app F ≫ (CategoryTheory.forget _).map
        ((pointSmallEtale p.point).sheafFiber.map g) := by rw [h]
    _ = _ := (e.hom.naturality g).symm

private theorem fiber_map_eq (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {T : Scheme.{u}} {p : SfMonodromyPoint T}
    {c : GaloisLisseFiniteCorrespondence p.point p.group}
    {J : SfContinuousRepresentations l E p ⥤ SfRationalModules l E T}
    {V W : SfContinuousRepresentations l E p} {f : V ⟶ W}
    {B : SfInvariantLattice l E V} {C : SfInvariantLattice l E W}
    {h : ∀ b : B.submodule, f.hom.hom b.val ∈ C.submodule}
    {N : SfLatticeNormalization l E p c J V B}
    {M : SfLatticeNormalization l E p c J W C}
    (F : SfNormalizationMap l E f B C h N M) (n : ℕ)
    (q : sfLatticeQuotient l E B n →ₗ[Padic.coefficientExtensionIntegers l E]
      sfLatticeQuotient l E C n)
    (hq : ∀ b : B.submodule, q (sfLatticeQuotientMk l E B n b) =
      sfLatticeQuotientMk l E C n ⟨f.hom.hom b.val, h b⟩) :
    ((pointSmallEtale p.point).sheafFiber
      (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).map
        (F.levels.app (op n)) ≫ (M.fiber n).hom =
      (N.fiber n).hom ≫ ModuleCat.ofHom q := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ ((N.fiber n).hom x)
  have hx : x = (N.fiber n).inv (sfLatticeQuotientMk l E B n b) := by
    change x = (N.fiber n).inv (Submodule.Quotient.mk b)
    rw [hb]
    exact (ConcreteCategory.congr_hom (N.fiber n).hom_inv_id x).symm
  subst x
  change (M.fiber n).hom
    (((pointSmallEtale p.point).sheafFiber.map (F.levels.app (op n)))
      ((N.fiber n).inv (sfLatticeQuotientMk l E B n b))) =
    q ((N.fiber n).hom ((N.fiber n).inv _))
  rw [Iso.inv_hom_id_apply]
  exact (F.fiber n b).trans (hq b).symm

private theorem finite_normalization_exact (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {T : Scheme.{u}} (p : SfMonodromyPoint T)
    (c : GaloisLisseFiniteCorrespondence p.point p.group)
    (J : SfContinuousRepresentations l E p ⥤ SfRationalModules l E T)
    {V W Z : SfContinuousRepresentations l E p} (f : V ⟶ W) (g : W ⟶ Z)
    (C : SfInvariantLattice l E V) (B : SfInvariantLattice l E W)
    (D : SfInvariantLattice l E Z)
    (hCB : ∀ a : C.submodule, f.hom.hom a.val ∈ B.submodule)
    (hBD : ∀ b : B.submodule, g.hom.hom b.val ∈ D.submodule)
    (N : SfLatticeNormalization l E p c J V C)
    (M : SfLatticeNormalization l E p c J W B)
    (P : SfLatticeNormalization l E p c J Z D)
    (F : SfNormalizationMap l E f C B hCB N M)
    (G : SfNormalizationMap l E g B D hBD M P)
    (qf : ∀ n : ℕ, sfLatticeQuotient l E C n →ₗ[Padic.coefficientExtensionIntegers l E]
      sfLatticeQuotient l E B n)
    (qg : ∀ n : ℕ, sfLatticeQuotient l E B n →ₗ[Padic.coefficientExtensionIntegers l E]
      sfLatticeQuotient l E D n)
    (hqf : ∀ (n : ℕ) (a : C.submodule), qf n (sfLatticeQuotientMk l E C n a) =
      sfLatticeQuotientMk l E B n ⟨f.hom.hom a.val, hCB a⟩)
    (hqg : ∀ (n : ℕ) (b : B.submodule), qg n (sfLatticeQuotientMk l E B n b) =
      sfLatticeQuotientMk l E D n ⟨g.hom.hom b.val, hBD b⟩)
    (hq : ∀ n : ℕ, Function.Injective (qf n) ∧ Function.Exact (qf n) (qg n) ∧
      Function.Surjective (qg n)) :
    (∀ n : ℕ, ∃ w : F.levels.app (op n) ≫ G.levels.app (op n) = 0,
      (ShortComplex.mk (F.levels.app (op n)) (G.levels.app (op n)) w).ShortExact) ∧
      ∀ n : ℕ, Epi (N.etale.map (homOfLE (Nat.le_succ n)).op) := by
  let H := (pointSmallEtale p.point).sheafFiber
    (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
  have hz : ∀ n, F.levels.app (op n) ≫ G.levels.app (op n) = 0 := by
    intro n
    have hqz : ModuleCat.ofHom (qf n) ≫ ModuleCat.ofHom (qg n) = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (hq n).2.1.apply_apply_eq_zero x
    apply eq_of_finite_fiber p c (N.flc n) (P.flc n)
    change H.map (F.levels.app (op n) ≫ G.levels.app (op n)) = H.map 0
    rw [Functor.map_comp, Functor.map_zero]
    apply (cancel_mono (P.fiber n).hom).mp
    rw [Category.assoc, fiber_map_eq l E G n (qg n) (hqg n),
      ← Category.assoc, fiber_map_eq l E F n (qf n) (hqf n),
      Category.assoc, hqz, comp_zero, zero_comp]
  refine ⟨fun n ↦ ⟨hz n, ?_⟩, fun n ↦ ?_⟩
  · let S := ShortComplex.mk (F.levels.app (op n)) (G.levels.app (op n)) (hz n)
    apply short_exact_of_finite_fiber p S (N.flc n) (M.flc n) (P.flc n)
    let Q := ShortComplex.mk (ModuleCat.ofHom (qf n)) (ModuleCat.ofHom (qg n)) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (hq n).2.1.apply_apply_eq_zero x)
    have hQ : Q.ShortExact :=
      ModuleCat.shortComplex_shortExact Q (hq n).2.1 (hq n).1 (hq n).2.2
    let e : (S.map H) ≅ Q := ShortComplex.isoMk
      (N.fiber n) (M.fiber n) (P.fiber n)
      (fiber_map_eq l E F n (qf n) (hqf n)).symm
      (fiber_map_eq l E G n (qg n) (hqg n)).symm
    exact (ShortComplex.shortExact_iff_of_iso e).mpr hQ
  · let t := N.etale.map (homOfLE (Nat.le_succ n)).op
    have ht : Function.Surjective (H.map t) := by
      intro x
      obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ ((N.fiber n).hom x)
      refine ⟨(N.fiber (n + 1)).inv (sfLatticeQuotientMk l E C (n + 1) b), ?_⟩
      apply (ModuleCat.mono_iff_injective (N.fiber n).hom).mp inferInstance
      exact (N.transition (n + 1) n (Nat.le_succ n) b).trans hb
    let S := ShortComplex.mk t (0 : N.etale.obj (op n) ⟶ N.etale.obj (op n)) comp_zero
    apply (S.exact_iff_epi rfl).mp
    apply exact_of_exact_finite_fiber p S (N.flc (n + 1)) (N.flc n) (N.flc n)
    apply ((S.map H).exact_iff_epi (by simp [S])).mpr
    exact (ModuleCat.epi_iff_surjective _).mpr ht

private theorem integral_composite_zero (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {T : Scheme.{u}} (p : SfMonodromyPoint T)
    (c : GaloisLisseFiniteCorrespondence p.point p.group)
    (J : SfContinuousRepresentations l E p ⥤ SfRationalModules l E T)
    {V W Z : SfContinuousRepresentations l E p} (f : V ⟶ W) (g : W ⟶ Z)
    (C : SfInvariantLattice l E V) (B : SfInvariantLattice l E W)
    (D : SfInvariantLattice l E Z)
    (hCB : ∀ a : C.submodule, f.hom.hom a.val ∈ B.submodule)
    (hBD : ∀ b : B.submodule, g.hom.hom b.val ∈ D.submodule)
    (N : SfLatticeNormalization l E p c J V C)
    (M : SfLatticeNormalization l E p c J W B)
    (P : SfLatticeNormalization l E p c J Z D)
    (F : SfNormalizationMap l E f C B hCB N M)
    (G : SfNormalizationMap l E g B D hBD M P)
    (hz : ∀ n : ℕ, F.levels.app (op n) ≫ G.levels.app (op n) = 0) :
    F.integral ≫ G.integral = 0 := by
  let U := SheafOfModules.toSheaf
    ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (ProEtale.lisseIntegerSheafSized l E T))
  apply U.map_injective
  rw [Functor.map_comp, Functor.map_zero]
  apply P.isLimit.hom_ext
  intro j
  obtain ⟨n⟩ := j
  let D := ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) T ⋙
      sheafCompose (ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
          AddCommGrpCat.{u + 1})
  have : (forget₂ (ModuleCat.{u + 1}
      (Padic.coefficientExtensionIntegers l E)) AddCommGrpCat.{u + 1}).Additive :=
    ⟨rfl⟩
  have : D.Additive := inferInstance
  change (U.map F.integral ≫ U.map G.integral) ≫ P.projection.app (op n) = _
  rw [Category.assoc, G.limit_comm n, ← Category.assoc, F.limit_comm n,
    Category.assoc, ← D.map_comp, hz n, D.map_zero, comp_zero, zero_comp]

private theorem rational_composite_zero (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {T : Scheme.{u}} (p : SfMonodromyPoint T)
    (c : GaloisLisseFiniteCorrespondence p.point p.group)
    (J : SfContinuousRepresentations l E p ⥤ SfRationalModules l E T)
    {V W Z : SfContinuousRepresentations l E p} (f : V ⟶ W) (g : W ⟶ Z)
    (C : SfInvariantLattice l E V) (B : SfInvariantLattice l E W)
    (D : SfInvariantLattice l E Z)
    (hCB : ∀ a : C.submodule, f.hom.hom a.val ∈ B.submodule)
    (hBD : ∀ b : B.submodule, g.hom.hom b.val ∈ D.submodule)
    (N : SfLatticeNormalization l E p c J V C)
    (M : SfLatticeNormalization l E p c J W B)
    (P : SfLatticeNormalization l E p c J Z D)
    (F : SfNormalizationMap l E f C B hCB N M)
    (G : SfNormalizationMap l E g B D hBD M P)
    (hz : F.integral ≫ G.integral = 0) :
    SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
        (ProEtale.lisseIntegerToFieldSized l E T) N.integral F.integral ≫
      SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
        (ProEtale.lisseIntegerToFieldSized l E T) M.integral G.integral = 0 := by
  unfold SheafOfModules.changeOfRingsHom
  rw [← Functor.map_comp, ← Functor.map_zero]
  congr 1
  apply PresheafOfModules.hom_ext
  intro X
  let r := ((ProEtale.lisseIntegerToFieldSized l E T).hom.app X).hom
  let L := ModuleCat.extendScalars.{u + 1, u + 1, u + 1} r
  have : L.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} r).isLeftAdjoint
  have : L.Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} r).left_adjoint_additive
  change L.map (F.integral.val.app X) ≫ L.map (G.integral.val.app X) = 0
  rw [← L.map_comp]
  have hX : F.integral.val.app X ≫ G.integral.val.app X = 0 :=
    congrArg (fun h ↦ h.val.app X) hz
  rw [hX, L.map_zero]

/-- An exact sequence of invariant lattices gives an exact rationalized sequence of
its prescribed inverse-limit monodromy models.
Source: Bhatt--Scholze, proof of Corollary 6.8.5, pp. 59--60.
(blueprint: lem-sfb-lattice-normalization-rational-exact)

Proof: use the supplied exact quotient maps, whose formulas specify reduction of the
original lattice maps at every positive uniformizer power. The kernel quotient tower has
surjective transition maps, since each transition is the natural further quotient. The finite
correspondence and geometric-fibre formulas for the two normalization maps identify the finite-level
sequences with these reductions. The exact comparison inverse image preserves their
exactness on the pro-etale site. Exact products and the epimorphic Milnor shift on the
kernel tower show that the inverse-limit sequence is exact: locally lift a compatible
quotient tuple to the middle product, solve its compatibility defect in the kernel
product, and subtract. The limit projections in the normalization and their commutation
with the two maps identify this with the sequence of integral models. Localization by l
is an exact filtered colimit of multiplication-by-l maps. The constant-scalar compatibility
identifies this localization with extension along the integral-to-field ring sheaf map.
Therefore the displayed rationalized integral-model sequence is short exact, including
zero lattices. This statement neither constructs compatible lattices nor transports
exactness to the original realization functor. -/
theorem sf_lattice_normalization_rational_exact (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {T : Scheme.{u}} (p : SfMonodromyPoint T)
    (c : GaloisLisseFiniteCorrespondence p.point p.group)
    (J : SfContinuousRepresentations l E p ⥤ SfRationalModules l E T)
    {V W Z : SfContinuousRepresentations l E p} (f : V ⟶ W) (g : W ⟶ Z)
    (C : SfInvariantLattice l E V) (B : SfInvariantLattice l E W)
    (D : SfInvariantLattice l E Z)
    (hCB : ∀ a : C.submodule, f.hom.hom a.val ∈ B.submodule)
    (hBD : ∀ b : B.submodule, g.hom.hom b.val ∈ D.submodule)
    (N : SfLatticeNormalization l E p c J V C)
    (M : SfLatticeNormalization l E p c J W B)
    (P : SfLatticeNormalization l E p c J Z D)
    (F : SfNormalizationMap l E f C B hCB N M)
    (G : SfNormalizationMap l E g B D hBD M P)
    (qf : ∀ n : ℕ, sfLatticeQuotient l E C n →ₗ[Padic.coefficientExtensionIntegers l E]
      sfLatticeQuotient l E B n)
    (qg : ∀ n : ℕ, sfLatticeQuotient l E B n →ₗ[Padic.coefficientExtensionIntegers l E]
      sfLatticeQuotient l E D n)
    (hqf : ∀ (n : ℕ) (a : C.submodule), qf n (sfLatticeQuotientMk l E C n a) =
      sfLatticeQuotientMk l E B n ⟨f.hom.hom a.val, hCB a⟩)
    (hqg : ∀ (n : ℕ) (b : B.submodule), qg n (sfLatticeQuotientMk l E B n b) =
      sfLatticeQuotientMk l E D n ⟨g.hom.hom b.val, hBD b⟩)
    (hq : ∀ n : ℕ, Function.Injective (qf n) ∧ Function.Exact (qf n) (qg n) ∧
      Function.Surjective (qg n)) :
    ∃ w : SheafOfModules.changeOfRingsHom
        (ProEtale.lisseIntegerToFieldSized l E T) N.integral F.integral ≫
      SheafOfModules.changeOfRingsHom
        (ProEtale.lisseIntegerToFieldSized l E T) M.integral G.integral = 0,
      (ShortComplex.mk
        (SheafOfModules.changeOfRingsHom
          (ProEtale.lisseIntegerToFieldSized l E T) N.integral F.integral)
        (SheafOfModules.changeOfRingsHom
          (ProEtale.lisseIntegerToFieldSized l E T) M.integral G.integral) w).ShortExact := by
  obtain ⟨hfinite, ht⟩ := finite_normalization_exact l E p c J f g C B D hCB hBD
    N M P F G qf qg hqf hqg hq
  have hi := integral_composite_zero l E p c J f g C B D hCB hBD
    N M P F G (fun n ↦ (hfinite n).choose)
  have w := rational_composite_zero l E p c J f g C B D hCB hBD N M P F G hi
  exact ⟨w, sf_monodromy_limit_rational_exact l E p c J f g C B D hCB hBD
    N M P F G hfinite ht w⟩

end AlgebraicGeometry.Scheme
