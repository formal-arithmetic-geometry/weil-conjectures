module

public import Sheaf.Paper.EtaleMonodromyRealizationData
import WeilConjectures.CategoryTheory.MittagLefflerLimitExact
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
import Sheaf.AlgebraicGeometry.WContractibleAffineCover
import Sheaf.AlgebraicGeometry.ProEtale.SectionsConservative
import Sheaf.Paper.IntegralRationalizationExact

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme


private theorem epi_tower_maps {C : Type*} [Category* C] (X : ℕᵒᵖ ⥤ C)
    (ht : ∀ n : ℕ, Epi (X.map (homOfLE (Nat.le_succ n)).op))
    {i j : ℕᵒᵖ} (f : i ⟶ j) : Epi (X.map f) := by
  obtain ⟨n⟩ := i
  obtain ⟨m⟩ := j
  have h : m ≤ n := leOfHom f.unop
  suffices h' : ∀ n : ℕ, ∀ h : m ≤ n, Epi (X.map (homOfLE h).op) by
    have hf : f = (homOfLE h).op := Subsingleton.elim _ _
    rw [hf]
    exact h' n h
  intro n h
  induction n, h using Nat.le_induction with
  | base => simpa using (inferInstance : Epi (𝟙 (X.obj (op m))))
  | succ n hn ih =>
    let :=  ih
    let :=  ht n
    have he : (homOfLE (Nat.le_succ n)).op ≫ (homOfLE hn).op =
        (homOfLE (Nat.le_trans hn (Nat.le_succ n))).op := Subsingleton.elim _ _
    rw [← he, X.map_comp]
    infer_instance

private theorem ab_evaluation_exact {T : Scheme.{u}} (W : T.ProEt)
    (hW : (ProEt.topology T).IsWeaklyContractible.{u + 1} W) :
    PreservesFiniteColimits
      ((sheafSections (ProEt.topology T) AddCommGrpCat.{u + 1}).obj (op W)) := by
  let ev := (sheafSections (ProEt.topology T) AddCommGrpCat.{u + 1}).obj (op W)
  have : ev.Additive := ⟨by intros; rfl⟩
  have : PreservesLimitsOfShape ℕᵒᵖ ev := by
    change PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op W))
    infer_instance
  have : PreservesFiniteLimits ev := by
    change PreservesFiniteLimits
      (sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op W))
    infer_instance
  have : ev.PreservesEpimorphisms := by
    constructor
    intro M N f hf
    have : Sheaf.IsLocallySurjective f :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1} f).mpr hf
    let f' := (sheafCompose (ProEt.topology T)
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).map f
    exact (AddCommGrpCat.epi_iff_surjective (ev.map f)).mpr (hW f' inferInstance)
  have : ev.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels ev
  exact Functor.preservesFiniteColimits_of_preservesHomology ev

private theorem limit_sections_shortExact {T : Scheme.{u}}
    (S : ShortComplex (ℕᵒᵖ ⥤ Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}))
    (hS : ∀ n : ℕᵒᵖ,
      (S.map ((CategoryTheory.evaluation _ _).obj n)).ShortExact)
    (ht : ∀ n : ℕ, Epi (S.X₁.map (homOfLE (Nat.le_succ n)).op))
    (W : T.ProEt) (hW : (ProEt.topology T).IsWeaklyContractible.{u + 1} W) :
    ((S.map lim).map
      ((sheafSections (ProEt.topology T) AddCommGrpCat.{u + 1}).obj (op W))).ShortExact := by
  let ev := (sheafSections (ProEt.topology T) AddCommGrpCat.{u + 1}).obj (op W)
  have : ev.Additive := ⟨by intros; rfl⟩
  have : PreservesLimitsOfShape ℕᵒᵖ ev := by
    change PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op W))
    infer_instance
  have : PreservesFiniteLimits ev := by
    change PreservesFiniteLimits
      (sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op W))
    infer_instance
  have : PreservesFiniteColimits ev := ab_evaluation_exact W hW
  let F := (Functor.whiskeringRight ℕᵒᵖ _ _).obj ev
  have hlevels (n : ℕᵒᵖ) :
      ((S.map F).map ((CategoryTheory.evaluation _ _).obj n)).ShortExact := by
    exact (hS n).map_of_exact ev
  have hML : ((S.map F).X₁ ⋙ CategoryTheory.forget AddCommGrpCat).IsMittagLeffler := by
    apply Functor.isMittagLeffler_of_surjective
    intro i j f
    have : Epi (S.X₁.map f) := epi_tower_maps S.X₁ ht f
    exact (AddCommGrpCat.epi_iff_surjective (ev.map (S.X₁.map f))).mp inferInstance
  have hlimit := (ShortComplex.mittagLeffler_quotient_and_limit_exact (S.map F) hlevels).2 hML
  exact (ShortComplex.shortExact_iff_of_iso
    (S.mapNatIso (preservesLimitNatIso ev))).mpr hlimit

private theorem ab_epi_of_sections {T : Scheme.{u}}
    {A B : Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}} (f : A ⟶ B)
    (h : ∀ (W : T.ProEt), (ProEt.topology T).IsWeaklyContractible.{u + 1} W →
      Function.Surjective (f.hom.app (op W))) : Epi f := by
  apply (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1} f).mp
  refine ⟨fun {V} s ↦ ?_⟩
  obtain ⟨I, W, a, hcov, hW⟩ := ProEt.exists_wContractible_affine_cover T V
  refine (ProEt.topology T).superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck hcov)
  rintro _ _ ⟨_, b, _, ⟨i⟩, rfl⟩
  obtain ⟨D, hD, e, _⟩ := hW i
  let : IsWContractibleRing D := hD
  have hw : (ProEt.topology T).IsWeaklyContractible.{u + 1} (W i) :=
    ProEt.isWeaklyContractible_of_iso e.symm
  exact (Presheaf.imageSieve f.hom s).downward_closed (h (W i) hw _) b

private theorem ab_limit_shortExact {T : Scheme.{u}}
    (S : ShortComplex (ℕᵒᵖ ⥤ Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}))
    (hS : ∀ n : ℕᵒᵖ,
      (S.map ((CategoryTheory.evaluation _ _).obj n)).ShortExact)
    (ht : ∀ n : ℕ, Epi (S.X₁.map (homOfLE (Nat.le_succ n)).op)) :
    (S.map lim).ShortExact := by
  have hm (n : ℕᵒᵖ) : Mono (S.f.app n) := (hS n).mono_f
  have : Mono S.f := NatTrans.mono_of_mono_app S.f
  have hmono : Mono (S.map lim).f := inferInstanceAs (Mono (lim.map S.f))
  have hepi : Epi (S.map lim).g := by
    apply ab_epi_of_sections
    intro W hW
    have hh := limit_sections_shortExact S hS ht W hW
    exact hh.ab_surjective_g
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  apply (S.map lim).exact_iff_epi_kernel_lift.mpr
  apply ab_epi_of_sections
  intro W hW
  let ev := (sheafSections (ProEt.topology T) AddCommGrpCat.{u + 1}).obj (op W)
  have : ev.Additive := ⟨by intros; rfl⟩
  have : PreservesLimitsOfShape ℕᵒᵖ ev := by
    change PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op W))
    infer_instance
  have : PreservesFiniteLimits ev := by
    change PreservesFiniteLimits
      (sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op W))
    infer_instance
  have hh := limit_sections_shortExact S hS ht W hW
  have he := ((S.map lim).exact_map_iff_epi_map_kernel_lift ev).mp hh.exact
  exact (AddCommGrpCat.epi_iff_surjective _).mp he

private theorem forget_module_sheaves_exact {T : Scheme.{u}}
    (R : Type (u + 1)) [CommRing R] :
    PreservesFiniteLimits (sheafCompose (ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})) ∧
    PreservesFiniteColimits (sheafCompose (ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})) := by
  let J := ProEt.topology T
  let G := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  have hlim : PreservesFiniteLimits (sheafCompose J G) := by
    have : PreservesFiniteLimits (sheafCompose J G ⋙ sheafToPresheaf _ _) :=
      inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj G))
    exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  let f : ℤ →+* R := Int.castRingHom R
  let U := ModuleCat.restrictScalars.{u + 1} f
  let V := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  have : U.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} f).isLeftAdjoint
  have : G.IsLeftAdjoint := inferInstanceAs (U ⋙ V).IsLeftAdjoint
  let e : Sheaf.composeAndSheafify J G ≅ sheafCompose J G :=
    Functor.isoWhiskerLeft (sheafCompose J G)
      (sheafificationNatIso J AddCommGrpCat.{u + 1}).symm ≪≫
        Functor.rightUnitor (sheafCompose J G)
  have : (Sheaf.composeAndSheafify J G).IsLeftAdjoint := inferInstance
  have : (sheafCompose J G).IsLeftAdjoint := Functor.isLeftAdjoint_of_iso e
  exact ⟨hlim, inferInstance⟩

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

private theorem integral_limit_shortExact (l : ℕ) [Fact l.Prime]
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
    (hfinite : ∀ n : ℕ, ∃ w : F.levels.app (op n) ≫ G.levels.app (op n) = 0,
      (ShortComplex.mk (F.levels.app (op n)) (G.levels.app (op n)) w).ShortExact)
    (ht : ∀ n : ℕ, Epi (N.etale.map (homOfLE (Nat.le_succ n)).op))
    (hz : F.integral ≫ G.integral = 0) :
    (ShortComplex.mk F.integral G.integral hz).ShortExact := by
  let R := ((sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (ProEtale.lisseIntegerSheafSized l E T))
  let U := SheafOfModules.toSheaf R
  let D := ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) T ⋙
      sheafCompose (ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
          AddCommGrpCat.{u + 1})
  have : (forget₂ (ModuleCat.{u + 1}
      (Padic.coefficientExtensionIntegers l E)) AddCommGrpCat.{u + 1}).Additive := ⟨rfl⟩
  have hh := forget_module_sheaves_exact (T := T)
    (Padic.coefficientExtensionIntegers l E)
  have := hh.1
  have := hh.2
  have : D.Additive := inferInstance
  have : PreservesFiniteLimits D := by dsimp [D]; infer_instance
  have : PreservesFiniteColimits D := by dsimp [D]; infer_instance
  have hzero : F.levels ≫ G.levels = 0 := by
    apply NatTrans.ext
    funext n
    obtain ⟨n⟩ := n
    exact (hfinite n).choose
  let S := ShortComplex.mk F.levels G.levels hzero
  let D' := (Functor.whiskeringRight ℕᵒᵖ _ _).obj D
  let SA := S.map D'
  have hlevels (n : ℕᵒᵖ) :
      (SA.map ((CategoryTheory.evaluation _ _).obj n)).ShortExact := by
    obtain ⟨n⟩ := n
    exact (hfinite n).choose_spec.map_of_exact D
  have ht' (n : ℕ) : Epi (SA.X₁.map (homOfLE (Nat.le_succ n)).op) := by
    let := ht n
    exact inferInstanceAs (Epi (D.map (N.etale.map (homOfLE (Nat.le_succ n)).op)))
  have hlim := ab_limit_shortExact SA hlevels ht'
  let eN := N.isLimit.conePointUniqueUpToIso (limit.isLimit _)
  let eM := M.isLimit.conePointUniqueUpToIso (limit.isLimit _)
  let eP := P.isLimit.conePointUniqueUpToIso (limit.isLimit _)
  have hF : U.map F.integral ≫ eM.hom = eN.hom ≫ lim.map SA.f := by
    apply limit.hom_ext
    intro n
    obtain ⟨n⟩ := n
    change (U.map F.integral ≫ eM.hom) ≫ limit.π _ (op n) =
      (eN.hom ≫ limMap (Functor.whiskerRight F.levels D)) ≫ limit.π _ (op n)
    calc
      _ = U.map F.integral ≫ M.projection.app (op n) := by
        rw [Category.assoc, show eM.hom ≫ limit.π _ (op n) =
          M.projection.app (op n) from
          M.isLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _) (op n)]
      _ = N.projection.app (op n) ≫ D.map (F.levels.app (op n)) := F.limit_comm n
      _ = (eN.hom ≫ limit.π _ (op n)) ≫ D.map (F.levels.app (op n)) := by
        rw [show eN.hom ≫ limit.π _ (op n) = N.projection.app (op n) from
          N.isLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _) (op n)]
      _ = _ := by simp only [Category.assoc, limMap_π, Functor.whiskerRight_app]
  have hG : U.map G.integral ≫ eP.hom = eM.hom ≫ lim.map SA.g := by
    apply limit.hom_ext
    intro n
    obtain ⟨n⟩ := n
    change (U.map G.integral ≫ eP.hom) ≫ limit.π _ (op n) =
      (eM.hom ≫ limMap (Functor.whiskerRight G.levels D)) ≫ limit.π _ (op n)
    calc
      _ = U.map G.integral ≫ P.projection.app (op n) := by
        rw [Category.assoc, show eP.hom ≫ limit.π _ (op n) =
          P.projection.app (op n) from
          P.isLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _) (op n)]
      _ = M.projection.app (op n) ≫ D.map (G.levels.app (op n)) := G.limit_comm n
      _ = (eM.hom ≫ limit.π _ (op n)) ≫ D.map (G.levels.app (op n)) := by
        rw [show eM.hom ≫ limit.π _ (op n) = M.projection.app (op n) from
          M.isLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _) (op n)]
      _ = _ := by simp only [Category.assoc, limMap_π, Functor.whiskerRight_app]
  apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful U
  exact (ShortComplex.shortExact_iff_of_iso
    (ShortComplex.isoMk eN eM eP hF.symm hG.symm)).mpr hlim


/-- Exact finite-level monodromy towers with epimorphic kernel transitions remain
short exact after the prescribed integral limits and rationalization.
The composite-zero equation of the rational maps is supplied separately.
Source: Bhatt--Scholze, Proposition 3.1.10 and proof of Corollary 6.8.5, pp. 59--60.
(blueprint: lem-sfb-monodromy-limit-rational-exact)

Proof: apply the exact comparison inverse image to the given short exact sequences.
Forget to abelian sheaves, where the normalization projections exhibit the three
integral models as the limits of these pulled-back towers. Exact products on the
pro-etale site and the epimorphic Milnor shift for the kernel tower imply exactness
of the limit sequence: locally lift a compatible quotient tuple to the middle product,
express its compatibility defect as a kernel tuple, lift that defect under 1 minus
shift on the kernel product, and subtract the lift. Sectionwise kernels give left
exactness. The limit-commutation fields identify the resulting two maps with the
prescribed integral maps. The coefficient sheaf is the uniformizer-adic completion,
and inverting l in it gives the continuous field-coefficient sheaf. On these integral
models this scalar extension is localization: constant-scalar compatibility identifies
the model actions, and sheafification preserves the localization tensor formula.
Localization is an exact filtered colimit of multiplication-by-l maps, so preserves
the integral short exact sequence. This gives precisely the displayed rational maps.
The consumer proves the supplied composite-zero equation by limit extensionality and
functorial scalar extension. The argument includes zero models and does not use
faithfulness of a geometric fibre,
construct lattice quotient maps, or identify a finite-level sheaf from its fibre. -/
theorem sf_monodromy_limit_rational_exact (l : ℕ) [Fact l.Prime]
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
    (hfinite : ∀ n : ℕ, ∃ w : F.levels.app (op n) ≫ G.levels.app (op n) = 0,
      (ShortComplex.mk (F.levels.app (op n)) (G.levels.app (op n)) w).ShortExact)
    (ht : ∀ n : ℕ, Epi (N.etale.map (homOfLE (Nat.le_succ n)).op))
    (w : SheafOfModules.changeOfRingsHom
        (ProEtale.lisseIntegerToFieldSized l E T) N.integral F.integral ≫
      SheafOfModules.changeOfRingsHom
        (ProEtale.lisseIntegerToFieldSized l E T) M.integral G.integral = 0) :
      (ShortComplex.mk
        (SheafOfModules.changeOfRingsHom
          (ProEtale.lisseIntegerToFieldSized l E T) N.integral F.integral)
        (SheafOfModules.changeOfRingsHom
          (ProEtale.lisseIntegerToFieldSized l E T) M.integral G.integral) w).ShortExact := by
  have hz := integral_composite_zero l E p c J f g C B D hCB hBD
    N M P F G (fun n ↦ (hfinite n).choose)
  have hS := integral_limit_shortExact l E p c J f g C B D hCB hBD
    N M P F G hfinite ht hz
  exact sf_integral_rationalization_shortExact l E T
    (ShortComplex.mk F.integral G.integral hz) hS w

end AlgebraicGeometry.Scheme
