/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.ConstructibleSheaf.Biproduct
public import WeilConjectures.ConstructibleSheaf.GenericConstancy
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.Refinements
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

/-!
# Kernels and cokernels of morphisms between finite locally constant sheaves

Let `Λ` be a ring and let `φ : F ⟶ G` be a morphism of finite locally constant sheaves of
`Λ`-modules on the small étale site of `X`. On a common trivialising cover `φ` is a morphism
`M_U ⟶ N_U` between constant sheaves with finitely generated values (the value of a constant
sheaf on a nonempty scheme is a stalk,
`AlgebraicGeometry.Scheme.moduleFinite_of_isFiniteSheaf_constantSheaf`),
which is, on a further étale cover, induced by a linear map `f : M ⟶ N`
(`CategoryTheory.exists_mem_forall_exists_constantSheafOverHom_comp_map_eq`); the kernel and
cokernel of `φ` restrict to the constant sheaves at `ker f` and `coker f` there. Hence
kernels and cokernels of morphisms between finite locally constant sheaves are locally
constant; their stalks are kernels and cokernels of maps between finitely generated modules,
hence finitely generated, for kernels when `Λ` is noetherian
(`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.kernel`,
`IsFiniteLocallyConstantSheaf.cokernel`). Pulling back to the strata of a common refinement of
stratifications, kernels, cokernels and direct sums of constructible sheaves of modules are
constructible (`IsConstructibleSheaf.kernel`, `IsConstructibleSheaf.cokernel`,
`IsConstructibleSheaf.biprod`).

Over a finite ring, extensions of finite locally constant sheaves are finite locally constant
(`IsFiniteLocallyConstantSheaf.of_shortExact`), hence extensions of constructible sheaves are
constructible (`IsConstructibleSheaf.of_shortExact`). Étale locally the outer terms of a short
exact sequence `0 ⟶ F₁ ⟶ F₂ ⟶ N_U ⟶ 0` are constant; a surjection `p : Λᵏ ⟶ N` lifts to `F₂`
on the members of a covering sieve, and there `F₂` is the cokernel of the morphism
`ker p ⟶ Λᵏ ⊞ F₁` between finite locally constant sheaves
(`CategoryTheory.ShortComplex.ShortExact.isoCokernelPresentation`).
(blueprint: `lemma:constructible-hom-constant-locally`, `lemma:constructible-flc-serre`)

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme

section Cover

variable {Y : Scheme.{u}}

/-- A covering sieve of `Etale.mk (𝟙 Y)` in the small étale site of `Y` gives an étale cover
of `Y`, indexed by the points of `Y`: for every point one chooses a member of the sieve whose
image contains it. -/
def Cover.ofSieve (S : Sieve (Etale.mk (𝟙 Y))) (hS : S ∈ Y.smallEtaleTopology _) :
    Cover.{u} etalePrecoverage Y where
  I₀ := Y
  X y := ((mem_smallEtaleTopology_iff S).mp hS y).choose.left
  f y := ((mem_smallEtaleTopology_iff S).mp hS y).choose_spec.choose.left
  mem₀ := by
    refine (presieve₀_mem_precoverage_iff _).mpr ⟨fun y ↦ ?_, fun y ↦ inferInstance⟩
    exact ⟨y, ((mem_smallEtaleTopology_iff S).mp hS y).choose_spec.choose_spec.2⟩

variable (S : Sieve (Etale.mk (𝟙 Y))) (hS : S ∈ Y.smallEtaleTopology _)

/-- The member of the sieve chosen for the point `y`, as an object of the small étale site. -/
def Cover.ofSieveObj (y : Y) : Y.Etale :=
  ((mem_smallEtaleTopology_iff S).mp hS y).choose

/-- The member of the sieve chosen for the point `y`. -/
def Cover.ofSieveHom (y : Y) : Cover.ofSieveObj S hS y ⟶ Etale.mk (𝟙 Y) :=
  ((mem_smallEtaleTopology_iff S).mp hS y).choose_spec.choose

lemma Cover.ofSieveHom_mem (y : Y) : S (Cover.ofSieveHom S hS y) :=
  ((mem_smallEtaleTopology_iff S).mp hS y).choose_spec.choose_spec.1

lemma Cover.ofSieve_f (y : Y) : (Cover.ofSieve S hS).f y = (Cover.ofSieveHom S hS y).left :=
  rfl

lemma Cover.ofSieve_X (y : Y) : (Cover.ofSieve S hS).X y = (Cover.ofSieveObj S hS y).left :=
  rfl

lemma Cover.ofSieveHom_left (y : Y) :
    (Cover.ofSieveHom S hS y).left = (Cover.ofSieveObj S hS y).hom :=
  (Category.comp_id _).symm.trans (MorphismProperty.Over.w (Cover.ofSieveHom S hS y))

/-- The members of the cover are nonempty. -/
lemma Cover.nonempty_ofSieveObj (y : Y) : Nonempty (Cover.ofSieveObj S hS y).left :=
  let h := ((mem_smallEtaleTopology_iff S).mp hS y).choose_spec.choose_spec.2
  ⟨h.choose⟩

/-- The empty sieve does not cover a nonempty scheme. -/
lemma bot_not_mem_smallEtaleTopology (U : Y.Etale) [Nonempty U.left] :
    (⊥ : Sieve U) ∉ Y.smallEtaleTopology U := by
  intro h
  obtain ⟨V, g, hg, -⟩ := (mem_smallEtaleTopology_iff _).mp h (Classical.arbitrary _)
  exact hg

end Cover

section Finite

variable {Y : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ]

/-- **The value of a finite constant sheaf on a nonempty scheme is finitely generated**: it is
the stalk at any geometric point. -/
lemma moduleFinite_of_isFiniteSheaf_constantSheaf [Nonempty Y] (M : ModuleCat.{u + 1} Λ)
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)] :
    Module.Finite Λ M := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let y : Y := Classical.arbitrary _
  let s : Spec (.of (SeparableClosure (Y.residueField y))) ⟶ Y :=
    (SpecToEquivOfField (SeparableClosure (Y.residueField y)) _).2
      ⟨y, CommRingCat.ofHom (algebraMap (Y.residueField y) _)⟩
  exact (ModuleCat.isFinitelyGenerated_iff M).1
    ((IsFiniteSheaf.isFinitelyGenerated_sheafFiber
      (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
      (F := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) _ s).of_iso
      ((pointSmallEtale s).sheafFiberConstantSheafIso M))


/-- A constant sheaf of modules with finitely generated value is finite locally constant. -/
instance isFiniteLocallyConstantSheaf_constantSheaf (M : ModuleCat.{u + 1} Λ)
    [Module.Finite Λ M] :
    IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) where
  toIsLocallyConstantSheaf := by
    have : etalePrecoverage.{u}.HasIsos := inferInstanceAs (precoverage @Etale).HasIsos
    refine ⟨⟨⟨.singleton (𝟙 Y) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ ?_⟩⟩⟩
    rw [isConstant_over_iff_upperStar]
    have : ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M).IsConstant
        Y.smallEtaleTopology := Sheaf.isConstant_of_iso _ (Iso.refl _)
    exact Sheaf.IsConstant.upperStar (X := Y) _ _ _
  toIsFiniteSheaf := ⟨fun Ω _ _ s ↦ by
    have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    exact ((ModuleCat.isFinitelyGenerated_iff M).2 inferInstance).of_iso
      ((pointSmallEtale s).sheafFiberConstantSheafIso M).symm⟩

end Finite

section Constant

variable {X : Scheme.{u}} {A : Type*} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]

/-- Two locally constant sheaves are trivialised by a common étale cover. -/
lemma IsLocallyConstantSheaf.exists_cover₂ (F G : Sheaf X.smallEtaleTopology A)
    [IsLocallyConstantSheaf F] [IsLocallyConstantSheaf G] :
    ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i,
      ((Etale.upperStar A (𝒰.f i)).obj F).IsConstant (𝒰.X i).smallEtaleTopology ∧
      ((Etale.upperStar A (𝒰.f i)).obj G).IsConstant (𝒰.X i).smallEtaleTopology := by
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
  obtain ⟨⟨𝒱, h𝒱⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := G)
  refine ⟨𝒰.bind fun i ↦ 𝒱.pullback₂ (𝒰.f i), fun ⟨i, j⟩ ↦ ?_⟩
  set f := pullback.snd (𝒱.f j) (𝒰.f i) ≫ 𝒰.f i
  change ((Etale.upperStar A f).obj F).IsConstant (pullback (𝒱.f j) (𝒰.f i)).smallEtaleTopology ∧
    ((Etale.upperStar A f).obj G).IsConstant (pullback (𝒱.f j) (𝒰.f i)).smallEtaleTopology
  constructor
  · have h₁ : ((Etale.upperStar A (𝒰.f i)).obj F).IsConstant (𝒰.X i).smallEtaleTopology :=
      (isConstant_over_iff_upperStar A (𝒰.etalePrecoverageToEtale i) F).mp (h𝒰 i)
    have h₂ : ((Etale.upperStar A (𝒰.f i) ⋙ Etale.upperStar A (pullback.snd (𝒱.f j) (𝒰.f i))).obj
        F).IsConstant (pullback (𝒱.f j) (𝒰.f i)).smallEtaleTopology :=
      Sheaf.IsConstant.upperStar A (pullback.snd (𝒱.f j) (𝒰.f i))
        ((Etale.upperStar A (𝒰.f i)).obj F)
    exact Sheaf.isConstant_congr _
      ((Etale.upperStarComp A (pullback.snd (𝒱.f j) (𝒰.f i)) (𝒰.f i)).app F).symm
  · have h₁ : ((Etale.upperStar A (𝒱.f j)).obj G).IsConstant (𝒱.X j).smallEtaleTopology :=
      (isConstant_over_iff_upperStar A (𝒱.etalePrecoverageToEtale j) G).mp (h𝒱 j)
    have h₂ : ((Etale.upperStar A (𝒱.f j) ⋙ Etale.upperStar A (pullback.fst (𝒱.f j) (𝒰.f i))).obj
        G).IsConstant (pullback (𝒱.f j) (𝒰.f i)).smallEtaleTopology :=
      Sheaf.IsConstant.upperStar A (pullback.fst (𝒱.f j) (𝒰.f i))
        ((Etale.upperStar A (𝒱.f j)).obj G)
    exact Sheaf.isConstant_congr _
      (((Etale.upperStarComp A (pullback.fst (𝒱.f j) (𝒰.f i)) (𝒱.f j)).app G).symm ≪≫
        eqToIso (congrArg (fun m ↦ (Etale.upperStar A m).obj G) pullback.condition))

/-- The nonempty members of an étale cover form an étale cover. -/
def Cover.nonemptyMembers (𝒰 : Cover.{u} etalePrecoverage X) : Cover.{u} etalePrecoverage X where
  I₀ := { i : 𝒰.I₀ // Nonempty (𝒰.X i) }
  X i := 𝒰.X i.1
  f i := 𝒰.f i.1
  mem₀ := by
    refine (presieve₀_mem_precoverage_iff _).mpr ⟨fun x ↦ ?_, fun i ↦ 𝒰.map_prop i.1⟩
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
    exact ⟨⟨i, ⟨y⟩⟩, y, hy⟩

instance (𝒰 : Cover.{u} etalePrecoverage X) (i : 𝒰.nonemptyMembers.I₀) :
    Nonempty (𝒰.nonemptyMembers.X i) :=
  i.2

end Constant

section Kernel

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ]
  {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G)

/-- **The kernel and cokernel of a morphism between finite locally constant sheaves of modules
are locally constant**: on a common trivialising cover `φ` is a morphism of constant sheaves
with finitely generated values, which is étale-locally induced by a linear map `f`, so that the
kernel and cokernel are étale-locally the constant sheaves at `ker f` and `coker f`.
(blueprint: `lemma:constructible-hom-constant-locally`, `lemma:constructible-flc-serre`) -/
theorem IsLocallyConstantSheaf.kernel_and_cokernel
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F] [IsLocallyConstantSheaf G] :
    IsLocallyConstantSheaf (kernel φ) ∧ IsLocallyConstantSheaf (cokernel φ) := by
  obtain ⟨𝒰₀, h𝒰₀⟩ := IsLocallyConstantSheaf.exists_cover₂ F G
  let 𝒰 := 𝒰₀.nonemptyMembers
  have key : ∀ i : 𝒰.I₀, ∃ 𝒱 : Cover.{u} etalePrecoverage (𝒰.X i), ∀ j,
      ((kernel φ).over (Etale.mk (𝒱.f j ≫ 𝒰.f i))).IsConstant
        (X.smallEtaleTopology.over (Etale.mk (𝒱.f j ≫ 𝒰.f i))) ∧
      ((cokernel φ).over (Etale.mk (𝒱.f j ≫ 𝒰.f i))).IsConstant
        (X.smallEtaleTopology.over (Etale.mk (𝒱.f j ≫ 𝒰.f i))) := by
    intro i
    set Y := 𝒰.X i
    set g := 𝒰.f i
    have hF : ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj F).IsConstant Y.smallEtaleTopology :=
      (h𝒰₀ i.1).1
    have hG : ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj G).IsConstant Y.smallEtaleTopology :=
      (h𝒰₀ i.1).2
    obtain ⟨M, ⟨eF⟩⟩ := ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj F).mem_essImage_of_isConstant
    obtain ⟨N, ⟨eG⟩⟩ := ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj G).mem_essImage_of_isConstant
    let ψ : (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M ⟶
        (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N :=
      eF.hom ≫ (Etale.upperStar (ModuleCat.{u + 1} Λ) g).map φ ≫ eG.inv
    have hfin : IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
      have := IsFiniteSheaf.upperStar (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) g F
      IsFiniteSheaf.of_iso (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) eF.symm
    have : Module.Finite Λ M := moduleFinite_of_isFiniteSheaf_constantSheaf (Y := Y) M
    obtain ⟨S, hS, hmem⟩ := exists_mem_forall_exists_constantSheafOverHom_comp_map_eq
      Y.smallEtaleTopology (T := Etale.mk (𝟙 Y)) M N ψ
    refine ⟨Cover.ofSieve S hS, fun y ↦ ?_⟩
    set V := Cover.ofSieveObj S hS y
    set a := Cover.ofSieveHom S hS y
    have := Cover.nonempty_ofSieveObj S hS y
    obtain ⟨f, hf⟩ := hmem a (Cover.ofSieveHom_mem S hS y) (bot_not_mem_smallEtaleTopology V)
    have hk := Sheaf.isConstant_kernel_over Y.smallEtaleTopology _ V f ψ hf
    have hc := Sheaf.isConstant_cokernel_over Y.smallEtaleTopology _ V f ψ hf
    rw [isConstant_over_iff_upperStar] at hk hc
    have hw : (Etale.upperStar (ModuleCat.{u + 1} Λ) g).map φ ≫ eG.symm.hom = eF.symm.hom ≫ ψ := by
      simp [ψ]
    constructor
    · rw [isConstant_over_iff_upperStar]
      change ((Etale.upperStar (ModuleCat.{u + 1} Λ) (a.left ≫ g)).obj (kernel φ)).IsConstant
        V.left.smallEtaleTopology
      refine Sheaf.isConstant_congr _ (?_ : (Etale.upperStar _ V.hom).obj (kernel ψ) ≅ _)
      refine eqToIso (congrArg (fun m ↦ (Etale.upperStar (ModuleCat.{u + 1} Λ) m).obj (kernel ψ))
        (Cover.ofSieveHom_left S hS y).symm) ≪≫
        (Etale.upperStar (ModuleCat.{u + 1} Λ) a.left).mapIso
          ((kernel.mapIso _ ψ eF.symm eG.symm hw).symm ≪≫
            (PreservesKernel.iso (Etale.upperStar (ModuleCat.{u + 1} Λ) g) φ).symm) ≪≫
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) a.left g).app (kernel φ)).symm
    · rw [isConstant_over_iff_upperStar]
      change ((Etale.upperStar (ModuleCat.{u + 1} Λ) (a.left ≫ g)).obj (cokernel φ)).IsConstant
        V.left.smallEtaleTopology
      refine Sheaf.isConstant_congr _ (?_ : (Etale.upperStar _ V.hom).obj (cokernel ψ) ≅ _)
      refine eqToIso (congrArg (fun m ↦ (Etale.upperStar (ModuleCat.{u + 1} Λ) m).obj (cokernel ψ))
        (Cover.ofSieveHom_left S hS y).symm) ≪≫
        (Etale.upperStar (ModuleCat.{u + 1} Λ) a.left).mapIso
          ((cokernel.mapIso _ ψ eF.symm eG.symm hw).symm ≪≫
            (PreservesCokernel.iso (Etale.upperStar (ModuleCat.{u + 1} Λ) g) φ).symm) ≪≫
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) a.left g).app (cokernel φ)).symm
  choose 𝒱 h𝒱 using key
  exact ⟨⟨⟨⟨𝒰.bind 𝒱, fun ⟨i, j⟩ ↦ (h𝒱 i j).1⟩⟩⟩, ⟨⟨⟨𝒰.bind 𝒱, fun ⟨i, j⟩ ↦ (h𝒱 i j).2⟩⟩⟩⟩

end Kernel

section FiniteStalks

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ]
  {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G)

/-- Filtered colimits of size `u` are exact in `ModuleCat.{u + 1} Λ`. -/
instance : AB5OfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
  AB5OfSize_shrink.{u, u, u + 1, u + 1} _

/-- Limits of size `u` exist in `ModuleCat.{u + 1} Λ`; stated explicitly, since the universe
constraint of the general instance does not unify. -/
instance : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
  hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _

/-- The stalk functors at geometric points, with values in `ModuleCat.{u + 1} Λ`, preserve
finite colimits. -/
instance {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    PreservesFiniteColimits ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)) :=
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  have : PreservesColimitsOfSize.{0, 0}
      ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)) :=
    ((pointSmallEtale s).skyscraperSheafAdjunction
      (A := ModuleCat.{u + 1} Λ)).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- Over a noetherian ring, the kernel of a morphism out of a finite sheaf is finite: its stalks
are kernels of maps out of finitely generated modules, submodules of noetherian modules. -/
theorem IsFiniteSheaf.kernel [IsNoetherianRing Λ]
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F] :
    IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (kernel φ) where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    have := (ModuleCat.isFinitelyGenerated_iff _).1
      (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
        (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (F := F) Ω s)
    let e := PreservesKernel.iso (pointSmallEtale s).sheafFiber φ
    have hι : Function.Injective (kernel.ι ((pointSmallEtale s).sheafFiber.map φ)) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    exact ((ModuleCat.isFinitelyGenerated_iff _).2
      (Module.Finite.of_injective (kernel.ι ((pointSmallEtale s).sheafFiber.map φ)).hom hι)).of_iso
      e.symm

/-- The cokernel of a morphism into a finite sheaf is finite: its stalks are cokernels of maps
into finitely generated modules. -/
theorem IsFiniteSheaf.cokernel
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) G] :
    IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (cokernel φ) where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    let e := PreservesCokernel.iso ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)) φ
    have := (ModuleCat.isFinitelyGenerated_iff ((pointSmallEtale s).sheafFiber.obj G)).1
      (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
        (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (F := G) Ω s)
    have hπ : Function.Surjective (cokernel.π ((pointSmallEtale s).sheafFiber.map φ)) :=
      (ModuleCat.epi_iff_surjective _).mp inferInstance
    exact ((ModuleCat.isFinitelyGenerated_iff
      (Limits.cokernel ((pointSmallEtale s).sheafFiber.map φ))).2
      (Module.Finite.of_surjective (cokernel.π ((pointSmallEtale s).sheafFiber.map φ)).hom
        hπ)).of_iso e.symm

/-- **The kernel of a morphism between finite locally constant sheaves of modules over a
noetherian ring is finite locally constant.** (blueprint: `lemma:constructible-flc-serre`) -/
theorem IsFiniteLocallyConstantSheaf.kernel [IsNoetherianRing Λ]
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F]
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) G] :
    IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (kernel φ) where
  toIsLocallyConstantSheaf := (IsLocallyConstantSheaf.kernel_and_cokernel φ).1
  toIsFiniteSheaf := IsFiniteSheaf.kernel φ

/-- **The cokernel of a morphism between finite locally constant sheaves of modules is finite
locally constant.** (blueprint: `lemma:constructible-flc-serre`) -/
theorem IsFiniteLocallyConstantSheaf.cokernel
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F]
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) G] :
    IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (cokernel φ) where
  toIsLocallyConstantSheaf := (IsLocallyConstantSheaf.kernel_and_cokernel φ).2
  toIsFiniteSheaf := IsFiniteSheaf.cokernel φ

/-- **The homology of a short complex of finite locally constant sheaves of modules over a
noetherian ring is finite locally constant**: it is the cokernel of a morphism into the cycles,
the kernel of the second morphism. -/
theorem IsFiniteLocallyConstantSheaf.homology [IsNoetherianRing Λ]
    (S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁]
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₂]
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃] :
    IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.homology := by
  have := IsFiniteLocallyConstantSheaf.kernel S.g
  have : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.cycles :=
    IsFiniteLocallyConstantSheaf.of_iso (F := Limits.kernel S.g)
      ((S.cyclesIsKernel.conePointUniqueUpToIso (kernelIsKernel S.g)).symm)
  have := IsFiniteLocallyConstantSheaf.cokernel S.toCycles
  exact IsFiniteLocallyConstantSheaf.of_iso (F := Limits.cokernel S.toCycles)
    ((cokernelIsCokernel S.toCycles).coconePointUniqueUpToIso S.homologyIsCokernel)

/-- **An extension of a constant sheaf by a finite locally constant sheaf is locally constant.**
Let `S` be a short exact sequence of sheaves of modules over a finite ring with `S.X₁` finite
locally constant and `S.X₃` constant with finitely generated value `N`. Choose a surjection
`p : Λ^k ⟶ N`; the images in `S.X₃` of the basis vectors lift to `S.X₂` over the members `V` of a
covering sieve, giving a lift `s : Λ^k_V ⟶ S.X₂|_V` of `p`. Then `S.X₂|_V` is the cokernel of a
morphism from the finite locally constant kernel of `p` to `Λ^k_V ⊞ S.X₁|_V`
(`CategoryTheory.ShortComplex.ShortExact.isoCokernelPresentation`), hence locally constant. -/
theorem IsLocallyConstantSheaf.of_shortExact_of_iso_constantSheaf [Finite Λ] {Y : Scheme.{u}}
    {S : ShortComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁]
    {N : ModuleCat.{u + 1} Λ} [Module.Finite Λ N]
    (eN : (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N ≅ S.X₃) :
    IsLocallyConstantSheaf S.X₂ := by
  let J := Y.smallEtaleTopology
  let A := ModuleCat.{u + 1} Λ
  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' Λ N
  let M : A := ModuleCat.of Λ (Fin k → Λ)
  let P := (constantSheaf J A).obj M
  let T : Y.Etale := Etale.mk (𝟙 Y)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ _
  have : (constantSheaf J A).IsLeftAdjoint := (constantSheafAdj J A hT).isLeftAdjoint
  let p : P ⟶ S.X₃ := (constantSheaf J A).map (ModuleCat.ofHom π) ≫ eN.hom
  have : Epi (ModuleCat.ofHom π) := (ModuleCat.epi_iff_surjective _).2 hπ
  have : Epi p := epi_comp _ _
  let ι (V : Y.Etale) : M ⟶ P.obj.obj (op V) :=
    (CategoryTheory.toSheafify J ((Functor.const _).obj M)).app (op V)
  let ν (l : Fin k) : S.X₃.obj.obj (op T) := (p.hom.app (op T)).hom ((ι T).hom (Pi.single l 1))
  have : Sheaf.IsLocallySurjective S.g := (Sheaf.isLocallySurjective_iff_epi' (φ := S.g)).2 hS.epi_g
  let R : Sieve T := ⨅ l, Presheaf.imageSieve S.g.hom (ν l)
  have hR : R ∈ J T := J.iInf_mem _ fun l ↦ Presheaf.imageSieve_mem J S.g.hom (U := op T) (ν l)
  have key (V : Y.Etale) (a : V ⟶ T) (ha : R a) :
      IsLocallyConstantSheaf ((Etale.upperStar A V.hom).obj S.X₂) := by
    have hx (l : Fin k) : ∃ x : S.X₂.obj.obj (op V),
        (S.g.hom.app (op V)).hom x = (S.X₃.obj.map a.op).hom (ν l) :=
      (iInf_le (fun l ↦ Presheaf.imageSieve S.g.hom (ν l)) l : R ≤ _) _ ha
    choose x hx using hx
    let Φ := J.overPullback A V
    let S' := S.map Φ
    have hS' : S'.ShortExact := hS.map_of_exact Φ
    let adjV := constantSheafAdj (J.over V) A (Over.mkIdTerminal (X := V))
    let xs : (Fin k → Λ) →ₗ[Λ] S.X₂.obj.obj (op V) :=
      ∑ l, (LinearMap.proj l : (Fin k → Λ) →ₗ[Λ] Λ).smulRight (x l)
    let s : (constantSheaf (J.over V) A).obj M ⟶ S'.X₂ :=
      (adjV.homEquiv _ _).symm (ModuleCat.ofHom xs)
    let c := constantSheafOverHom J A V M
    have hs : s ≫ S'.g = c ≫ Φ.map p := by
      apply (adjV.homEquiv _ _).injective
      rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
        Equiv.apply_symm_apply, constantSheafAdj_homEquiv_constantSheafOverHom]
      ext1
      refine LinearMap.pi_ext' fun l ↦ LinearMap.ext_ring ?_
      have h₁ := congrArg (fun f ↦ f.hom (Pi.single l 1))
        ((CategoryTheory.toSheafify J ((Functor.const _).obj M)).naturality a.op)
      have h₂ := congrArg (fun f ↦ f.hom ((ι T).hom (Pi.single l 1))) (p.hom.naturality a.op)
      change (S.g.hom.app (op V)).hom (xs (Pi.single l 1)) = (p.hom.app (op V)).hom _
      have hxs : xs (Pi.single l 1) = x l := by simp [xs, Pi.single_apply]
      rw [hxs, hx l]
      exact h₂.symm.trans (congrArg (p.hom.app (op V)).hom h₁.symm)
    have : Epi (s ≫ S'.g) := by
      rw [hs]
      have : Epi (Φ.map p) := Φ.map_epi p
      infer_instance
    let L := hS'.presentation s
    let Ψ := (Etale.overSheafEquiv V A).functor
    have : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) P := isFiniteLocallyConstantSheaf_constantSheaf M
    have : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃ :=
      have := isFiniteLocallyConstantSheaf_constantSheaf (Y := Y) N
      IsFiniteLocallyConstantSheaf.of_iso eN
    have : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (Ψ.obj L.X₁) := by
      have := IsFiniteLocallyConstantSheaf.kernel p
      have := IsFiniteLocallyConstantSheaf.upperStar V.hom (kernel p)
      exact IsFiniteLocallyConstantSheaf.of_iso
        ((overSheafEquivFunctorObjOverIso A V (kernel p)).symm ≪≫ Ψ.mapIso
          (PreservesKernel.iso Φ p ≪≫ (kernelIsIsoComp c (Φ.map p)).symm ≪≫
            kernelIsoOfEq hs.symm))
    have : IsLocallyConstantSheaf (Ψ.obj L.X₂) := by
      have := preservesBinaryBiproducts_of_preservesBinaryProducts Φ
      have := IsFiniteLocallyConstantSheaf.biprod P S.X₁
      have := IsFiniteLocallyConstantSheaf.upperStar V.hom (P ⊞ S.X₁)
      exact IsLocallyConstantSheaf.of_iso
        ((overSheafEquivFunctorObjOverIso A V (P ⊞ S.X₁)).symm ≪≫ Ψ.mapIso
          (Φ.mapBiprod P S.X₁ ≪≫ biprod.mapIso (asIso c).symm (Iso.refl _)))
    have := (IsLocallyConstantSheaf.kernel_and_cokernel (Ψ.map L.f)).2
    exact IsLocallyConstantSheaf.of_iso ((PreservesCokernel.iso Ψ L.f).symm ≪≫
      Ψ.mapIso (hS'.isoCokernelPresentation s).symm ≪≫ overSheafEquivFunctorObjOverIso A V S.X₂)
  have (y : Y) :
      IsLocallyConstantSheaf ((Etale.upperStar A ((Cover.ofSieve R hR).f y)).obj S.X₂) := by
    rw [Cover.ofSieve_f, Cover.ofSieveHom_left]
    exact key _ _ (Cover.ofSieveHom_mem R hR y)
  exact IsLocallyConstantSheaf.of_cover (Cover.ofSieve R hR) S.X₂

/-- **Local constancy of extensions.** For a finite ring `Λ`, the middle term of a short exact
sequence of sheaves of `Λ`-modules whose outer terms are finite locally constant is locally
constant: on a common trivialising cover of the outer terms this is
`IsLocallyConstantSheaf.of_shortExact_of_iso_constantSheaf`. -/
theorem IsLocallyConstantSheaf.of_shortExact [Finite Λ] {X : Scheme.{u}}
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁]
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃] :
    IsLocallyConstantSheaf S.X₂ := by
  obtain ⟨𝒰₀, h𝒰₀⟩ := IsLocallyConstantSheaf.exists_cover₂ S.X₁ S.X₃
  let 𝒰 := 𝒰₀.nonemptyMembers
  have (i : 𝒰.I₀) :
      IsLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj S.X₂) := by
    let F := Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)
    have hS' : (S.map F).ShortExact := hS.map_of_exact F
    have : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (S.map F).X₁ :=
      IsFiniteLocallyConstantSheaf.upperStar (𝒰.f i) S.X₁
    have : IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (F.obj S.X₃) :=
      IsFiniteSheaf.upperStar (𝒰.f i) S.X₃
    have : (F.obj S.X₃).IsConstant (𝒰.X i).smallEtaleTopology := (h𝒰₀ i.1).2
    obtain ⟨N, ⟨eN⟩⟩ := (F.obj S.X₃).mem_essImage_of_isConstant
    have : IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
        ((constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N) :=
      IsFiniteSheaf.of_iso eN.symm
    have : Module.Finite Λ N := moduleFinite_of_isFiniteSheaf_constantSheaf (Y := 𝒰.X i) N
    exact IsLocallyConstantSheaf.of_shortExact_of_iso_constantSheaf hS' eN
  exact IsLocallyConstantSheaf.of_cover 𝒰 S.X₂

/-- **Finiteness of extensions.** The middle term of a short exact sequence of sheaves of modules
whose outer terms are finite is finite: its stalks are extensions of finitely generated
modules. -/
theorem IsFiniteSheaf.of_shortExact {X : Scheme.{u}}
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁]
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃] :
    IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₂ where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    let Fib := (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
    have hS' := hS.map_of_exact Fib
    have : Module.Finite Λ (S.map Fib).X₁ := (ModuleCat.isFinitelyGenerated_iff _).1
      (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
        (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (F := S.X₁) Ω s)
    have : Module.Finite Λ (S.map Fib).X₃ := (ModuleCat.isFinitelyGenerated_iff _).1
      (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
        (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (F := S.X₃) Ω s)
    rw [ModuleCat.isFinitelyGenerated_iff]
    exact Module.Finite.of_exact
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS'.exact)
      ((ModuleCat.epi_iff_surjective _).1 hS'.epi_g)


/-- Blueprint `lemma-constructible-flc-serre`: Kernels, cokernels and extensions of finite
locally constant sheaves.

**The extension clause.** For a finite ring `Λ`, the middle term of a short exact sequence of
sheaves of `Λ`-modules whose outer terms are finite locally constant is finite locally constant:
its stalks are extensions of finitely generated modules (`IsFiniteSheaf.of_shortExact`), and on
an étale cover trivialising the outer terms it is the cokernel of a morphism between finite
locally constant sheaves (`IsLocallyConstantSheaf.of_shortExact`). -/
theorem IsFiniteLocallyConstantSheaf.of_shortExact [Finite Λ]
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁]
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃] :
    IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₂ where
  toIsLocallyConstantSheaf := IsLocallyConstantSheaf.of_shortExact hS
  toIsFiniteSheaf := IsFiniteSheaf.of_shortExact hS

end FiniteStalks

section Constructible

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ]
  {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G)

/-- **The kernel of a morphism between constructible sheaves of modules over a noetherian ring
is constructible**: on the common refinement of witnessing stratifications, the pullback of the
kernel to a stratum is the kernel of a morphism between finite locally constant sheaves.
(blueprint: `thm:constructible-serre`) -/
theorem IsConstructibleSheaf.kernel [IsNoetherianRing Λ]
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F]
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) G] :
    IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (kernel φ) := by
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := F)
  obtain ⟨T, hT⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := G)
  refine ⟨S.inter T, fun k ↦ ?_⟩
  have hF := (S.inter_refines_left T).isFiniteLocallyConstantSheaf_upperStar F hS k
  have hG := (S.inter_refines_right T).isFiniteLocallyConstantSheaf_upperStar G hT k
  have := IsFiniteLocallyConstantSheaf.kernel
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) ((S.inter T).immersion k)).map φ)
  exact IsFiniteLocallyConstantSheaf.of_iso (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
    (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (PreservesKernel.iso (Etale.upperStar (ModuleCat.{u + 1} Λ) ((S.inter T).immersion k)) φ).symm

/-- **The cokernel of a morphism between constructible sheaves of modules is constructible.**
(blueprint: `thm:constructible-serre`) -/
theorem IsConstructibleSheaf.cokernel
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F]
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) G] :
    IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (cokernel φ) := by
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := F)
  obtain ⟨T, hT⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := G)
  refine ⟨S.inter T, fun k ↦ ?_⟩
  have hF := (S.inter_refines_left T).isFiniteLocallyConstantSheaf_upperStar F hS k
  have hG := (S.inter_refines_right T).isFiniteLocallyConstantSheaf_upperStar G hT k
  have := IsFiniteLocallyConstantSheaf.cokernel
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) ((S.inter T).immersion k)).map φ)
  exact IsFiniteLocallyConstantSheaf.of_iso (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
    (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (PreservesCokernel.iso (Etale.upperStar (ModuleCat.{u + 1} Λ) ((S.inter T).immersion k)) φ).symm

/-- **A retract of a constructible sheaf of modules over a noetherian ring is constructible**:
it is the kernel of the complementary idempotent. -/
theorem IsConstructibleSheaf.of_retract [IsNoetherianRing Λ] {S : Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)} (e : Retract S F)
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F] :
    IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S := by
  have h : e.i ≫ (𝟙 F - e.r ≫ e.i) = 0 := by simp
  have := IsConstructibleSheaf.kernel (𝟙 F - e.r ≫ e.i)
  refine IsConstructibleSheaf.of_iso (F' := S)
    ⟨Limits.kernel.ι _ ≫ e.r, Limits.kernel.lift _ e.i h, (cancel_mono (Limits.kernel.ι _)).1 ?_,
      by simp⟩
  have := Limits.kernel.condition (𝟙 F - e.r ≫ e.i)
  rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at this
  simpa using this.symm

variable (F G) in
/-- **The direct sum of two constructible sheaves of modules is constructible**: on the common
refinement of witnessing stratifications, the pullback of `F ⊞ G` to a stratum is the direct sum
of two finite locally constant sheaves. (blueprint: `lemma:constructible-flc-biproduct`) -/
theorem IsConstructibleSheaf.biprod
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F]
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) G] :
    IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (F ⊞ G) := by
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := F)
  obtain ⟨T, hT⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := G)
  refine ⟨S.inter T, fun k ↦ ?_⟩
  have hF := (S.inter_refines_left T).isFiniteLocallyConstantSheaf_upperStar F hS k
  have hG := (S.inter_refines_right T).isFiniteLocallyConstantSheaf_upperStar G hT k
  have := IsFiniteLocallyConstantSheaf.biprod (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
    (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) ((S.inter T).immersion k)).obj F)
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) ((S.inter T).immersion k)).obj G)
  exact IsFiniteLocallyConstantSheaf.of_iso (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
    (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      ((S.inter T).immersion k)).leftAdjointBiprodIso F G).symm

/-- **The middle term of a short exact sequence of sheaves of modules over a finite ring whose
outer terms are constructible is constructible**: on the common refinement of witnessing
stratifications, the pullback of the sequence to a stratum is a short exact sequence of finite
locally constant sheaves. (blueprint: `thm:constructible-serre`) -/
theorem IsConstructibleSheaf.of_shortExact [Finite Λ]
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁]
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃] :
    IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₂ := by
  obtain ⟨T₁, hT₁⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := S.X₁)
  obtain ⟨T₃, hT₃⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := S.X₃)
  refine ⟨T₁.inter T₃, fun k ↦ ?_⟩
  have h₁ := (T₁.inter_refines_left T₃).isFiniteLocallyConstantSheaf_upperStar S.X₁ hT₁ k
  have h₃ := (T₁.inter_refines_right T₃).isFiniteLocallyConstantSheaf_upperStar S.X₃ hT₃ k
  let F := Etale.upperStar (ModuleCat.{u + 1} Λ) ((T₁.inter T₃).immersion k)
  have : PreservesFiniteLimits F := inferInstance
  have : PreservesFiniteColimits F := inferInstance
  have hS' : (S.map F).ShortExact := hS.map_of_exact F
  have : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (S.map F).X₁ := h₁
  have : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (S.map F).X₃ := h₃
  exact IsFiniteLocallyConstantSheaf.of_shortExact hS'

end Constructible

end AlgebraicGeometry.Scheme

end
