/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.GenericConstancy
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Sites.EpiMono

/-!
# Extensions of finite locally constant sheaves over a noetherian ring

Let `Λ` be a noetherian ring and `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` a short exact sequence of étale sheaves
of `Λ`-modules on a scheme `X`. If `F₁` and `F₃` are finite locally constant, so is `F₂`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory

open Opposite

section LocalLift

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {Λ : Type v'} [Ring Λ]
  [HasSheafify J (ModuleCat.{v'} Λ)] [J.WEqualsLocallyBijective (ModuleCat.{v'} Λ)]
  [J.HasSheafCompose (CategoryTheory.forget (ModuleCat.{v'} Λ))]
  [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{v'} Λ)]

/-- **A morphism out of a constant sheaf at a finite free module lifts locally along an
epimorphism**: given `q : (ι →₀ Λ)_C ⟶ G` with `ι` finite and an epimorphism `p : E ⟶ G`, every
object `T` has a covering sieve over whose members `U` the restriction of `q` to `J.over U`
factors through `p`. -/
theorem exists_mem_forall_exists_lift_constantSheafOverHom {ι : Type v'} [Finite ι]
    {E G : Sheaf J (ModuleCat.{v'} Λ)} (q : (constantSheaf J _).obj (ModuleCat.of Λ (ι →₀ Λ)) ⟶ G)
    (p : E ⟶ G) [Epi p] (T : C) :
    ∃ S ∈ J T, ∀ ⦃U : C⦄ (g : U ⟶ T), S g →
      ∃ s : (constantSheaf (J.over U) _).obj (ModuleCat.of Λ (ι →₀ Λ)) ⟶ E.over U,
        s ≫ (J.overPullback _ U).map p =
          constantSheafOverHom J _ U _ ≫ (J.overPullback _ U).map q := by
  classical
  let M := ModuleCat.of Λ (ι →₀ Λ)
  let η := CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)
  let t : ι → ToType (G.obj.obj (op T)) := fun k ↦
    q.hom.app (op T) (η.app (op T) (Finsupp.single k 1))
  have hp : Presheaf.IsLocallySurjective J p.hom :=
    (Sheaf.isLocallySurjective_iff_epi' (A := ModuleCat.{v'} Λ) p).2 inferInstance
  refine ⟨⨅ k, Presheaf.imageSieve p.hom (t k), J.iInf_mem _ fun k ↦ hp.imageSieve_mem (t k),
    fun U g hg ↦ ?_⟩
  have hg' (k : ι) : Presheaf.imageSieve p.hom (t k) g :=
    (iInf_le (fun k ↦ Presheaf.imageSieve p.hom (t k)) k : _) g hg
  let u : ι → ToType (E.obj.obj (op U)) := fun k ↦ Presheaf.localPreimage p.hom (t k) g (hg' k)
  have hu (k : ι) : p.hom.app (op U) (u k) = G.obj.map g.op (t k) :=
    Presheaf.app_localPreimage p.hom (t k) g (hg' k)
  let L : M ⟶ (sheafSections (J.over U) (ModuleCat Λ)).obj (op (Over.mk (𝟙 U))) |>.obj
      (E.over U) := ModuleCat.ofHom (Finsupp.linearCombination Λ u)
  refine ⟨((constantSheafAdj (J.over U) _ Over.mkIdTerminal).homEquiv M _).symm L, ?_⟩
  apply ((constantSheafAdj (J.over U) _ Over.mkIdTerminal).homEquiv M _).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right, constantSheafAdj_homEquiv_constantSheafOverHom]
  ext : 1
  refine (Finsupp.lhom_ext' fun k ↦ LinearMap.ext_ring ?_)
  change p.hom.app (op U) (Finsupp.linearCombination Λ u (Finsupp.single k 1)) =
    q.hom.app (op U) (η.app (op U) (Finsupp.single k 1))
  rw [Finsupp.linearCombination_single, one_smul, hu]
  change G.obj.map g.op (q.hom.app (op T) (η.app (op T) (Finsupp.single k 1))) = _
  erw [← NatTrans.naturality_apply q.hom, ← NatTrans.naturality_apply η]
  rfl

end LocalLift

end CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ]

/-- The middle term of a short exact sequence of sheaves of modules whose outer terms have
finitely generated stalks has finitely generated stalks. -/
theorem IsFiniteSheaf.of_shortExact
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁]
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃] :
    IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₂ where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    let Φ := (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
    have hS' := hS.map_of_exact Φ
    have := (ModuleCat.isFinitelyGenerated_iff _).1
      (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
        (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (F := S.X₁) Ω s)
    have := (ModuleCat.isFinitelyGenerated_iff _).1
      (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
        (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (F := S.X₃) Ω s)
    have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS'.exact
    have hepi : Function.Surjective (Φ.map S.g) :=
      (ModuleCat.epi_iff_surjective _).1 hS'.epi_g
    exact (ModuleCat.isFinitelyGenerated_iff _).2
      (Module.Finite.of_exact (f := (Φ.map S.f).hom) (g := (Φ.map S.g).hom) hex hepi)

section Lift

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ] [IsNoetherianRing Λ]

open Limits in
/-- If, in a short exact sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of sheaves of modules over a
noetherian ring with `F₁` and `F₃` finite locally constant, the quotient map has a "partial
section" `s : P ⟶ F₂` out of a finite locally constant sheaf `P` with `s ≫ (F₂ ⟶ F₃)` an
epimorphism, then `F₂` is locally constant: it is the cokernel of the kernel of the
epimorphism `F₁ ⊞ P ⟶ F₂`, and this kernel is identified with the kernel of `P ⟶ F₃`. -/
theorem IsLocallyConstantSheaf.of_shortExact_of_lift
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁]
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃]
    {P : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) P]
    (s : P ⟶ S.X₂) [Epi (s ≫ S.g)] :
    IsLocallyConstantSheaf S.X₂ := by
  have := hS.mono_f
  have := hS.epi_g
  let θ : S.X₁ ⊞ P ⟶ S.X₂ := biprod.desc S.f s
  have hθ : Epi θ := by
    rw [Preadditive.epi_iff_cancel_zero]
    intro Z h hh
    have hf : S.f ≫ h = 0 := by simpa [θ] using congrArg (biprod.inl ≫ ·) hh
    have hd := hS.exact.g_desc h hf
    have h0 : (s ≫ S.g) ≫ hS.exact.desc h hf = 0 := by
      rw [Category.assoc, hd]
      simpa [θ] using congrArg (biprod.inr ≫ ·) hh
    rw [← hd, (cancel_epi (s ≫ S.g)).1 (h0.trans comp_zero.symm), comp_zero]
  have hθ' : θ = biprod.fst ≫ S.f + biprod.snd ≫ s :=
    biprod.hom_ext' _ _ (by simp [θ]) (by simp [θ])
  let σ : kernel (s ≫ S.g) ⟶ S.X₁ := hS.exact.lift (kernel.ι (s ≫ S.g) ≫ s) (by simp)
  have hσ : σ ≫ S.f = kernel.ι (s ≫ S.g) ≫ s := hS.exact.lift_f _ _
  let e : kernel θ ≅ kernel (s ≫ S.g) :=
    { hom := kernel.lift _ (kernel.ι θ ≫ biprod.snd) (by
        have : biprod.snd ≫ s = θ - biprod.fst ≫ S.f := by rw [hθ']; abel
        rw [Category.assoc, ← Category.assoc biprod.snd, this, Preadditive.sub_comp,
          Preadditive.comp_sub, ← Category.assoc, kernel.condition, zero_comp]
        simp)
      inv := kernel.lift θ (biprod.lift (-σ) (kernel.ι (s ≫ S.g))) (by
        rw [hθ', Preadditive.comp_add, biprod.lift_fst_assoc, biprod.lift_snd_assoc,
          Preadditive.neg_comp, hσ, neg_add_cancel])
      hom_inv_id := by
        refine equalizer.hom_ext (biprod.hom_ext _ _ ?_ ?_)
        · rw [← cancel_mono S.f]
          simp only [Category.assoc, kernel.lift_ι, biprod.lift_fst, Preadditive.comp_neg,
            Preadditive.neg_comp, hσ, Category.id_comp, kernel.lift_ι_assoc]
          have h : kernel.ι θ ≫ (biprod.fst ≫ S.f + biprod.snd ≫ s) = 0 := by
            rw [← hθ']; exact kernel.condition θ
          rw [Preadditive.comp_add] at h
          rw [neg_eq_iff_add_eq_zero, add_comm]
          exact h
        · simp
      inv_hom_id := by
        refine equalizer.hom_ext ?_
        simp }
  have := IsFiniteLocallyConstantSheaf.kernel (s ≫ S.g)
  have : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (kernel θ) :=
    IsFiniteLocallyConstantSheaf.of_iso e.symm
  have := IsFiniteLocallyConstantSheaf.biprod (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
    (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁ P
  have := (IsLocallyConstantSheaf.kernel_and_cokernel (kernel.ι θ)).2
  let e₂ : cokernel (kernel.ι θ) ≅ S.X₂ :=
    (cokernelIsCokernel (kernel.ι θ)).coconePointUniqueUpToIso
      (Abelian.epiIsCokernelOfKernel (KernelFork.ofι _ (kernel.condition θ)) (kernelIsKernel θ))
  exact IsLocallyConstantSheaf.of_iso e₂


end Lift

section Extension

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ] [IsNoetherianRing Λ]

omit [IsNoetherianRing Λ] in
/-- A constant sheaf of `Λ`-modules with finitely generated value is finite locally constant. -/
lemma isFiniteLocallyConstantSheaf_constantSheaf (N : ModuleCat.{u + 1} Λ) [Module.Finite Λ N] :
    IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N).IsConstant
      X.smallEtaleTopology := Sheaf.isConstant_of_iso _ (Iso.refl _)
  have : IsLocallyConstantSheaf
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N) :=
    ⟨⟨⟨Cover.mkOfCovers PUnit (fun _ ↦ X) (fun _ ↦ 𝟙 X) (fun x ↦ ⟨⟨⟩, x, rfl⟩)
      (fun _ ↦ inferInstance), fun _ ↦
      (isConstant_over_iff_upperStar _ _ _).2 (Sheaf.IsConstant.upperStar (X := X) _ _ _)⟩⟩⟩
  have : IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N) :=
    ⟨fun Ω _ _ s ↦ ((ModuleCat.isFinitelyGenerated_iff N).2 inferInstance).of_iso
      ((pointSmallEtale s).sheafFiberConstantSheafIso N).symm⟩
  exact {}

open Limits in
/-- Blueprint `lemma-constructible-flc-serre`, extension clause, over a noetherian ring: **the
middle term of a short exact sequence of sheaves of modules over a noetherian ring whose outer
terms are finite locally constant is finite locally constant.** Étale locally the outer terms
are constant, at finitely generated modules `M` and `N`; on a further étale cover a free module
mapping onto `N` lifts to the middle term, which is then the cokernel of a morphism between
finite locally constant sheaves. -/
theorem IsFiniteLocallyConstantSheaf.of_shortExact_of_isNoetherianRing
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁]
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃] :
    IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₂ where
  toIsFiniteSheaf := IsFiniteSheaf.of_shortExact hS
  toIsLocallyConstantSheaf := by
    obtain ⟨𝒰₀, h𝒰₀⟩ := IsLocallyConstantSheaf.exists_cover₂ S.X₁ S.X₃
    let 𝒰 := 𝒰₀.nonemptyMembers
    have key (i : 𝒰.I₀) :
        IsLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj S.X₂) := by
      set Y := 𝒰.X i
      set g := 𝒰.f i
      let SY := S.map (Etale.upperStar (ModuleCat.{u + 1} Λ) g)
      have hSY : SY.ShortExact := hS.map_of_exact _
      have h₁ : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
          (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) SY.X₁ :=
        IsFiniteLocallyConstantSheaf.upperStar g S.X₁
      have h₃ : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
          (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) SY.X₃ :=
        IsFiniteLocallyConstantSheaf.upperStar g S.X₃
      have hC : (SY.X₃).IsConstant Y.smallEtaleTopology := (h𝒰₀ i.1).2
      obtain ⟨N, ⟨e₃⟩⟩ := SY.X₃.mem_essImage_of_isConstant
      have : IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
          (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N) :=
        IsFiniteSheaf.of_iso (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
          (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) e₃.symm
      have : Module.Finite Λ N := moduleFinite_of_isFiniteSheaf_constantSheaf (Y := Y) N
      obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := Λ) (M := N)
      let ι := ULift.{u + 1} (Fin n)
      let π : (ι →₀ Λ) →ₗ[Λ] N := Finsupp.linearCombination Λ (v ∘ ULift.down)
      have hπ : Function.Surjective π := by
        rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, Set.range_comp,
          ULift.down_surjective.range_eq, Set.image_univ, hv]
      let F := ModuleCat.of Λ (ι →₀ Λ)
      let q : (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj F ⟶ SY.X₃ :=
        (constantSheaf _ _).map (ModuleCat.ofHom π) ≫ e₃.hom
      have : Epi (ModuleCat.ofHom π) := (ModuleCat.epi_iff_surjective _).2 hπ
      have : (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).IsLeftAdjoint :=
        (constantSheafAdj _ _ terminalIsTerminal).isLeftAdjoint
      have hq : Epi q := epi_comp _ _
      have := hSY.epi_g
      obtain ⟨R, hR, hlift⟩ := exists_mem_forall_exists_lift_constantSheafOverHom
        Y.smallEtaleTopology q SY.g (Etale.mk (𝟙 Y))
      suffices h : ∀ y, IsLocallyConstantSheaf
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) ((Cover.ofSieve R hR).f y)).obj SY.X₂) from
        IsLocallyConstantSheaf.of_cover (Cover.ofSieve R hR) SY.X₂
      intro y
      set V := Cover.ofSieveObj R hR y
      obtain ⟨s, hs⟩ := hlift (Cover.ofSieveHom R hR y) (Cover.ofSieveHom_mem R hR y)
      let Φ := (Etale.overSheafEquiv V (ModuleCat.{u + 1} Λ)).functor
      let T := (SY.map (Y.smallEtaleTopology.overPullback (ModuleCat.{u + 1} Λ) V)).map Φ
      have hT : T.ShortExact := (hSY.map_of_exact _).map_of_exact _
      have hT₁ : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
          (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) T.X₁ := by
        have := IsFiniteLocallyConstantSheaf.upperStar
          (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
          (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) V.hom SY.X₁
        exact IsFiniteLocallyConstantSheaf.of_iso (overSheafEquivFunctorObjOverIso _ V SY.X₁).symm
      have hT₃ : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
          (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) T.X₃ := by
        have := IsFiniteLocallyConstantSheaf.upperStar
          (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
          (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) V.hom SY.X₃
        exact IsFiniteLocallyConstantSheaf.of_iso (overSheafEquivFunctorObjOverIso _ V SY.X₃).symm
      let P := Φ.obj ((constantSheaf (Y.smallEtaleTopology.over V) (ModuleCat.{u + 1} Λ)).obj F)
      have hP : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
          (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) P := by
        have := isFiniteLocallyConstantSheaf_constantSheaf (X := Y) F
        have := IsFiniteLocallyConstantSheaf.upperStar
          (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
          (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) V.hom
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj F)
        exact IsFiniteLocallyConstantSheaf.of_iso ((overSheafEquivFunctorObjOverIso _ V _).symm ≪≫
          Φ.mapIso (asIso (constantSheafOverHom Y.smallEtaleTopology _ V F)).symm)
      have hepi : Epi (Φ.map s ≫ T.g) := by
        change Epi (Φ.map s ≫
          Φ.map ((Y.smallEtaleTopology.overPullback (ModuleCat.{u + 1} Λ) V).map SY.g))
        rw [← Φ.map_comp, hs, Φ.map_comp]
        have : (Y.smallEtaleTopology.overPullback (ModuleCat.{u + 1} Λ) V).PreservesEpimorphisms :=
          inferInstance
        have h₁ : Epi (Φ.map (constantSheafOverHom Y.smallEtaleTopology _ V F)) := inferInstance
        have h₂ : Epi (Φ.map ((Y.smallEtaleTopology.overPullback (ModuleCat.{u + 1} Λ) V).map q)) :=
          Φ.map_epi _
        exact epi_comp _ _
      have hloc : IsLocallyConstantSheaf (Φ.obj (SY.X₂.over V)) :=
        IsLocallyConstantSheaf.of_shortExact_of_lift hT (Φ.map s)
      have := IsLocallyConstantSheaf.of_iso (overSheafEquivFunctorObjOverIso _ V SY.X₂)
      rw [Cover.ofSieve_f, Cover.ofSieveHom_left]
      exact this
    exact IsLocallyConstantSheaf.of_cover 𝒰 S.X₂


/-- **The middle term of a short exact sequence of sheaves of modules over a noetherian ring
whose outer terms are constructible is constructible**: on the common refinement of
witnessing stratifications, the pullback of the sequence to a stratum is a short exact sequence
of finite locally constant sheaves. -/
theorem IsConstructibleSheaf.of_shortExact_of_isNoetherianRing
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
  exact IsFiniteLocallyConstantSheaf.of_shortExact_of_isNoetherianRing hS'
end Extension

end AlgebraicGeometry.Scheme
