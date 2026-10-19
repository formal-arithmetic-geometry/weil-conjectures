/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q115
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Pi.Basic
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Constructibility of a finite clopen componentwise constant module sheaf

Source: literature/stacks-project/etale-cohomology.tex, Tags 03RU and 03RW,
and the blueprint proof of lem-fin-normal-open-lisse-image
(blueprint: lem-fin-normal-clopen-constructible-module).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The componentwise product of the direct images of finite constant module sheaves.
Source: Stacks Project, Etale Cohomology, Tags 03RU and 03RW; this is the displayed
formula in lem-fin-normal-clopen-constructible-module
(blueprint: lem-fin-normal-clopen-constructible-module). -/
noncomputable def finiteNormalClopenConstantModuleSheaf
    {Λ : Type (u + 1)} [CommRing Λ]
    {Y : Scheme.{u}} {r : ℕ} (C : Fin r → Scheme.{u})
    (ι : ∀ a : Fin r, C a ⟶ Y) (M : Fin r → ModuleCat.{u + 1} Λ) :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (Pi.functor (Fin r)).obj
    ((Functor.pi (fun a ↦ Etale.lowerStar (ModuleCat.{u + 1} Λ) (ι a))).obj
      (fun a ↦
        (constantSheaf (C a).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M a)))

private lemma clopenCofanGeometry
    {Y : Scheme.{u}} {r : ℕ} (C : Fin r → Scheme.{u})
    (ι : ∀ a : Fin r, C a ⟶ Y) (hc : IsColimit (Cofan.mk Y ι)) :
    (⋃ a, Set.range (ι a)) = Set.univ ∧
      Pairwise (fun a b ↦ Disjoint (Set.range (ι a)) (Set.range (ι b))) := by
  let e : (∐ C) ≅ Y := (coproductIsCoproduct C).coconePointUniqueUpToIso hc
  have he (a : Fin r) : Sigma.ι C a ≫ e.hom = ι a := by
    exact (coproductIsCoproduct C).comp_coconePointUniqueUpToIso_hom hc ⟨a⟩
  constructor
  · apply Set.eq_univ_of_forall
    intro y
    obtain ⟨a, x, hx⟩ := (sigmaOpenCover C).exists_eq (e.inv y)
    refine Set.mem_iUnion.mpr ⟨a, x, ?_⟩
    have h' : (ι a) x = e.hom (e.inv y) := by
      calc
        (ι a) x = e.hom (Sigma.ι C a x) := by rw [← Scheme.Hom.comp_apply, he]
        _ = e.hom (e.inv y) := congrArg (fun z ↦ e.hom z) hx
    exact h'.trans ((homeoOfIso e).apply_symm_apply y)
  · intro a b hab
    apply Set.disjoint_iff_forall_ne.mpr
    rintro _ ⟨x, rfl⟩ _ ⟨z, rfl⟩ hxz
    have h : Sigma.ι C a x = Sigma.ι C b z := by
      apply e.hom.isOpenEmbedding.injective
      simpa only [← Scheme.Hom.comp_apply, he] using hxz
    exact hab (congrArg Sigma.fst ((sigmaι_eq_iff C a b x z).mp h))

private lemma restrictionPushforwardZero
    {Λ : Type (u + 1)} [CommRing Λ]
    {U V Y : Scheme.{u}} (i : U ⟶ Y) (j : V ⟶ Y)
    [IsOpenImmersion i] (h : Disjoint (Set.range i) (Set.range j))
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsZero ((Etale.openImmersionRestriction (ModuleCat.{u + 1} Λ) i).obj
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) j).obj F)) := by
  apply Sheaf.isZero_of_isZero_obj
  intro T
  let b := (MorphismProperty.Over.map ⊤ (inferInstance : Etale i)).obj T.unop
  let P := (MorphismProperty.Over.pullback @Etale ⊤ j).obj b
  have : IsEmpty P.left := by
    refine ⟨fun z ↦ ?_⟩
    have hw := congrArg (fun f : P.left ⟶ Y ↦ f z) (pullback.condition (f := b.hom) (g := j))
    apply Set.disjoint_iff_forall_ne.mp h
      ⟨T.unop.hom (pullback.fst b.hom j z), rfl⟩
      ⟨pullback.snd b.hom j z, rfl⟩
    change i (T.unop.hom (pullback.fst b.hom j z)) = j (pullback.snd b.hom j z) at hw
    exact hw
  exact (Scheme.Etale.isTerminalSectionsOfIsEmpty F P).isZero

private lemma productIsoSingle
    {D : Type*} [Category D] [HasZeroMorphisms D]
    {I : Type*} (F : I → D) [HasProduct F]
    (a : I) (h : ∀ b, b ≠ a → IsZero (F b)) : Nonempty ((∏ᶜ F) ≅ F a) := by
  classical
  let f : F a ⟶ ∏ᶜ F := Pi.lift (fun b ↦ if e : b = a then eqToHom (congrArg F e.symm)
    else 0)
  refine ⟨⟨Pi.π F a, f, ?_, ?_⟩⟩
  · apply Pi.hom_ext
    intro b
    by_cases e : b = a
    · subst b
      simp [f]
    · exact (h b e).eq_of_tgt _ _
  · simp [f]

/-- A finite disjoint clopen coproduct of schemes carrying finite constant module values
is constructible in both the module-sheaf and general constructibility formulations.
The component restrictions are identified with the specified constant sheaves.

Proof. The coproduct legs are clopen and form a finite covering. On the a-th leg,
the upper-star restriction of the componentwise product has only the a-th nonzero
factor, hence is the constant sheaf with value M a; the empty product gives the zero
sheaf when the index is empty. These identifications provide the finite locally constant
models on the clopen stratification. The same stratification satisfies both
constructibility predicates, and the component projections give the displayed
isomorphisms. This uses def-weil-pbc-etale-site,
def-weil-sheaf-of-modules-category, lem-weil-pbc-open-immersion-etale,
lem-weil-pbc-etale-inverse-image-restriction,
lem-weil-pbc-module-abelian-inverse-image-comparison,
lem-weil-pbc-finite-locally-constant-module-values,
def-constructible-stratification, def-weil-constructible-subset,
def-weil-pbc-etale-constructible-sheaf, and def-constructible-constructible.
Source: literature/stacks-project/etale-cohomology.tex, Tags 03RU and 03RW, and the
blueprint proof of lem-fin-normal-open-lisse-image
(blueprint: lem-fin-normal-clopen-constructible-module). -/
theorem finite_normal_clopen_constructible_module
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (Y : Scheme.{u}) (r : ℕ) (C : Fin r → Scheme.{u})
    (ι : ∀ a : Fin r, C a ⟶ Y) (hc : IsColimit (Cofan.mk Y ι))
    (M : Fin r → ModuleCat.{u + 1} Λ)
    (hM : ∀ a : Fin r, Finite (M a))
    (hopen : ∀ a : Fin r, IsOpenImmersion (ι a))
    (hclosed : ∀ a : Fin r, IsClosedImmersion (ι a)) :
    IsConstructibleEtaleModuleSheaf
        (finiteNormalClopenConstantModuleSheaf C ι M) ∧
      IsConstructibleSheaf (finiteNormalClopenConstantModuleSheaf C ι M) ∧
      ∀ a : Fin r, Nonempty
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (ι a)).obj
          (finiteNormalClopenConstantModuleSheaf C ι M) ≅
          (constantSheaf (C a).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M a)) := by
  classical
  let : ∀ a, IsOpenImmersion (ι a) := hopen
  let : ∀ a, IsClosedImmersion (ι a) := hclosed
  obtain ⟨hcover, hdisj⟩ := clopenCofanGeometry C ι hc
  let F (a : Fin r) :=
    (constantSheaf (C a).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M a)
  let G (a : Fin r) := (Etale.lowerStar (ModuleCat.{u + 1} Λ) (ι a)).obj (F a)
  have he (a : Fin r) : Nonempty
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (ι a)).obj
        (finiteNormalClopenConstantModuleSheaf C ι M) ≅ F a) := by
    let R := Etale.openImmersionRestriction (ModuleCat.{u + 1} Λ) (ι a)
    have hz (b : Fin r) (hba : b ≠ a) : IsZero (R.obj (G b)) :=
      restrictionPushforwardZero (ι a) (ι b) (hdisj hba.symm) (F b)
    obtain ⟨e⟩ := productIsoSingle (fun b ↦ R.obj (G b)) a hz
    exact ⟨(Etale.upperStarIsoOpenImmersionRestriction
        (ModuleCat.{u + 1} Λ) (ι a)).app _ ≪≫
      PreservesProduct.iso R G ≪≫ e ≪≫
      asIso ((Etale.openImmersionRestrictionLowerStarAdjunction
        (ModuleCat.{u + 1} Λ) (ι a)).counit.app (F a))⟩
  let S : Stratification Y :=
    { n := r
      stratum a := Set.range (ι a)
      isLocallyClosed_stratum a := (ι a).isOpenEmbedding.isOpen_range.isLocallyClosed
      isConstructible_stratum a := by
        apply IsRetrocompact.isConstructible (ι a).isOpenEmbedding.isOpen_range
        intro U hU _
        exact hU.inter_left (ι a).isClosedEmbedding.isClosed_range
      iUnion_stratum_eq_univ := hcover
      pairwise_disjoint_stratum := hdisj
      domain := C
      immersion := ι
      isImmersion a := inferInstance
      range_immersion _ := rfl }
  have hfinite (a : Fin r) :
      ∃ d : LocallyConstantDatum
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (ι a)).obj
          (finiteNormalClopenConstantModuleSheaf C ι M)), ∀ i : d.cover.I₀,
        ∃ N : ModuleCat.{u + 1} Λ, Finite N ∧
          Nonempty (((Etale.upperStar (ModuleCat.{u + 1} Λ) (ι a)).obj
              (finiteNormalClopenConstantModuleSheaf C ι M)).over
              (d.cover.etalePrecoverageToEtale i) ≅
            (constantSheaf ((C a).smallEtaleTopology.over
              (d.cover.etalePrecoverageToEtale i)) (ModuleCat.{u + 1} Λ)).obj N) := by
    let H := (Etale.upperStar (ModuleCat.{u + 1} Λ) (ι a)).obj
      (finiteNormalClopenConstantModuleSheaf C ι M)
    obtain ⟨e⟩ := he a
    have hconst : H.IsConstant (C a).smallEtaleTopology :=
      Sheaf.isConstant_of_iso (C a).smallEtaleTopology e
    have : etalePrecoverage.{u}.HasIsos :=
      inferInstanceAs (precoverage @Etale).HasIsos
    let d : LocallyConstantDatum H :=
      ⟨.singleton (𝟙 (C a)) (Precoverage.mem_coverings_of_isIso _),
        fun _ ↦ by have := hconst; exact H.isConstant_over _⟩
    refine ⟨d, fun i ↦ ⟨M a, hM a, ⟨?_⟩⟩⟩
    exact ((C a).smallEtaleTopology.overPullback (ModuleCat.{u + 1} Λ)
        (d.cover.etalePrecoverageToEtale i)).mapIso e ≪≫
      ((C a).smallEtaleTopology.overPullbackConstantSheafIso
        (ModuleCat.{u + 1} Λ) (d.cover.etalePrecoverageToEtale i)).app (M a)
  refine ⟨⟨S, hfinite⟩, ⟨S, ?_⟩, he⟩
  intro a
  exact (finite_locally_constant_module_values_iff _).1.mp (hfinite a)

end AlgebraicGeometry.Scheme
