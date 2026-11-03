/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.ModuleObjects.Free

import WeilConjectures.AlgebraicGeometry.FiniteAffineProEtaleRefinement
import WeilConjectures.AlgebraicGeometry.ScalarPerfectChartTorVanishing
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.Data.Finset.Max

/-!
# Finite Tor amplitude of locally constant perfect duals

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
  sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-internal-hom.proof.md,
  paragraph 2 final sentence and paragraph 3 parenthetical
  (blueprint: lem-sfb-internal-hom-dual-tor-amplitude).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

/-- The termwise scalar extension of a coefficient complex to a pro-etale chart.
The zero-morphism preservation witness is explicit so this construction does not depend on a
file-local instance. Source: def-weil-pbc-strict-perfect-coefficient-package
(blueprint: lem-sfb-internal-hom-dual-tor-amplitude). -/
noncomputable def scalarExtensionComplex
    {Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})}
    {U : Scheme.{u}}
    (G : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ.X ⥤
      Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj Λ.X U))
    (hG : G.PreservesZeroMorphisms)
    (F : CochainComplex
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ.X) ℤ) :
    CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj Λ.X U)) ℤ :=
  by
    letI : G.PreservesZeroMorphisms := hG
    exact (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj F

/-- A finite projective module object is a retract of a finite free module object.
The maps between finite free condensed modules are matrices over `R = Λ(*)`. Thus a
retract is scalar extension of the corresponding finite projective R-module; maps between
retracts are likewise R-linear matrices. This identifies complexes of these retracts with
the termwise scalar models of the statement, including their differentials.
Source: def-pc-perfect-ring-complex and def-weil-pbc-strict-perfect-coefficient-package;
(blueprint: lem-sfb-internal-hom-dual-tor-amplitude). -/
def FiniteProjectiveCondensedModule
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (M : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ.X) : Prop :=
  ∃ n : ℕ, ∃ i : M ⟶ Mod.finiteFree Λ.X n,
    ∃ p : Mod.finiteFree Λ.X n ⟶ M, i ≫ p = 𝟙 M

/-- The relative derived internal Hom dual `RHom_B(P,B)` used in the statement.
Source: sk-def-sfb-derived-tensor-hom (blueprint: lem-sfb-internal-hom-dual-tor-amplitude). -/
noncomputable def relativeInternalHomDual
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X] (S : Scheme.{u})
    (P : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj Λ.X S))) : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj Λ.X S)) :=
  ((CondensedRing.derivedHom Λ.X S).obj (Opposite.op P)).obj
    ((DerivedCategory.singleFunctor _ 0).obj (Mod.regular (condensedRingObj Λ.X S)))

/-- Vanishing on original charts is detected by a covering refinement of those charts.
The covering sieve at a test object is given by the affine-refinement base changes;
each arrow factors through an original chart. Source: Stacks 04TQ.
(blueprint: lem-sfb-internal-hom-dual-tor-amplitude). -/
private theorem isZero_sheaf_of_refined_cover
    {S : Scheme.{u}} {I : Type*} {J : Type*}
    (U : I → S.ProEt) (α : J → I) (V : ∀ j, (U (α j)).left.Opens)
    (hcover : Presieve.ofArrows (fun j ↦ (V j).toScheme)
      (fun j ↦ (V j).ι ≫ (U (α j)).hom) ∈ Scheme.proetalePrecoverage S)
    (M : Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
    (hM : ∀ j, IsZero ((upperStar Ab.{u + 1} (U (α j)).hom).obj M)) :
    IsZero M := by
  let z : M ⟶ 0 := 0
  have hz (j : J) : IsIso
      ((localizationRestriction Ab.{u + 1} (U (α j)).hom inferInstance).map z) := by
    have : (localizationRestriction Ab.{u + 1} (U (α j)).hom inferInstance).Additive :=
      ⟨fun {_ _} f g ↦ by ext T; rfl⟩
    have h := (hM j).of_iso
      ((upperStarIsoLocalizationRestriction Ab.{u + 1} (U (α j)).hom inferInstance).app M).symm
    exact h.isIso
      ((localizationRestriction Ab.{u + 1} (U (α j)).hom inferInstance).map_isZero
        (isZero_zero _)) _
  have : IsIso z := by
    apply Sheaf.isIso_of_isIso_app_of_mem _ z
    intro T
    refine ⟨_, Scheme.ProEt.ofArrows_baseChange_mem_topology T
      (fun j ↦ (V j).ι ≫ (U (α j)).hom) hcover, ?_⟩
    rintro W f ⟨-, a, -, ⟨j⟩, rfl⟩
    apply isIso_app_of_isIso_localizationRestriction Ab.{u + 1} z
      (U (α j)).hom (hz j) W
      (a.left ≫ pullback.snd T.hom ((V j).ι ≫ (U (α j)).hom) ≫ (V j).ι)
    rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc]
    exact MorphismProperty.Over.w a
  exact (isZero_zero _).of_iso (asIso z)

/-- The empty-cover sheaf condition makes every abelian sheaf on the empty scheme zero.
Source: Stacks 098K, empty covering; the existing pro-etale terminal-sections theorem.
(blueprint: lem-sfb-internal-hom-dual-tor-amplitude). -/
private theorem isZero_sheaf_on_empty
    (S : Scheme.{u}) [IsEmpty S]
    (M : Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) : IsZero M := by
  apply Sheaf.isZero_of_isZero_obj
  intro U
  have : IsEmpty U.unop.left := ⟨fun x ↦ isEmptyElim (show S from U.unop.hom x)⟩
  exact (Scheme.ProEt.isTerminalSectionsOfIsEmpty M U.unop).isZero

/-- The dual of a pro-etale locally constant perfect complex has finite Tor amplitude.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
  sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-internal-hom.proof.md, paragraphs 2--3
(blueprint: lem-sfb-internal-hom-dual-tor-amplitude).

Proof:
1. On the empty scheme all sections of every abelian sheaf are terminal, so every
   module object is zero. Take the interval [0,0].
2. Otherwise use finite_affine_proetale_refinement to select finitely many original
   charts whose affine opens cover S. Replace the bounds of the selected scalar
   models by their minimum and maximum, then take the minimum lower endpoint and
   maximum upper endpoint over the finite nonempty index set.
3. Apply scalarPerfect_chart_tor_vanishing to each selected original chart, with
   its fixed ordered model interval. Widen its two vanishings to the common
   interval and its reflection. The bounds do not depend on the test module.
4. Apply the sheaf local-isomorphism criterion to each cohomology sheaf mapped
   to zero. The affine refinement covers every test object by base change, and
   its arrows factor through the selected original charts. Faithfulness of the
   module forgetful functor reflects zero to module objects.

The hypothesis `_hΛ` is the recorded six-case admissible coefficient predicate. Its
admissibility and the separatedness assumptions are not needed by this argument. -/
theorem internalHom_dual_tor_amplitude
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X]
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ.X)
    (P : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj Λ.X S)))
    (hP : ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S,
      ∀ i : 𝒰.I₀,
        ∃ F : CochainComplex
          (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ.X) ℤ,
          (∃ c d : ℤ, ∀ n : ℤ, n < c ∨ d < n → IsZero (F.X n)) ∧
          (∀ n : ℤ, FiniteProjectiveCondensedModule Λ (F.X n)) ∧
          ∃ hG : ((upperStarFromPoint (𝒰.X i)).mapMod Λ.X).PreservesZeroMorphisms,
          Nonempty
            (((CondensedRing.upperStar Λ.X (𝒰.f i)).mapDerivedCategory).obj P ≅
              DerivedCategory.Q.obj
                (scalarExtensionComplex (Λ := Λ) (U := 𝒰.X i)
                  ((upperStarFromPoint (𝒰.X i)).mapMod Λ.X) hG F))) :
    ∃ a b : ℤ, a ≤ b ∧
      (∀ N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
          (condensedRingObj Λ.X S),
        ∀ q : ℤ, q < a ∨ b < q → IsZero
          ((DerivedCategory.homologyFunctor _ q).obj
            (((CondensedRing.derivedTensor Λ.X S).obj P).obj
              ((DerivedCategory.singleFunctor _ 0).obj N)))) ∧
      (∀ N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
          (condensedRingObj Λ.X S),
        ∀ q : ℤ, q < -b ∨ -a < q → IsZero
          ((DerivedCategory.homologyFunctor _ q).obj
            (((CondensedRing.derivedTensor Λ.X S).obj
              (relativeInternalHomDual Λ S P)).obj
              ((DerivedCategory.singleFunctor _ 0).obj N)))) ∧
      (IsEmpty S → a = 0 ∧ b = 0) := by
  classical
  by_cases hS : IsEmpty S
  · let := hS
    refine ⟨0, 0, le_rfl, ?_, ?_, fun _ ↦ ⟨rfl, rfl⟩⟩
    · intro N q _
      apply (IsZero.iff_id_eq_zero _).2
      apply (Mod.forget _).map_injective
      exact (isZero_sheaf_on_empty S _).eq_of_src _ _
    · intro N q _
      apply (IsZero.iff_id_eq_zero _).2
      apply (Mod.forget _).map_injective
      exact (isZero_sheaf_on_empty S _).eq_of_src _ _
  · have : Nonempty S := not_isEmpty_iff.mp hS
    have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace
      (S ↘ Spec (.of k))
    obtain ⟨𝒰, h𝒰⟩ := hP
    choose F hb hp hG he using h𝒰
    choose lo hi hF using hb
    have (i : 𝒰.I₀) : WeaklyEtale (𝒰.f i) := 𝒰.forgetQc.map_prop i
    let U : 𝒰.I₀ → S.ProEt := fun i ↦ Scheme.ProEt.mk (𝒰.f i)
    obtain ⟨n, hn, α, V, _, hcover⟩ :=
      Scheme.finite_affine_proetale_refinement S 𝒰.I₀ U 𝒰.mem₀
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    let l : Fin n → ℤ := fun j ↦ min (lo (α j)) (hi (α j))
    let h : Fin n → ℤ := fun j ↦ max (lo (α j)) (hi (α j))
    obtain ⟨ja, _, hja⟩ := Finset.exists_min_image Finset.univ l Finset.univ_nonempty
    obtain ⟨jb, _, hjb⟩ := Finset.exists_max_image Finset.univ h Finset.univ_nonempty
    have hlh (j : Fin n) : l j ≤ h j := min_le_max
    have hab : l ja ≤ h jb := (hlh ja).trans (hjb ja (Finset.mem_univ _))
    have hlocal (j : Fin n) := scalarPerfect_chart_tor_vanishing Λ (𝒰.f (α j)) P
      (F (α j)) (l j) (h j) (hlh j)
      (fun q hq ↦ hF (α j) q (by
        rcases hq with hq | hq
        · exact Or.inl (hq.trans_le (min_le_left _ _))
        · exact Or.inr ((le_max_right _ _).trans_lt hq)))
      (hp (α j)) (hG (α j)) (he (α j))
    refine ⟨l ja, h jb, hab, ?_, ?_, fun he ↦ (hS he).elim⟩
    · intro N q hq
      apply (IsZero.iff_id_eq_zero _).2
      apply (Mod.forget _).map_injective
      have hz := isZero_sheaf_of_refined_cover U α V hcover
        (((DerivedCategory.homologyFunctor _ q).obj
          (((CondensedRing.derivedTensor Λ.X S).obj P).obj
            ((DerivedCategory.singleFunctor _ 0).obj N))).X) (fun j ↦ ?_)
      · exact hz.eq_of_src _ _
      · apply (hlocal j N q).1
        rcases hq with hq | hq
        · exact Or.inl (hq.trans_le (hja j (Finset.mem_univ _)))
        · exact Or.inr ((hjb j (Finset.mem_univ _)).trans_lt hq)
    · intro N q hq
      apply (IsZero.iff_id_eq_zero _).2
      apply (Mod.forget _).map_injective
      have hz := isZero_sheaf_of_refined_cover U α V hcover
        (((DerivedCategory.homologyFunctor _ q).obj
          (((CondensedRing.derivedTensor Λ.X S).obj (relativeInternalHomDual Λ S P)).obj
            ((DerivedCategory.singleFunctor _ 0).obj N))).X) (fun j ↦ ?_)
      · exact hz.eq_of_src _ _
      · apply (hlocal j N q).2
        have h₁ := hja j (Finset.mem_univ _)
        have h₂ := hjb j (Finset.mem_univ _)
        omega

end AlgebraicGeometry.ProEtale
