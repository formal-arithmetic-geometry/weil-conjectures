/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import Sheaf.CategoryTheory.SiteCechComplex
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Category.Grp.EpiMono
import Sheaf.AlgebraicGeometry.ModuleInjectiveOpenCoverCechAcyclic
import Sheaf.AlgebraicGeometry.ModuleOpenRestrictionInjectives
import Sheaf.AlgebraicGeometry.ModuleSectionsSurjectiveOfCechH1
import Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives
import Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence

/-!
# Module cohomology vanishing from cofinal basis Čech coverings

Source: Stacks Project, Cohomology of Sheaves, Lemma 20.11.9, Tag 01EW,
with restriction to open subschemes as in Tag 01E1
(blueprint: lem-weil-pbc-module-cech-vanishing-basis).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option linter.unusedVariables false in
/-- Higher module cohomology vanishes on a basis if higher Čech cohomology vanishes
for a cofinal collection of coverings whose members and finite nonempty intersections
belong to the basis. The type `K` indexes the collection `Cov`; `U c`, `V c`, and
`hom c` give its target, family of opens, and inclusion arrows. `S c` is any choice
of the iterated fibre products defining its Čech complex.

Source: Stacks Project, Cohomology of Sheaves, Lemma 20.11.9 (01EW), and 01E1
(blueprint: lem-weil-pbc-module-cech-vanishing-basis).

Proof:
1. Fix the basis and collection and induct on positive degree, simultaneously for
all modules with vanishing higher Čech cohomology on this collection.
2. Embed such a module G into an injective I, using
lem-weil-pbc-scheme-modules-enough-injectives and def-sp-injective-resolutions.
Take Q = I/G, giving a short exact sequence (def-weil-pbc-exact-sequence).
3. By lem-weil-pbc-module-injective-open-cover-cech-acyclic (01EP), I also has
vanishing higher Čech cohomology on every covering in the collection.
4. Kernels are sectionwise. On each basis open W, cofinality and the vanishing
of Čech H¹(G) give surjectivity I(W) → Q(W), by
lem-weil-pbc-module-ses-cech-h1-surjective (01EU).
5. All intersection opens of a covering belong to the basis. Thus products of
these section sequences give a short exact sequence of Čech complexes, using
functoriality of def-weil-pbc-site-cech-complex and
lem-weil-pbc-cochain-complexes-degreewise-exact.
6. Its long exact cohomology sequence (lem-weil-pbc-complex-ses-homology-long-exact)
and the vanishing for G and I show that Q has the same Čech vanishing property.
7. Restriction to an open is exact and preserves injectives, by
lem-weil-pbc-module-open-restriction-injectives. Its sections are the original
sections by lem-weil-pbc-module-restriction-open-immersion-colimits (01E1).
8. Compute module cohomology on the open subscheme as right derived global sections
(def-sc-ringed-space-module-cohomology, def-sp-left-exact-additive), with enough
injectives supplied by lem-sc-ringed-space-module-sheaves-enough-injectives.
9. Use lem-weil-pbc-derived-functor-long-exact and
lem-weil-pbc-derived-functor-injective-vanishing. In degree one, surjectivity on
sections and Mathlib's rightDerivedZeroIsoSelf give vanishing.
In degree p ≥ 2, apply the induction hypothesis to Q in degree p-1 and shift
along the long exact sequence. Apply this result to F. -/
theorem isZero_moduleCohomology_restrict_of_cech_basis
    (X : Scheme.{u}) (F : X.Modules) (B : Set X.Opens)
    (hB : IsTopologicalBasis ((fun W : X.Opens => (W : Set X)) '' B))
    (K : Type w) (J : K → Type (max u v)) (U : K → X.Opens)
    (V : ∀ c : K, J c → X.Opens) (hom : ∀ (c : K) (j : J c), V c j ⟶ U c)
    (S : ∀ c : K, SiteCechComplex (V c) (hom c))
    (hcover : ∀ c : K, iSup (V c) = U c)
    (hbase : ∀ c : K, U c ∈ B ∧ (∀ j : J c, V c j ∈ B) ∧
      ∀ (p : ℕ) (t : Fin (p + 1) → J c), (⨅ k, V c (t k)) ∈ B)
    (hcofinal : ∀ (W : X.Opens), W ∈ B →
      ∀ (A : Type (max u v)) (Z : A → X.Opens), iSup Z = W →
        ∃ c : K, U c = W ∧ ∀ j : J c, ∃ a : A, V c j ≤ Z a)
    (hvanish : ∀ (c : K) (p : ℕ), 0 < p →
      IsZero (((S c).cohomologyFunctor p).obj F.val.presheaf)) :
    ∀ (p : ℕ), 0 < p → ∀ W : X.Opens, W ∈ B →
      IsZero ((RingedSpace.moduleCohomology W.toScheme.toRingedSpace p).obj
        ((restrictFunctor W.ι).obj F)) := by
  classical
  -- Cofinality and the intersection condition suffice for this dimension-shifting proof.
  let : EnoughInjectives X.Modules := enoughInjectives X
  let : Preadditive (TopCat.Presheaf AddCommGrpCat.{u} X) :=
    inferInstanceAs (Preadditive (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}))
  let : Abelian (TopCat.Presheaf AddCommGrpCat.{u} X) :=
    inferInstanceAs (Abelian (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}))
  let : (toPresheaf X).Additive :=
    inferInstanceAs ((SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.toPresheaf X.ringCatSheaf.obj).Additive)
  let T : X.Modules ⥤ (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) := toPresheaf X
  let : T.Additive := inferInstanceAs ((toPresheaf X).Additive)
  let : PreservesLimits T := inferInstanceAs (PreservesLimits (toPresheaf X))
  let P (G : X.Modules) : Prop :=
    ∀ (c : K) (p : ℕ), 0 < p →
      IsZero (((S c).cohomologyFunctor p).obj G.val.presheaf)
  have hsurj (A : ShortComplex X.Modules) (hA : A.ShortExact) (hG : P A.X₁)
      (W : X.Opens) (hW : W ∈ B) :
      Function.Surjective (A.g.val.app (op W)) := by
    let Cov : ∀ (I : Type (max u v)) (Z : I → X.Opens),
        (∀ i, Z i ≤ W) → Prop := fun I Z _ ↦
      ∃ c : K, ∃ e : J c = I, (e ▸ V c) = Z ∧ U c = W
    apply Scheme.module_sections_surjective_of_cech_h1_vanishing X A hA W Cov
    · intro I Z hZ hCov x hx
      obtain ⟨c, rfl, rfl, hU⟩ := hCov
      rw [← hU, ← hcover c] at hx
      exact Opens.mem_iSup.mp hx
    · intro I Z hZ hc
      have hZW : iSup Z = W := by
        apply le_antisymm (iSup_le hZ)
        intro x hx
        obtain ⟨i, hi⟩ := hc x hx
        exact Opens.mem_iSup.mpr ⟨i, hi⟩
      obtain ⟨c, hU, href⟩ := hcofinal W hW I Z hZW
      refine ⟨J c, V c, ?_, ⟨c, rfl, rfl, hU⟩, href⟩
      intro j
      rw [← hU]
      exact leOfHom (hom c j)
    · intro I Z hZ hCov f C
      obtain ⟨c, rfl, rfl, hU⟩ := hCov
      subst W
      have hf : f = hom c := funext fun j ↦ Subsingleton.elim _ _
      subst f
      obtain ⟨e, _⟩ := C.comparison_exists (S c)
      exact (hG c 1 (by decide)).of_iso
        ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) 1).mapIso
          (e.app A.X₁.val.presheaf))
  have hfibre (c : K) (n : ℕ) (t : Fin (n + 1) → J c) :
      (S c).W n t = ⨅ k, V c (t k) := by
    apply le_antisymm
    · exact le_iInf fun k ↦ leOfHom ((S c).pr n t k)
    · obtain ⟨a, _, _⟩ := (S c).universal n t (⨅ k, V c (t k))
        (fun k ↦ homOfLE (iInf_le (fun k ↦ V c (t k)) k))
        (fun _ ↦ Subsingleton.elim _ _)
      exact leOfHom a
  have hquot (A : ShortComplex X.Modules) (hA : A.ShortExact)
      (h₁ : P A.X₁) (h₂ : P A.X₂) : P A.X₃ := by
    intro c p hp
    have : Mono A.f := hA.mono_f
    have hAT : (A.map T).Exact :=
      hA.exact.map_of_mono_of_preservesKernel T inferInstance inferInstance
    let C : (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
        CochainComplex AddCommGrpCat.{max u v} ℕ := (S c).complexFunctor
    have hC : ((A.map T).map C).ShortExact := by
      apply HomologicalComplex.shortExact_of_degreewise_shortExact
      intro n
      refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
      · apply (ShortComplex.ab_exact_iff_function_exact _).mpr
        exact (S c).degreewise_exact _ hAT n
      · apply (AddCommGrpCat.mono_iff_injective _).mpr
        intro a b hab
        funext t
        exact (AddCommGrpCat.mono_iff_injective
          ((T.map A.f).app (op ((S c).W n t)))).mp
            inferInstance (congrFun hab t)
      · apply (AddCommGrpCat.epi_iff_surjective _).mpr
        intro a
        have hb (t : Fin (n + 1) → J c) : (S c).W n t ∈ B := by
          rw [hfibre]
          exact (hbase c).2.2 n t
        choose b hb using fun t ↦ hsurj A hA h₁ ((S c).W n t) (hb t) (a t)
        exact ⟨b, funext hb⟩
    have h := hC.homology_exact₃ p (p + 1) (by simp)
    exact h.isZero_X₂_iff.mpr
      ⟨(h₂ c p hp).eq_of_src _ _,
        (h₁ c (p + 1) (Nat.zero_lt_succ p)).eq_of_tgt _ _⟩
  have hrestrict (U : X.Opens) :
      (∀ (S : ShortComplex X.Modules), S.ShortExact →
        (S.map (restrictFunctor U.ι)).ShortExact) ∧
      (∀ (I : X.Modules), Injective I → Injective ((restrictFunctor U.ι).obj I)) := by
    let O := SheafOfModules.overFunctor.{u} X.ringCatSheaf U
    let R := restrictFunctor U.ι
    let : O.Additive := (module_open_restriction_injectives X U).1
    let : R.Additive := ⟨by intros; rfl⟩
    have hO := (module_open_restriction_injectives X U).2.1
    let : O.PreservesMonomorphisms := Functor.preservesMonomorphisms_of_map_exact O hO
    let : O.PreservesEpimorphisms := Functor.preservesEpimorphisms_of_map_exact O hO
    constructor
    · intro S hS
      have : Mono S.f := hS.mono_f
      have : Epi S.g := hS.epi_g
      have hSO : (S.map O).ShortExact :=
        { exact := hO S hS.exact
          mono_f := by change Mono (O.map S.f); infer_instance
          epi_g := by change Epi (O.map S.g); infer_instance }
      have hSOE := hSO.map_of_exact (overEquiv U).functor
      apply ShortComplex.shortExact_of_iso (S.mapNatIso (overFunctorEquiv U))
      exact hSOE
    · intro I hI
      let : Injective (O.obj I) := (module_open_restriction_injectives X U).2.2.1 I hI
      have h := (overEquiv U).map_injective_iff (O.obj I)
      have h' : Injective ((overEquiv U).functor.obj (O.obj I)) := h.mpr inferInstance
      exact Injective.of_iso ((overFunctorEquiv U).app I) h'
  have hvan : ∀ q : ℕ, ∀ G : X.Modules, P G → ∀ W : X.Opens, W ∈ B →
      IsZero ((RingedSpace.moduleCohomology W.toScheme.toRingedSpace (q + 1)).obj
        ((restrictFunctor W.ι).obj G)) := by
    intro q
    induction q with
    | zero =>
      intro G hG W hU
      let A := ShortComplex.mk (Injective.ι G) (cokernel.π (Injective.ι G))
        (cokernel.condition _)
      have hS : A.ShortExact := .mk' (ShortComplex.exact_cokernel _)
        inferInstance inferInstance
      let E := RingedSpace.globalSectionsFunctor W.toScheme.toRingedSpace
      let : PreservesFiniteLimits E :=
        inferInstanceAs (PreservesFiniteLimits
          (SheafOfModules.evaluation (moduleRings W.toScheme.toRingedSpace)
            (Opposite.op ⊤)))
      let R := restrictFunctor W.ι
      let : R.Additive := ⟨by intros; rfl⟩
      have hRS := (hrestrict W).1 A hS
      let : EnoughInjectives (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) :=
        (RingedSpace.moduleSheaves_abelian_enoughInjectives W.toScheme.toRingedSpace).2
      let : Injective (R.obj A.X₂) := (hrestrict W).2 A.X₂ inferInstance
      obtain ⟨δ, _, hall⟩ := hRS.exists_rightDerived_full_long_exact E
      obtain ⟨_, w₁, w₂, h₁, h₂⟩ := hall 0
      have hepi : Epi (E.map (R.map A.g)) := by
        apply (ModuleCat.epi_iff_surjective _).mpr
        change Function.Surjective (A.g.val.app (Opposite.op (W.ι ''ᵁ ⊤)))
        have htop : W.ι ''ᵁ ⊤ = W := by simp
        rw [htop]
        exact hsurj A hS hG W hU
      have hepi' : Epi ((E.rightDerived 0).map (R.map A.g)) := by
        rw [← NatIso.naturality_2 E.rightDerivedZeroIsoSelf (R.map A.g)]
        infer_instance
      exact h₂.isZero_X₂_iff.mpr ⟨h₁.epi_f_iff.mp hepi',
        (E.isZero_rightDerived_obj_injective_succ 0 (R.obj A.X₂)).eq_of_tgt _ _⟩
    | succ q ih =>
      intro G hG W hU
      let A := ShortComplex.mk (Injective.ι G) (cokernel.π (Injective.ι G))
        (cokernel.condition _)
      have hS : A.ShortExact := .mk' (ShortComplex.exact_cokernel _)
        inferInstance inferInstance
      have hI : P A.X₂ := by
        intro c p hp
        exact module_injective_open_cover_cech_acyclic A.X₂ (U c) (J c) (V c)
          (fun j ↦ leOfHom (hom c j)) (hcover c) (S c) p hp
      let E := RingedSpace.globalSectionsFunctor W.toScheme.toRingedSpace
      let : PreservesFiniteLimits E :=
        inferInstanceAs (PreservesFiniteLimits
          (SheafOfModules.evaluation (moduleRings W.toScheme.toRingedSpace)
            (Opposite.op ⊤)))
      let R := restrictFunctor W.ι
      let : R.Additive := ⟨by intros; rfl⟩
      have hRS := (hrestrict W).1 A hS
      let : EnoughInjectives (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) :=
        (RingedSpace.moduleSheaves_abelian_enoughInjectives W.toScheme.toRingedSpace).2
      let : Injective (R.obj A.X₂) := (hrestrict W).2 A.X₂ inferInstance
      obtain ⟨δ, _, hall⟩ := hRS.exists_rightDerived_full_long_exact E
      obtain ⟨_, w₁, w₂, _, h₂⟩ := hall (q + 1)
      exact h₂.isZero_X₂_iff.mpr
        ⟨(ih A.X₃ (hquot A hS hG hI) W hU).eq_of_src _ _,
          (E.isZero_rightDerived_obj_injective_succ (q + 1) (R.obj A.X₂)).eq_of_tgt _ _⟩
  intro p hp W hW
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  exact hvan q F hvanish W hW

end AlgebraicGeometry.Scheme.Modules
