module
public import Sheaf.RingTheory.GlobalDimension
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Homology.Augment
@[expose] public section
universe u v
open CategoryTheory
namespace ModuleCat
/-- One component of Stacks 065R. The induction on `n` starts at `n = 0`, where a
resolution of length zero is equivalent to projectivity and the Ext-one criterion gives
vanishing in every positive degree. For the successor step, take the kernel of a
projective epimorphism onto `X`; its resolution bound drops by one. The contravariant
long exact Ext sequence for the resulting short exact sequence identifies the relevant
Ext group of `X` with a neighboring Ext group of the kernel, while Ext of the projective
term vanishes. This proves the forward implication. Conversely, choose the canonical
free module surjecting onto `X`; the same long exact sequence and the vanishing
hypothesis give the required vanishing for the kernel, so the induction hypothesis
provides its shorter resolution, which is spliced with the free epimorphism. The
construction is carried out in `ModuleCat` and uses `HasExt.standard` only to select the
standard small Ext model.
Source: Stacks Project, Algebra, Lemma 065R.
(blueprint: lem-weil-pbc-projective-resolution-ext-degree). -/
theorem projective_resolution_ext_degree
    {R : Type u} [CommRing R] (X : ModuleCat.{max u v} R) (n : ℕ) :
    (HasProjectiveResolutionLE X n ↔
      ∀ Y : ModuleCat.{max u v} R,
        Subsingleton
          (@Abelian.Ext _ _ _ (HasExt.standard (ModuleCat.{max u v} R)) X Y (n + 1))) := by
  let := HasExt.standard (ModuleCat.{max u v} R)
  constructor
  · rintro ⟨P, hP⟩ Y
    refine ⟨fun a b ↦ ?_⟩
    have hz (a : Abelian.Ext X Y (n + 1)) : a = 0 := by
      obtain ⟨f, hf, rfl⟩ := P.extMk_surjective a (n + 2) (by omega)
      have hfzero : f = 0 := (hP (n + 1) (by omega)).eq_of_src _ _
      subst f
      exact P.extMk_zero _ _
    rw [hz a, hz b]
  · intro h
    induction n generalizing X with
    | zero =>
      have : Projective X := projective_iff_subsingleton_ext_one.mpr (fun {Y} ↦ h Y)
      refine ⟨ProjectiveResolution.self X, fun i hi ↦ ?_⟩
      exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
    | succ n ih =>
      let S := ShortComplex.mk _ _ (Limits.kernel.condition (Projective.π X))
      have hS : S.ShortExact := { exact := ShortComplex.exact_kernel (Projective.π X) }
      have hK : ∀ Y : ModuleCat.{max u v} R,
          Subsingleton (Abelian.Ext S.X₁ Y (n + 1)) := by
        intro Y
        refine ⟨fun a b ↦ ?_⟩
        have hz (a : Abelian.Ext S.X₁ Y (n + 1)) : a = 0 := by
          obtain ⟨e, he⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS Y a
            (n₁ := n + 1 + 1) (by omega) ((h Y).elim _ _)
          rw [← he, Abelian.Ext.eq_zero_of_projective e, Abelian.Ext.comp_zero]
        rw [hz a, hz b]
      obtain ⟨Q, hQ⟩ := ih S.X₁ hK
      have := hS.mono_f
      have := hS.epi_g
      let δ := Q.π.f 0 ≫ S.f
      have w : Q.complex.d 1 0 ≫ δ = 0 := by
        simp [δ, ← Category.assoc]
      let K := Q.complex.augment δ w
      have hδ : K.d 1 0 ≫ S.g = 0 := by
        simp [K, δ, Category.assoc]
      let π := (ChainComplex.toSingle₀Equiv K S.X₃).symm ⟨S.g, hδ⟩
      have hzero : (ShortComplex.mk δ S.g hδ).Exact := by
        let φ : ShortComplex.mk δ S.g hδ ⟶ S :=
          { τ₁ := Q.π.f 0, τ₂ := 𝟙 _, τ₃ := 𝟙 _ }
        exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hS.exact
      have hone : (ShortComplex.mk (Q.complex.d 1 0) δ w).Exact := by
        let φ : ShortComplex.mk _ _ Q.complex_d_comp_π_f_zero ⟶
            ShortComplex.mk (Q.complex.d 1 0) δ w :=
          { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := S.f }
        apply (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
        exact ShortComplex.exact_of_g_is_cokernel _ Q.isColimitCokernelCofork
      have hπ : QuasiIso π := ⟨fun i ↦ by
        cases i with
        | zero =>
          rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
          · exact ⟨hzero, by change Epi S.g; infer_instance⟩
          all_goals rfl
        | succ i =>
          rw [quasiIsoAt_iff_exactAt']
          · rw [HomologicalComplex.exactAt_iff' K (i + 2) (i + 1) i
              (by simp) (by simp)]
            cases i with
            | zero => exact hone
            | succ i => simpa [K, HomologicalComplex.sc',
                HomologicalComplex.shortComplexFunctor'] using Q.exact_succ i
          · apply ChainComplex.exactAt_succ_single_obj⟩
      let P : ProjectiveResolution S.X₃ :=
        { complex := K
          projective := fun i ↦ by
            cases i with
            | zero => exact inferInstanceAs (Projective S.X₂)
            | succ i => exact Q.projective i
          π := π
          quasiIso := hπ }
      refine ⟨P, fun i hi ↦ ?_⟩
      cases i with
      | zero => omega
      | succ i => exact hQ i (by omega)
end ModuleCat
