/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.Topology.AbelianOpenExtensionByZeroStalks
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import WeilConjectures.Topology.TopologicalFilteredCohomology
import WeilConjectures.Topology.AbelianSheafFiniteGenerationExhaustion
import WeilConjectures.Topology.AbelianIntegerExtensionMono
public import Mathlib.Algebra.Category.Grp.Zero

/-! # Finite-generation reduction for topological cohomology

## References

* Stacks Project, Tags 02UX and 01FF.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace TopCat

-- These exact-sequence arguments work over any open, not only the whole space.
private lemma reduction_zero_middle (X : TopCat.{u})
    (S : ShortComplex (X.Sheaf AddCommGrpCat.{u})) (hS : S.ShortExact) (p : ℕ)
    (U : Opens X)
    (h₁ : IsZero (CategoryTheory.Sheaf.H' S.X₁ p U))
    (h₃ : IsZero (CategoryTheory.Sheaf.H' S.X₃ p U)) :
    IsZero (CategoryTheory.Sheaf.H' S.X₂ p U) := by
  have hsub₁ := AddCommGrpCat.subsingleton_of_isZero h₁
  have hsub₃ := AddCommGrpCat.subsingleton_of_isZero h₃
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, rfl⟩ := Abelian.Ext.covariant_sequence_exact₂ _ hS x (hsub₃.elim _ _)
  rw [hsub₁.elim y 0, Abelian.Ext.zero_comp]

private lemma reduction_zero_right (X : TopCat.{u})
    (S : ShortComplex (X.Sheaf AddCommGrpCat.{u})) (hS : S.ShortExact) (p : ℕ)
    (U : Opens X)
    (h₂ : IsZero (CategoryTheory.Sheaf.H' S.X₂ p U))
    (h₁ : IsZero (CategoryTheory.Sheaf.H' S.X₁ (p + 1) U)) :
    IsZero (CategoryTheory.Sheaf.H' S.X₃ p U) := by
  have hsub₂ := AddCommGrpCat.subsingleton_of_isZero h₂
  have hsub₁ := AddCommGrpCat.subsingleton_of_isZero h₁
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, rfl⟩ :=
    Abelian.Ext.covariant_sequence_exact₃ _ hS x rfl (hsub₁.elim _ _)
  rw [hsub₂.elim y 0, Abelian.Ext.zero_comp]

private lemma reduction_zero_colimit (X : TopCat.{u}) [CompactSpace X]
    (hbas : ∀ (U : Set X), IsOpen U → ∀ x ∈ U, ∃ V : Set X, IsOpen V ∧
      IsCompact V ∧ x ∈ V ∧ V ⊆ U)
    (hint : ∀ (U V : Set X), IsOpen U → IsOpen V → IsCompact U → IsCompact V →
      IsCompact (U ∩ V))
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ X.Sheaf AddCommGrpCat.{u}) (c : Cocone D) (hc : IsColimit c)
    (p : ℕ) (hzero : ∀ i, IsZero (CategoryTheory.Sheaf.H' (D.obj i) p (⊤ : Opens X))) :
    IsZero (CategoryTheory.Sheaf.H' c.pt p (⊤ : Opens X)) := by
  let H := CategoryTheory.Sheaf.cohomologyPresheafFunctor
    (Opens.grothendieckTopology X) p ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op (⊤ : Opens X))
  have hD : IsZero (D ⋙ H) := (D ⋙ H).isZero hzero
  have hz := (colimit.isColimit (D ⋙ H)).isZero_pt hD
  have hiso := topological_filtered_cohomology X hbas hint I D p
    (⊤ : Opens X) (by simpa using isCompact_univ (X := X))
  have hcolim : IsZero (H.obj (colimit D)) := hz.of_iso
    (asIso (colimit.desc (D ⋙ H) (H.mapCocone (colimit.cocone D)))).symm
  exact hcolim.of_iso (H.mapIso (hc.coconePointUniqueUpToIso (colimit.isColimit D)))

/-- It suffices to control the finitely generated subsheaves of the constant integer sheaf,
in addition to the compact-open extension-by-zero generators themselves. -/
theorem noetherian_vanishing_of_constant_subsheaves
    (X : TopCat.{u}) [CompactSpace X]
    (d : ℕ)
    (hbas : ∀ (U : Set X), IsOpen U → ∀ x ∈ U, ∃ V : Set X, IsOpen V ∧
      IsCompact V ∧ x ∈ V ∧ V ⊆ U)
    (hint : ∀ (U V : Set X), IsOpen U → IsOpen V → IsCompact U → IsCompact V →
      IsCompact (U ∩ V))
    (hvanish : ∀ (p : ℕ), d < p → ∀ (U : Opens X), IsCompact (U : Set X) →
      IsZero (CategoryTheory.Sheaf.H'
        ((TopCat.Sheaf.abelianOpenExtensionByZero U).obj
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) p
        (⊤ : Opens X)))
    (hsub : ∀ (K : X.Sheaf AddCommGrpCat.{u})
      (ι : K ⟶ (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))), Mono ι →
      (∃ (n : ℕ) (U : Fin n → Opens X)
        (_ : ∀ i, IsCompact ((U i : Opens X) : Set X)),
        ∃ g : (∐ fun i ↦ (TopCat.Sheaf.abelianOpenExtensionByZero (U i)).obj
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K, Epi g) →
      ∀ (q : ℕ), d < q → IsZero (CategoryTheory.Sheaf.H' K q (⊤ : Opens X)))
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (p : ℕ) (hp : d < p) :
    IsZero (CategoryTheory.Sheaf.H' F p (⊤ : Opens X)) := by
  have hquot (U : Opens X) (hU : IsCompact (U : Set X))
      (G : X.Sheaf AddCommGrpCat.{u})
      (ρ : (TopCat.Sheaf.abelianOpenExtensionByZero U).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ G)
      (hρ : Epi ρ) : IsZero (CategoryTheory.Sheaf.H' G p (⊤ : Opens X)) := by
    let _ := hρ
    obtain ⟨ι, hι⟩ := abelianIntegerExtension_exists_mono X U
    let _ := hι
    let K := kernel ρ
    obtain ⟨I, hI, hne, hdir, D, c, ⟨hc⟩, hstage⟩ :=
      abelianSheaf_finiteGeneration_exhaustion X hbas K
    let _ := hI
    let _ := hne
    let _ := hdir
    have hK : IsZero (CategoryTheory.Sheaf.H' K (p + 1) (⊤ : Opens X)) := by
      apply reduction_zero_colimit X hbas hint I D (Cocone.mk K c) hc (p + 1)
      intro i
      have hmono := (hstage i).1
      let _ := hmono
      exact hsub (D.obj i) (c.app i ≫ kernel.ι ρ ≫ ι) inferInstance (hstage i).2
        (p + 1) (Nat.lt_trans hp (Nat.lt_succ_self p))
    let S := ShortComplex.mk (kernel.ι ρ) ρ (kernel.condition ρ)
    have hS : S.ShortExact := ShortComplex.ShortExact.mk'
      (ShortComplex.exact_kernel ρ) inferInstance inferInstance
    exact reduction_zero_right X S hS p ⊤ (hvanish p hp U hU) hK
  let E (U : Opens X) := (TopCat.Sheaf.abelianOpenExtensionByZero U).obj
    ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
  have hfinite : ∀ (n : ℕ) (U : Fin n → Opens X),
      (∀ i, IsCompact ((U i : Opens X) : Set X)) →
      ∀ (T : X.Sheaf AddCommGrpCat.{u}) (g : (∐ fun i ↦ E (U i)) ⟶ T),
      Epi g → IsZero (CategoryTheory.Sheaf.H' T p (⊤ : Opens X)) := by
    intro n
    induction n with
    | zero =>
      intro U hU T g hg
      let _ := hg
      have hgzero : g = 0 := by
        apply Sigma.hom_ext
        intro i
        exact Fin.elim0 i
      have hz : IsZero T := IsZero.of_epi_eq_zero g hgzero
      rw [AddCommGrpCat.isZero_iff_subsingleton]
      refine subsingleton_of_forall_eq 0 fun x ↦ ?_
      rw [← Abelian.Ext.comp_mk₀_id x, hz.eq_of_src (𝟙 T) 0,
        Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]
    | succ n ih =>
      intro U hU T g hg
      let _ := hg
      let gfirst : (∐ fun i : Fin n ↦ E (U i.castSucc)) ⟶ T :=
        Sigma.desc (fun i ↦ Sigma.ι (fun j ↦ E (U j)) i.castSucc ≫ g)
      let A := image gfirst
      let f : A ⟶ T := image.ι gfirst
      let Q := cokernel f
      let glast : E (U (Fin.last n)) ⟶ Q :=
        Sigma.ι (fun j ↦ E (U j)) (Fin.last n) ≫ g ≫ cokernel.π f
      have hlast : Epi glast := by
        apply Preadditive.epi_of_cancel_zero
        intro Z a ha
        apply (cancel_epi (cokernel.π f)).1
        simp only [comp_zero]
        apply (cancel_epi g).1
        simp only [comp_zero]
        apply Sigma.hom_ext
        intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simpa [glast, Category.assoc] using ha
        · have hfirst : gfirst ≫ cokernel.π f = 0 := by
            calc
              gfirst ≫ cokernel.π f =
                  factorThruImage gfirst ≫ f ≫ cokernel.π f := by
                rw [← Category.assoc]
                exact congrArg (fun k ↦ k ≫ cokernel.π f) (image.fac gfirst).symm
              _ = 0 := by rw [cokernel.condition, comp_zero]
          have hcomp := congrArg (fun k ↦
            Sigma.ι (fun j : Fin n ↦ E (U j.castSucc)) j ≫ k ≫ a) hfirst
          simpa [gfirst, Category.assoc] using hcomp
      have hA := ih (fun i ↦ U i.castSucc) (fun i ↦ hU i.castSucc)
        A (factorThruImage gfirst) inferInstance
      have hQ := hquot (U (Fin.last n)) (hU (Fin.last n)) Q glast hlast
      let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
      have hS : S.ShortExact := ShortComplex.ShortExact.mk'
        (ShortComplex.exact_cokernel f) inferInstance inferInstance
      exact reduction_zero_middle X S hS p ⊤ hA hQ
  obtain ⟨I, hI, hne, hdir, D, c, ⟨hc⟩, hstage⟩ :=
    abelianSheaf_finiteGeneration_exhaustion X hbas F
  let _ := hI
  let _ := hne
  let _ := hdir
  apply reduction_zero_colimit X hbas hint I D (Cocone.mk F c) hc p
  intro a
  obtain ⟨n, U, hU, g, hg⟩ := (hstage a).2
  exact hfinite n U hU (D.obj a) g hg

end TopCat
