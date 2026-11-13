/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.AlgebraicGeometry.SchemeTheoreticSupport

/-! # Support of a finite type module proper over a base

## Main statements

* `module_support_proper_over_base` states closedness of the support and the
  characterization of proper support by a proper closed subscheme annihilating
  the module.

## References

* Stacks Project, Cohomology of Schemes, Lemma 0CYS, together with
  Morphisms Lemmas 056J, 05JU, Definition 05JV, and Lemma 01QY.
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules

/-- For a quasi-coherent finite type module, the support is closed, and it is proper
over the base exactly when the module is annihilated by the ideal of a proper closed
subscheme, equivalently a finite type quasi-coherent pushforward from that subscheme.
The last conjunct permits taking the scheme-theoretic support: its ideal agrees on
all affine opens with the annihilator, and its underlying set is exactly the support
(Stacks, Tag 0CYS). -/
theorem module_support_proper_over_base {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    (∃ Z : TopologicalSpace.Closeds X,
      (Z : Set X) = {x : X | ¬ Subsingleton (F.presheaf.stalk x)}) ∧
      (HasSupportProperOver f F ↔
        ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (_ : IsClosedImmersion i),
          IsProper (i ≫ f) ∧
            (∀ (V : X.Opens) (a : Γ(X, V)), a ∈ i.ker.idealOfOpens V →
              ∀ s : Γ(F, V), a • s = 0) ∧
            ∃ (G : Z.Modules) (_ : G.IsQuasicoherent) (_ : G.IsFiniteType),
              Nonempty (F ≅ (pushforward i).obj G)) ∧
      (∃ (Z : Scheme.{u}) (i : Z ⟶ X) (_ : IsClosedImmersion i),
        (∀ U : X.affineOpens,
          i.ker.ideal U = Module.annihilator Γ(X, U) Γ(F, U)) ∧
          Set.range i = {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ∧
          (∀ (V : X.Opens) (a : Γ(X, V)), a ∈ i.ker.idealOfOpens V →
            ∀ s : Γ(F, V), a • s = 0) ∧
          (∃ (G : Z.Modules) (_ : G.IsQuasicoherent) (_ : G.IsFiniteType),
            Nonempty (F ≅ (pushforward i).obj G)) ∧
          (HasSupportProperOver f F ↔ IsProper (i ≫ f))) := by
  classical
  let C : TopologicalSpace.Closeds X :=
    ⟨{x : X | ¬ Subsingleton (F.presheaf.stalk x)},
      (finite_type_module_support_closed X F).2.2.2⟩
  obtain ⟨I, hI, hi, hker, _, _, hrange, hkill, _⟩ := schemeTheoreticSupport X F
  have : IsClosedImmersion I.subschemeι := hi
  have hann : ∀ (V : X.Opens) (a : Γ(X, V)),
      a ∈ I.subschemeι.ker.idealOfOpens V → ∀ s : Γ(F, V), a • s = 0 := by
    intro V a ha s
    rw [hker] at ha
    exact hkill V ⟨a, ha⟩ s
  have hpush : ∃ (G : I.subscheme.Modules) (_ : G.IsQuasicoherent) (_ : G.IsFiniteType),
      Nonempty (F ≅ (pushforward I.subschemeι).obj G) := by
    obtain ⟨hq, he, hf⟩ :=
      (closedImmersion_pushforward_annihilated I.subschemeι).2 F hann
    have := hq
    have := hf (inferInstance : F.IsFiniteType)
    have := he
    exact ⟨(tensorPullback I.subschemeι).obj F, inferInstance, inferInstance,
      ⟨asIso ((Classical.choose
        (exists_tensorPullbackAdjunction I.subschemeι)).unit.app F)⟩⟩
  have hproper : HasSupportProperOver f F ↔ IsProper (I.subschemeι ≫ f) := by
    constructor
    · rintro ⟨D, hD, hp⟩
      exact (closed_subset_proper_over_base_properties f D).2.1.mp hp
        I.subscheme I.subschemeι (hrange.trans hD.symm)
    · intro hp
      exact ⟨C, rfl, (closed_subset_proper_over_base_properties f C).1.mpr
        ⟨I.subscheme, I.subschemeι, inferInstance, hrange, hp⟩⟩
  refine ⟨⟨C, rfl⟩, ⟨?_, ?_⟩, I.subscheme, I.subschemeι, inferInstance,
    ?_, hrange, hann, hpush, hproper⟩
  · intro hp
    exact ⟨I.subscheme, I.subschemeι, inferInstance, hproper.mp hp, hann, hpush⟩
  · rintro ⟨Z, i, hi, hp, _, G, hq, hf, ⟨e⟩⟩
    have : IsClosedImmersion i := hi
    let D : TopologicalSpace.Closeds X :=
      ⟨Set.range i.base, i.isClosedEmbedding.isClosed_range⟩
    have hCD : C ≤ D := by
      intro x hx
      by_contra hn
      have hz := (closedImmersion_pushforward_stalks i i.isClosedEmbedding G).1 x hn
      let T := SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
          TopCat.Presheaf.stalkFunctor Ab.{u} x
      have heq := ConcreteCategory.bijective_of_isIso (T.map e.hom)
      have : Subsingleton (F.presheaf.stalk x) :=
        ⟨fun a b ↦ heq.1 (hz.elim _ _)⟩
      exact hx this
    have hD : IsClosedSubsetProperOver f D :=
      (closed_subset_proper_over_base_properties f D).1.mpr
        ⟨Z, i, inferInstance, rfl, hp⟩
    exact ⟨C, rfl, (closed_subset_proper_over_base_properties f D).2.2.1 C hCD hD⟩
  · intro U
    rw [hker]
    exact hI U

end AlgebraicGeometry.Scheme.Modules
