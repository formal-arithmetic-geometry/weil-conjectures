/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Sheaf.CategoryTheory.DeltaFunctor

/-!
# The canonical delta-functor of topological abelian sheaf cohomology

Source: Stacks Project, Cohomology of Sheaves, Sections 20.2 and 20.3
(blueprint: def-sc-topological-abelian-cohomology-delta-functor).
-/

set_option autoImplicit false
universe uC
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

/-- Global cohomology, using exactly Mathlib's `Sheaf.H'` at the whole space.
Source: Stacks, Cohomology of Sheaves, Section 20.2
(blueprint: def-sc-topological-abelian-cohomology-delta-functor). -/
noncomputable def abelianCohomologyFunctor (X : TopCat.{uC}) (n : ℕ) :
    X.Sheaf AddCommGrpCat.{uC} ⥤ AddCommGrpCat.{uC + 1} :=
  @CategoryTheory.Sheaf.cohomologyPresheafFunctor _ _ (Opens.grothendieckTopology X)
    _ (HasExt.standard _) n ⋙ (evaluation _ _).obj (op (⊤ : Opens X))

/-- The canonical connecting map is composition with the extension class of the sequence.
Source: Stacks, Cohomology of Sheaves, Section 20.3
(blueprint: def-sc-topological-abelian-cohomology-delta-functor). -/
noncomputable def abelianCohomologyBoundary (X : TopCat.{uC})
    (S : ShortComplex (X.Sheaf AddCommGrpCat.{uC})) (hS : S.ShortExact) (n : ℕ) :
    (abelianCohomologyFunctor X n).obj S.X₃ ⟶
      (abelianCohomologyFunctor X (n + 1)).obj S.X₁ :=
  AddCommGrpCat.ofHom
    (@Abelian.Ext.postcomp _ _ _ (HasExt.standard _) _ _ _
      (@ShortComplex.ShortExact.extClass _ _ _ (HasExt.standard _) S hS) _ _ _ rfl)

/-- Evaluation of a degree-zero class on the generator at the whole space is the
canonical identification with global sections. Source: Stacks, Section 20.2
(blueprint: def-sc-topological-abelian-cohomology-delta-functor). -/
noncomputable def abelianCohomologySection (X : TopCat.{uC})
    (F : X.Sheaf AddCommGrpCat.{uC})
    (c : (abelianCohomologyFunctor X 0).obj F) : F.obj.obj (op ⊤) :=
  (@Abelian.Ext.addEquiv₀ _ _ _ (HasExt.standard _) _ _ c).hom.app (op ⊤)
    (((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{uC}).unit.app
      ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).obj
        (⊤ : Opens X))).app (op ⊤) (FreeAbelianGroup.of (𝟙 (⊤ : Opens X))))

/-- The Ext boundary maps obey the delta-functor laws.
Source: Stacks, Cohomology of Sheaves, Sections 20.2 and 20.3
(blueprint: def-sc-topological-abelian-cohomology-delta-functor).

Proof: the free abelian sheaf on the representable whole space represents global
sections, by sheafification, the free-forgetful adjunction, and Yoneda. Its Ext groups
are therefore the right derived functors of global sections. The Ext long exact
sequence proves exactness at each of its three repeating positions and injectivity
of the initial map. Naturality of extension classes gives naturality of the boundary.
Additivity comes from the Ext bifunctor. This is the LES assertion of
lem-weil-pbc-right-derived-universal-delta-functor. -/
theorem abelianCohomologyDeltaFunctor_laws (X : TopCat.{uC}) :
    (∀ n : ℕ, (abelianCohomologyFunctor X n).Additive) ∧
    (∀ (S : ShortComplex (X.Sheaf AddCommGrpCat.{uC})) (_hS : S.ShortExact),
      Mono ((abelianCohomologyFunctor X 0).map S.f)) ∧
    (∀ (S : ShortComplex (X.Sheaf AddCommGrpCat.{uC})) (_hS : S.ShortExact) (n : ℕ),
      ∃ h : (abelianCohomologyFunctor X n).map S.f ≫
          (abelianCohomologyFunctor X n).map S.g = 0,
        (ShortComplex.mk ((abelianCohomologyFunctor X n).map S.f)
          ((abelianCohomologyFunctor X n).map S.g) h).Exact) ∧
    (∀ (S : ShortComplex (X.Sheaf AddCommGrpCat.{uC})) (hS : S.ShortExact) (n : ℕ),
      ∃ h : (abelianCohomologyFunctor X n).map S.g ≫
          abelianCohomologyBoundary X S hS n = 0,
        (ShortComplex.mk ((abelianCohomologyFunctor X n).map S.g)
          (abelianCohomologyBoundary X S hS n) h).Exact) ∧
    (∀ (S : ShortComplex (X.Sheaf AddCommGrpCat.{uC})) (hS : S.ShortExact) (n : ℕ),
      ∃ h : abelianCohomologyBoundary X S hS n ≫
          (abelianCohomologyFunctor X (n + 1)).map S.f = 0,
        (ShortComplex.mk (abelianCohomologyBoundary X S hS n)
          ((abelianCohomologyFunctor X (n + 1)).map S.f) h).Exact) ∧
    (∀ (S T : ShortComplex (X.Sheaf AddCommGrpCat.{uC}))
      (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ),
      abelianCohomologyBoundary X S hS n ≫
          (abelianCohomologyFunctor X (n + 1)).map φ.τ₁ =
        (abelianCohomologyFunctor X n).map φ.τ₃ ≫ abelianCohomologyBoundary X T hT n) := by
  sorry

/-- Global cohomology with its canonical Ext connecting maps.
Source: Stacks, Cohomology of Sheaves, Sections 20.2 and 20.3
(blueprint: def-sc-topological-abelian-cohomology-delta-functor). -/
noncomputable def abelianCohomologyDeltaFunctor (X : TopCat.{uC}) :
    CohomologicalDeltaFunctor (X.Sheaf AddCommGrpCat.{uC}) AddCommGrpCat.{uC + 1} where
  F := abelianCohomologyFunctor X
  additive := (abelianCohomologyDeltaFunctor_laws X).1
  delta := abelianCohomologyBoundary X
  mono_zero := (abelianCohomologyDeltaFunctor_laws X).2.1
  exact_middle := (abelianCohomologyDeltaFunctor_laws X).2.2.1
  exact_right := (abelianCohomologyDeltaFunctor_laws X).2.2.2.1
  exact_left := (abelianCohomologyDeltaFunctor_laws X).2.2.2.2.1
  naturality := (abelianCohomologyDeltaFunctor_laws X).2.2.2.2.2

end TopCat.Sheaf
