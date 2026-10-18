/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import WeilConjectures.CategoryTheory.PBCFiltration
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The two-step filtered derived category of modules

Source: Stacks Project, Tags 03TB and 03TJ, and the two-step localization in
blueprint prop-trf-trace-formal-laws, proof of clause (2)
(blueprint: def-trf-two-step-filtered-module-derived).

The two-step object is a monomorphism of complexes. Its two graded complexes are
its domain and its cokernel. No bound on cochain degrees is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable (R : Type u) [CommRing R]

/-- Pairs `K' ⊆ K`, with filtration-preserving chain maps given by commutative squares.
Source: Stacks, Tag 03TB, specialized to two steps
(blueprint: def-trf-two-step-filtered-module-derived). -/
abbrev TwoStepModuleComplex :=
  ObjectProperty.FullSubcategory
    (fun K : Arrow (CochainComplex (ModuleCat.{u} R) ℤ) ↦ Mono K.hom)

/-- The two graded complexes, with `true` the subcomplex and `false` the quotient.
Source: Stacks, Tag 012K, and blueprint trace formal laws, clause (2)
(blueprint: def-trf-two-step-filtered-module-derived). -/
noncomputable def twoStepGradedComplex (b : Bool) :
    TwoStepModuleComplex R ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  ObjectProperty.ι _ ⋙ if b then Arrow.leftFunc else coker _

/-- A homotopy on the total complex preserving the subcomplex in every degree.
The factorization condition means exactly `h(K') ⊆ L'`; monicity makes the
restriction unique. Source: Stacks, Tag 03TB, filtered homotopy convention
(blueprint: def-trf-two-step-filtered-module-derived). -/
def twoStepModuleHomotopyRel : HomRel (TwoStepModuleComplex R) :=
  fun {K L} f g ↦ ∃ h : Homotopy f.hom.right g.hom.right,
    ∀ n m : ℤ, ∃ lift : K.obj.left.X n ⟶ L.obj.left.X m,
      lift ≫ L.obj.hom.f m = K.obj.hom.f n ≫ h.hom n m

/-- The homotopy category of pairs, quotienting by filtered chain homotopies.
Source: Stacks, Tag 03TB, two-step specialization
(blueprint: def-trf-two-step-filtered-module-derived). -/
abbrev TwoStepModuleHomotopy := CategoryTheory.Quotient (twoStepModuleHomotopyRel R)

/-- The filtered chain-homotopy quotient functor.
Source: Stacks, Tag 03TB (blueprint: def-trf-two-step-filtered-module-derived). -/
noncomputable def twoStepModuleHomotopyQuotient :
    TwoStepModuleComplex R ⥤ TwoStepModuleHomotopy R :=
  CategoryTheory.Quotient.functor (twoStepModuleHomotopyRel R)

/-- The maps inverted in `DF₂(R)`: a homotopy class has a representative that is a
quasi-isomorphism on both the subcomplex and the quotient complex.
Source: Stacks, Tags 03TB and 03TJ, two-step specialization
(blueprint: def-trf-two-step-filtered-module-derived). -/
def twoStepModuleQuasiIso : MorphismProperty (TwoStepModuleHomotopy R) :=
  fun {K L} q ↦ ∃ f : K.as ⟶ L.as,
    (twoStepModuleHomotopyQuotient R).map f = q ∧
      ∀ b : Bool, QuasiIso ((twoStepGradedComplex R b).map f)

/-- The unbounded two-step filtered derived category, constructed by localization.
Source: Stacks, Tags 03TB and 03TJ, and blueprint trace formal laws, clause (2)
(blueprint: def-trf-two-step-filtered-module-derived). -/
abbrev TwoStepModuleDerived := (twoStepModuleQuasiIso R).Localization

/-- The localization functor from the two-step homotopy category.
Source: Stacks, Tag 03TB (blueprint: def-trf-two-step-filtered-module-derived). -/
noncomputable def twoStepModuleQh : TwoStepModuleHomotopy R ⥤ TwoStepModuleDerived R :=
  (twoStepModuleQuasiIso R).Q

/-- The canonical functor from pairs of complexes to `DF₂(R)`.
Source: Stacks, Tag 03TB (blueprint: def-trf-two-step-filtered-module-derived). -/
noncomputable def twoStepModuleQ : TwoStepModuleComplex R ⥤ TwoStepModuleDerived R :=
  twoStepModuleHomotopyQuotient R ⋙ twoStepModuleQh R

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- Filtered homotopic maps induce equal ordinary derived maps on each graded piece.
Source: Stacks, Tags 012K and 03TB.
Proof: restrict the homotopy to the subcomplex using its unique factorizations;
pass it to the cokernel to obtain the quotient homotopy. Ordinary localization
identifies homotopic maps, giving the two equalities.
(blueprint: def-trf-two-step-filtered-module-derived). -/
theorem twoStepGraded_homotopy (b : Bool) (K L : TwoStepModuleComplex R)
    (f g : K ⟶ L) (h : twoStepModuleHomotopyRel R f g) :
    (twoStepGradedComplex R b ⋙ DerivedCategory.Q).map f =
      (twoStepGradedComplex R b ⋙ DerivedCategory.Q).map g := by
  sorry

/-- Each graded operation descends to the filtered homotopy category.
Source: Stacks, Tags 012K and 03TB
(blueprint: def-trf-two-step-filtered-module-derived). -/
noncomputable def twoStepGradedHomotopy (b : Bool) :
    TwoStepModuleHomotopy R ⥤ DerivedCategory (ModuleCat.{u} R) :=
  CategoryTheory.Quotient.lift (twoStepModuleHomotopyRel R)
    (twoStepGradedComplex R b ⋙ DerivedCategory.Q) (twoStepGraded_homotopy R b)

/-- The graded operations invert filtered quasi-isomorphisms.
Source: Stacks, Tag 03TB.
Proof: choose the representative in the definition of the filtered
quasi-isomorphism. Its graded maps are ordinary quasi-isomorphisms, and hence
become isomorphisms under the ordinary derived localization. Descent to the
homotopy quotient preserves those images.
(blueprint: def-trf-two-step-filtered-module-derived). -/
theorem twoStepGraded_inverts (b : Bool) :
    (twoStepModuleQuasiIso R).IsInvertedBy (twoStepGradedHomotopy R b) := by
  sorry

/-- The canonical graded functors `DF₂(R) → D(R)`; they are the localization lifts
of subcomplex and quotient, with no choice of a graded model or arbitrary map.
Source: Stacks, Tags 012K and 03TB
(blueprint: def-trf-two-step-filtered-module-derived). -/
noncomputable def twoStepGraded (b : Bool) :
    TwoStepModuleDerived R ⥤ DerivedCategory (ModuleCat.{u} R) :=
  Localization.Construction.lift (twoStepGradedHomotopy R b) (twoStepGraded_inverts R b)

end CochainComplex
