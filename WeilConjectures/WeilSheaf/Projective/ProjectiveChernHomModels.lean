/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedForgetTwoInjective.StandardBifunctorHomModel
import all WeilConjectures.WeilSheaf.Native.NativeStandardHomRepresentatives
import WeilConjectures.WeilSheaf.DerivedHomPrecomposition
import WeilConjectures.WeilSheaf.DerivedHom
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.Algebra.Homology.BifunctorHomCone
import WeilConjectures.Algebra.Homology.BifunctorHomComplex
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra

/-! # Native derived Hom models without separatedness

The construction of the two-variable native Hom only needs K-injective resolutions.
(blueprint: lem-pur-b3-projective-chern-hom-models).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.RingedForgetTwoInjective

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
  [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (Y : Scheme.{u}) [Y.Over (Spec (CommRingCat.of k₀))]

/-- The actual product-total native Hom has a two-variable derived extension on any base.

Source: Stacks 0A95 and 08J7; the proof of nativeStandardHomRepresentatives.
(blueprint: lem-pur-b3-projective-chern-hom-models).

Proof: use the homotopy-category equivalence from K-injective complexes to the derived
category in the second variable. The Hom complex is functorial in both variables.
Precomposition with a quasi-isomorphism into a K-injective target is a quasi-isomorphism,
so the representative comparison is invertible for every source. The naturality and
inversion equations give Representatives. This is the same construction as the existing
nativeStandardHomRepresentatives, whose geometric hypotheses are unused here. The models
include zero complexes and the empty scheme. -/
theorem exists_projectiveChernHomModels :
    ∃ H : (DerivedCategory (ProEtaleWeilSheaf k₀ l Y))ᵒᵖ ×
        DerivedCategory (ProEtaleWeilSheaf k₀ l Y) ⥤
          DerivedCategory (ProEtaleWeilSheaf k₀ l Y),
      Nonempty (Representatives
        (standardHomModel (ProEtaleWeilSheaf.ihomBifunctor k₀ l Y)).complex H) := by
  let H₀ := ProEtaleWeilSheaf.ihomBifunctor k₀ l Y
  have hinv : ∀ (K J I : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ)
      [J.IsKInjective] [I.IsKInjective] (a : K ⟶ J) [QuasiIso a],
      IsIso (DerivedCategory.Q.map
        (CochainComplex.bifunctorHomMapLeft (H := H₀) (Y := I) a)) := by
    intro K J I _ _ a _
    have := ProEtaleWeilSheaf.quasiIso_bifunctorHomMapLeft (I := I) a
    infer_instance
  exact ⟨NativeStandardAssembly.derivedBifunctor H₀,
    ⟨NativeStandardAssembly.representatives H₀ hinv⟩⟩

end AlgebraicGeometry.WeilComplex
