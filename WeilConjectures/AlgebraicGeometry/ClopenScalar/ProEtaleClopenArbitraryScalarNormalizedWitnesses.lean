/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenDerivedScalarData
import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenScalarComparisonDescent
import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenDerivedScalarModels
import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenDerivedScalarUnits
import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenScalarComparisonCoherence

/-! # Normalized scalar witnesses for arbitrary coefficient presentations

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 0D6D.
(blueprint: lem-pur-clopen-arbitrary-scalar-normalized-witnesses)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe t u w
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.SuccessiveDerivedQuotient
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived
attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors HasDerivedCategory.standard
  SheafOfModules.monoidalCategory
namespace AlgebraicGeometry.Scheme.ProEt.ClopenScalar

end AlgebraicGeometry.Scheme.ProEt.ClopenScalar

namespace AlgebraicGeometry.Scheme.ProEt.ClopenScalar

/-- Assemble normalized comparison witnesses for arbitrary prescribed scalar presentations.
Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 0D6D
(blueprint: lem-pur-clopen-arbitrary-scalar-normalized-witnesses).

Proof: descend the section-normalized comparison for the given presentations. The model
properties supply the computed and extended clauses of the coherence hypothesis. Choose
unit normalizations, which are proof data for the already prescribed presentation functors.
Apply scalar comparison coherence, and retain sections, degree, representative and coherence.
This does not change representatives from cochain localization to the homotopy quotient. -/
theorem clopen_arbitrary_scalar_normalized_witnesses
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (p : Presentations.{t, u} X) (N : Normalization (J := topology X) p)
    (q : ∀ i, Presentations.{t, u} (Y i))
    (Ni : ∀ i, Normalization (J := topology (Y i)) (q i)) :
    ∃ (U : Units p) (V : ∀ i, Units (q i))
      (d : ∀ i, Comparison (j i) p (q i)),
      ∀ i, (d i).sections ∧ (d i).degree ∧ (d i).representative ∧
        Coherence (j i) N (Ni i) U (V i) (d i) := by
  classical
  obtain ⟨d, hd⟩ := clopen_scalar_comparison_descent
    X I Y j hdisjoint hcover p N q Ni
  have hm := clopen_scalar_model_properties
    X I Y j hdisjoint hcover p N q Ni d
  obtain ⟨U⟩ := clopen_scalar_unit_normalization N
  have hv (i : I) := clopen_scalar_unit_normalization (Ni i)
  let V := fun i ↦ Classical.choice (hv i)
  have hc := clopen_scalar_comparison_coherence
    X I Y j hdisjoint hcover p N q Ni U V d
    (fun i ↦ ⟨(hd i).1, (hd i).2.1, (hd i).2.2.1,
      (hm i).1, (hm i).2, (hd i).2.2.2⟩)
  refine ⟨U, V, d, fun i ↦ ?_⟩
  exact ⟨(hd i).1, (hd i).2.1, (hd i).2.2.1, (hc i)⟩

end AlgebraicGeometry.Scheme.ProEt.ClopenScalar
