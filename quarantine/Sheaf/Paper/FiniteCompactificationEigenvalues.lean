/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K7
-/
module

public import Sheaf.Paper.WeilCompactSupportCohomology
public import Sheaf.Paper.AdicPunctualWeights
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.Paper.FiniteCompactificationStalkReturn

/-! Auxiliary finite compactification result.
Source: blueprint main-20261015, sk-l-dl-general-quasifinite.
(blueprint: lem-zl-finite-compactification-eigenvalues).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- Finite-fibre Frobenius orbit formula for the degree-zero compact-support
image of a finite compactification. It is independent of embeddings into ℂ and weights.

Source: blueprint main-20261015, `lem-zl-quasi-finite.proof.md`, clause (2), and
`lem-zl-finite-pushforward.proof.md`, finite-stalk and Frobenius-cycle calculation;
Stacks 03QP(1); Deligne, Weil II (1.1.10)--(1.1.14).
(blueprint: lem-zl-finite-compactification-eigenvalues).

Proof: unpack the finite Weil presentation, residue embedding and nonzero
eigenvector in the punctual eigenvalue hypothesis. Apply
sfFiniteCompactificationStalkReturn to this exact presentation. Its evaluation
maps are jointly injective, so at least one evaluation of this vector is nonzero.
For that component, with positive return degree e, the power-eigenvector identity
and linearity give evaluation(F_y^e v)=β^e evaluation(v). The return formula
identifies the left side with F_x(evaluation(v)), so the nonzero component is an
eigenvector of the original source local operator with eigenvalue β^e.
Its source finite Weil presentation witnesses SfPunctualEigenvalue. The same
component supplies f₀(x)=y, e≠0 and #κ(x)=#κ(y)^e. Empty fibres and zero stalks
cannot supply a nonzero component. No embedding into ℂ or weight occurs. -/
theorem sfFiniteCompactificationEigenvalues
    [QuasiSeparated Y₀.hom] (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left)
    [IsFinite c.g] (F : sfCommonStageWeilSheaf D l hl X₀ Ω)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) (β : Ω)
    (hβ : SfPunctualEigenvalue D l hl Ω Y₀
      (zlWeilHigherShriek D l hl Ω f₀ c 0 F) y β) :
    ∃ (x : {x : X₀.left // x ∈ closedPoints X₀.left}) (e : ℕ),
      f₀.left x.val = y.val ∧ e ≠ 0 ∧
        Nat.card (X₀.left.residueField x.val) = Nat.card (Y₀.left.residueField y.val) ^ e ∧
        SfPunctualEigenvalue D l hl Ω X₀ F x (β ^ e)  := by
  classical
  obtain ⟨L, K, hK, ι, hι, hv⟩ := hβ
  obtain ⟨A⟩ := sfFiniteCompactificationStalkReturn D l hl Ω f₀ c F y L K hK ι hι
  obtain ⟨v, hv⟩ := hv.exists_hasEigenvector
  have hn : ∃ i, A.evaluation i v ≠ 0 := by
    by_contra h
    apply hv.2
    apply A.jointly_injective
    funext i
    simpa using not_exists.mp h i
  obtain ⟨i, hi⟩ := hn
  refine ⟨A.point i, A.degree i, A.mapsTo i, A.degree_ne_zero i,
    A.cardinality i, A.stage i, A.source i, A.source_iso i,
    A.embedding i, A.compatible i, ?_⟩
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := A.evaluation i v)
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hi⟩
  rw [← A.return_formula i v, hv.pow_apply, map_smul]

end WeilConjectures
