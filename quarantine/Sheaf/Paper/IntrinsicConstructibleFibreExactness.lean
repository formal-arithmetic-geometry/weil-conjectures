/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B9
-/
module

public import Sheaf.Paper.AdicNormalizedFibreData

/-! # Exactness and zero detection of intrinsic fibres

Source: Bhatt--Scholze, §6.8.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme.ContinuousRational.NormalizedFibre
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Intrinsic geometric fibres are linear, preserve constructible short exact sequences,
and jointly detect zero objects. Finite dimensionality and the other detection properties
are consequences proved separately.
Source: Bhatt--Scholze, Corollary 6.8.5 and Lemma 6.8.7.
(blueprint: lem-per-intrinsic-constructible-fibre-exactness).

Proof: additivity and E-linearity follow from balanced module inverse image, evaluation,
and restriction of scalars along constant functions. For exactness choose a common
lisse stratification for a short exact sequence. On pro-etale covers the last term is
finite free; local splitting of epimorphisms onto free modules gives a split sequence.
Additive inverse image preserves this splitting. Pull the covers to the geometric point;
local exactness descends, and exact final-object sections give the vector-space sequence.
For zero detection choose etale local monodromy presentations on each connected lisse
chart. Restrict to an affine neighbourhood of the chosen geometric base point before
applying the separated completed-system comparison. Its normalized stalk quotients are
B/ϖ^(n+1)B for an invariant lattice B, with limit B, hence rational fibre V. Zero fibres
force V=0. Cover restriction reflects isomorphisms, and stratum restrictions jointly
reflect vanishing, so the realized sheaf is zero. Faithfulness of the rational heart
realization then gives zero in the heart. Empty schemes use the empty cover. -/
theorem intrinsic_constructible_fibre_exactness (X : Base.{u} l)
    (k : Type u) [Field k] [X.scheme.Over (Spec (.of k))]
    [LocallyOfFiniteType (X.scheme ↘ Spec (.of k))]
    [QuasiCompact (X.scheme ↘ Spec (.of k))]
    [IsSeparated (X.scheme ↘ Spec (.of k))] (hl : IsUnit (l : k))
    (R : Family.{u} l) :
    (∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
      ∃ ha : (omega l E X (R.realization E X) κ x).Additive,
      let : (omega l E X (R.realization E X) κ x).Additive := ha
      (omega l E X (R.realization E X) κ x).Linear E ∧
      ∀ S : ShortComplex (Heart l E X),
        (S.map (realize l E X (R.realization E X))).ShortExact →
          (S.map (omega l E X (R.realization E X) κ x)).ShortExact) ∧
    (∀ F : Heart l E X,
      (∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme),
        IsZero ((omega l E X (R.realization E X) κ x).obj F)) → IsZero F) := by sorry

end AlgebraicGeometry.Scheme.ContinuousRational.NormalizedFibre
