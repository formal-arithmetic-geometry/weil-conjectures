/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.SixFunctorsBasics.BrownHypotheses
import Sheaf.SixFunctorsBasics.BrownHypothesesCriteria
public import Sheaf.Paper.FiniteFieldFiber
import Sheaf.SixFunctorsBasics.BrownHypothesesArbitraryFieldCompactness

/-!
# Brown hypotheses over the geometric field of a finite-field datum

Source: blueprint latest, sk-lem-brown-hypotheses.proof.md, paragraphs 1--2.
The geometric finite-field specialization is separate from the general formal criteria,
so those criteria do not depend on the special compactness theorem.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace CategoryTheory

attribute [local instance 30000] brownHypothesesCondensedMonoidal
  brownHypothesesCondensedBraided brownHypothesesSheafMonoidal
  brownHypothesesSheafBraided brownHypothesesCoefficientMonObj
  brownHypothesesModuleMonoidalClosed
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar BrownHypothesesFor

-- Unfold coefficient admissibility only where its cases are used.
attribute [local irreducible] IsLocalizingAdmissibleCoefficient

/-- Brown's hypotheses for the geometric field of a finite-field datum, using the
project's admissibility predicate and an explicit structure morphism.

Source: blueprint latest, sk-lem-brown-hypotheses.proof.md, paragraphs 1--2,
with the field hypothesis of det-brown-hypotheses-generation.
(blueprint: lem-sfb-brown-finite-field-admissible).

Proof: install the structure morphism as the scheme-over instance. Finite type
makes X compact and locally Noetherian. Admissible-coefficient smallness supplies
thickness and essential smallness. Choose a small skeleton once and apply the
finite-field compactness theorem directly to these representatives. The representative
Brown criterion transports compactness to every constructible finite-Tor object and
supplies generation. All finite-field hypotheses remain explicit. -/
theorem brownHypotheses_of_finiteFieldDatum
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ≠ D.p) {X : Scheme.{u}} (aX : X ⟶ Spec (.of D.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    BrownHypothesesFor Λ X := by
  let _ : X.Over (Spec (.of D.k)) := ⟨aX⟩
  let _ : IsSeparated (X ↘ Spec (.of D.k)) := ‹IsSeparated aX›
  let _ : LocallyOfFiniteType (X ↘ Spec (.of D.k)) := ‹LocallyOfFiniteType aX›
  let _ : QuasiCompact (X ↘ Spec (.of D.k)) := ‹QuasiCompact aX›
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  obtain ⟨_, _, _, _, hSums, _⟩ := brownHypotheses_structural Λ X
  exact (brownHypothesesFor_iff_compact_of_noetherian ℓ X Λ hΛ).mpr
    ⟨hSums, brownHypotheses_finiteField_object_compactness D ℓ hℓ X Λ hΛ hSums⟩


end CategoryTheory
