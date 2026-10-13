/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechTotalComplex
public import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.Algebra.Homology.KInjectiveRestrictOpen
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import Sheaf.Paper.QCohAcyclicDerivedSectionsComparison
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns

/-! # Čech totalization of a quasi-coherent resolution

Source: Stacks Project, Cohomology, Lemma 08C2.
(blueprint: lem-sc-qcoh-alternating-cech-resolution-quasi-iso)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Čech totalization sends a quasi-coherent complex's K-injective resolution to a
quasi-isomorphism, without boundedness of the coefficient complex.

Source: Stacks Project, Cohomology, Lemma 08C2, affine-basis application using Tag 01XB.
(blueprint: lem-sc-qcoh-alternating-cech-resolution-quasi-iso).

Proof: Restrict the resolution to each nonempty affine intersection. Restriction preserves
K-injectivity. Affine quasi-coherent derived sections agree with termwise sections even
for unbounded complexes: affine vanishing and the cohomological bound remove the negative
truncation tail, and the bounded-below spectral sequence computes the remaining part.
Thus every intersection section map is a quasi-isomorphism. Finite products preserve
these quasi-isomorphisms, so every column map is a quasi-isomorphism. The integer double
complexes have zero columns outside 0 through r-1: negative columns are extended by
zero, and there are no increasing (p+1)-tuples for p ≥ r. Apply the existing theorem
HomologicalComplex₂.total.quasiIso_map_of_finitely_many_columns with bounds 0 and r-1.
It proves the total map is a quasi-isomorphism by finite column induction, without a
spectral sequence. For r = 0 both totals are zero. No assertion that sections preserve
arbitrary quasi-isomorphisms is used. -/
theorem qcoh_alternatingCech_resolution_quasiIso
    (X : Scheme.{u}) (r : ℕ) (U : Fin r → X.Opens) (hU : iSup U = ⊤)
    (hAffine : ∀ (p : ℕ) (t : Fin (p + 1) → Fin r), IsAffineOpen (⨅ k, U (t k)))
    (F J : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent)
    [J.IsKInjective] (i : F ⟶ J) [QuasiIso i] :
    QuasiIso ((alternatingCechTotalFunctor U).map i) := by sorry

end AlgebraicGeometry
