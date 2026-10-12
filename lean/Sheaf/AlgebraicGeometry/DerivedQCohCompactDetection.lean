/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedQCohDirectSums
public import Sheaf.CategoryTheory.CompactObject
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.DerivedQCohPerfectGeneration
import Sheaf.AlgebraicGeometry.PerfectObjectCompact
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory

/-! # Isomorphism detection by compact quasi-coherent derived objects

Source: Stacks Project, Tags 09IS and 09M1; detection step of Tag 0A9R.
(blueprint: lem-sc-derived-qcoh-compact-detection).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- All compact objects jointly detect isomorphisms in D_QCoh(X).
Source: Stacks Project, Tags 09IS and 09M1; the detection step of Tag 0A9R.
(blueprint: lem-sc-derived-qcoh-compact-detection).

Proof: Choose small-Hom derived models on X and its opens using K-injective
resolutions. Localization equivalences preserve quasi-coherence, shifted Hom
sets, and coproducts, so they transport the hypothesis and the desired conclusion.
Complete g to a distinguished triangle A → B → C → A[1]. The cone C has
quasi-coherent cohomology by the cohomology exact sequence. Every shift of a
perfect object is perfect, hence compact by Tag 09M1. The assumed Hom bijections
and the long exact Hom sequence therefore give Hom(P[n], C) = 0 for every
perfect P and integer n. The class of objects Q with Hom(Q[n], C) = 0 for all n
is closed under isomorphisms, shifts, cones, retracts, and arbitrary coproducts:
the cone assertion follows from exactness, and the coproduct assertion from the
universal property identifying Hom from a sum with a product. Perfect generation
makes this class all of D_QCoh(X). In particular the identity of C is zero, so C
is a zero object. Exactness now makes Hom(T, g) bijective for every T; Yoneda
implies g is an isomorphism. Transport this conclusion to the given model.
For the empty scheme the derived category is zero and the same argument applies. -/
theorem derivedQCoh_compact_detection (X : Scheme.{u}) [IsNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    let _ : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
    ∀ (A B : schemeDerivedQCohCategory X) (g : A ⟶ B),
      (∀ P : schemeDerivedQCohCategory X, IsCompactObject P →
        Function.Bijective (fun a : P ⟶ A ↦ a ≫ g)) → IsIso g := by
  sorry

end AlgebraicGeometry
