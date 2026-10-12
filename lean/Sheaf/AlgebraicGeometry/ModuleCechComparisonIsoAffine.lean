/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.ModuleCechComparison
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Sheaf.Paper.CechComparisonMapNaturality
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray

/-! # The canonical Čech comparison for affine-intersection covers

Source: Stacks Project, Cohomology of Schemes, Tag 01XD, via Cohomology of Sheaves,
Tags 01ET and 01EQ (blueprint: lem-sc-cech-comparison-map-iso-affine).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- For a quasi-coherent module and an open cover whose nonempty finite intersections
are affine, the canonical Čech comparison is an isomorphism of global-section modules.
Thus this canonical map gives the identification of `lem-pc-cech-computes`.
Source: Stacks Project, Tags 01XD, 01ET and 01EQ
(blueprint: lem-sc-cech-comparison-map-iso-affine).
Proof: fix a degree p. The canonical comparison of
lem-sc-cech-comparison-map-naturality is defined by the alpha and beta maps of an
injective resolution and is independent of the resolution. Under the present affine
intersection and quasi-coherence hypotheses, lem-pc-cech-computes identifies Čech
cohomology with sheaf cohomology. Stacks 01ET identifies the isomorphism as the
canonical map of 01EQ: higher cohomology on the intersections vanishes by 01XB,
so the Čech-to-cohomology spectral sequence degenerates. Consequently the canonical
comparison in degree p is an isomorphism, giving precisely that identification. -/
theorem moduleCechComparison_isIso_of_affine (X : Scheme.{u}) {ι : Type u}
    (U : ι → X.Opens)
    (hU : ∀ (n : ℕ) (y : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hcover : iSup U = ⊤) (F : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F] (p : ℕ)
    (c : ((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).homology p ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace p).obj F)
    (hc : IsModuleCechComparison U F p c) : IsIso c := by
  sorry

end AlgebraicGeometry.Scheme.Modules
