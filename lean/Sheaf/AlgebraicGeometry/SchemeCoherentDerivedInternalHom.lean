/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import WeilConjectures.AlgebraicGeometry.CoherentModuleLocalOnOpenCover
import Sheaf.Paper.DerivedInternalHomRestrictOpen
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.AffineDerivedTildeHomologyComparison
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import Sheaf.AlgebraicGeometry.AffinePseudoCoherentRHomQuasiCoherent
import Sheaf.Algebra.Homology.BoundedAboveCoherentRHom

/-! # Coherent derived internal Hom on a locally Noetherian scheme

Source: Stacks Project, perfect.tex, Tag 0D0C, lemma-coherent-internal-hom
(blueprint: lem-sfb-scheme-coherent-derived-internal-hom).
-/

@[expose] public section
set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Derived internal Hom from a bounded-above coherent complex to a bounded-below
coherent complex has coherent cohomology and is bounded below.
Source: Stacks Project, perfect.tex, Tag 0D0C, lemma-coherent-internal-hom
(blueprint: lem-sfb-scheme-coherent-derived-internal-hom).

Proof:
1. Choose global bounds a for K and b for L. Cover X by spectra of Noetherian rings
   using pqf-def-locnoeth. Exact open restriction preserves cohomology and these bounds
   (lem-sc-derived-open-restriction-adjunction-exact). Coherence restricts by
   lem-weil-pbc-coherent-module-local-on-open-cover. Use
   lem-sc-derived-internal-hom-restrict-open to restrict the derived internal Hom.
2. On Spec A, coherent sheaves are quasi-coherent of finite type by
   pqf-lem-coherent-ft-locnoeth. Choose module-derived representatives M,N via
   lem-pc-affine-qcoh-derived-equivalence. The comparison
   new-affine-derived-tilde-homology-comparison, the unit of
   lem-weil-pbc-affine-tilde-gamma-adjunction and the criterion
   lem-weil-pbc-quasi-coherent-finite-type-affine show their cohomology is finite,
   with the same upper and lower bounds: the unit also reflects zero modules.
3. By lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion, M is pseudo-coherent
   and admits a bounded-above finite projective representative. Apply
   lem-sc-affine-pseudo-coherent-rhom-qcoherent to identify the restricted sheaf RHom
   with the tilde construction on module RHom(M,N).
4. Apply lem-trf-bounded-above-coherent-rhom: its cohomology is finite and vanishes
   below b-a. Apply new-affine-derived-tilde-homology-comparison and the affine
   finite-type criterion again. The resulting sheaves are quasi-coherent of finite
   type, hence coherent by pqf-lem-coherent-ft-locnoeth.
5. Coherence glues by lem-weil-pbc-coherent-module-local-on-open-cover. In each
   degree below b-a all restrictions vanish, so the sheaf axiom makes the global
   cohomology sheaf zero. The same bound works on every chart, without quasi-compactness. -/
theorem scheme_coherent_derived_internal_hom
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (K L : DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (hK : ∀ j : ℤ, RingedSpace.IsCoherent X.toRingedSpace
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) j).obj K))
    (hL : ∀ j : ℤ, RingedSpace.IsCoherent X.toRingedSpace
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) j).obj L))
    (hK_bound : ∃ a : ℤ, ∀ j : ℤ, a < j → IsZero
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) j).obj K))
    (hL_bound : ∃ b : ℤ, ∀ j : ℤ, j < b → IsZero
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) j).obj L)) :
    (∀ j : ℤ, RingedSpace.IsCoherent X.toRingedSpace
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) j).obj
          ((derivedInternalHomOfUniverses.{u, u, u, w}
            (Opens.grothendieckTopology X) X.sheaf).obj (op K, L)))) ∧
    (∃ b : ℤ, ∀ j : ℤ, j < b → IsZero
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) j).obj
          ((derivedInternalHomOfUniverses.{u, u, u, w}
            (Opens.grothendieckTopology X) X.sheaf).obj (op K, L)))) := by
  sorry

end AlgebraicGeometry
