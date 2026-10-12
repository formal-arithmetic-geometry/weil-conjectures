/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
import Sheaf.AlgebraicGeometry.EtaleCechVanishingCriterion
import Sheaf.AlgebraicGeometry.EtaleQuasiCoherentDescent
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.Paper.EtaleStandardCoverCech
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.RingTheory.FaithfullyFlat.Amitsur
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Étale acyclicity of a quasi-coherent module on an affine scheme

Source: blueprint `lem-sc-etale-affine-qcoherent`, order 959;
Stacks Project, Étale Cohomology, Theorem 03P2 (affine case)
(blueprint: lem-sc-etale-affine-qcoherent).
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

set_option autoImplicit false

/-- Higher étale cohomology of the associated quasi-coherent sheaf vanishes on an affine.

Source: Stacks Project, Étale Cohomology, Theorem 03P2 (affine case)
(blueprint: lem-sc-etale-affine-qcoherent).
Proof:
1. Take the affine objects of the small étale site and finite jointly surjective affine
   étale covering families. Iterated fibre products are affine by
   `lem-weil-pbc-fibre-product-affine-spectra`, and every covering of an affine object
   admits such a refinement by `lem-weil-pbc-etale-covering-affine-refinement`.
   These verify conditions (1) and (2) of `lem-weil-pbc-cech-vanishing-criterion`.
2. On an affine object `u : U ⟶ X`, the module `u^*F` is quasi-coherent by
   `lem-weil-pbc-module-pullback-quasi-coherent`, and its associated presheaf is a sheaf
   by `lem-sc-etale-qcoherent-descent`. The composition isomorphisms of
   `lem-pc-module-pullback-identity-composition` identify its restrictions and Čech
   complex with those of `F_et` over `U`, using `def-sc-etale-qcoherent-module` and
   `def-weil-pbc-etale-site`. By `lem-sc-etale-standard-cover-cech`, replace the finite
   cover by its affine disjoint union `Spec B ⟶ Spec A`, with `A ⟶ B` faithfully flat.
   With `M = Γ(U,u^*F)`, `lem-weil-pbc-fibre-product-affine-spectra` and
   `lem-weil-pbc-module-pullback-affine-sections` identify the terms with
   `M ⊗_A B^{⊗_A(p+1)}`. Pullback coherence identifies the face maps with the Amitsur
   maps. By `lem-pc-cech-exact` the positive Čech cohomology vanishes, verifying
   condition (3) of `lem-weil-pbc-cech-vanishing-criterion`.
3. Apply that criterion at the final affine object `X`. Evaluation there is global
   sections by `def-weil-pbc-global-sections-functor`. An injective resolution is
   bounded below and K-injective by `prop-weil-pbc-kinjective-resolutions-exist`;
   thus derived evaluation computes the étale cohomology of
   `def-weil-pbc-etale-cohomology`, which vanishes in every positive degree.

For every `n`, this gives affine acyclicity in degree `n + 1`: the affine Cech
criterion and faithfully flat Amitsur exactness establish vanishing in every positive
degree, and the injective K-injective resolution identifies derived evaluation with
`Sheaf.H`. (blueprint: lem-sc-etale-affine-qcoherent-succ)

Proof: apply the affine Čech vanishing criterion to the affine basis of the small
étale site. Finite affine refinements are stable under iterated fibre products, and
the standard disjoint-union cover identifies the Čech complex with the Amitsur
complex of a faithfully flat algebra. The Amitsur complex is exact in positive
degrees, so the criterion gives vanishing of derived evaluation at the terminal
affine object. An injective K-injective resolution identifies that derived
evaluation with `Sheaf.H`, yielding the stated subsingleton.
-/
theorem etale_affine_qcoherent_succ
    (X : Scheme.{u}) [IsAffine X]
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    Subsingleton (Sheaf.H
      (AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsSheaf F) (n + 1)) := by
  sorry

theorem etale_affine_qcoherent
    (X : Scheme.{u}) [IsAffine X]
    (F : X.Modules) [F.IsQuasicoherent] :
    ∀ (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H (AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsSheaf F) q) := by
  intro q hq
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hq
  simpa [Nat.add_comm] using
    etale_affine_qcoherent_succ X F n

end AlgebraicGeometry.Etale
