/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RepleteSheafTopos
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteOnContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Sheaf.AlgebraicGeometry.WContractibleAffineCover
public import Sheaf.CategoryTheory.SiteCoveringAxioms

/-!
# Repleteness of the pro-étale topos

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
`sk-prop-pe-replete/det-pe-replete-epimorphism.md`
(blueprint: det-pe-replete-epimorphism).
-/

@[expose] public section

universe u w

namespace AlgebraicGeometry.Scheme

/-- Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
`sk-prop-pe-replete/det-pe-replete-epimorphism.md`, node `det-pe-replete-epimorphism`
(blueprint: det-pe-replete-epimorphism).

For every scheme, the topos of set-valued sheaves on its small pro-étale site is
replete: inverse sequences with epimorphic transition maps have epimorphic limit
projections at every natural-number index.

Proof:
1. Fix an inverse sequence `F` with epimorphic adjacent maps and an index `m`.
   By `det-pe-replete-definition` and the local-surjectivity criterion
   `lem-weil-pbc-site-sheaf-sets-epi-locally-surjective`, it suffices to lift each
   section `y` of `F_m` over an arbitrary site object `U` after a covering of `U`.
2. By `det-pe-wcb-cover`, cover `U` by affines `W_i = Spec D_i`, with each `D_i`
   w-contractible. By `det-pe-weak-contractible-equivalences`, each `W_i` is weakly
   contractible. This applies to arbitrary `U`, without quasi-compactness assumptions.
3. Apply `det-pe-replete-on-contractible` to the original sequence and each `W_i`.
   The map on sections of the limit projection at `m` is surjective there, so the
   restriction of `y` lifts to a section of the limit over `W_i`.
4. These separate lifts make the projection locally surjective, hence epimorphic by
   `lem-weil-pbc-site-sheaf-sets-epi-locally-surjective`. No compatibility on overlaps
   is required. Since the sequence and `m` were arbitrary, the topos is replete.
-/
theorem isReplete_proEtale (X : Scheme.{u}) :
    CategoryTheory.GrothendieckTopology.IsReplete.{u + 1, u, w} (ProEt.topology X) := by
  intro F hF m
  apply (CategoryTheory.Sheaf.isLocallySurjective_iff_epi _).1
  constructor
  intro U y
  obtain ⟨I, W, f, hcov, hW⟩ := ProEt.exists_wContractible_affine_cover X U
  have hcov' : CategoryTheory.Sieve.ofArrows W f ∈ ProEt.topology X U :=
    CategoryTheory.Precoverage.generate_mem_toGrothendieck hcov
  apply (ProEt.topology X).superset_covering _ hcov'
  rintro V g ⟨_, a, _, ⟨i⟩, rfl⟩
  obtain ⟨D, hD, e, _⟩ := hW i
  have : IsWContractibleRing D := hD
  have hw : (ProEt.topology X).IsWeaklyContractible.{max (u + 1) w} (W i) :=
    ProEt.isWeaklyContractible_of_iso e.symm
  exact (CategoryTheory.Presheaf.imageSieve _ y).downward_closed
    ((proetale_surjective_sections_of_epi_tower X F hF (W i) hw).2 m _) a

end AlgebraicGeometry.Scheme
