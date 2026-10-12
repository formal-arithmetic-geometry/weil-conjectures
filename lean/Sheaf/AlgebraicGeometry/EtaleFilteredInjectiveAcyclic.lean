/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Acyclicity of filtered colimits of injective étale sheaves

Source: Stacks Project, Cohomology on Sites, Tag 0739, the final claim and its proof,
applied to the qcqs objects of the small étale site as in Tag 073E.
(blueprint: lem-weil-pbc-etale-filtered-injective-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Filtered colimits of injective abelian étale sheaves are global-sections acyclic
on a qcqs scheme. The colimit need not itself be injective.
Source: Stacks Project, Tag 0739, final paragraph; Tag 073E, proof.
(blueprint: lem-weil-pbc-etale-filtered-injective-acyclic).

Proof:
1. Take `B` to consist of the qcqs objects of the small étale site, and take the
finite coverings with source and members in `B`. Finite affine refinements are
cofinal. All their iterated fibre products are qcqs: maps from qcqs schemes to
qcqs schemes are qcqs, and these properties persist under base change and composition.
2. Sections on objects of `B` commute with filtered colimits. For abelian sheaves
this follows from the module-valued sections result with the ring of integers.
A term of a finite-cover Čech complex is a finite product of sections on these
fibre products. Finite products of abelian groups are finite biproducts, so they
commute with colimits. Compatibility with restriction maps identifies the whole
Čech complex of `colim J` with the filtered colimit of the Čech complexes of `J i`.
3. Each `J i` is injective, hence its positive Čech cohomology vanishes. Exactness
of filtered colimits of abelian groups implies that the colimit Čech complex is
exact in every positive degree.
4. Apply the Čech vanishing criterion to `B` and these cofinal finite coverings.
It gives vanishing of positive derived sections on each object of `B`. The identity
of `Y` is a terminal étale object in `B`; sections there are naturally global
sections. Transport derived sections along this natural isomorphism to obtain
vanishing of the stated positive right derived global sections. -/
theorem isZero_rightDerived_globalSections_colimit_of_injective
    (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y]
    (I : Type u) [SmallCategory I] [IsFiltered I]
    (J : I ⥤ Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hJ : ∀ i : I, Injective (J.obj i)) (n : ℕ) :
    IsZero (((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived
      (n + 1)).obj (colimit J)) := by
  sorry

end AlgebraicGeometry.Scheme
