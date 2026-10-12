/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.EtaleCechVanishingCriterion
import Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings
import Sheaf.AlgebraicGeometry.EtaleSectionsFilteredColimit
import Sheaf.CategoryTheory.InjectiveSheafCechAcyclic

/-!
# Acyclicity of filtered colimits of injective etale sheaves

Source: Stacks Project, Tag 0739, proof, last paragraph, and Tag 03Q5.
(blueprint: lem-weil-pbc-etale-injective-colimit-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A filtered colimit of injective etale abelian sheaves is acyclic for global
sections on a quasi-compact quasi-separated scheme.
Source: Stacks Project, Tag 0739, proof, last paragraph, applied to the qcqs
etale basis as in Tag 03Q5.
(blueprint: lem-weil-pbc-etale-injective-colimit-acyclic)

Proof: Let B consist of the qcqs objects in the small etale site. Every covering
of a B-object admits a finite affine etale refinement. Finite fibre products
of objects in these coverings remain qcqs, by base change and composition of
qcqs morphisms. Sections of a filtered colimit commute with evaluation on B:
use finite local representatives and a common upper stage for their finitely
many matching equalities. Apply this also on every covering fibre product.
Thus on a finite B-cover the Cech complex of the colimit is the colimit of
the Cech complexes of the injectives: its products are finite and commute with
filtered colimits. The latter complexes have zero positive cohomology by
injective Cech acyclicity. Exactness of filtered colimits of abelian groups
therefore gives zero positive Cech cohomology for the colimit. The Cech
vanishing criterion on B gives zero positive right derived evaluation on
every B-object. The terminal etale object X belongs to B, and evaluation
there is naturally global sections. Transporting right derived evaluation
along this natural isomorphism yields the stated vanishing. No torsion
hypothesis or bound on the index below the coefficient universe is used;
all covers in this calculation are finite. For the zero diagram and for
empty X the groups vanish as well. -/
theorem isZero_rightDerived_globalSections_colimit_of_injective_coefficientSize
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {J : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hinjective : ∀ i, Injective (J.obj i)) {c : Cocone J} (hc : IsColimit c)
    (q : ℕ) (hq : 0 < q) :
    IsZero (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived q).obj
      c.pt) := by
  sorry

end AlgebraicGeometry.Scheme
