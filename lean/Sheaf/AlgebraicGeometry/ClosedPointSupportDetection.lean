/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Sheaf.AlgebraicGeometry.EtaleSupport
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.GeometricStalkCohomology
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.EtaleLfpAndFiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.GeometricStalkAsPullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.AlgebraicGeometry.EtaleGloballyGenerated
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.ClosedPointSupportGlobalGeneration
import Sheaf.AlgebraicGeometry.ClosedPointSupportVanishing
import Sheaf.AlgebraicGeometry.UnboundedEtaleCohomologyAcyclicBasis

/-!
# Detection of derived etale sheaves supported at closed points

Source: Stacks Project, Tag 0F1G, Lemma 59.97.4; blueprint
`sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-0f1g.md`
(blueprint: lem-kun-0f1g).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Over a separably closed field, an unbounded derived abelian etale sheaf supported
at closed points vanishes if and only if all its global hypercohomology groups vanish.
The support hypothesis uses the union of the geometric-stalk supports of all cohomology
sheaves. Exactness of geometric stalks identifies this with the condition that the derived
stalk can be nonzero only at a closed point.

Source: Stacks Project, Tag 0F1G, Lemma 59.97.4
(blueprint: lem-kun-0f1g).

Proof plan:
1. If `Q` is zero, take its zero K-injective representative. Its complex of sections
   is zero, so every global hypercohomology group is zero (`def-kun-rgamma-unbounded`).
2. Set `F_q = H^q(Q)`. By `lem-kun-stalks-of-cohomology`, the stalk of `F_q` is the
   cohomology of the stalk of `Q`. Thus each `F_q` is supported at closed points, in
   the sense of `def-kun-support`.
3. Use the quasi-compact objects of the small etale site as a covering basis. Affine
   opens cover every object (`lem-weil-pbc-affine-opens-basis`) and are quasi-compact
   (`lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`). Their inclusions and
   composites are etale (`lem-weil-pbc-etale-composition-cancellation`), giving covers
   in `def-weil-pbc-etale-site`. Each such object is of finite type over the field:
   etale maps are locally of finite presentation (`lem-kun-etale-lfp`), finite-type
   algebras compose by adjoining their finite lists of generators, and the source is
   quasi-compact (`def-weil-finite-type-morphism`). The basis includes `X` itself.
4. For a basis object `j : U → X`, restriction is inverse image
   (`lem-weil-pbc-etale-inverse-image-restriction`), and the stalk at a geometric point
   of `U` equals the stalk at its image (`lem-kun-stalk-as-pullback` and
   `lem-weil-pbc-inverse-image-composition`). A nonzero stalk therefore maps to a
   closed point `x` of `X`. Passing to affine neighborhoods, etale composition and
   cancellation reduce to an etale algebra. Its residue-field extension is finite
   separable (`lem-weil-pbc-etale-algebra-residue-field-separable`). Since `κ(x)` is
   finite over the base field (`lem-kun-closed-point-field`), the residue field at
   the original point is also finite over it. The same closed-point criterion on
   the finite-type scheme `U` makes that point closed. Hence `F_q|_U` has closed-point
   support as well.
5. By `lem-kun-0f1f-vanish`, each restricted `F_q` has no positive-degree cohomology
   on every basis object. Apply `lem-kun-0bkz` to this basis and the unbounded object
   `Q` to identify `H^q(X,Q)` with `H^0(X,F_q)`. Degree-zero sheaf cohomology is ordinary
   sections: an injective resolution starts with the sheaf as the first kernel, and
   sections preserve kernels. Thus all the sections of every `F_q` vanish.
6. By `lem-kun-0f1f-gen` and `def-kun-global-generated`, the evaluation map from the
   sum indexed by global sections onto `F_q` is an epimorphism. All these sections
   are zero, so this evaluation is zero. Cancellation then gives `id(F_q) = 0`,
   hence `F_q` is zero for every integer `q`.
7. Finally `lem-kun-d-zero-cohomology` implies that `Q` is zero. No lower bound,
   torsion condition, or constructibility assumption is used. -/
theorem isZero_iff_cohomology_of_support_closedPoints
    {K : Type u} [Field K] [IsSepClosed K]
    (X : Scheme.{u}) [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    (Q : _root_.DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hQ : X.etaleComplexSupport Q ⊆ closedPoints X) :
    IsZero Q ↔ ∀ i : ℤ, IsZero ((cohomology AddCommGrpCat.{u + 1} X i).obj Q) := by
  sorry

end AlgebraicGeometry.Etale
