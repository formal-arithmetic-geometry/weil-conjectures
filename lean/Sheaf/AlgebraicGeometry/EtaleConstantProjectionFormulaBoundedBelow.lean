/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Additive
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.FilteredColimitDerivedTensor
import Sheaf.Algebra.Homology.FilteredColimitsTensor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.CategoryTheory.RightDerivedFunctorTruncationIso
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Sites.GlobalSections
import Sheaf.Paper.ProjectionMateExact
import Sheaf.CategoryTheory.TruncationTriangle

import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Single
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Sheaf.Algebra.Homology.IntegerFlatRepresentative
import Sheaf.RingTheory.Flat.LazardPresentation
import WeilConjectures.CategoryTheory.RightDerivedFunctorTruncationIso
import WeilConjectures.CategoryTheory.TruncationTriangle
/-!
# Tensoring derived global sections with a bounded-below constant integer complex

Source: Stacks Project, Etale Cohomology, Tag 0F0E (lemma-pull-out-constant);
Weil conjectures blueprint, sec-smooth-purity/sk-prop-sf-kunneth-ordinary,
lem-kun-0f0e (blueprint: lem-kun-0f0e).

Integer modules are encoded as modules over `ULift ℤ`, as in def-kun-derived-tensor.
This is the usual category of abelian groups, with its integer tensor product, transported
along `ULift.ringEquiv`. Both inputs lie in the full bounded-below derived subcategories.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The canonical constant-coefficient projection map is an isomorphism for bounded-below
integer complexes on a quasi-compact quasi-separated scheme.
Source: Stacks Project, Tag 0F0E (blueprint: lem-kun-0f0e).

Proof plan from the DAG:
1. Identify the map with the counit mate of def-kun-constant-projection-morphism.
Apply lem-weil-pbc-ringed-projection-mate-exact to the terminal ringed-topos morphism.
This gives the identity comparison for the unit and compatibility with triangles in K.
In E, tensor distributes over the two summands of a mapping cone; naturality identifies
its off-diagonal differential, with the same signs on the shifted summands. Applying
RΓ, triangulated by lem-pc-right-derived-functor-triangulated, gives triangle compatibility.
Consequently the isomorphism property is stable under shifts and finite extensions.
2. Global sections is left exact on the Grothendieck category of abelian etale sheaves.
Apply lem-weil-pbc-derived-functor-truncation-iso to 0 → C in degree c - 1 to show
that RΓ preserves a lower cohomological bound c. The standard t-structure then supplies
a representative of RΓ(C) zero below c.
3. A bounded-below flat integer complex P is K-flat, as is its constant complex.
Indeed flat integer groups are torsion free, and their subgroups are flat by
lem-weil-pbc-pid-torsion-free-module-flat. Thus the good truncations of P are bounded
flat complexes, K-flat by lem-pc-bounded-above-flat-kflat-site. Their filtered colimit
is P. Constant sheaves are exact, preserve flatness and colimits; use
lem-pc-module-filtered-colimits-tensor and exact filtered colimits to pass acyclicity
to this colimit. The argument also applies to the stupid tails and heads of P.
4. For E a sheaf in degree zero and K a flat group M in degree zero, write M as a
directed colimit of finite free groups by lem-kun-lazard-flat-module. Constant sheaves
and sheaf tensor preserve this colimit. On the target use
lem-weil-pbc-cohomology-filtered-colimit, valid because X is qcqs; on the source use
lem-pc-filtered-colimit-derived-tensor. Each finite free comparison is a finite sum of
the unit comparison from step 1. Naturality identifies the systems, so their colimit
comparison is invertible. Step 2 handles negative degrees.
5. Keep K = M[0] flat. For each integer n truncate E at n. Flat tensor commutes with
cohomology, and lem-weil-pbc-derived-functor-truncation-iso identifies the degree-n
source and target with those for the truncation. The latter has finite cohomological
support. Its canonical truncation triangles (lem-weil-pbc-truncation-triangle) reduce
it to shifts of sheaves. Step 4 and the long exact cohomology sequences give the claim.
6. Induct on the number of nonzero terms of a bounded flat coefficient complex P.
The stupid truncation triangle removing its lowest term reduces to a shorter complex
and a shifted flat group. Step 1 and the five lemma give the middle comparison.
7. For general K choose the bounded-below flat model P from
lem-kun-torsionfree-complex-model. Let E have a representative zero below a, and P
one zero below b. Fix n and N ≥ max(b, n - a + 1). The stupid tail T above N has both
E tensor T and RΓ(E) tensor T zero below a + N + 1 ≥ n + 2; step 2 gives the same bound
after RΓ. Step 3 ensures these ordinary tensors compute derived tensor. The triangle
T → P → B, with B the bounded stupid head, therefore induces degree-n isomorphisms
from the P terms to the B terms on both sides. Step 6 makes the comparison for B
invertible. Its natural square gives invertibility in degree n for P. Since n is arbitrary,
the original map is an isomorphism. -/
theorem isIso_constantDerivedProjectionMap_of_boundedBelow
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (E : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))))
    (K : DerivedCategory.Plus (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    IsIso (constantDerivedProjectionMap (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) X
      (DerivedCategory.Plus.ι.obj E) (DerivedCategory.Plus.ι.obj K)) := by
  sorry

end AlgebraicGeometry.Etale
