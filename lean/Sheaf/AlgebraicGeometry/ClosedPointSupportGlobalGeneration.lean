/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Sheaf.AlgebraicGeometry.EtaleSupport
public import Mathlib.Topology.JacobsonSpace
public import Sheaf.AlgebraicGeometry.EtaleGloballyGenerated
import Sheaf.AlgebraicGeometry.ClosedPointSheafApproximation
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.ClosedPointField
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.AlgebraicGeometry.GeometricStalkColimits
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.OpenClosed.Stalk
import Mathlib.CategoryTheory.Sites.Point.Basic
import Sheaf.AlgebraicGeometry.GlobalGeneratedStalkwise
import Sheaf.AlgebraicGeometry.PointedEtaleStalk
import Sheaf.AlgebraicGeometry.SepClosedEtaleGlobalGeneration
import Sheaf.CategoryTheory.GloballyGeneratedSheafColimit

/-!
# Global generation of abelian étale sheaves supported on closed points

Source: Stacks Project, Lemma 59.97.3 (Tag 0F1F), second assertion;
blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-0f1f-gen.md`
(blueprint: lem-kun-0f1f-gen).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An abelian étale sheaf supported on closed points of a finite-type scheme over a
separably closed field is globally generated, with no torsion or stalk-finiteness hypothesis.
Source: Stacks Project, Lemma 59.97.3 (Tag 0F1F), second assertion
(blueprint: lem-kun-0f1f-gen).

Proof:
1. By `lem-kun-cp-approximation`, express `F` as the filtered colimit of finitely
   generated subsheaves `F_i`, each with finite closed-point support `Z_i`. Give `Z_i`
   its reduced closed subscheme structure and write `j_i : Z_i → X`. The last clause
   of that lemma and `lem-kun-04ca` give an isomorphism `F_i ≅ j_{i*}G_i`, with
   `G_i` the restriction of `F_i` to `Z_i`.
2. The finite space `Z_i` is discrete: the complement of a singleton is a finite
   union of closed singletons (`def-weil-closed-points`). Its singleton open schemes
   are affine (`def-pc-scheme`), reduced (`def-pc-reduced-scheme`), and have one prime.
   Their rings are local and equal to their localization at that minimal prime;
   `lem-weil-pbc-minimal-prime-reduced-localization-field` makes them fields.
   The quotient-chart description of a closed immersion (`def-weil-closed-immersion`)
   identifies these fields with the residue fields of `X` (`def-weil-residue-field`).
   Hence `Z_i` is the finite disjoint union of `Spec κ_X(z)`, including the empty case.
3. By `lem-kun-closed-point-field`, each such residue field is separably closed.
   By `lem-kun-03qu-global-generation`, `G_i` on each singleton component is globally
   generated. Apply `lem-kun-global-generated-stalkwise`: every stalk element is a
   finite integer linear combination of germs of sections on that component. Here
   the constant integer sheaf (`def-kun-constant-sheaf`) has stalk `ℤ`: refine a
   locally constant representative to a pointed neighbourhood where it is constant.
   `lem-kun-stalks-commute-colimits` identifies the evaluation source stalk with the
   direct sum of these integer stalks (`def-kun-global-generated`).
4. Extend each component section by zero on the other components. Their inclusions
   are étale (`lem-weil-pbc-open-immersion-etale`) and jointly cover `Z_i`
   (`def-weil-pbc-etale-site`). The sheaf axiom (`def-weil-pbc-abelian-etale-sheaves`)
   glues them: distinct overlaps are empty and diagonal overlaps agree. It also gives
   zero sections on the empty scheme. The direct-image formula
   (`def-weil-pbc-direct-image`) identifies these with global sections of `F_i`.
5. Outside `Z_i` every geometric stalk of `F_i` is zero by `def-kun-support`.
   A geometric point over `z ∈ Z_i` factors through its closed immersion: in a quotient
   chart the defining ideal maps to zero in the geometric-point field. The stalk
   isomorphism of `lemma-openclosed-stalk-lowerstar` identifies the stalk with that of
   `G_i` at this point. Restricting pointed neighbourhoods to the open singleton
   component gives the same germs (`def-weil-pbc-geometric-stalks`), with inverse
   obtained by viewing a neighbourhood over the component as one over `Z_i`.
   The global extension in Step 4 has the original germ, by the direct-image formula
   and naturality of the isomorphism. Extend the finitely many sections in Step 3;
   their integer combination proves stalkwise surjectivity of the evaluation of `F_i`.
   Apply `lem-kun-global-generated-stalkwise`, also when `Z_i` is empty.
6. All `F_i` are globally generated. Their subsheaf index is small: subsheaves are
   compatible families of subgroups of the section groups of the fixed sheaf `F`.
   Apply `lem-kun-colim-gbl-gen` to this small filtered diagram. Its global-sections
   convention agrees with `def-kun-global-generated`, since `X` is the final object
   of the small étale site. Its colimit is `F` by Step 1, proving the result. -/
theorem isGloballyGeneratedAbelianEtaleSheaf_of_support_subset_closedPoints
    {K : Type u} [Field K] [IsSepClosed K] (X : Scheme.{u})
    [X.Over (Spec (.of K))] [LocallyOfFiniteType (X ↘ Spec (.of K))]
    [QuasiCompact (X ↘ Spec (.of K))]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : etaleSheafSupport F ⊆ closedPoints X) :
    IsGloballyGeneratedAbelianEtaleSheaf F := by
  sorry

end AlgebraicGeometry.Scheme
