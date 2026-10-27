/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import WeilConjectures.AlgebraicGeometry.FieldExtensionFpqcCover
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.SeparatedLqfFpqcDescent
import WeilConjectures.AlgebraicGeometry.FpqcDescentEtale
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability
import WeilConjectures.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange
import Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFpqcCover

/-! # Effectivity of fpqc group forms over a field

Source: Anantharaman, *Schemas en groupes, espaces homogenes et espaces algebriques
sur une base de dimension 1*, Theorem 4.A and section 4.1, printed pages 54--55,
field case (blueprint: lem-sfb-field-fpqc-group-form-effectivity).

The representing isomorphisms are isomorphisms of group-valued functors, so they
retain the specified multiplication, identity and inversion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An fpqc sheaf of groups over a field which becomes a separated locally finitely
presented group scheme on an fpqc cover is a separated locally finite type group scheme.
Source: Anantharaman, Theorem 4.A, section 4.1, printed pages 54--55, field case
(blueprint: lem-sfb-field-fpqc-group-form-effectivity).

Proof:
1. Choose a point of the nonempty fpqc cover and its residue field L. Base change of
   the representing group scheme gives a separated locally finitely presented L-group H.
   By lem-pc-field-extension-fpqc-cover, Spec L covers Spec k. Base-change permanence
   (lem-weil-pbc-qcqs-morphism-permanence, lem-weil-pbc-separated-base-change) and
   lem-pc-yoneda give the canonical group descent datum and its cocycle on H.
2. Apply lem-sfb-lft-group-etale-component-quotient to H. Its intrinsic quotient
   q : H -> E is quasi-compact, with E separated etale, and isomorphism compatibility
   descends its datum to E. The decomposition in
   lem-weil-pbc-etale-fibre-discrete-separable-points and pqf-def-quasifinite show that
   E is locally quasi-finite. Apply lem-a1-separated-lqf-fpqc-effective-descent and
   lem-galois-fpqc-descend-etale to obtain an etale k-scheme Q with Q_L isomorphic to E.
3. The maps V_L -> H -> E = Q_L agree on double overlaps by compatibility with the
   datum. By lem-weil-pbc-fpqc-representable-descent they glue uniquely, naturally
   in V, to a transformation from the original sheaf G to the functor of points of Q.
4. Decompose Q into its open-and-closed spectra of finite separable fields, using
   lem-weil-pbc-etale-fibre-discrete-separable-points. Pulling back each piece gives
   open subfunctors G_a covering G. Their L-schemes X_a are quasi-compact since q is
   quasi-compact and each component has finite base change. By
   lem-sfb-lft-group-quasicompact-open-ample, X_a is finite type and has an ample
   invertible module.
5. The datum preserves X_a. Apply lem-sfb-field-ample-scheme-datum-effectivity,
   which does not require descent of the ample module, to obtain a k-scheme Y_a.
   The fpqc equalizers for G_a and for the functor of points of Y_a are identified
   by the given isomorphism over L and its datum compatibility. Representable
   descent (lem-weil-pbc-fpqc-representable-descent) therefore identifies them over k.
6. The fpqc sheaf G is a Zariski sheaf. Its represented open covering from step 5
   satisfies lem-pc-schemes-criterion, giving a representing k-scheme Y. Transfer
   the group operations by lem-pc-yoneda, preserving the given group functor.
   Its L-base change is H. Finally lem-weil-pbc-fpqc-descend-separated and
   lem-weil-pbc-fpqc-descend-locally-finite-type give the asserted properties of Y.
No smoothness, reducedness, commutativity, quasi-compactness of the group scheme,
or finite type of the covering scheme is required. -/
theorem exists_groupScheme_of_fpqc_form
    {k : Type u} [Field k]
    (G : (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u})
    (hG : Presheaf.IsSheaf (Scheme.fpqcTopology.over (Spec (.of k)))
      (G ⋙ forget GrpCat))
    {T : Scheme.{u}} (t : T ⟶ Spec (.of k))
    [Flat t] [Surjective t] [QuasiCompact t]
    (hlocal : ∃ P : Grp (Over T),
      IsSeparated P.X.hom ∧ LocallyOfFinitePresentation P.X.hom ∧
        Nonempty (yonedaGrp.obj P ≅ (Over.map t).op ⋙ G)) :
    ∃ P : Grp (Over (Spec (.of k))),
      IsSeparated P.X.hom ∧ LocallyOfFiniteType P.X.hom ∧
        Nonempty (yonedaGrp.obj P ≅ G) := by
  sorry

end AlgebraicGeometry
