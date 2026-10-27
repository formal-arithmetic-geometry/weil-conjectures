/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Quasi-compact open immersions of algebraic spaces are finitely presented

Source: Stacks Project, Morphisms of Spaces, Tag 06CN; Morphisms, Tags 01TT and 01TU
(blueprint: lem-sfb-space-qc-open-finite-presentation).

Finite presentation is expressed as quasi-compactness, quasi-compactness of the relative
sheaf diagonal, and local finite presentation on compatible étale scheme charts.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-compact open immersion of algebraic spaces is of finite presentation.
There are no quasi-compactness, separation or Noetherian assumptions on the target.
Source: Stacks Project, Morphisms of Spaces, Tag 06CN, and Morphisms, Tags 01TT and 01TU
(blueprint: lem-sfb-space-qc-open-finite-presentation).

Proof:
1. Choose a surjective étale scheme atlas `V → X` using def-trf-algebraic-space.
   By def-a1-space-open-subspace its pullback `W = V ×_X U` is an open subscheme
   of `V`. By lem-trf-space-fibre-products-etale-covers the map `W → U` is a
   surjective étale atlas. Thus `W → V` gives compatible scheme charts for `j`.
2. At each point of `W`, use lem-weil-pbc-affine-opens-basis to choose an affine
   open of `V` contained in the image of `W`. Its inverse image is isomorphic to
   it by def-weil-open-immersion. The induced identity ring map has a presentation
   with zero generators and relations, so def-sbc-locally-finite-presentation
   gives local finite presentation. This property is étale-local, hence holds on
   all compatible étale scheme charts of `j`.
3. Two sections of `U` with the same image in `X` give sections of the same open
   scheme test. An open immersion has at most one section, since such a section
   identifies its image with the entire test scheme. Thus `j` is a monomorphism.
   Its relative sheaf diagonal is an isomorphism: the inverse on matching pairs
   keeps their common section. The formulas commute with restriction maps.
4. Every affine scheme test of that diagonal is isomorphic to the affine test
   scheme. It is quasi-compact by lem-weil-pbc-affine-scheme-qcqs and its identity
   atlas is surjective étale. The diagonal is therefore quasi-compact. Combine
   this with the given quasi-compactness of `j` and step 2, exactly the three
   conditions for finite presentation. Empty sources satisfy the same argument. -/
theorem finitePresentation_of_quasiCompact_openImmersion
    {S : Scheme.{u}} (U X : AlgebraicSpace S) (j : U ⟶ X)
    (hj : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom)
    (hqc : IsQuasiCompactPresheafMap j.hom.hom) :
    IsQuasiCompactPresheafMap j.hom.hom ∧
      IsQuasiCompactPresheafMap (pullback.diagonal j.hom.hom) ∧
      MapIsLocallyOfFinitePresentation j := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
