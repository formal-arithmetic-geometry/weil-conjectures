/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Separated finite-presentation envelopes of finite-type algebraic spaces

Source: Stacks Project, Limits of Spaces, Tag 0873,
proposition-separated-closed-in-finite-presentation
(blueprint: lem-sfb-space-separated-finite-type-fp-envelope).

The base is the universe-polymorphic spectrum of the integers. Quasi-compactness
uses quasi-compact scheme atlases, including after every affine scheme test.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A separated finite-type map to a qcqs algebraic space admits a closed immersion
into a separated finitely presented algebraic space over the same target.
Source: Stacks Project, Limits of Spaces, Tag 0873
(blueprint: lem-sfb-space-separated-finite-type-fp-envelope).

Proof, following the accepted DAG split:
1. By lem-sfb-space-quasicompact-affine-tests, affine-test quasi-compactness gives
   quasi-compact pullbacks over quasi-compact scheme tests. For a quasi-compact space
   test C, choose a quasi-compact scheme atlas U of C and one T of X times_Y U.
   The composite T to X times_Y C is surjective etale by
   lem-trf-space-fibre-products-etale-covers and
   lem-weil-pbc-etale-covering-composition. Conversely affine schemes are qcqs by
   lem-weil-pbc-affine-scheme-qcqs. Thus the affine-test and quasi-compact-space-test
   conventions agree. Taking C = Y shows X is quasi-compact. The closed diagonal
   is proper by lem-sfb-space-closed-subspace-proper, hence quasi-compact.
   Then lem-sfb-space-qcqs-source-products and quasi-separatedness of Y show X is qs.
2. Apply lem-sfb-space-finite-type-fp-envelope to get X closed in W, with W to Y
   finitely presented. By lem-sfb-space-fp-qcqs-source, W is qcqs.
3. Apply lem-sfb-space-closed-subspace-fp-approximation to X closed in W. This gives
   a nonempty directed system of finitely presented closed subspaces W_a of W,
   containing X, with limit X over W. It is also the limit over Y: directedness
   makes the composites of a compatible cone to W agree, so its unique factorization
   over W is its unique factorization over Y. Closed immersion transitions are affine
   by def-weil-closed-immersion. Each W_a is qcqs by lem-sfb-space-fp-qcqs-source,
   and W_a to Y is finitely presented by lem-sfb-space-separated-fp-composition.
4. Apply lem-sfb-space-fixed-base-eventually-separated: the base Y is qs, stages
   are qcqs, transitions are affine, and the limit map is the separated f.
   Choose a separated stage Z = W_a. Its closed immersion from X and finitely
   presented map g to Y satisfy i followed by g = f by the approximation triangles.
-/
theorem exists_separated_finitePresentation_closed_envelope
    {X Y : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))} (f : X ⟶ Y)
    (hYqc : ∃ (U : Over (Spec (.of (ULift.{u} ℤ))))
      (a : yoneda.obj U ⟶ Y.obj.obj),
      CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a)
    (hYqs : IsQuasiCompactPresheafMap (prod.lift (𝟙 Y.obj.obj) (𝟙 Y.obj.obj)))
    (hsep : MapIsSeparated f)
    (hqc : IsQuasiCompactPresheafMap f.hom.hom)
    (hlft : MapIsLocally (@LocallyOfFiniteType) f) :
    ∃ (Z : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))) (i : X ⟶ Z) (g : Z ⟶ Y),
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom ∧
      MapIsSeparated g ∧ IsQuasiCompactPresheafMap g.hom.hom ∧
      IsQuasiCompactPresheafMap (pullback.diagonal g.hom.hom) ∧
      MapIsLocallyOfFinitePresentation g ∧ i ≫ g = f := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
