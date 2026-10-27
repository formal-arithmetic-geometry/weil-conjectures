/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.SpaceSeparatedFiniteTypeFPEnvelope
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import WeilConjectures.AlgebraicGeometry.EventuallyClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Proper algebraic spaces as limits over a fixed scheme base

Source: Stacks Project, Limits of Spaces, Tag 0A0W,
lemma-proper-limit-of-proper-finite-presentation, specialized to a scheme base
(blueprint: lem-sfb-proper-space-fixed-base-fp-limit).

The ambient base is the universe-polymorphic spectrum of the integers. The
natural transformation to the constant diagram on `T` fixes the base throughout.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A proper algebraic space over a qcqs scheme is a directed inverse limit of proper,
finitely presented spaces over that same scheme, with closed transition and cone maps.
Source: Stacks Project, Limits of Spaces, Tag 0A0W
(blueprint: lem-sfb-proper-space-fixed-base-fp-limit).

Proof, following the accepted DAG split:
1. Use lem-sfb-space-separated-finite-type-fp-envelope to embed X as a closed
   subspace of a separated finitely presented Z over T. Quasi-compactness and
   lem-sfb-space-qcqs-source-products make Z qcqs.
2. Apply lem-sfb-space-closed-subspace-fp-approximation to X in Z. Its nonempty
   directed system has closed transition and cone maps. By
   lem-sfb-space-separated-fp-composition its stages are finitely presented over T;
   lem-sfb-space-closed-subspace-proper and lem-sfb-space-qcqs-source-products
   make the stages separated and qcqs.
3. Choose a finite affine open cover of T using
   lem-weil-pbc-qcqs-finite-affine-open-cover, allowing the empty cover for empty T.
   By lem-sfb-space-flat-proper-fp-locality it suffices to prove eventual properness
   on each member V. Apply lem-sfb-space-weak-chow to Z over V, obtaining a proper
   universally surjective scheme cover P with an immersion into projective space.
4. Pull the stages and X back to P. These are closed subschemes with closed
   transitions by lem-weil-pbc-closed-immersion-base-change. The fibre-product
   universal property gives the same inverse limit after both base changes.
   The schemes are qcqs and their maps to projective space are immersions, hence
   locally of finite type, by lem-weil-pbc-proper-fp-permanence and
   lem-weil-pbc-immersion-base-change-lft.
5. By lem-sfb-space-proper-base-change and lem-sfb-space-proper-composition the
   limiting scheme is proper over V. Use lem-sfb-space-representable-proper-tests
   to read this as scheme properness. Projective space is proper over V by
   lemma-nagata-projective-space-base-change-proper. Apply
   lem-weil-pbc-proper-over-separated and lem-weil-pbc-proper-immersion-closed:
   the limiting immersion into projective space is closed.
6. Projective space is qcqs by lem-weil-pbc-affine-scheme-qcqs and
   lem-weil-pbc-qcqs-morphism-permanence. Apply
   lem-weil-pbc-eventually-closed-immersion to obtain closed projective immersions
   at all sufficiently large stages. They are proper over V by
   lem-weil-pbc-proper-fp-permanence.
7. The universally surjective Chow cover of each such stage remains surjective
   after every space base change. For any closed subset C of that stage, its image
   in the base equals the image of its inverse image in the proper scheme cover,
   and is therefore closed. Thus the stage is universally closed, and its existing
   separated finite-presentation map is proper. This uses
   lem-sfb-space-weak-chow, lem-sfb-space-representable-proper-tests,
   lem-weil-pbc-proper-fp-permanence and lem-sfb-space-proper-base-change.
8. Choose a common bound for the finite affine cover and use
   lem-sfb-space-flat-proper-fp-locality. For an empty cover choose any index.
   Restrict to the nonempty directed upper tail. Every old index has a larger
   tail index; compatible cones extend uniquely along the transitions, so the
   restricted cone still has limit X. All its maps retain their stated properties. -/
theorem exists_proper_finitePresentation_closedImmersion_limit
    (T : Over (Spec (.of (ULift.{u} ℤ))))
    [CompactSpace T.left] [QuasiSeparatedSpace T.left]
    (X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (f : X ⟶ schemeSpace T) (hf : MapIsProper f) :
    ∃ (K : Type u) (_ : PartialOrder K) (_ : Nonempty K) (_ : IsDirected K (· ≤ ·))
      (D : Kᵒᵖ ⥤ AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
      (p : D ⟶ (Functor.const Kᵒᵖ).obj (schemeSpace T))
      (π : (Functor.const Kᵒᵖ).obj X ⟶ D),
      (∀ k : Kᵒᵖ, MapIsProper (p.app k) ∧
        IsQuasiCompactPresheafMap (p.app k).hom.hom ∧
        IsQuasiCompactPresheafMap (pullback.diagonal (p.app k).hom.hom) ∧
        MapIsLocallyOfFinitePresentation (p.app k)) ∧
      (∀ (k l : Kᵒᵖ) (a : k ⟶ l),
        IsRepresentableWith (fun _ _ q ↦ IsClosedImmersion q.left) (D.map a).hom.hom) ∧
      (∀ k : Kᵒᵖ,
        IsRepresentableWith (fun _ _ q ↦ IsClosedImmersion q.left) (π.app k).hom.hom ∧
        π.app k ≫ p.app k = f) ∧
      Nonempty (IsLimit (Cone.mk X π)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
