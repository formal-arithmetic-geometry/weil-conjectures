/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCompactFppfLocal
import Sheaf.AlgebraicGeometry.SpaceEventualClosedImmersion

/-! # Finite-presentation closed envelopes for quasi-affine morphisms

Source: Stacks Project, Limits of Algebraic Spaces, Tag 0871,
lemma-quasi-affine-closed-in-finite-presentation
(blueprint: lem-sfb-space-quasiaffine-fp-envelope).

The quasi-affine hypothesis uses representability with the existing scheme property.
Quasi-compactness of the base uses the existing scheme-atlas predicate. Morphism
quasi-compactness and quasi-separatedness use the shared affine-test predicates.
Separation of the base is absolute.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally finite type quasi-affine morphism to a qcqs algebraic space has a closed
embedding into an algebraic space of finite presentation over that target.
Source: Stacks Project, Limits of Algebraic Spaces, Tag 0871,
lemma-quasi-affine-closed-in-finite-presentation
(blueprint: lem-sfb-space-quasiaffine-fp-envelope).

Proof:
1. By [lem-sfb-space-quasiaffine-affine-factorization], factor `g` as a quasi-compact
   open immersion `A → Z` followed by an affine map `Z → B`. By
   [lem-sfb-space-affine-locality], `Z` is qcqs. Pull back its quasi-compact atlas to
   see that `A` is quasi-compact, using [lem-sfb-space-quasicompact-fppf-local].
2. By [lem-sfb-space-affine-fp-limit], write `Z` as a small nonempty directed limit
   of affine finitely presented `B`-spaces `Z_i`, with affine transitions. Their
   qcqs property follows from [lem-sfb-space-affine-locality]. Apply
   [lem-sfb-space-limit-open-cover-descent] to the two-member cover `A, Z` of `Z`.
   Obtain a quasi-compact open `U_0` at a stage whose inverse image is `A`.
3. For later stages take the inverse images `U_i` of `U_0`. By the same open-cover
   descent lemma they are qcqs with affine transitions. Their sheaf limit is `A`:
   on every test scheme the compatible tuples are exactly those in the `Z_i`
   whose initial component lies in `U_0`. The directed tail is cofinal.
4. Apply [lem-sfb-space-eventual-closed-immersion] over the common base `B` to
   the identity closed immersion of `A` into this limit. Since `g` is locally of
   finite type, some projection `e : A → U_i` is a closed immersion.
5. By [lem-sfb-space-qcqs-permanence], `U_i → Z_i` is a quasi-compact open
   immersion, hence finitely presented by [lem-sfb-space-qc-open-finite-presentation].
   Its composite `v : U_i → B` is finitely presented by
   [lem-sfb-space-separated-fp-composition]. Put `C = U_i`; all projections are
   `B`-maps, giving `e ≫ v = g`. -/
theorem exists_closedImmersion_finitePresentation_of_quasiAffine
    {S : Scheme.{u}} {A B : AlgebraicSpace S} (g : A ⟶ B)
    (hlft : MapIsLocally (@LocallyOfFiniteType) g)
    (hqa : IsRepresentableWith (fun _ _ p ↦ IsQuasiAffineHom p.left) g.hom.hom)
    (hqc : IsQuasiCompact B.obj)
    (hqs : IsAbsolutelyQuasiSeparated B) :
    ∃ (C : AlgebraicSpace S) (e : A ⟶ C) (v : C ⟶ B),
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) e.hom.hom ∧
      (MapIsQuasiCompact v.hom.hom ∧
        MapIsQuasiSeparated v.hom.hom ∧
        MapIsLocallyOfFinitePresentation v) ∧
      e ≫ v = g := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
