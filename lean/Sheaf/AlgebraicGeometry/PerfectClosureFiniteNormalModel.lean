/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W5
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Sheaf.AlgebraicGeometry.ReducedAlgebraicNormalizationFieldChange
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.DescendFinite
import WeilConjectures.AlgebraicGeometry.DescendClosedImmersion
import WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization

/-!
# A finite normal model over a finite part of a perfect closure

Source: Stacks Project, Varieties, Tag 0BXT, proof through the dense-open descent.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite normal model of perfect-closure normalization, with a dense closed-immersion
locus on both source and target.

Source: Stacks Project, Varieties, Tag 0BXT, proof, and Limits, Tags 01ZM, 01ZO,
01Z4 and 01ZP.
(blueprint: lem-weil-pbc-perfect-closure-finite-normal-model).

Proof: Write K as the directed union of its finite intermediate extensions of k.
On affine charts tensor product commutes with that union, so X_K is the inverse
limit of X_E, with affine transitions. Normalize the reduction of X_K componentwise.
Finite type over K makes X_K Noetherian; component normalization is finite and
surjective, has normal domain stalks, and is finitely presented over X_K.
Finite-presentation descent gives a model over some finite intermediate field E.
Descend finiteness after enlarging E. Its base change to K remains the normal
componentwise normalization.
On the dense normal locus of the reduction of X_K, normalization is a closed
immersion with dense inverse image. Descend this quasi-compact open and then the
closed immersion, enlarging E again. Purely inseparable base-change projections
are homeomorphisms, hence reflect surjectivity and both density assertions.
The normality over K persists under these enlargements. For empty X all schemes
and opens here are empty, and the bottom intermediate field suffices. -/
theorem exists_perfectClosure_finite_normal_model
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [IsPurelyInseparable k K] [PerfectField K]
    (X : Scheme.{u}) (q : X ⟶ Spec (.of k))
    [LocallyOfFiniteType q] [QuasiCompact q] :
    ∃ E : IntermediateField k K, Module.Finite k E ∧
      ∃ (Y : Scheme.{u})
        (f : Y ⟶ pullback q (Spec.map (CommRingCat.ofHom (algebraMap k E))))
        (U : (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k E)))).Opens),
        IsFinite f ∧ Surjective f ∧
        Dense (Set.range U.ι) ∧
        Dense (f ⁻¹ᵁ U : Set Y) ∧ IsClosedImmersion (f ∣_ U) ∧
        ∀ z : (pullback
            (f ≫ pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap k E))))
            (Spec.map (CommRingCat.ofHom (algebraMap E K))) : Scheme.{u}),
          IsDomain ((pullback
            (f ≫ pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap k E))))
            (Spec.map (CommRingCat.ofHom (algebraMap E K)))).presheaf.stalk z) ∧
          IsIntegrallyClosed ((pullback
            (f ≫ pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap k E))))
            (Spec.map (CommRingCat.ofHom (algebraMap E K)))).presheaf.stalk z) := by
  sorry

end AlgebraicGeometry
