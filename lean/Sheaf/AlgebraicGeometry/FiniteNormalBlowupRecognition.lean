/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Blowup.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry
import WeilConjectures.Blowup.Complement
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Gluing

/-! # Recognition of a finite normal model of an integral blowup

Source: ILO, Exposé VIII, 3.4.6(i), printed p. 111, normalization part;
Stacks Project, Tags 02ND and 035P
(blueprint: lem-trf-finite-normal-blowup-recognition).

The function-field isomorphisms are characterized by the commuting generic-point
morphisms, so they identify the fields through the given structure maps. The affine
integral-closure assertion is the elementwise characterization in the common field:
the image of the upstairs ring consists exactly of the elements integral over the
downstairs ring. The normalization is the existing normalization in the function
field, without an assumption that its structure morphism is finite.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- A finite normal model of an integral blowup, identical on a dense open, is its
normalization, with the affine integral-closure identifications in the common field.

Source: ILO, Exposé VIII, 3.4.6(i), printed p. 111, normalization part;
Stacks Project, Tags 02ND, 01WN, 01RV and 035P
(blueprint: lem-trf-finite-normal-blowup-recognition).

Proof:
1. By lem-sfb-integral-blowup-projective-geometry the ordinary blowup is integral.
   By thm-nagata-global-blowup-complement its inverse image of U is isomorphic to U,
   hence is a nonempty dense integral open. The given restriction of f is an isomorphism
   onto this open.
2. The inverse image V is irreducible because it is isomorphic to U. Its density makes
   Y irreducible. The domain stalks make Y reduced; V also makes Y nonempty. Apply the
   reduced-and-irreducible characterization in def-pc-integral-scheme.
3. A finite morphism is closed by lem-weil-pbc-finite-closed-map-finite-fibres. Its image
   contains the dense open above U, so f is surjective. Generic stalks are unchanged on
   nonempty opens (def-sc-function-field, lem-sc-integral-function-field-affine-fraction).
   Restricting to the common open gives the field identifications induced by p and f.
4. Apply lem-sfb-finite-normal-cover-normalization to f. On an affine open Spec C its
   preimage is Spec D, where C injects into D and D is the integral closure of C in k(Y).
   Indeed D is finite, hence integral over C, and is integrally closed in its fraction
   field by normality of Y; an element integral over C is integral over D and lies in D.
   Transport to k(X). By def-fin-normalization-extension and def-sc-normalization these
   affine identifications glue to an isomorphism with the normalization over the blowup.
5. For uniqueness, any competing morphism over the blowup gives on each affine open a
   C-algebra map from the integral closure into D. For z in that closure write bz = a
   with a,b in C and b nonzero, using lem-sc-integral-function-field-affine-fraction.
   Both maps send z to elements satisfying b times the image equals a; cancellation in
   the domain D makes them equal. Apply lem-weil-pbc-scheme-morphism-gluing. Thus the
   local identifications give the unique isomorphism. Finiteness of normalization is
   a consequence, rather than a hypothesis; no excellence is used. -/
theorem finite_normal_blowup_recognition
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (J : X.IdealSheafData) (hJ : J ≠ ⊥)
    (hfinite : J.toModules.IsQuasiCoherentFiniteType)
    (U : X.Opens) [Nonempty U] (hUdense : Dense (U : Set X))
    (hJU : J.comap U.ι = ⊤)
    {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : Y ⟶ J.blowup) [IsFinite f]
    (hnormal : ∀ y : Y,
      IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
    (hVdense : Dense ((f ≫ J.blowupMap) ⁻¹' (U : Set X)))
    (hVU : IsIso ((f ≫ J.blowupMap) ∣_ U)) :
    ∃ (_ : IsIntegral J.blowup) (_ : IsIntegral Y),
      Surjective f ∧
      ∃ (eB : J.blowup.functionField ≅ X.functionField)
        (eY : Y.functionField ≅ X.functionField),
        Spec.map eB.hom ≫ J.blowup.fromSpecFunctionField ≫ J.blowupMap =
          X.fromSpecFunctionField ∧
        Spec.map eY.hom ≫ Y.fromSpecFunctionField ≫ f =
          Spec.map eB.hom ≫ J.blowup.fromSpecFunctionField ∧
        (∀ (A : J.blowup.Opens) (_hA : IsAffineOpen A) [Nonempty A],
          ∃ (_ : Nonempty (f ⁻¹ᵁ A)),
            IsAffineOpen (f ⁻¹ᵁ A) ∧ Function.Injective (f.app A) ∧
            Function.Injective (Y.germToFunctionField (f ⁻¹ᵁ A) ≫ eY.hom) ∧
            f.app A ≫ Y.germToFunctionField (f ⁻¹ᵁ A) ≫ eY.hom =
              J.blowup.germToFunctionField A ≫ eB.hom ∧
            ∀ z : X.functionField,
              (∃ d : Γ(Y, f ⁻¹ᵁ A),
                (Y.germToFunctionField (f ⁻¹ᵁ A) ≫ eY.hom) d = z) ↔
              (J.blowup.germToFunctionField A ≫ eB.hom).hom.IsIntegralElem z) ∧
        ∃! e : Y ≅ J.blowup.normalization,
          e.hom ≫ J.blowup.fromNormalization = f := by
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
