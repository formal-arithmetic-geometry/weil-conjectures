/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.FieldTheory.AlgebraicClosure
public import Sheaf.TraceFormula.LocalDimensionFormula
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.GlobalSectionsSeparable
import WeilConjectures.AlgebraicGeometry.GlobalSectionsProper
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.NormalSteinConstantField
import Sheaf.TraceFormula.SmoothGeometricallyNormal
import Sheaf.AlgebraicGeometry.FiniteSeparableBaseRefinement
import WeilConjectures.Mathlib.RingTheory.Etale.Field

/-! # Constants and markings of a finite smooth projective curve cover

Source: Stacks Project, Tags 03H0, 0BUG, 0G80, 0C4Q; de Jong, Families of curves and
alterations, §3.5 (blueprint: lem-sfb-smooth-cover-constant-field-marking).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Generic evaluation identifies the global sections of the covering curve with its
specified algebraic constant field. The inverse evaluation isomorphism induces the canonical
factorization, and the marking is already reduced and finite étale over those constants.
Source: Stacks Project, Tags 03H0, 0BUG, 0G80, 0C4Q; de Jong §3.5
(blueprint: lem-sfb-smooth-cover-constant-field-marking).

The equations `hK_C` and `hK_Y` specify the ground-field inclusions, and `hE` specifies
exactly the relative algebraic closure in the generic stalk, not an abstract isomorphic field.
The map in the intersection clause is the canonical dominant generic-stalk map of `ν`.
The function field remains the same generic stalk `Y.functionField`; the generic-composite
identity specifies its E-structure. Reducedness of the pullback says precisely that the
scheme-theoretic inverse image equals the reduced inverse image. No nonemptiness is imposed
on U or M.

Proof (the seven steps of the node):
1. By lem-pc-projective-proper and lem-pc-h0-proper-variety, Γ(Y,O_Y) is a finite field over K.
   By lem-trf-smooth-geometrically-normal, the local rings of Y are normal domains.
   lem-sc-integral-scheme-stalks-in-function-field embeds global sections into the generic stalk.
2. Apply lem-sfb-normal-stein-constant-field to Y over Spec K. Its affine Stein construction
   is Spec Γ(Y,O_Y), with evaluation map and geometrically connected fibres. Its generic-field
   description identifies this very embedded field with E, hence gives finite dimension over K.
3. The inverse of evaluation defines qE by lem-weil-pbc-morphism-into-affine-scheme. Evaluating
   again gives the generic-composite identity; restriction to K gives the factorization.
   lem-pc-global-sections-separable gives separable minimal polynomials over K.
4. lem-weil-pbc-finite-separable-base-refinement makes qE smooth and projective.
   lem-trf-smooth-connected-fibre-normal-integrality makes every field base change integral,
   including inseparable extensions. The underlying curve and its generic stalk have not changed.
5. Since M lies in U, its inverse image is étale over M by
   lem-weil-pbc-etale-scheme-base-change and finite by lem-weil-pbc-finite-morphism-permanence.
   etale-proposition-etale-reduced makes it reduced. Compose with the finite étale M over K,
   using lem-weil-pbc-finite-composition and lem-weil-pbc-etale-composition-cancellation.
6. Spec E over Spec K is étale by lem-weil-pbc-finite-separable-extension-etale. Apply
   lem-weil-pbc-etale-composition-cancellation to get the marking étale over E. This base map
   is separated by lem-weil-pbc-affine-source-morphism-separated; apply
   lem-weil-pbc-finite-permanence-over-separated for finiteness. This also covers empty M or U.
7. For C, lem-pc-projective-proper and lem-pc-h0-proper-variety give Γ(C,O_C)=K, and
   lem-trf-smooth-geometrically-normal gives normality. Apply
   lem-sfb-normal-sections-algebraic-constants with A=R=K to see that K is algebraically
   closed in C.functionField. Injectivity of the induced function-field map then gives E∩F=K. -/
theorem smooth_cover_constant_field_marking
    (K : Type u) [Field K] (C Y : Scheme.{u})
    (c : C ⟶ Spec (CommRingCat.of K)) (y : Y ⟶ Spec (CommRingCat.of K))
    [IsSmoothProjectiveCurve c] [GeometricallyIntegral c] [IsSmoothProjectiveCurve y]
    [Algebra K C.functionField] [Algebra K Y.functionField]
    (hK_C : algebraMap K C.functionField =
      (C.germToFunctionField ⊤ (h := ⟨⟨genericPoint C, trivial⟩⟩)).hom.comp
        (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom))
    (hK_Y : algebraMap K Y.functionField =
      (Y.germToFunctionField ⊤ (h := ⟨⟨genericPoint Y, trivial⟩⟩)).hom.comp
        (y.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom))
    (ν : Y ⟶ C) [IsFinite ν] [Surjective ν] (hν : ν ≫ c = y)
    (U : C.Opens) [Etale (ν ∣_ U)]
    (M : Scheme.{u}) (iM : M ⟶ C) [IsClosedImmersion iM] [IsReduced M]
    [IsFinite (iM ≫ c)] [Etale (iM ≫ c)] (hM : Set.range iM ⊆ (U : Set C))
    (E : IntermediateField K Y.functionField) (hE : E = algebraicClosure K Y.functionField) :
    FiniteDimensional K E ∧ Algebra.IsSeparable K E ∧
    algebraicClosure K C.functionField = ⊥ ∧
    (∀ z : C.functionField,
      @algebraMap C.functionField Y.functionField _ _ (ν.dominantFunctionFieldAlgebra) z ∈ E ↔
        z ∈ Set.range (algebraMap K C.functionField)) ∧
    ∃ e : Γ(Y, ⊤) ≃+* E,
      (∀ s : Γ(Y, ⊤), (e s : Y.functionField) =
        Y.germToFunctionField ⊤ (h := ⟨⟨genericPoint Y, trivial⟩⟩) s) ∧
      ∃ qE : Y ⟶ Spec (CommRingCat.of E),
        qE = Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom e.symm.toRingHom) ∧
        qE ≫ Spec.map (CommRingCat.ofHom (algebraMap K E)) = y ∧
        Y.fromSpecFunctionField ≫ qE =
          Spec.map (CommRingCat.ofHom (algebraMap E Y.functionField)) ∧
        IsSmoothProjectiveCurve qE ∧ GeometricallyIntegral qE ∧
        IsReduced (pullback ν iM) ∧
        IsFinite (pullback.fst ν iM ≫ qE) ∧ Etale (pullback.fst ν iM ≫ qE) := by
  sorry

end AlgebraicGeometry
