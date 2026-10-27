/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.FieldTheory.Separable
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.Sober
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Localization.Integral

/-!
# A finite étale generic point on a finite normal cover

Source: Stacks Project, Tags 00U3, 035H, 035L, 035B, 0AVK and 0307;
de Jong (1997), Lemma 3.7, p. 608; de Jong (1996), §§4.16--4.17, pp. 71--72
(blueprint: lem-sfb-finite-etale-generic-normal-cover).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A nonempty finite étale scheme over the function field has a point over a finite
separable extension, whose normalization gives a finite proper surjective normal integral
cover. Its generic field and generic fibre are canonically the chosen extension.

Source: Stacks Project, Tags 00U3, 035H, 035L, 035B, 0AVK and 0307;
de Jong (1997), Lemma 3.7, p. 608; de Jong (1996), §§4.16--4.17, pp. 71--72
(blueprint: lem-sfb-finite-etale-generic-normal-cover).

The map `j_L` is the existing relative-normalization factorization map
`(S.fromSpecOfAlgebraFunctionField L).toNormalization`. The field-spectrum isomorphism
`e` identifies its source with the generic stalk of `S.normalizationIn L`. The map `a`
is the function-field map induced by the normalization morphism: its composite with
`S.fromSpecFunctionField` is the generic-point restriction of that morphism. The equation
`e.hom ≫ a = Spec.map (CommRingCat.ofHom (algebraMap S.functionField L))` makes the
identification an identification over the original function field. The two projection
identities specify the canonical generic-fibre isomorphism, including its base-field map.

Proof:
1. By lem-weil-pbc-etale-fibre-discrete-separable-points (Stacks 02GL(2), 00U3),
   choose a point of the nonempty finite étale scheme. Its residue field L is finite
   separable over K. The residue-field spectrum gives u, over Spec K.
2. Spec k is Noetherian. By lem-weil-pbc-finite-type-over-noetherian and
   lem-weil-pbc-locally-noetherian-quasi-separated, S is Noetherian and quasi-separated.
   Apply lem-weil-pbc-normalization-in-residue-field-extension at the generic point.
   By lem-weil-pbc-relative-normalization(iii), its affine rings are the integral
   closures of the affine coordinate rings in L, so it is S.normalizationIn L
   (def-fin-normalization-extension). It is normal integral, and the factorization
   map j_L is its generic point with function field L. The factorization through
   Spec K identifies this function field with L over K via the map induced by q.
3. By lem-fin-normalization-extension-finite (035B, 0AVK), q is finite. By
   lem-weil-pbc-finite-proper and lem-weil-pbc-proper-closed-image its image is closed.
   This image contains the generic point, hence is all of S. Finite type of S_L over
   k follows by lem-sfb-finite-type-composition-base-change.
4. Choose a nonempty affine open Spec A of S. By
   lem-sc-integral-function-field-affine-fraction, K is Frac A. If B is the integral
   closure of A in L, the generic fibre has ring B tensor_A K by
   lem-weil-pbc-fibre-product-affine-spectra. For T = A minus zero, the maps
   b tensor (a/s) ↦ ab/s and b/s ↦ b tensor (1/s) identify this ring with T⁻¹B.
   By lem-weil-pbc-integral-closure-commutes-localization (0307), T⁻¹B is the
   integral closure of K in L, hence L since L/K is finite. The map is multiplication
   b tensor c ↦ bc, so its spectrum has projections j_L and Spec of K → L.
   This proves the specified canonical generic-fibre isomorphism. -/
theorem exists_finite_etale_generic_normal_cover
    {k : Type u} [Field k] (S : Scheme.{u}) [IsIntegral S]
    (s : S ⟶ Spec (.of k)) [IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s]
    (P : Scheme.{u}) [Nonempty P] (p : P ⟶ Spec S.functionField)
    [IsFinite p] [Etale p] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra S.functionField L),
      FiniteDimensional S.functionField L ∧ Algebra.IsSeparable S.functionField L ∧
      ∃ u : Spec (.of L) ⟶ P,
        u ≫ p = Spec.map (CommRingCat.ofHom (algebraMap S.functionField L)) ∧
        IsIntegral (S.normalizationIn L) ∧
        (∀ y : S.normalizationIn L,
          IsDomain ((S.normalizationIn L).presheaf.stalk y) ∧
          IsIntegrallyClosed ((S.normalizationIn L).presheaf.stalk y)) ∧
        IsFinite (S.fromNormalizationIn L) ∧ IsProper (S.fromNormalizationIn L) ∧
        Surjective (S.fromNormalizationIn L) ∧
        LocallyOfFiniteType (S.fromNormalizationIn L ≫ s) ∧
        QuasiCompact (S.fromNormalizationIn L ≫ s) ∧
        IsGenericPoint
          ((S.fromSpecOfAlgebraFunctionField L).toNormalization (IsLocalRing.closedPoint L))
          Set.univ ∧
        (∃ (e : Spec (.of L) ≅ Spec (S.normalizationIn L).functionField)
          (a : Spec (S.normalizationIn L).functionField ⟶ Spec S.functionField),
          e.hom ≫ (S.normalizationIn L).fromSpecFunctionField =
            (S.fromSpecOfAlgebraFunctionField L).toNormalization ∧
          (S.normalizationIn L).fromSpecFunctionField ≫ S.fromNormalizationIn L =
            a ≫ S.fromSpecFunctionField ∧
          e.hom ≫ a = Spec.map (CommRingCat.ofHom (algebraMap S.functionField L))) ∧
        ∃ e : Spec (.of L) ≅ pullback (S.fromNormalizationIn L) S.fromSpecFunctionField,
          e.hom ≫ pullback.fst (S.fromNormalizationIn L) S.fromSpecFunctionField =
            (S.fromSpecOfAlgebraFunctionField L).toNormalization ∧
          e.hom ≫ pullback.snd (S.fromNormalizationIn L) S.fromSpecFunctionField =
            Spec.map (CommRingCat.ofHom (algebraMap S.functionField L)) := by
  sorry

end AlgebraicGeometry
