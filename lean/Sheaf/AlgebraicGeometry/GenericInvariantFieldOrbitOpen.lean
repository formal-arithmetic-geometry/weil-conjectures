/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.StalkAut
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Sheaf.TraceFormula.LocalDimensionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.AdmissibleFiniteTypeFieldQuotient

/-!
# Generic invariant-field orbit open

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé X, Lemma 2.2(iii),
printed pp. 149–150; the agent-formulated spreading argument recorded in the DAG;
Stacks Project Tags 03JE, 03BJ, 03BL and 01S4
(blueprint: lem-sfb-generic-invariant-field-orbit-open).

The coordinate rings are the actual section rings of the affine opens. The quotient ring
is the subring of sections fixed by the action, written out as the equalizers of pullback and
restriction maps on common subopens (the formula of `finiteQuotientInvariantSections` of
lem-sfb-admissible-finite-type-field-quotient), and both scheme maps are specified by
canonical affine-spectrum formulas. The fraction-field identity is expressed inside the
function field of `W`, using its injective germ maps.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- A finite invariant function-field extension spreads to a finite affine quotient with
radicial residual map and nonempty geometric orbit fibres. The fixed ring `SN` is pinned by
its equalizer formula; on the invariant open `a ⁻¹ᵁ U` it consists of the fixed sections.

Source: ILO, Travaux de Gabber, X Lemma 2.2(iii), printed pp. 149–150; Stacks Project
Tags 03JE, 03BJ, 03BL and 01S4
(blueprint: lem-sfb-generic-invariant-field-orbit-open).

Proof plan, following the node's eleven steps:
1. Finite type over the field makes `X` Noetherian; H-projectivity makes `a` proper,
   hence finite type and separated (lem-wf-affine-noetherian-components,
   lem-weil-pbc-affine-scheme-qcqs, pqf-def-locnoeth, lem-kun-projective-implies-proper,
   def-weil-proper-morphism and lem-pc-separated-quasi-separated).
2. The finite function-field extension makes the generic fibre a singleton: a localized
   affine coordinate domain inside that finite-dimensional field is itself a field
   (lem-sc-integral-function-field-affine-fraction,
   lem-weil-pbc-finite-dimensional-domain-is-field). Apply
   lem-weil-pbc-generic-finite-morphism-open-neighborhood (Stacks 02NW).
3. Choose a nonempty affine open in this finite locus. Its inverse image is affine,
   the restriction is finite surjective, and the two coordinate rings are domains;
   their fraction fields are the given function fields (lem-weil-pbc-affine-opens-basis,
   lem-weil-pbc-finite-local-on-target, def-weil-finite-integral-morphism and
   lem-sc-integral-function-field-affine-fraction). The base coordinate ring is Noetherian
   by lem-weil-pbc-lft-affine-pairs and lem-wf-affine-noetherian-components.
4. The fixed ring is a finite submodule of the finite coordinate algebra over the
   Noetherian base (lem-weil-pbc-noetherian-submodule-finite).
5. Apply lem-sfb-admissible-finite-type-field-quotient on this invariant affine open:
   the quotient is Spec of the fixed ring, finite surjective, with geometric orbit fibres.
6. For a fixed fraction `z = c/d`, the nonzero product of all translates of `d` is fixed,
   and multiplying `z` by this product gives a fixed numerator. This proves precisely
   Frac of the fixed ring equals the fixed subfield of the fraction field.
7. Pure inseparability gives powers of each finite module generator in the base field;
   in characteristic zero each generator already belongs to that field
   (def-weil-pbc-finite-purely-inseparable-extension).
8. Invert the product of their denominators. Invariants commute with this localization,
   and Frobenius applied to a linear combination gives a uniform power for every fixed
   section; in characteristic zero the fixed ring is the base image
   (lem-weil-pbc-principal-localization-open-immersion and lem-weil-pbc-basic-open-pullback).
9. The maps remain finite surjective; the uniform power, or the characteristic-zero
   equality, implies radiciality by the field-point criterion (def-weil-radicial-morphism).
10. Over an algebraic closure every base point extends uniquely to the fixed ring, by
    unique roots of the uniform power equations. Apply the quotient orbit assertion there.
11. Finite algebras over algebraically closed fields have residue field the base field,
    so these geometric-point orbits are precisely the orbits on the geometric fibre schemes
    (lem-trf-finite-radicial-basechange, lem-weil-pbc-finite-algebra-is-integral and
    lem-a1-integral-residue-extension-algebraic). No normality or faithful action is used.
-/
theorem generic_invariant_field_orbit_open
    (k : Type u) [Field k]
    (W X : Scheme.{u}) [IsIntegral W] [IsIntegral X]
    (pW : W ⟶ Spec (.of k)) (pX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType pW] [QuasiCompact pW]
    [LocallyOfFiniteType pX] [QuasiCompact pX]
    (a : W ⟶ X) [IsHProjective a] [Surjective a]
    (ha : a ≫ pX = pW)
    (N : Type v) [Group N] [Finite N] (act : N →* Aut W)
    (hk : ∀ g : N, (act g).hom ≫ pW = pW)
    (hinv : ∀ g : N, (act g).hom ≫ a = a)
    (hfinite : (@algebraMap X.functionField W.functionField _ _
      a.dominantFunctionFieldAlgebra).Finite)
    (hpure : ∀ z : W.functionField,
      (∀ g : N, (Scheme.functionFieldAut (act g)).hom z = z) →
        ∃ (n : ℕ) (c : X.functionField),
          @algebraMap X.functionField W.functionField _ _
            a.dominantFunctionFieldAlgebra c = z ^ (ringExpChar k) ^ n) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U),
      Dense (U : Set X) ∧ Set.Nonempty (U : Set X) ∧
      ∃ (hV : IsAffineOpen (a ⁻¹ᵁ U)) (hη : genericPoint W ∈ a ⁻¹ᵁ U)
        (SN : Subring Γ(W, a ⁻¹ᵁ U)),
        SN = ⨅ (g : N) (T : W.Opens) (hT : T ≤ a ⁻¹ᵁ U)
            (hTg : T ≤ (act g).hom ⁻¹ᵁ (a ⁻¹ᵁ U)),
          ((act g).hom.appLE (a ⁻¹ᵁ U) T hTg).hom.eqLocus
            (W.presheaf.map (homOfLE hT).op).hom ∧
        IsFinite (a ∣_ U) ∧ Surjective (a ∣_ U) ∧
        ∃ (q : (a ⁻¹ᵁ U).toScheme ⟶
            Spec (.of SN))
          (r : Γ(X, U) →+* SN),
          q = hV.isoSpec.hom ≫ Spec.map
            (CommRingCat.ofHom SN.subtype) ∧
          SN.subtype.comp r = (a.app U).hom ∧
          ∃ b : Spec (.of SN) ⟶ U.toScheme,
            b = Spec.map (CommRingCat.ofHom r) ≫ hU.isoSpec.inv ∧
            q ≫ b = a ∣_ U ∧
            IsFinite q ∧ Surjective q ∧
            IsFinite b ∧ UniversallyInjective b ∧ Surjective b ∧
            (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
              (t : Spec (.of Ω) ⟶
                Spec (.of SN)),
              Nonempty ↥(pullback q t) ∧
              ∀ x y : ↥(pullback q t), ∃ (g : N) (l : pullback q t ⟶ pullback q t),
                l ≫ pullback.fst q t ≫ (a ⁻¹ᵁ U).ι =
                  pullback.fst q t ≫ (a ⁻¹ᵁ U).ι ≫ (act g).hom ∧
                l ≫ pullback.snd q t = pullback.snd q t ∧ l x = y) ∧
            (∀ z : W.functionField,
              (∀ g : N, (Scheme.functionFieldAut (act g)).hom z = z) ↔
                ∃ c d : SN,
                  W.presheaf.germ (a ⁻¹ᵁ U) (genericPoint W) hη (d : Γ(W, a ⁻¹ᵁ U)) ≠ 0 ∧
                  z = W.presheaf.germ (a ⁻¹ᵁ U) (genericPoint W) hη
                      (c : Γ(W, a ⁻¹ᵁ U)) /
                    W.presheaf.germ (a ⁻¹ᵁ U) (genericPoint W) hη (d : Γ(W, a ⁻¹ᵁ U))) ∧
            (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ U.toScheme),
              Nonempty ↥(pullback (a ∣_ U) t) ∧
              ∀ x y : ↥(pullback (a ∣_ U) t),
                ∃ (g : N) (l : pullback (a ∣_ U) t ⟶ pullback (a ∣_ U) t),
                  l ≫ pullback.fst (a ∣_ U) t ≫ (a ⁻¹ᵁ U).ι =
                    pullback.fst (a ∣_ U) t ≫ (a ⁻¹ᵁ U).ι ≫ (act g).hom ∧
                  l ≫ pullback.snd (a ∣_ U) t = pullback.snd (a ∣_ U) t ∧ l x = y) ∧
            (∀ p : ℕ, p.Prime → CharP k p →
              ∃ m : ℕ, ∀ t : SN,
                (t : Γ(W, a ⁻¹ᵁ U)) ^ p ^ m ∈ Set.range (a.app U).hom) ∧
            (CharZero k → (a.app U).hom.range =
              SN) := by
  sorry

end AlgebraicGeometry
