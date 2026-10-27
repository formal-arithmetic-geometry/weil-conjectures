/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.RegularClosedImmersionCodimension
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import WeilConjectures.RingTheory.IsRegularSystemOfParameters
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Limits.HasLimits

/-! # Mixed-characteristic regular pair models over a complete trait

Source: ILO, Travaux de Gabber, XVI 3.7, printed p.254, and the agent-formulated
simultaneous approximation input using I 2.9, I 10.3(i), IV 4.1.8
(blueprint: lem-per-trait-test-mixed-regular-pair-models).

The quotient diagram is represented by a ring diagram `Q` with specified ring
isomorphisms `eQ` to the actual equation quotients. The natural transformation `q`
is required to be the quotient map under these isomorphisms. This expresses the
canonical quotient diagram without choosing a second construction of that functor.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace RingTheory

/-- A complete strictly henselian mixed-characteristic regular local pair has simultaneous
regular integral finite-type flat models over a complete strictly henselian DVR, with
regular characteristic-`p` equation quotients, compatible colimits and marked parameters.
The residue-field identification of the trait is the one induced by its structure map to
the original ring. Quasi-projectivity is expressed as an immersion into finite-dimensional
projective space commuting with the structure maps, and the regular immersion has constant
codimension `d`.
Source: ILO XVI 3.7, p.254; I 2.9, I 10.3(i), IV 4.1.8, and the simultaneous-pair input
(blueprint: lem-per-trait-test-mixed-regular-pair-models).

Proof plan:
1. The generators and dimension make `t` a regular system of parameters
   (`def-weil-pbc-regular-system-of-parameters`). Apply
   `lem-per-complete-mixed-regular-pair-approximation` to obtain the trait and marked
   affine pairs. The index cannot be empty: otherwise its limit would be `Spec ℤ`,
   contradicting locality of the original ring.
2. Take coordinate rings of the affine pairs. The affine-spectrum correspondence,
   `lem-weil-pbc-lft-affine-pairs`, `lem-weil-pbc-flat-ring-map-iff-flat-affine` and
   `def-pc-integral-scheme` give finite generation, flatness and integrality.
3. Identify the closed coordinate rings with the equation quotients using
   `def-weil-closed-immersion`. Regular schemes are locally Noetherian with regular
   stalks (`def-weil-regular-scheme`); `pqf-lem-affine-open-locnoeth` and
   `lem-weil-pbc-affine-open-stalk-localization` give regular Noetherian coordinate
   rings. Their characteristic is exactly `p`, since the regular sequence makes the
   quotient nonzero and its `𝔽_p`-structure kills `p`.
4. Translate the specified affine scheme limits into ring colimits using the Spec
   morphism correspondence and `def-weil-pbc-category-colimit`. The limiting pair
   identifies the quotient map with the residue map and preserves the marked equations.
5. Retain the input's quasi-projectivity. At each source point use the whole affine
   target and the length-`d` equations in
   `def-per-regular-closed-immersion-codimension` to obtain constant codimension `d`.
-/
theorem exists_trait_test_mixed_regular_pair_models
    (B : Type u) [CommRing B] [IsRegularLocalRing B] [CharZero B]
    [IsStrictlyHenselianLocalRing B] [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (p ℓ d : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField B) p]
    (hℓ : ℓ.Prime) (hℓB : IsUnit (ℓ : B)) (hd : 1 ≤ d)
    (hdim : ringKrullDim B = (d : WithBot ℕ∞)) (t : Fin d → B)
    (ht : Ideal.ofList (List.ofFn t) = IsLocalRing.maximalIdeal B)
    (htreg : RingTheory.Sequence.IsRegular B (List.ofFn t)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsDomain C) (_ : IsDiscreteValuationRing C)
      (_ : CharZero C) (_ : IsStrictlyHenselianLocalRing C)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal C) C)
      (_ : CharP (IsLocalRing.ResidueField C) p)
      (e : IsLocalRing.ResidueField C ≃+* IsLocalRing.ResidueField B) (_ : Algebra C B),
      IsUnit (ℓ : C) ∧
      (∀ c : C, e (IsLocalRing.residue C c) = IsLocalRing.residue B (algebraMap C B c)) ∧
      ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
        (A : I ⥤ CommAlgCat.{u} C) (s : (i : I) → Fin d → A.obj i)
        (Q : I ⥤ CommRingCat.{u})
        (eQ : (i : I) → Q.obj i ≃+* (A.obj i ⧸ Ideal.ofList (List.ofFn (s i))))
        (q : A ⋙ forget₂ (CommAlgCat.{u} C) CommRingCat.{u} ⟶ Q)
        (ι : A ⟶ (Functor.const I).obj (CommAlgCat.of C B))
        (ν : Q ⟶ (Functor.const I).obj (CommRingCat.of (IsLocalRing.ResidueField B))),
        (∀ (i j : I) (f : i ⟶ j) (r : Fin d), A.map f (s i r) = s j r) ∧
        (∀ i : I, (eQ i).toRingHom.comp (q.app i).hom =
          Ideal.Quotient.mk (Ideal.ofList (List.ofFn (s i)))) ∧
        (∀ i : I, IsRegularRing (A.obj i) ∧ IsDomain (A.obj i) ∧
          Algebra.FiniteType C (A.obj i) ∧ Module.Flat C (A.obj i) ∧
          RingTheory.Sequence.IsRegular (A.obj i) (List.ofFn (s i)) ∧
          IsRegularRing (A.obj i ⧸ Ideal.ofList (List.ofFn (s i))) ∧
          CharP (A.obj i ⧸ Ideal.ofList (List.ofFn (s i))) p) ∧
        Nonempty (IsColimit ((forget₂ (CommAlgCat.{u} C) CommRingCat.{u}).mapCocone
          { pt := CommAlgCat.of C B, ι := ι })) ∧
        Nonempty (IsColimit { pt := CommRingCat.of (IsLocalRing.ResidueField B), ι := ν }) ∧
        (∀ (i : I) (r : Fin d), ι.app i (s i r) = t r) ∧
        (∀ i : I, (ν.app i).hom.comp (q.app i).hom =
          (IsLocalRing.residue B).comp (ι.app i).hom.toRingHom) ∧
        (∀ i : I,
          IsIntegral (Spec (CommRingCat.of (A.obj i))) ∧
          IsRegularScheme (Spec (CommRingCat.of (A.obj i))) ∧
          Flat (Spec.map (CommRingCat.ofHom (algebraMap C (A.obj i)))) ∧
          LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap C (A.obj i)))) ∧
          QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap C (A.obj i)))) ∧
          (∃ (n : ℕ) (j : Spec (CommRingCat.of (A.obj i)) ⟶
            ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (CommRingCat.of C))),
            IsImmersion j ∧
            j ≫ (ProjectiveSpace.over (ULift.{u} (Fin (n + 1)))
              (Spec (CommRingCat.of C))).hom =
                Spec.map (CommRingCat.ofHom (algebraMap C (A.obj i)))) ∧
          IsRegularScheme
            (Spec (CommRingCat.of (A.obj i ⧸ Ideal.ofList (List.ofFn (s i))))) ∧
          IsRegularClosedImmersionWithCodimension
            (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (Ideal.ofList (List.ofFn (s i)))))) (fun _ => d)) := by
  sorry

end RingTheory
