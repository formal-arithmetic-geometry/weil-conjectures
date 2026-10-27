/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ThickeningAffineScheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Compatible local deformations of isolated curve singularities

Source: Stacks Project, Tag 0DZP, `lemma-curve-isolated`, first smooth arrow;
Tag 06HN, `lemma-smooth-morphism-essentially-surjective`, compatible induction;
Tag 0E7Y, middle paragraph (blueprint: lem-sfb-isolated-curve-formal-lifting).

The index `n` denotes the paper's level `n + 1`. Reduction is encoded by its
surjective homomorphism with the prescribed kernel, equivalently by an isomorphism
from the quotient. The helpers below construct the coefficient rings and their
canonical maps, and the special-fibre maps determined by adjacent reductions.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The coefficient ring at level `n + 1`, written using `(t - 0)^(n+1)`.
Source: Stacks 0E7Y (blueprint: lem-sfb-isolated-curve-formal-lifting). -/
abbrev isolatedCurveLevelRing (k : Type u) [Field k] (n : ℕ) :=
  Polynomial k ⧸ (Ideal.span {Polynomial.X - Polynomial.C (0 : k)}) ^ (n + 1)

/-- The canonical adjacent reduction of the coefficient rings.
Source: Stacks 06HN (blueprint: lem-sfb-isolated-curve-formal-lifting). -/
noncomputable def isolatedCurveLevelReduction (k : Type u) [Field k] (n : ℕ) :
    isolatedCurveLevelRing k (n + 1) →+* isolatedCurveLevelRing k n :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))

/-- The canonical level-one identification with `k`, by evaluation at zero.
Source: Stacks 0E7Y (blueprint: lem-sfb-isolated-curve-formal-lifting). -/
noncomputable def isolatedCurveLevelZero (k : Type u) [Field k] :
    isolatedCurveLevelRing k 0 ≃ₐ[k] k :=
  (Ideal.quotientEquivAlgOfEq k (pow_one _)).trans
    (Polynomial.quotientSpanXSubCAlgEquiv 0)

/-- The element `t` in the coefficient ring.
Source: Stacks 0E7Y (blueprint: lem-sfb-isolated-curve-formal-lifting). -/
noncomputable def isolatedCurveLevelParameter (k : Type u) [Field k] (n : ℕ) :
    isolatedCurveLevelRing k n :=
  Ideal.Quotient.mk _ Polynomial.X

/-- The scalar map into the local ring induced by a scheme over an affine base.
Source: Stacks 0DZP (blueprint: lem-sfb-isolated-curve-formal-lifting). -/
noncomputable def isolatedCurveScalarToStalk {A : Type u} [CommRing A] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of A)) (y : Y) : A →+* Y.presheaf.stalk y :=
  (StructureSheaf.toStalk A (g y) ≫ g.stalkMap y).hom

/-- The special-fibre map at any level, determined by the initial identification
and adjacent reductions. Source: Stacks 06HN
(blueprint: lem-sfb-isolated-curve-formal-lifting). -/
def isolatedCurveSpecialMap {X : Scheme.{u}} (Y : ℕ → Scheme.{u})
    (j : ∀ n : ℕ, Y n ⟶ Y (n + 1)) (e : X ≅ Y 0) : ∀ n : ℕ, X ⟶ Y n
  | 0 => e.hom
  | n + 1 => isolatedCurveSpecialMap Y j e n ≫ j n

/-- Compatible prescribed local deformations lift to a proper flat formal curve.
Source: Stacks 0DZP, first smooth arrow, and 06HN, as used in 0E7Y
(blueprint: lem-sfb-isolated-curve-formal-lifting).

Proof plan:
1. Use `lem-sfb-isolated-curve-two-affine-cover` to fix `X = U ∪ V`, with all
marked points in `V` and both `U` and `U ∩ V` smooth affine.
2. Start at `X` with the prescribed local identifications; flatness over the field
is `lem-pc-flat-field`. The kernel of the next coefficient reduction is square zero.
3. The deformation of `V` is affine by `lem-weil-pbc-thickening-affine-scheme`.
Identify its stalks by `lem-weil-pbc-affine-open-stalk-localization` and compose the
prescribed local reductions with the previously chosen identifications.
4. Apply `lem-sfb-affine-isolated-deformation-lift` to extend the affine chart and
its local identifications, retaining their reduction equations.
5. Apply `lem-sfb-smooth-open-deformation-lift` to glue it to the smooth open.
Compose its stalk identifications with the affine ones. The gluing square gives
exactly the local reduction equation in the conclusion.
6. Properness follows from `lem-sfb-proper-nilpotent-base-change-reflection`.
7. The coefficient rings are finite-dimensional over `k`, hence Noetherian.
Use `pqf-def-locnoeth`, `pqf-lem-lft-fp-locnoeth`, and
`lem-pc-separated-quasi-separated` to deduce finite presentation from properness.
8. Continue recursively, keeping the chosen identifications. Compose adjacent
reductions for longer reductions; associativity gives their compatibility.
The same induction covers an empty marked list and the empty scheme. -/
theorem exists_isolatedCurve_formal_lifting
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (r : ℕ) (p : Fin r → X)
    (hp : Function.Injective p) (hclosed : ∀ i : Fin r, IsClosed ({p i} : Set X))
    (hsmooth : ∀ x : X, x ∉ Set.range p →
      ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f))
    (C : Fin r → ℕ → Type v) [∀ (i : Fin r) (n : ℕ), CommRing (C i n)]
    [∀ (i : Fin r) (n : ℕ), IsLocalRing (C i n)]
    [∀ (i : Fin r) (n : ℕ), Algebra (isolatedCurveLevelRing k n) (C i n)]
    [∀ (i : Fin r) (n : ℕ), Module.Flat (isolatedCurveLevelRing k n) (C i n)]
    [∀ (i : Fin r) (n : ℕ), Algebra.EssFiniteType (isolatedCurveLevelRing k n) (C i n)]
    (c : ∀ (i : Fin r) (n : ℕ), C i (n + 1) →+* C i n)
    (hcscalar : ∀ (i : Fin r) (n : ℕ),
      (c i n).comp (algebraMap (isolatedCurveLevelRing k (n + 1)) (C i (n + 1))) =
        (algebraMap (isolatedCurveLevelRing k n) (C i n)).comp
          (isolatedCurveLevelReduction k n))
    (hcsurj : ∀ (i : Fin r) (n : ℕ), Function.Surjective (c i n))
    (hcker : ∀ (i : Fin r) (n : ℕ), RingHom.ker (c i n) =
      Ideal.span {(algebraMap (isolatedCurveLevelRing k (n + 1)) (C i (n + 1))
        (isolatedCurveLevelParameter k (n + 1))) ^ (n + 1)})
    (eC : ∀ i : Fin r, C i 0 ≃+* X.presheaf.stalk (p i))
    (heC : ∀ (i : Fin r) (a : k),
      eC i (algebraMap (isolatedCurveLevelRing k 0) (C i 0)
        ((isolatedCurveLevelZero k).symm a)) = isolatedCurveScalarToStalk f (p i) a) :
    ∃ (Y : ℕ → Scheme.{u}) (g : ∀ n : ℕ, Y n ⟶ Spec (.of (isolatedCurveLevelRing k n)))
      (e : X ≅ Y 0) (j : ∀ n : ℕ, Y n ⟶ Y (n + 1)),
      (∀ n : ℕ, IsProper (g n) ∧ Flat (g n) ∧ LocallyOfFinitePresentation (g n)) ∧
      e.hom ≫ g 0 = f ≫ Spec.map (CommRingCat.ofHom (isolatedCurveLevelZero k).toRingHom) ∧
      (∀ n : ℕ, IsPullback (j n) (g n) (g (n + 1))
        (Spec.map (CommRingCat.ofHom (isolatedCurveLevelReduction k n)))) ∧
      ∃ h : ∀ (i : Fin r) (n : ℕ),
        (Y n).presheaf.stalk (isolatedCurveSpecialMap Y j e n (p i)) ≃+* C i n,
        (∀ (i : Fin r) (n : ℕ) (a : isolatedCurveLevelRing k n),
          h i n (isolatedCurveScalarToStalk (g n)
            (isolatedCurveSpecialMap Y j e n (p i)) a) = algebraMap _ _ a) ∧
        (∀ (i : Fin r) (n : ℕ)
          (a : (Y (n + 1)).presheaf.stalk (isolatedCurveSpecialMap Y j e (n + 1) (p i))),
          c i n (h i (n + 1) a) =
            h i n ((j n).stalkMap (isolatedCurveSpecialMap Y j e n (p i)) a)) ∧
        (∀ (i : Fin r) (a : (Y 0).presheaf.stalk (e.hom (p i))),
          h i 0 a = (eC i).symm (e.hom.stalkMap (p i) a)) := by
  sorry

end AlgebraicGeometry
