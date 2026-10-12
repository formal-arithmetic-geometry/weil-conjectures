/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer

import Sheaf.AlgebraicGeometry.AbelianSheavesGModules
import Sheaf.RepresentationTheory.SylowModuleFiltration
import Sheaf.FieldTheory.OpenSubgroupFixedField
import Sheaf.AlgebraicGeometry.FiniteEtaleTrace
import Sheaf.AlgebraicGeometry.FiniteEtaleTraceDegree
import WeilConjectures.SixFunctors.Finite.GlobalSections
import WeilConjectures.SixFunctors.Finite.Exact

/-! Generic finite trace and filtration data. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.IsConnectedCurve

/-- Finite primary summands become filtered by prime constant generic sheaves after
prime-to-primary finite separable extensions. The original second cohomology injects
into the product of the second cohomology of these filtered generic sheaves.
No constant-sheaf vanishing hypothesis is used in this construction.

Source: blueprint `lem-sc-affine-generic-second`, proof paragraphs 1--2.
(blueprint: lem-sc-generic-finite-trace-filtration-data)

Proof: identify the finite stalk with its continuous Galois module. Split into primary
summands. For each summand choose the open subgroup furnished by the Sylow filtration
lemma and its finite separable fixed field. Refine each finite trivial vector-space
quotient by a basis to obtain rank-one prime constant quotients. Transport the chain
through the field/sheaf equivalence. Use hmodel for the normalization and identify its
function field with the extension. Restriction followed by trace is multiplication by
the prime-to-primary degree; Bezout rescaling gives a retraction. Apply generic direct
image and cohomology, then the finite-pushforward cohomology comparison. Combine the
primary retractions to obtain the displayed injection. The zero module uses r = 0;
zero filtration terms are retained and the initial term is the zero sheaf. -/
theorem exists_generic_finite_trace_filtration_data
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C] [IsIntegral C]
    (hmodel : ∀ (L : Type u) [Field L] [Algebra C.functionField L]
      [FiniteDimensional C.functionField L],
      IsFinite (C.fromNormalizationIn L) ∧ IsAffine (C.normalizationIn L) ∧
        IsConnectedCurve (C.fromNormalizationIn L ≫ f) ∧
        Smooth (C.fromNormalizationIn L ≫ f) ∧
        ∃ e : Spec (.of L) ≅ Spec (C.normalizationIn L).functionField,
          e.hom ≫ (C.normalizationIn L).fromSpecFunctionField =
            (C.fromSpecOfAlgebraFunctionField L).toNormalization)
    (M : Sheaf (Spec C.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hM : M.IsTorsion)
    (hfinite : Finite (((Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom
        (algebraMap C.functionField (AlgebraicClosure C.functionField))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj M)) :
    ∃ (r : ℕ) (D : Fin r → Scheme.{u}) (g : ∀ i, D i ⟶ Spec (.of k)),
      (∀ i, IsConnectedCurve (g i)) ∧ (∀ i, Smooth (g i)) ∧
      (∀ i, IsAffine (D i)) ∧
      ∃ hIntegral : ∀ i, IsIntegral (D i),
      letI : ∀ i, IsIntegral (D i) := hIntegral;
      ∃ (n : Fin r → ℕ)
        (F : ∀ i, ℕ → Sheaf (Spec (D i).functionField).smallEtaleTopology
          AddCommGrpCat.{u + 1}),
        (∀ i, IsZero (F i 0)) ∧
        (∀ i (a : ℕ), a < n i →
          ∃ (S : ShortComplex (Sheaf (Spec (D i).functionField).smallEtaleTopology
              AddCommGrpCat.{u + 1})) (ℓ : ℕ),
            ℓ.Prime ∧ S.ShortExact ∧ Nonempty (S.X₁ ≅ F i a) ∧
              Nonempty (S.X₂ ≅ F i (a + 1)) ∧
              Nonempty (S.X₃ ≅ (Spec (D i).functionField).constantZMod ℓ)) ∧
        ∃ j : Sheaf.H
          ((Etale.lowerStar AddCommGrpCat.{u + 1} C.fromSpecFunctionField).obj M) 2 →
          ∀ i, Sheaf.H
            ((Etale.lowerStar AddCommGrpCat.{u + 1} (D i).fromSpecFunctionField).obj
              (F i (n i))) 2,
          Function.Injective j := by sorry

end AlgebraicGeometry.IsConnectedCurve
