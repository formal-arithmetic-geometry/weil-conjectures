/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T8
-/
module

public import Sheaf.Paper.ConstructibleExceptionalCoefficientAssemblyData
public import Sheaf.Paper.RefinementOpenRestriction

/-! # Invertibility of the canonical open map on the finite-Tor domain -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The canonical inverse-transpose open map is invertible on each finite-Tor input.
Source: Stacks 0F7B and 0F7I; Zheng Section 5, Lemma 5.13 and Constructions 5.14--5.15;
the finite and integral cases of lem-sf-ring-open-refinement, steps 1 and 2.
(blueprint: lem-sf-ring-open-map-invertibility).

Proof: refinementOpenMap is defined using the inverse of restriction to the clopen
section and the open adjunction. Its restriction to X is an isomorphism by the
open-unit and restriction calculation. For finite coefficients the input has bounded
constructible cohomology and etale origin. Proper base change identifies the image on
the complement of X with the direct image of zero, hence zero. The cone therefore
restricts to zero both on X and on its complement; open-closed conservativity makes
the cone zero. Transport through the canonical constant-ring module equivalence.
For completed integral coefficients take the normalized strict reduction system of
the input, whose finite levels satisfy the same origin and common bounds. Apply the
same open-unit/counit word as an actual semilinear-system map. The finite argument
makes every evaluation of its cone zero; conservative system evaluations make the
system map invertible. Its total limit is invertible. Primitive open and proper
realization and their unit/counit normalization identify this total-limit map with
refinementOpenMap itself. Thus no equality of integral arrows is deduced from
agreement of their reductions. All constructions apply to the empty input scheme,
zero complexes, and identity refinements, and use only relative separatedness of f.
Naturality, shifts, the normalization equation and the proper pushforward word are
not part of this assertion: they are proved separately from the explicit formula. -/
theorem ringOpenMap_isIso
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d) (s : RingStage.{max u v} l)
    (hi : (s.coefficients l).pull (c.i ≫ r.hom) =
      proEtaleRingCompositeCoefficients c.i r.hom
        ((s.coefficients l).ring d.Z) ((s.coefficients l).ring c.Z)
        ((s.coefficients l).ring X)
        ((s.coefficients l).pull r.hom) ((s.coefficients l).pull c.i))
    (K : C.{u, v} l Ω X (s.stage l)) :
    IsIso ((PurCompactSupport.refinementOpenMap (s.coefficients l) r hi).app
      ((RingStage.inclusion.{u, v} l Ω X s).obj K)) := by sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
