/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
public import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.StackPointTopology
import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Quasi-compact algebraic stacks and surjections

Source: Stacks Project, stacks-properties.tex, Tag 04YC (lemma-quasi-compact-stack),
conditions (2), (3) and (5); Tag 04XI (lemma-characterize-surjective)
(blueprint: lem-sfb-algebraic-stack-quasicompact-surjection).

The arbitrary stack morphism uses the existing field-extension-local surjectivity
predicate. Smoothness and representability are required only of the scheme atlases.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- Quasi-compactness is equivalent to a surjection from a quasi-compact algebraic
stack, an affine smooth surjective scheme atlas, and a quasi-compact such atlas.
Source: Stacks Project, stacks-properties.tex, Tag 04YC, conditions (2), (3), (5),
and Tag 04XI for the field-extension-local interpretation of surjectivity
(blueprint: lem-sfb-algebraic-stack-quasicompact-surjection).

Proof:
1. Given a quasi-compact V and a field-extension-locally surjective f:V → F,
choose a quasi-compact smooth atlas U → V using def-sfb-stack-qcqs-morphism.
By lem-sfb-stack-point-topology its point map is surjective and |f| is continuous.
Field lifting makes |f| surjective. Pull an open cover of |F| back to U and take
its finite subcover. Surjectivity gives a finite subcover of |F|.
2. Choose a smooth scheme atlas T → F by def-sfb-algebraic-moduli-stack and its
affine open cover by lem-pc-fppf-affine-open-cover. The restricted maps are smooth
by lem-sfb-smooth-atlas-open-image, hence flat and locally finitely presented by
lem-sfb-stack-chartwise-smooth-etale-calculus. Regard each source as a space via
def-trf-scheme-algebraic-space. Their point images are open by
lem-sfb-stack-point-topology-flat-lfp-open and cover by lem-sfb-stack-point-topology.
3. Quasi-compactness of |F| selects finitely many such affine charts. Form their
scheme coproduct by lem-weil-pbc-scheme-coproduct-family. It is affine by
lem-weil-pbc-finite-affine-coproduct-spectrum, namely Spec of the product ring.
4. Glue the restricted atlas objects by the etale descent of
def-sfb-stable-pointed-moduli-groupoids; the coprojections are etale by
lem-weil-pbc-open-immersion-etale. Disjoint overlaps give the unique comparisons.
The glued map is representable by lem-sfb-stack-diagonal-space-source-representability
and smooth by source locality in lem-sfb-stack-chartwise-smooth-etale-calculus.
Its point image is all of |F|, so lem-sfb-representable-stack-point-surjectivity
makes it a surjective atlas after every scheme base change.
5. An affine scheme is quasi-compact by lem-weil-pbc-affine-scheme-qcqs. A
quasi-compact smooth atlas is exactly IsQuasiCompactModuli. Conversely, the identity
of a quasi-compact F supplies the required stack surjection. Enlarge the universe
of this witness by the canonical universe lift when needed. Empty stacks and the
empty finite chart family are allowed: its coproduct is Spec of the zero ring. -/
theorem algebraic_stack_quasicompact_surjection {S : Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) (hF : IsAlgebraicModuliStack F) :
    (IsQuasiCompactModuli F ↔
      ∃ (V : BasedCategory.{max u v₁ v₂, max (u + 1) w₁ w₂} (Over S))
        (f : BasedFunctor V F),
        IsAlgebraicModuliStack V ∧ IsQuasiCompactModuli V ∧ IsSurjectiveModuliMap f) ∧
    (IsQuasiCompactModuli F ↔
      ∃ (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
        IsAffine U.left ∧ IsSmoothModuliAtlas F U a) ∧
    (IsQuasiCompactModuli F ↔
      ∃ (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
        CompactSpace U.left ∧ IsSmoothModuliAtlas F U a) := by
  sorry

end CategoryTheory
