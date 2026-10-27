/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.RelativeModuliInertia
public import Mathlib.AlgebraicGeometry.Scheme
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.AlgebraicStackQuasicompactSurjection
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Quasi-compactness and the absolute structure morphism of a stack

Source: Stacks Project, stacks-properties.tex, Tag 04YC (lemma-quasi-compact-stack);
stacks-morphisms.tex, Tag 050U (definition-quasi-compact); schemes.tex, Tag 01JQ
(lemma-fibre-product-affines)
(blueprint: lem-sfb-stack-quasicompact-absolute-criterion).

The base is Spec of the universe lift of the integers. Its represented stack is
modeled by the identity category over Sch/Spec Z, using `moduliBaseStructure`.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- An algebraic stack over Spec Z has a quasi-compact smooth surjective scheme
atlas if and only if its absolute structure morphism is quasi-compact, tested on
all quasi-compact algebraic stacks. No quasi-separatedness is required.
Source: Stacks Project, Tags 04YC, 050U and 01JQ
(blueprint: lem-sfb-stack-quasicompact-absolute-criterion).

Proof:
1. A scheme T is a discrete algebraic stack: its diagonal is given by scheme
fibre products and its identity is an etale surjective atlas, hence smooth
(def-trf-scheme-algebraic-space and
lem-sfb-fibred-groupoid-representable-smooth-calculus). If T is quasi-compact,
its identity atlas makes it quasi-compact (def-sfb-stack-qcqs-morphism).
In particular Spec Z is quasi-compact by lem-weil-pbc-affine-scheme-qcqs.
Testing a quasi-compact structure morphism against the identity of Spec Z makes
A ×_Z Z quasi-compact. Projection is an equivalence with A: its inverse sends
x to (x,p(x),id), and the comparison in each triple identifies the other component.
This uses def-sfb-stable-pointed-moduli-groupoids and gives the required atlas.
2. Conversely, given a quasi-compact atlas of A and a quasi-compact algebraic
stack V over Z, choose affine smooth surjective atlases U → A and W → V by
lem-sfb-algebraic-stack-quasicompact-surjection. They are representable by
algebraic spaces by def-sfb-algebraic-moduli-stack. The products A ×_Z V and
U ×_Z V are algebraic by lem-sfb-algebraic-stack-fibre-products.
3. The natural map U ×_Z W → A ×_Z V factors through U ×_Z V as two base
changes of the given atlases. In the triple description of
def-sfb-stable-pointed-moduli-groupoids, forgetting the forced component and
inserting it with its identity comparison give the required identifications.
Thus lem-sfb-fibred-groupoid-representable-smooth-calculus makes this composite
representable, smooth and surjective.
4. By lem-weil-pbc-fibre-product-affine-spectra, U ×_Z W is Spec(R ⊗_Z B),
hence quasi-compact by lem-weil-pbc-affine-scheme-qcqs. This is a quasi-compact
scheme atlas of A ×_Z V, so def-sfb-stack-qcqs-morphism proves it quasi-compact.
Since V was arbitrary, the structure morphism is quasi-compact. Only Z, U and W
are required to be affine; no separation of either stack is used. -/
theorem isQuasiCompactModuli_iff_absoluteStructure
    (A : BasedCategory.{v₁, w₁} (Over (Spec (.of (ULift.{u} ℤ)))))
    (hA : IsAlgebraicModuliStack A) :
    IsQuasiCompactModuli A ↔
      IsQuasiCompactAlgebraicModuliMap.{u, v₁, w₁, u, u + 1, v₂, w₂}
        (moduliBaseStructure A) := by
  sorry

end CategoryTheory
