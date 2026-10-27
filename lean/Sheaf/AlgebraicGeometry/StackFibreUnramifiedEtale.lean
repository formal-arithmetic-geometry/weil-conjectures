/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.ModuliChartNormalization
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus

/-! # Unramified field fibres detect the étale locus of a flat presentation

Source: Stacks Project, Morphisms of Stacks, Tag 06N2 (lemma-etale-at-point),
with the fibre hypothesis on an étale scheme chart
(blueprint: lem-sfb-stack-fibre-unramified-etale).

The two scheme projections and their specified 2-isomorphism define the actual map
from the chart to the 2-fibre product, using `moduliTwoFiberLift`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- A flat locally finitely presented scheme presentation is étale near the image
of an unramified point on an étale chart of a field fibre.
Source: Stacks Project, Morphisms of Stacks, Tag 06N2 (lemma-etale-at-point)
(blueprint: lem-sfb-stack-fibre-unramified-etale).

Proof plan, following the four steps of the node:
1. The algebraic-space diagonal of `X` makes both scheme maps `q` and `a`
representable: their scheme base changes are pullbacks of the diagonal along the
pair of test maps. The groupoid 2-fibre-product formula identifies these pullbacks.
The chartwise calculus gives local finite type from local finite presentation
(lem-sfb-stack-chartwise-smooth-etale-calculus).
2. Apply lem-sfb-stack-unramified-locus-base-change to `q`. Its largest unramified
open `W` pulls back to the largest unramified open in the field fibre. The chart
clause identifies its inverse image in `V` with the union of open neighbourhoods
where `V → Spec k` is unramified. The given neighbourhood therefore contains `v`
in this inverse image, and its image `b(v)` lies in `W`. No surjectivity of the
chart is used.
3. The restriction to `W` is unramified by that locus lemma. Flatness survives
restriction since open subschemes have the same local rings. Local finite
presentation survives restriction: a basic-open localization of a finite
presentation `B = R[x]/(r)` has finite presentation `R[x,t]/(r,bt-1)`.
4. On every scheme base change and étale scheme chart, this restriction is flat,
locally finitely presented and unramified. It is étale by
 def-weil-etale-morphism. Thus `W` is the required open neighbourhood.
-/
theorem stack_fibre_unramified_etale
    {S : Scheme.{u}} {X : BasedCategory.{v, w} (Over S)}
    (hX : IsAlgebraicModuliStack X) (U : Over S)
    (q : BasedFunctor (discreteModuli (yoneda.obj U)) X)
    (hqFlat : ModuliSpaceTest @Flat q)
    (hqLfp : ModuliSpaceTest @LocallyOfFinitePresentation q)
    (k : Type u) [Field k] (s : Spec (.of k) ⟶ S)
    (a : BasedFunctor (discreteModuli (yoneda.obj (Over.mk s))) X)
    (V : Over S) (b : V ⟶ U) (r : V ⟶ Over.mk s)
    (e : (discreteModuliMap (yoneda.map b)).comp q ≅
      (discreteModuliMap (yoneda.map r)).comp a)
    (hc : IsEtaleModuliMap (moduliTwoFiberLift
      (discreteModuliMap (yoneda.map b)) (discreteModuliMap (yoneda.map r)) e))
    (v : V.left)
    (hv : ∃ N : V.left.Opens, v ∈ N ∧ IsUnramified (N.ι ≫ r.left)) :
    ∃ W : U.left.Opens, b.left v ∈ W ∧
      IsEtaleModuliMap ((discreteModuliMap (yoneda.map
        (Over.homMk W.ι : Over.mk (W.ι ≫ U.hom) ⟶ U))).comp q) := by
  sorry

end CategoryTheory
