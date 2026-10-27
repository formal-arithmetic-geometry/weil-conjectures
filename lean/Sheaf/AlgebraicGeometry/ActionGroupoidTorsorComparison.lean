/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.AlgebraicGeometry.SchemeActionTorsorGroupoids
public import Sheaf.CategoryTheory.SiteStackification
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffineFlatDescent
import Sheaf.AlgebraicGeometry.FppfFamilyAffineEffectivityReduction

/-! # Action-groupoid stackification and equivariant scheme torsors

Source: Stacks Project, examples-stacks.tex, Tags 0370 and 04WM;
descent.tex, Tags 0245 and 023Q
(blueprint: lem-sfb-action-groupoid-torsor-comparison).

The group acts on an arbitrary scheme. The torsors are schemes and the comparison
extends the actual trivial-torsor functor, including right translation by the inverse
on arrows. Based functors and vertical natural isomorphisms retain pullback compatibility.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.SchemeAction

/-- The scheme-torsor groupoid is a stack, and the specified trivial-torsor functor
extends to an equivalence over the big fppf site.
Source: Stacks 0370 and 04WM
(blueprint: lem-sfb-action-groupoid-torsor-comparison).

Proof:
1. Affineness is stable under base change and finite coproducts, including the empty
coproduct (`lem-weil-pbc-affine-morphism-permanence`, `pqf-lem-affine-local-target`).
Apply `lem-trf-fppf-family-affine-effectivity-reduction` and
`lem-galois-affine-flat-descent-effective` to descend affine morphisms on fppf covers.
2. Equivariant isomorphisms glue uniquely: fppf covers are fpqc
(`lem-trf-fppf-covering-is-fpqc`), and morphisms into any scheme descend uniquely
(`lem-weil-pbc-fpqc-representable-descent`). Glue inverses as well; equivariance and
compatibility with the maps to `V` are equalities checked after the same cover.
3. Refine a torsor descent datum by local trivializations. Its underlying schemes
are then the affine morphisms `G × U → U`, so Step 1 descends them as schemes.
Glue the comparisons with the original local torsors and their inverses by Step 2.
4. Descend the action and the maps to `V` by representable fpqc descent. The action
laws, equivariance and all transition compatibilities are checked on the covers.
The trivializations give the required fppf torsor property. Thus this is an fppf stack.
5. The trivial-torsor functor sends `x` to `G × T` with map `(h,t) ↦ h • x(t)`.
The arrow with label `g` goes to `h ↦ h * g⁻¹`; it commutes with left translations
and the orbit maps. Successive labels `g,b` give `h * g⁻¹ * b⁻¹ = h * (b*g)⁻¹`.
All formulas commute with base substitution.
6. Stackification universality (`lem-sfb-groupoid-stackification-local-description`)
extends this functor with a vertical invertible comparison to the original functor.
7. On trivial objects the arrow presheaf is already a sheaf, by fpqc morphism descent.
An equivariant automorphism of `G` is right multiplication by its value at the unit.
Compatibility with the orbit maps therefore identifies it uniquely with `R(g⁻¹)`
for an arrow `g • x = y`. The local-description node extends full faithfulness
from trivial objects to arbitrary objects by sheaf gluing.
8. Trivialize any torsor locally and take `x = f(e)` in that trivialization.
Equivariance identifies it with the trivial-torsor image of `x`. The stack criterion
`lem-sfb-stack-fully-faithful-local-equivalence` now gives an equivalence over the base,
with its inverse and vertical unit and counit. No condition on `V` was used. -/
theorem actionGroupoid_torsor_comparison
    (k : Type u) [Field k]
    (G V : Over (Spec (CommRingCat.of k))) [GrpObj G] [ModObj G V]
    [Smooth G.hom] [IsAffineHom G.hom]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (A : BasedCategory.{u, u + 1} (Over (Spec (CommRingCat.of k))))
    (i : BasedFunctor (actionGroupoid G V) A) (hi : IsFppfStackification i) :
    IsFppfModuliStack (torsorGroupoid G V) ∧
      ∃ (F : BasedFunctor A (torsorGroupoid G V))
        (H : BasedFunctor (torsorGroupoid G V) A),
        Nonempty (F.comp H ≅ BasedFunctor.id A) ∧
        Nonempty (H.comp F ≅ BasedFunctor.id (torsorGroupoid G V)) ∧
        Nonempty (i.comp F ≅ trivialTorsorFunctor G V) := by
  sorry

end AlgebraicGeometry.SchemeAction
