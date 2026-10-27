/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Topology.Irreducible

/-!
# Generic comparison of positive multiples of coherent algebraic-space modules

Source: Stacks Project, Spaces Cohomology, Tag 07UT, final proof paragraph
(blueprint: lem-sfb-space-generic-multiple-embedding).

The ideal product is specified with its inclusion into the original module by its
least-submodule universal property. This determines the submodule generated locally
by products, including products that exist only after passing to an étale cover.
Finite products below represent finite direct sums in the additive module category.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Two coherent modules of full support on a reduced irreducible Noetherian algebraic
space have positive multiples admitting an ideal-multiple embedding, generically an
isomorphism. The module `P`, together with `p`, is precisely `JG`: its universal
property says it is the least submodule containing every local product of sections.
On the open subspace, the same restricted inclusion identifies `P` with `G`.
Source: Stacks, Spaces Cohomology, Tag 07UT, final proof paragraph
(blueprint: lem-sfb-space-generic-multiple-embedding).

Proof:
1. Apply lem-sfb-space-generic-freeness to G and H and intersect the nonempty
   opens. Irreducibility makes the intersection nonempty. If the positive generic
   ranks are r and s, take a=s and b=r to obtain an isomorphism of the direct sums.
2. By lem-sfb-space-reduced-closed-support and
   lem-sfb-space-closed-immersion-quasi-coherent-modules, the complement is cut out
   by a quasi-coherent ideal I, equal to the unit ideal on the open. The ideal and
   all ideal products are coherent by lem-sfb-space-noetherian-coherent-support;
   finite sums are coherent by lem-sfb-space-coherent-kernel-cokernel-extension.
3. Apply lem-sfb-space-homs-over-open to extend the generic isomorphism to a map
   from I^n times the source sum. Its coherent kernel K vanishes on the open.
4. By lem-sfb-space-power-ideal-kills choose d with I^d K=0. Apply
   lem-sfb-space-artin-rees to obtain c; then I^(c+d)M intersect K is contained in
   I^d K and is zero. The map restricted to this ideal multiple is injective.
5. Set J=I^(n+c+d). Multiplication is coordinatewise on the sums, and the resulting
   map restricts to the original isomorphism. Since J is the unit ideal on a
   nonempty open, it is nonzero. Its product with G has the stated universal
   property because products generate the image subsheaf locally. -/
theorem exists_generic_multiple_embedding
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hqc : CompactSpace (Point X.obj.obj))
    (hqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
      (b : yoneda.obj V ⟶ X.obj.obj), IsAffine U.left → IsAffine V.left →
        CompactSpace (Point (Limits.pullback a b)))
    (hred : ∀ T : X.EtaleSite, IsReduced (X.etaleForget.obj T))
    (hirr : IrreducibleSpace (Point X.obj.obj))
    (G H : X.Modules) [G.IsQuasicoherent] [H.IsQuasicoherent]
    (hG : ∀ T : X.EtaleSite,
      Scheme.Modules.IsQuasiCoherentFiniteType ((X.schemeRestriction T).obj G))
    (hH : ∀ T : X.EtaleSite,
      Scheme.Modules.IsQuasiCoherentFiniteType ((X.schemeRestriction T).obj H))
    (hsG : ∀ (T : X.EtaleSite) (x : X.etaleForget.obj T),
      ¬ Subsingleton (((X.schemeRestriction T).obj G).presheaf.stalk x))
    (hsH : ∀ (T : X.EtaleSite) (x : X.etaleForget.obj T),
      ¬ Subsingleton (((X.schemeRestriction T).obj H).presheaf.stalk x)) :
    ∃ (a b : ℕ), 1 ≤ a ∧ 1 ≤ b ∧
      ∃ (J P : X.Modules) (j : J ⟶ SheafOfModules.unit X.structureSheaf)
        (p : P ⟶ G),
        Mono j ∧ J.IsQuasicoherent ∧ ¬ IsZero J ∧ Mono p ∧
        (∀ (N : X.Modules) (n : N ⟶ G), Mono n →
          ((∀ (T : X.EtaleSite) (r : J.val.obj (op T)) (s : G.val.obj (op T)),
            ∃ z : N.val.obj (op T),
              n.val.app (op T) z = j.val.app (op T) r • s) ↔
            ∃ l : P ⟶ N, l ≫ n = p)) ∧
        ∃ (V : OpenSubspace X), (pointImage V.val.ι).Nonempty ∧
          ∃ α : (∏ᶜ fun _ : Fin a ↦ P) ⟶ (∏ᶜ fun _ : Fin b ↦ H),
            Mono α ∧
            ∀ (T : X.EtaleSite),
              (∃ q : yoneda.obj T.obj.left ⟶ V.val.toFunctor,
                q ≫ V.val.ι = T.obj.hom) →
              IsIso ((X.etalePullback T).map j) ∧
              IsIso ((X.etalePullback T).map p) ∧
              IsIso ((X.etalePullback T).map α) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
