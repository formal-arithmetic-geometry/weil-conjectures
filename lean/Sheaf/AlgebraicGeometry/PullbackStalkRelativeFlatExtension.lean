/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Sheaf.AlgebraicGeometry.PullbackStalkTensorFlat

/-! # Relative flat scalar extension to a fibre-product stalk

Source: Stacks Project, Algebra, Section Tag 051D, Lemma 10.100.1(1);
Examples, Tag 0FLS, the canonical stalk map.
(blueprint: lem-pc-pullback-stalk-relative-flat-extension).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Extending a relatively flat module to a fibre-product stalk gives a module flat
 over the new base stalk. This is a statement about an arbitrary module over one
source stalk, independent of any sheaf or global flatness condition.
Source: Stacks Project, Algebra, Tag 051D, Lemma 10.100.1(1), and Examples, Tag 0FLS.
(blueprint: lem-pc-pullback-stalk-relative-flat-extension).

Proof: Write x = fst(z), t = snd(z), s = f(x), and R, A, B, C for the stalk
rings at s, x, t, z. The equality f(x) = p(t), obtained from pullback.condition,
identifies the two base stalks. Give A and B their R-actions via the stalk maps.
Choose affine neighbourhoods of x and t above an affine neighbourhood of s.
The affine fibre product has coordinate ring A0 tensor_R0 B0, and C is its
localization at z. Inverting the elements outside the primes of x and t first
gives A tensor_R B. These elements are already units in C, so C is a further
localization of D = A tensor_R B; its inclusions of A and B are the two projection
stalk maps. The flatness of C over D is the existing fibre-product stalk lemma 0FLS.
For an injection N -> N' of B-modules, R-flatness of M makes M tensor_R N ->
M tensor_R N' injective. Give these tensors their D-actions, with A acting on M
and B on N. D-flatness of C makes the map obtained by C tensor_D (-) injective.
The balanced isomorphism
(C tensor_A M) tensor_B N = C tensor_D (M tensor_R N)
sends (c tensor m) tensor n to c tensor (m tensor n); its inverse has the reverse
formula. The balancing identities follow from the maps A -> C and B -> C and
their agreement on R. These isomorphisms commute with N -> N' on pure tensors.
Thus tensoring the injection with C tensor_A M is injective. The injectivity
criterion for flatness proves B-flatness of C tensor_A M. This proves the conclusion
with the B-action restricted along snd.stalkMap. No flatness of either scheme
morphism and no finite-generation condition on M is needed. For M = 0 all tensors
are zero. Empty fibre products supply no point z. -/
theorem pullback_stalk_relative_flat_extension
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S) (z : ↥(pullback f p))
    (M : ModuleCat.{u} (X.presheaf.stalk ((pullback.fst f p) z)))
    (hM : Module.Flat (S.presheaf.stalk (f ((pullback.fst f p) z)))
      ((ModuleCat.restrictScalars (f.stalkMap ((pullback.fst f p) z)).hom).obj M)) :
    Module.Flat (T.presheaf.stalk ((pullback.snd f p) z))
      ((ModuleCat.restrictScalars ((pullback.snd f p).stalkMap z).hom).obj
        ((ModuleCat.extendScalars ((pullback.fst f p).stalkMap z).hom).obj M)) := by sorry

end AlgebraicGeometry
