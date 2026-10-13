/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectMorphism
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Localization of an affine coordinate Tor bound

Source: Stacks Project, Tags 0B67 and 069C.
(blueprint: lem-pc-affine-sections-tor-bound-stalk).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A fixed affine coordinate Tor bound holds at every source stalk in that affine open.
Source: Stacks Project, Tag 0B67, `lemma-tor-amplitude-localization`,
implication (1) to (2), applied to B[0];
Tag 069C, proof of (1) implies (2).

Proof: write A = Γ(Y,U), B = Γ(X,V), and φ = f.appLE U V e. For y in V,
let q be the prime of B corresponding to y and p its inverse image in A.
The affine stalk isomorphisms identify the given stalk homomorphism with
A_p to B_q; compatibility follows by composing the section-to-germ maps with φ.
For any A_p-module M, restrict scalars to A. A projective A-resolution of B
computes the Tor' groups in the hypothesis. Localizing this resolution at p
is exact and gives a projective A_p-resolution of B tensor_A A_p. Its tensor
with M agrees with the original resolution tensor_A M. Consequently these
Tor groups vanish above d. To localize in the B variable at q, compute the same Tor
groups instead with an A_p-projective resolution of M, using balancedness of Tor. Tensoring it with
B tensor_A A_p gives a complex of B-modules. Localizing that complex at q is exact,
commutes with homology, and replaces B tensor_A A_p by B_q. It therefore gives
Tor_j over A_p of B_q and M equal to the localization of the already zero group.
Transport across the affine stalk isomorphisms to obtain precisely the stated
Tor' object with f.stalkMap y.
No finite type or Noetherian hypothesis is needed. For V empty there is no y;
for d = 0 this is the preservation of flatness under these localizations.
(blueprint: lem-pc-affine-sections-tor-bound-stalk). -/
theorem affineSections_torBound_stalk
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (hU : IsAffineOpen U)
    (V : X.Opens) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (d : ℕ)
    (hbound : ∀ M : ModuleCat.{u} Γ(Y, U), ∀ j : ℕ, d < j →
      IsZero (((Tor' (ModuleCat.{u} Γ(Y, U)) j).obj
        ((ModuleCat.restrictScalars (f.appLE U V e).hom).obj
          (ModuleCat.of Γ(X, V) Γ(X, V)))).obj M)) :
    ∀ y : X, y ∈ V → ∀ M : ModuleCat.{u} (Y.presheaf.stalk (f y)),
      ∀ j : ℕ, d < j →
        IsZero (((Tor' (ModuleCat.{u} (Y.presheaf.stalk (f y))) j).obj
          ((ModuleCat.restrictScalars (f.stalkMap y).hom).obj
            (ModuleCat.of (X.presheaf.stalk y) (X.presheaf.stalk y)))).obj M) := by sorry

end AlgebraicGeometry
