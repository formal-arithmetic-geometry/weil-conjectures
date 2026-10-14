/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap

/-! # Bar enlargement of a split compact-generator tower

Source: finite-piece and target-chain bar argument in
`lem-sc-flat-telescope-target-refinement`, following the generator resolution.
(blueprint: lem-sc-compact-flat-telescope-bar-enlargement).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
namespace AlgebraicGeometry

/-- A split bounded-above compact-generator tower augmented into a flat telescope
admits a flat bar refinement and a split presentation of its enlarged bar total.
The input has the compact-generator structure needed for the finite-piece argument;
no resolution of a general input tower is asserted here.

Source: `lem-sc-flat-telescope-target-refinement`, proof from "Close finite sets"
through the final augmentation identity; the agent-written finite-piece bar argument
of `lem-sc-flat-telescope-arrow-bar-data`.

Proof. Fix generator decompositions in each term. Starting with finitely many
summands in finitely many degrees, close under the differential upwards: each
summand maps through finitely many next-degree summands by hgen. The upper bound
ends the procedure, producing finite subcomplexes. Keep stage-labelled copies of
these subcomplexes for stages at most n, with an arrow when the transition carries
one into the other. A finite subcomplex at an earlier stage maps into a finite
subcomplex at stage n: factor its finitely many generator terms through finite
subcoproducts, then close under the differential. Thus the stage-n subdiagram is
cofinal in this filtered diagram D_n, whose colimit is L_n. No compatibility of
generator decompositions across stages is required, and sums of images are never
assumed flat. Each diagram object retains its finite generator terms.
The unnormalized bar total
R_n of D_n is bounded above and flat; its augmentation c_n is a quasi-isomorphism
by exactness of filtered colimits of module sheaves. Simplicial degree p has
cochain degree -p; the common upper bound for the finite initial tower segment
makes the associated total-complex argument legitimate. Inclusions give s_n.

Write T as the supplied telescope and take finite cone blocks C_k, using domain
indices at most k and codomain indices at most k+1. They are bounded above and
flat, with split inclusions and union T. Each finite source subcomplex maps through
some C_k by finite support in each of its finitely many degrees. Monicity into T
makes that factor a chain map. Adjoin the target chain to the union of D_n, with
arrows from a source object to every block through which it factors. The least
factorization index is monotone and left adjoint to the target-chain inclusion.
Inserting the adjunction unit in bar strings, with alternating signs, gives a
homotopy equivalence from the enlarged bar total to the target-chain bar total.

Let F_n be the bar total on D_n and target indices at most n. Bar inclusions give
u and a, and satisfy the two transition identities strictly. The union bar total
has the degreewise split exact presentation by 1-shift on the sum of F_n: a
simplex's first stage splits the augmentation, and the finite-support recurrence
identifies its kernel. This gives exactly the displayed degreewise splittings; the cone calculation
is left to the caller. Compare the target-chain bar resolution of the augmented constant
right functor with its two-term representable resolution by 1-shift. Successive
projective lifts give maps and homotopies lifting the identity of that functor;
tensor with C_k. Every homotopy is finite on each input, so totalization is valid.
The finite-block telescope maps homotopy equivalently to T by the same split
exact-sequence cone calculation. Cancel the target-chain bar equivalence to see
that the enlarged bar augmentation into T is a homotopy equivalence.
Use that canonical bar augmentation as e, and the sum of stage inclusions
as b. The finite-support recurrence gives hzero and the splittings. Naturality
with a gives the displayed sum identity. Include the zero subcomplex to handle empty
source diagrams. Every construction is existential, not a choice in a definition.
(blueprint: lem-sc-compact-flat-telescope-bar-enlargement). -/
theorem exists_compact_flat_telescope_bar_enlargement (Y : Scheme.{u})
    (L : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (l : ∀ n : ℕ, L n ⟶ L (n + 1))
    (hb : ∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((L n).X i))
    (hsplit : ∀ (n : ℕ) (i : ℤ), IsSplitMono ((l n).f i))
    (hgen :
      ∀ (n : ℕ) (i : ℤ), ∃ (I : Type u)
        (G : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace)),
        Nonempty ((L n).X i ≅ ∐ G) ∧
        (∀ j : I, SheafOfModules.IsFlat (G j)) ∧
        ∀ (j : I) (K : Type u)
          (H : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
          (f : G j ⟶ ∐ H),
          ∃ (S : Finset K) (g : G j ⟶ ∐ (fun k : {k // k ∈ S} ↦ H k.1)),
            g ≫ Sigma.desc (fun k : {k // k ∈ S} ↦ Sigma.ι H k.1) = f)
    (T : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hT : isFlatTelescope Y T) (p : ∀ n : ℕ, L n ⟶ T)
    (hp : ∀ n : ℕ, l n ≫ p (n + 1) = p n) :
    let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
    let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
    ∃ (R F : ℕ → CochainComplex A ℤ)
      (s : ∀ n : ℕ, R n ⟶ R (n + 1))
      (u : ∀ n : ℕ, F n ⟶ F (n + 1))
      (c : ∀ n : ℕ, R n ⟶ L n) (a : ∀ n : ℕ, R n ⟶ F n),
      (∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((R n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((R n).X i)) ∧
      (∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((F n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((F n).X i)) ∧
      (∀ n : ℕ, QuasiIso (c n)) ∧
      (∀ n : ℕ, s n ≫ c (n + 1) = c n ≫ l n) ∧
      (∀ n : ℕ, s n ≫ a (n + 1) = a n ≫ u n) ∧
      ∃ (B : CochainComplex A ℤ) (b : (∐ F) ⟶ B) (e : B ⟶ T)
        (hzero : flatTelescopeDifferential F u ≫ b = 0),
        (∀ i : ℤ, Nonempty
          (((ShortComplex.mk (flatTelescopeDifferential F u) b hzero).map
            (HomologicalComplex.eval A (ComplexShape.up ℤ) i)).Splitting)) ∧
        IsIso (Q.map e) ∧
        Limits.Sigma.map a ≫ b ≫ e = Sigma.desc (fun n : ℕ ↦ c n ≫ p n) := by sorry

end AlgebraicGeometry
