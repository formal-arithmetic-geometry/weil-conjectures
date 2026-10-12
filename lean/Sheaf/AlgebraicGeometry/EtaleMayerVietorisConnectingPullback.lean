/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleOpenCohomologyMaps
import Sheaf.AlgebraicGeometry.EtaleMayerVietoris
import Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import Sheaf.AlgebraicGeometry.OpenRestrictionPullbackUnit
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Compatible connecting maps for the two étale Mayer–Vietoris sequences

Source: Stacks Project, Tag 0A50 and its proof.
(blueprint: lem-weil-pbc-etale-mayer-vietoris-connecting-pullback).
-/

@[expose] public section

universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- There are exact Mayer–Vietoris sequences with pullback-compatible connecting maps.
Source: Stacks Project, Tag 0A50, construction in its proof; compatibility with pullback
is the agent-written argument of steps 1–4 of the parent node.
(blueprint: lem-weil-pbc-etale-mayer-vietoris-connecting-pullback)

Proof: Choose nonnegative injective resolutions I of G and J of g⁻¹G. Exact inverse
image and the K-injectivity of J give a comparison β : g⁻¹I → J over the augmentations;
a homotopy from a complex in degree zero to J is zero in degree minus one, so this
comparison respects the augmentations exactly. For each W = X, U, V, U ∩ V, the unit
of inverse image followed by β gives a complex map I(W) → J(g⁻¹W). Naturality of both
maps makes the two restriction squares commute. Additivity preserves the difference
sign in the Mayer–Vietoris short exact sequences of complexes of sections. These
sequences are degreewise exact: the sheaf condition gives exactness at the first two
terms, and injectivity makes restriction from U to U ∩ V surjective, giving exactness
at the third term. The inverse-image opens cover Y since preimage preserves joins
and the top open; their intersection is g⁻¹(U ∩ V). Their homology sequences are exact, including
the initial degree-zero injection, and their
connecting maps commute with this morphism by δ_naturality. Restriction preserves
injectives; the restriction-to-sections identifications identify the horizontal maps
with cohomologyMap and openCohomologyRestriction. The unit-composition compatibility
identifies the vertical maps with cohomologyMap g and openCohomologyPullback. Transport
the homology sequences and their connecting maps along the Ext/derived-sections
comparison for Sheaf.H, computed on these same resolutions. Explicitly, Hom from
the constant integer sheaf is sections by evaluation at 1. An Ext cocycle pulls back
by the exact inverse-image functor and is precomposed with the constant-sheaf
comparison used in cohomologyMap. On its representing section this is the adjunction
unit; composing with β gives the section map above. On each open use the restricted
injective resolution and the identity lift of the coefficient comparison. Thus these
identifications intertwine the prescribed Ext pullbacks with the chain-level maps,
rather than using only existence of a coefficient-natural isomorphism. This gives
the two exact sequences and the last displayed square. Resolution independence makes these maps
independent of the comparison
choices. This statement does not assert the other two kinds of cohomology squares;
they follow separately from restriction naturality. When one open is empty or both
opens are all of X, this is the split sequence with zero connecting maps; for g the
identity choose the same resolution on both sides. -/
theorem etale_mayerVietoris_connecting_pullback
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ∃ δX : ∀ q : ℕ, Sheaf.H ((upperStar AddCommGrpCat.{u + 1} ((U ⊓ V).ι)).obj G) q →+ Sheaf.H G
        (q + 1),
    ∃ δY : ∀ q : ℕ, Sheaf.H ((upperStar AddCommGrpCat.{u + 1} ((g ⁻¹ᵁ (U ⊓ V)).ι)).obj ((upperStar
        AddCommGrpCat.{u + 1} (g)).obj G)) q →+ Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (g)).obj
        G) (q + 1),
    Function.Injective (fun x : Sheaf.H G 0 => ((cohomologyMap U.ι G) 0 x, (cohomologyMap V.ι G) 0
        x)) ∧
    (∀ q : ℕ, Function.Exact (fun x : Sheaf.H G q => ((cohomologyMap U.ι G) q x, (cohomologyMap V.ι
        G) q x))
        (fun x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (U.ι)).obj G) q × Sheaf.H ((upperStar
        AddCommGrpCat.{u + 1} (V.ι)).obj G) q =>
          (openCohomologyRestriction (inf_le_left : U ⊓ V ≤ U) G) q x.1 - (openCohomologyRestriction
        (inf_le_right : U ⊓ V ≤ V) G) q x.2) ∧
      Function.Exact (fun x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (U.ι)).obj G) q × Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1} (V.ι)).obj G) q =>
          (openCohomologyRestriction (inf_le_left : U ⊓ V ≤ U) G) q x.1 - (openCohomologyRestriction
        (inf_le_right : U ⊓ V ≤ V) G) q x.2) (δX q) ∧
      Function.Exact (δX q)
        (fun x => ((cohomologyMap U.ι G) (q + 1) x, (cohomologyMap V.ι G) (q + 1) x))) ∧
    Function.Injective (fun x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (g)).obj G) 0 =>
        ((cohomologyMap (g ⁻¹ᵁ U).ι ((upperStar AddCommGrpCat.{u + 1} g).obj G)) 0
        x, (cohomologyMap (g ⁻¹ᵁ V).ι ((upperStar AddCommGrpCat.{u + 1} g).obj G)) 0 x)) ∧
    (∀ q : ℕ, Function.Exact (fun x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (g)).obj G) q =>
        ((cohomologyMap (g ⁻¹ᵁ U).ι ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q x, (cohomologyMap
        (g ⁻¹ᵁ V).ι ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q x))
        (fun x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} ((g ⁻¹ᵁ U).ι)).obj ((upperStar
        AddCommGrpCat.{u + 1} (g)).obj G)) q × Sheaf.H ((upperStar AddCommGrpCat.{u + 1} ((g ⁻¹ᵁ
        V).ι)).obj ((upperStar AddCommGrpCat.{u + 1} (g)).obj G)) q =>
          (openCohomologyRestriction (g.preimage_mono (inf_le_left : U ⊓ V ≤ U))
          ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q x.1 - (openCohomologyRestriction
        (g.preimage_mono (inf_le_right : U ⊓ V ≤ V))
          ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q x.2) ∧
      Function.Exact (fun x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} ((g ⁻¹ᵁ U).ι)).obj
        ((upperStar AddCommGrpCat.{u + 1} (g)).obj G)) q × Sheaf.H ((upperStar AddCommGrpCat.{u +
        1} ((g ⁻¹ᵁ V).ι)).obj ((upperStar AddCommGrpCat.{u + 1} (g)).obj G)) q =>
          (openCohomologyRestriction (g.preimage_mono (inf_le_left : U ⊓ V ≤ U))
          ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q x.1 - (openCohomologyRestriction
        (g.preimage_mono (inf_le_right : U ⊓ V ≤ V))
          ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q x.2) (δY q) ∧
      Function.Exact (δY q)
        (fun x => ((cohomologyMap (g ⁻¹ᵁ U).ι ((upperStar AddCommGrpCat.{u + 1} g).obj G)) (q + 1)
        x, (cohomologyMap (g ⁻¹ᵁ V).ι ((upperStar AddCommGrpCat.{u + 1} g).obj G)) (q + 1) x))) ∧
    (∀ q : ℕ, ∀ x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} ((U ⊓ V).ι)).obj G) q,
      δY q ((openCohomologyPullback g (U ⊓ V) G) q x) = cohomologyMap g G (q + 1) (δX q x)) := by
  sorry

end AlgebraicGeometry.Etale
