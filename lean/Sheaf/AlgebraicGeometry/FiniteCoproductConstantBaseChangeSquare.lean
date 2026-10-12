/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.Paper.FiniteCoproductCohomologyAssembly
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import Sheaf.AlgebraicGeometry.ConstantPullbackCompositionCoherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Product coordinates for constant-coefficient base change

Source: blueprint sk-prop-ext-invariance, first step, and Stacks Tag 0A5B,
first paragraph of the proof (finite disjoint unions).
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Etale

/-- The target product coordinates for finite-coproduct base change commute with
the normalized constant-coefficient restriction maps on the source.
Source: blueprint sk-prop-ext-invariance, first step; Stacks Tag 0A5B,
first paragraph of the proof, and cohomology functoriality (Tag 01F7).
(blueprint: lem-sc-finite-coproduct-constant-base-change-square)

Proof: Inverse image of the constant Z/n sheaf is canonically the constant Z/n sheaf
on each D i. Normalize each restriction by the cohomology equivalence induced
by that sheaf isomorphism, giving the source restriction maps in the formula.
Base change preserves the disjoint coproduct: coprojections are clopen immersions
whose disjoint images cover C,
and their inverse images have those same properties after base change. Apply
finiteCoproductCohomologyAssembly on the base change of C to its pulled-back
coprojections. The pullback square identifies the restriction of the pulled-back
coefficient sheaf with the pullback of the component constant sheaf, using
upperStarComp and the constant-sheaf isomorphisms. This gives eK. Functoriality
of cohomology pullback for the commuting square, together with naturality in
the coefficient sheaf and coherence of the constant-sheaf identifications,
gives the displayed equality in each coordinate. This proves no bijectivity
of any field-extension comparison: it only diagonalizes the given map.
The empty family gives singleton products on both sides. The construction uses
no invertibility, and includes n=0, n=1 and q=0. -/
theorem finiteCoproductConstantBaseChangeSquare
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {I : Type u} [Finite I] {C : Scheme.{u}} (D : I → Scheme.{u})
    (f : C ⟶ Spec (.of k)) (g : ∀ i, D i ⟶ Spec (.of k))
    (ι : ∀ i, D i ⟶ C) (hw : ∀ i, ι i ≫ f = g i)
    (hc : IsColimit (Cofan.mk C ι)) (n q : ℕ) :
    ∃ eK : Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1}
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj
          (C.constantZMod n)) q ≃
      ∀ i, Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1}
          (pullback.fst (g i) (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj
            ((D i).constantZMod n)) q,
    ∀ (x : Sheaf.H (C.constantZMod n) q) (i : I),
      eK (cohomologyMap
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (C.constantZMod n) q x) i =
      cohomologyMap
        (pullback.fst (g i) (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        ((D i).constantZMod n) q
        (Sheaf.H.map
          ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (ι i)).hom.app
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))) q
          (cohomologyMap (ι i) (C.constantZMod n) q x)) := by sorry

end AlgebraicGeometry.Etale
