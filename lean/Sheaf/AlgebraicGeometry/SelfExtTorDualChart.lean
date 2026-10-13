/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.RingTheory.KoszulRegularSequence
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Modules.Dual

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure

/-! # Evaluation between self Ext and self Tor

Source: Stacks Project, Tags 0BQY, 08DH and 068G.
(blueprint: lem-sc-self-ext-tor-dual-chart). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/-- The Ext--Tor evaluation map is invertible on regular affine charts.

Source: Stacks Project, duality.tex, lemma-regular-ideal-ext (0BQY), its
zero-differential Hom calculation; cohomology.tex, derived evaluation (08DH);
more-algebra.tex, equation-simple-tor-product (068G).
(blueprint: lem-sc-self-ext-tor-dual-chart).

Proof: Use the canonical cap action of Ext on Tor. Locally an Ext class is a
derived morphism B -> B[n]. Tensoring it with B and taking degree-minus-n
homology gives Tor_n(B,B) -> Tor_0(B,B) = B. Equivalently compute this action
by evaluating a cocycle in Hom(P,B) on cycles in P tensor B, for a free
resolution P of B. Changing a cocycle or cycle by a boundary does not change
the value, and resolution comparison preserves evaluation. This construction
sheafifies, giving a bilinear pairing of the Ext and Tor sheaves. The Tor sheaf
carries the quotient scalar action, so the pairing descends to ordinary pullback
to Z. Curry it to obtain κ into the internal dual of the pulled-back Tor sheaf.
The cap action, quotient action and currying commute with restriction;
no regularity is needed to define the map. On a regular affine chart use the
augmented finite free Koszul resolution of A/I. Hom into A/I and tensor with A/I
both have zero differential. The displayed evaluation is functional evaluation
of Hom_A(K_n,A/I) on K_n tensor_A A/I. The increasing wedge basis is finite,
so this pairing is perfect and κ is an isomorphism. Localization preserves that
pairing, giving an isomorphism of over-site sheaves. The same resolution computes
in the supplied derived universe. For n=0 the pairing is multiplication on A/I;
for n above the generator length both sides vanish. Empty charts and zero quotient
rings also give isomorphisms of zero objects. -/
theorem selfExt_tor_dual_chart
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let Q := (Scheme.Modules.tensorPullback i).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj
          (S.obj B ⊗ S.obj B))
    ∃ κ : (Scheme.Modules.tensorPullback i).obj G ⟶ Scheme.Modules.dual Q,
      ∀ (V : Z.Opens) (U : Y.affineOpens)
        (_hU : ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
          Ideal.span (Set.range f) = i.ker.ideal U ∧
            RingTheory.Sequence.IsKoszulRegular f),
        IsIso (((Scheme.Modules.restrictFunctor V.ι).map κ).over
          (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1))) := by sorry

end AlgebraicGeometry
