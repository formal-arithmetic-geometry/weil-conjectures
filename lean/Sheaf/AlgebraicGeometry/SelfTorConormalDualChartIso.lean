/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.RingTheory.SelfTorConormalComparison
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Chart factorizations of the canonical exterior-to-self-Tor comparison

Source: Stacks Project, Tags 09PQ, 062I, 0BQY and 06YH.
(blueprint: new-r4-self-tor-conormal-dual-chart-iso). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/-- Sheafify an affine module, extend it to Y, and apply ordinary tensor pullback to Z.
Only its restriction over the chosen affine chart is used below.
Source: Stacks Project, Tags 01I6, 0096 and 06YH.
(blueprint: new-r4-self-tor-conormal-dual-chart-iso). -/
noncomputable def selfTorAffineComparisonFunctor {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    (U : Y.affineOpens) : ModuleCat.{u} (Γ(Y, U.1) : Type u) ⥤ Z.Modules :=
  tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
    Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i

/-- The dual of the canonical comparison has, on every affine chart, the factorization
obtained by sheafifying the normalized algebraic comparison. No regularity is required
for this construction or for the two coordinate identifications.

Source: Stacks Project, Tag 09PQ (canonical Tor products), Tag 062I (the conormal
identification), and Tag 06YH (K-flat computation of derived tensor).
(blueprint: new-r4-self-tor-conormal-dual-chart-iso).

Proof: On U=Spec A, write I for the immersion ideal. Use a projective resolution of A/I
and sheafify it on U. Tensoring it with A/I computes the restriction of the given
K-flat derived tensor, since a bounded-above complex of flat sheaves is K-flat and
resolution comparison is a quasi-isomorphism. The quotient action identifies its
ordinary pullback with the same Tor module on the inverse-image closed chart. The
pulled-back ideal has sections I/I², and exterior powers commute with the tilde
functor and localization. These give the source and target coordinate isomorphisms.
The algebraic comparison is normalized on every tuple of ideal elements and every
projective resolution. Localization preserves that normalization, so uniqueness of
the normalized algebraic map shows that the chart maps agree on basic open overlaps.
Sheaf descent glues them to the global morphism τ. This is the canonical exterior-to-Tor
map, including on singular charts. Dualize the coordinate square, restrict to V, and
apply the over-site restriction. Both coordinate maps stay isomorphisms; their
composite gives exactly the displayed factorization through the functorial image of
the algebraic comparison. Extension along U is used only to write that functor on Z;
over the inverse-image chart it is the original tilde module. For n=0 the map is the
unit; empty charts, zero quotients, and n above the regular rank require no exceptions. -/
theorem selfTor_conormal_dual_chart_iso
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let Q := (Scheme.Modules.tensorPullback i).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj
          (S.obj B ⊗ S.obj B))
    ∃ τ : Scheme.Modules.exteriorSheaf
      ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n ⟶ Q,
      ∀ (V : Z.Opens) (U : Y.affineOpens),
        let W := V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1)
        let F := (selfTorAffineComparisonFunctor i U).op ⋙ Scheme.Modules.dualFunctor Z ⋙
          Scheme.Modules.restrictFunctor V.ι ⋙ SheafOfModules.overFunctor _ W
        let c := selfTorConormalComparison (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
        ∃ (a : (((Scheme.Modules.restrictFunctor V.ι).obj
              (Scheme.Modules.dual Q)).over W) ≅ F.obj (op _))
          (b : F.obj (op _) ≅ (((Scheme.Modules.restrictFunctor V.ι).obj
              (Scheme.Modules.dual (Scheme.Modules.exteriorSheaf
                ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n))).over W)),
          ((Scheme.Modules.restrictFunctor V.ι).map (Scheme.Modules.dualMap τ)).over W =
            a.hom ≫ F.map c.op ≫ b.hom := by sorry

end AlgebraicGeometry
