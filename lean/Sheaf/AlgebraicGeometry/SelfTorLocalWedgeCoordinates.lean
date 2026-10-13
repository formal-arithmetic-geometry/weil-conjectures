/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.RingTheory.SelfTorConormalComparison
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Local Koszul agreement on wedges in affine self-Tor coordinates

Source: Stacks Project, Tags 09PQ, 01R3 and 06YH.
(blueprint: new-h3-self-tor-local-wedge-coordinates). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/-- Normalized affine coordinates agree locally on a single pure wedge. This assertion
provides neither equality on general exterior sections nor equality of module maps.
Source: Stacks Project, Tag 09PQ (Koszul normalization and resolution independence),
Tag 01R3 (conormal classes), and Tag 06YH (K-flat computation).
(blueprint: new-h3-self-tor-local-wedge-coordinates).

Proof: On each affine chart U, identify the closed chart with Spec(A/I). Sheafify a
projective resolution of A/I by exists_affine_quotient_sheafified_resolution. Its
bounded-above projective complex sheafifies to a K-flat resolution; tensoring with
A/I and comparing with the fixed derived tensor gives the target coordinate t_U.
The quotient ideal kills the resulting homology, so its tensor pullback is the
associated quotient-module sheaf. Apply affineOpen_kernel_conormal_sections to
the identity ring coordinates; its unit formula identifies each ideal class with
the pulled-back kernel section. The exterior universal property and restriction
isomorphism give s_U. Choose these resolution and conormal coordinates for all U.
For V contained in U and a point x in W contained in i^-1 V, shrink around x to a
principal-open refinement of U and V. The finitely many entries of the wedge are
locally linear combinations of conormal classes of ideal sections: lift the
conormal quotient classes locally, and clear their finitely many denominators on
a common principal refinement. Flat localization preserves the quotient complex,
its augmentation, and homology. Lift each resulting finite tuple's Koszul
augmentation to the localized projective resolution. The normalization of
selfTorConormalComparison identifies the image of its wedge cycle with the value
of the algebraic comparison. Homotopic lifts give the same homology class, and
comparison of projective resolutions preserves the augmentation and this class.
Hence the two charts give the same value for each lifted ideal tuple.
Multilinearity extends this equality to the cleared tuple of local conormal
sections, with identical restricted scalar coefficients on both sides. Invert the
cleared denominators to get equality for the original wedge on a neighbourhood
W' of x. This is the displayed equality of restrictions of the two values.
No passage from wedges to general sheafified sections is used here. For n=0 the
empty tuple gives the quotient unit. For an empty W the pointwise clause is
vacuous. Zero quotients, the zero ideal and nonregular ideals use the same
resolution and normalization argument; no Koszul acyclicity is assumed. -/
theorem exists_local_wedge_selfTor_coordinates
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
    let E := Scheme.Modules.exteriorSheaf
      ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n
    let T := fun U : Y.affineOpens ↦
      tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
        Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
    let c := fun U : Y.affineOpens ↦
      selfTorConormalComparison (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
    ∃ (s : ∀ U : Y.affineOpens,
        E.over (i ⁻¹ᵁ U.1) ≅ ((T U).obj _).over (i ⁻¹ᵁ U.1))
      (t : ∀ U : Y.affineOpens,
        ((T U).obj _).over (i ⁻¹ᵁ U.1) ≅ Q.over (i ⁻¹ᵁ U.1)),
      let φ := fun U ↦ (s U).hom ≫ ((T U).map (c U)).over (i ⁻¹ᵁ U.1) ≫ (t U).hom
      ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
        (W : Z.Opens) (hW : W ≤ i ⁻¹ᵁ V.1)
        (a : Fin n → ((Scheme.Modules.tensorPullback i).obj i.ker.toModules).val.obj (op W))
        (x : Z) (hx : x ∈ W),
        ∃ (W' : Z.Opens) (hW' : W' ≤ W), x ∈ W' ∧
          Q.presheaf.map (homOfLE hW').op
              ((φ U).val.app (op (Over.mk (homOfLE
                (hW.trans ((TopologicalSpace.Opens.map i.base).monotone h)))))
                (Scheme.Modules.exteriorSheafSection
                  ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n W a)) =
            Q.presheaf.map (homOfLE hW').op
              ((φ V).val.app (op (Over.mk (homOfLE hW)))
                (Scheme.Modules.exteriorSheafSection
                  ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n W a)) := by sorry

end AlgebraicGeometry
