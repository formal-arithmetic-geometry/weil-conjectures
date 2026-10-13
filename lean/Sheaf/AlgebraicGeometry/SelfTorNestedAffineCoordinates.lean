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

/-! # Affine normalized self-Tor coordinates

Source: Stacks Project, Tags 09PQ, 01R3 and 06YH.
(blueprint: new-e1-self-tor-nested-affine-coordinates). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/-- Choose affine source and target coordinates using quotient resolutions and conormal
classes. The conjugated comparisons agree on the whole smaller affine chart's sections.
No assertion on an arbitrary subopen, an incomparable overlap or a global map is made.
Source: Stacks Project, Tags 09PQ, 01R3 and 06YH.
(blueprint: new-e1-self-tor-nested-affine-coordinates).

Proof: On U = Spec A use the quotient presentation defined by i.ker.ideal U and a
projective resolution P of A/I. Apply exists_affine_quotient_sheafified_resolution to its
augmentation. Its tensor with A/I computes the restriction of the fixed derived tensor:
termwise projectives sheafify to flat modules, the bounded-above cochain resolution is
K-flat, and comparison with a K-flat model gives the same homology. The quotient action
on this homology identifies its tensor pullback with the associated Tor module on the
closed affine chart. This gives t_U. The conormal sections theorem identifies i*ker(i)
with the associated I/I², preserving the class of each ideal section. Applying the
exterior universal property and sheafification gives s_U. Use these specific coordinates,
rather than arbitrary isomorphisms. For V affine inside U, cover V by principal opens
of U lying in V, then refine each by principal opens of V. Quotient resolutions and
the conormal unit localize. Flat localization commutes with resolution homology, and
sends the normalized algebraic comparison to the normalized comparison: apply its
Koszul normalization on tuples of ideal elements and extend by multilinearity to
localized tuples. Uniqueness of the normalized comparison identifies the two products.
The chosen resolution identifications commute with these comparison maps in the
derived category, independently of the resolutions. Thus the conjugated comparisons
have identical images of pure wedges on each refinement. Those wedges generate the
localized exterior modules; the target sheaf's separatedness then identifies their
values on all sections over i^-1 V. This is exactly the displayed nested top-component
equation. Degree zero uses the empty wedge and the quotient unit; the empty chart,
zero quotient, zero ideal and nonregular ideals require no exceptions. -/
theorem exists_nested_affine_selfTor_coordinates
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
      ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1),
        (φ U).val.app
            (op (Over.mk (homOfLE ((TopologicalSpace.Opens.map i.base).monotone h)))) =
          (φ V).val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ V.1)))) := by sorry

end AlgebraicGeometry
