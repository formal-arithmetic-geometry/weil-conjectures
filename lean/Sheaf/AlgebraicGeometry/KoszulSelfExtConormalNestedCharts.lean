/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Sheaf.RingTheory.KoszulRegularSequence
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Modules.Dual

/-! # Naturality of the regular affine Koszul comparisons

Source: Stacks Project, Tags 0BQY and 062I.
(blueprint: new-s3-koszul-conormal-nested-charts). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The normalized chart comparisons respect inclusions of regular affine charts.

Source: Stacks Project, Tag 0BQY, the zero-differential Hom calculation,
and Tag 062I, the conormal basis.
(blueprint: new-s3-koszul-conormal-nested-charts).

Proof: On a regular affine chart resolve the quotient by the augmented Koszul
complex. Apply the finite-free internal Hom comparison with quotient coefficients.
All differentials are zero. Identify the degree-n Hom term with the dual of the
nth conormal exterior power by sending a functional on a wedge of the generators
to the functional on the corresponding wedge of their conormal classes. These
classes form a basis, so this is an isomorphism. Sheafify and tensor-pull back;
restriction along V then gives the displayed over-site comparison.
To check an inclusion of two regular affine charts, restrict the larger resolution
to the smaller one. Its sections are flat over those of the larger affine, so it
is still a resolution. Around each point of the inverse-image smaller chart,
compare this resolution with the one used there. Their conormal bases have equal
rank over the nonzero local quotient ring. Express one generator row in the other;
shrink until its reduction is an invertible matrix. Its exterior powers give a
chain map lifting the identity of the quotient. The contraction equation in degree
one and the derivation rule prove the chain equations. After reduction its degree-n
map is the exterior power of the change of conormal basis. Dualizing therefore
identifies the two functional-pairing maps. Two lifts of the identity are homotopic,
so the induced cohomology map is independent of the chosen matrix. The formulas
commute with localization. Equality of germs gives equality on every subopen of
the smaller chart by separatedness. Choose these intrinsic chart maps simultaneously.
This statement checks nested charts only, and selects no point-indexed cover.
For n=0 use the quotient unit; for n above the generator length use the zero object.
Empty inverse-image charts have unique maps. No data definition chooses a chart
comparison from this existence statement. -/
theorem koszulRegularImmersion_self_ext_conormal_nested_charts
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (V : Z.Opens) (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let T := (Scheme.Modules.restrictFunctor V.ι).obj
      ((Scheme.Modules.tensorPullback i).obj G)
    let F := (Scheme.Modules.restrictFunctor V.ι).obj
      (Scheme.Modules.dual (Scheme.Modules.exteriorSheaf
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n))
    ∃ c : ∀ (U : Y.affineOpens)
      (_hU : ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f),
        F.over (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1)) ≅ T.over (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1)),
      ∀ (U₀ U₁ : Y.affineOpens)
        (h₀ : ∃ (m : ℕ) (f : Fin m → Γ(Y, U₀.1)),
          Ideal.span (Set.range f) = i.ker.ideal U₀ ∧
            RingTheory.Sequence.IsKoszulRegular f)
        (h₁ : ∃ (m : ℕ) (f : Fin m → Γ(Y, U₁.1)),
          Ideal.span (Set.range f) = i.ker.ideal U₁ ∧
            RingTheory.Sequence.IsKoszulRegular f)
        (_h : U₀.1 ≤ U₁.1) (A : V.toScheme.Opens)
        (hA₀ : A ≤ V.ι ⁻¹ᵁ (i ⁻¹ᵁ U₀.1))
        (hA₁ : A ≤ V.ι ⁻¹ᵁ (i ⁻¹ᵁ U₁.1)),
        (c U₀ h₀).hom.val.app (op (Over.mk (homOfLE hA₀))) =
          (c U₁ h₁).hom.val.app (op (Over.mk (homOfLE hA₁))) := by sorry

end AlgebraicGeometry
