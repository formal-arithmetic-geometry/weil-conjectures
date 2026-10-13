/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators

/-! # The two-section product identity for transported tensor boundaries

Source: Stacks Project, Tags 09MS and 0B8S.
(blueprint: lem-sc-square-zero-tensor-boundary-product).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
universe u wC wD
attribute [local irreducible] RingedSpace.moduleCohomology
  RingedSpace.moduleSectionBoundary boundaryCoefficientCohomologyIso
  canonicalTensorBoundaryComparisons
noncomputable section

/-- The boundary of a product of two arbitrary sections is the sum of their two acted-on
boundaries. The second section is arbitrary in degree e+1, rather than a power of the
first; no sequence of classes or exponent recurrence is asserted.

Source: Stacks Project, Tag 09MS, the direct-sum exact sequence after equation
(30.17.5.1), and Tag 0B8S, the square-zero boundary derivation calculation.
(blueprint: lem-sc-square-zero-tensor-boundary-product).
Proof: take the direct sums of the ideal sequences in nonnegative tensor degrees.
Local frames of L make the middle graded algebra a polynomial algebra; the quotient
is its restriction to Z and the kernel is square zero because I squared is zero.
Apply the square-zero boundary derivation theorem to the degree-n section f and the
arbitrary degree-n(e+1) section x. Include their homogeneous summands, then project
the resulting identity onto degree n(e+2). The first kernel action is multiplication
by f on the tensor-degree e coefficient, giving mulTensorPowSection f F e 1.
The other action is tensoring the degree-n kernel class with x; its degree-zero
coefficient is identified with F by the right unitor, giving rho inverse followed
by F whiskered with x. The section comparison maps are formed from the monoidal
pullback and tensor-power exponent isomorphisms, so they send the product to
lambda inverse followed by f tensor x. The kernel comparisons are uniquely fixed
by their inclusion equations. Naturality of the closed-immersion edge and of the
cohomology boundary therefore identifies these two projected actions with the two
displayed H maps. Finally the resolution boundary equals the canonical triangle
boundary used in moduleSectionBoundary. This proves the identity for arbitrary x,
without a power calculation or induction. -/
theorem transportedTensorBoundary_product
    {X Z : Scheme.{u}} (j : Z ⟶ X) [IsClosedImmersion j]
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (Opposite.op ⊤)))]
    (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥) (n : ℕ)
    (hshort : ∀ d : ℕ, (ShortComplex.kernelSequence
      ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
        (L.tensorPow d))).ShortExact)
    (D : TensorBoundaryComparisonData j L n)
    (hD : canonicalTensorBoundaryComparisons j L hI n = D) :
    let F : Z.Modules := (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n)
    let N : Z.Modules := ((tensorPullback j).obj L).tensorPow n
    let H := RingedSpace.moduleCohomology Z.toRingedSpace 1
    let b : ∀ e : ℕ, H.obj (show Z.Modules from F ⊗ N.tensorPow e) ≃+
        (RingedSpace.moduleCohomology X.toRingedSpace 1).obj
          (kernel ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
            (L.tensorPow (n * (e + 1))))) :=
      fun e ↦ Iso.addCommGroupIsoToAddEquiv (D.k e)
    let δ : ∀ e : ℕ, (𝟙_ Z.Modules ⟶ N.tensorPow (e + 1)) →
        (RingedSpace.moduleCohomology X.toRingedSpace 1).obj
          (kernel ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
            (L.tensorPow (n * (e + 1))))) :=
      fun (e : ℕ) (x : 𝟙_ Z.Modules ⟶ N.tensorPow (e + 1)) ↦
      RingedSpace.moduleSectionBoundary X.toRingedSpace
        (ShortComplex.kernelSequence
          ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
            (L.tensorPow (n * (e + 1))))) (hshort (n * (e + 1)))
        ((x ≫ (D.a e).inv).app ⊤ (1 : Γ(Z, ⊤)))
    ∀ (e : ℕ) (f : 𝟙_ Z.Modules ⟶ N) (x : 𝟙_ Z.Modules ⟶ N.tensorPow (e + 1))
      (cx : H.obj (show Z.Modules from F ⊗ N.tensorPow e))
      (cf : H.obj (show Z.Modules from F ⊗ N.tensorPow 0))
      (cp : H.obj (show Z.Modules from F ⊗ N.tensorPow (e + 1))),
      δ e x = b e cx → δ 0 (tensorPowSection f 1) = b 0 cf →
      δ (e + 1) ((λ_ (𝟙_ Z.Modules)).inv ≫ (f ⊗ₘ x)) = b (e + 1) cp →
      cp = H.map (mulTensorPowSection f F e 1) cx +
        H.map ((ρ_ F).inv ≫ F ◁ x) (H.map (ρ_ F).hom cf) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
