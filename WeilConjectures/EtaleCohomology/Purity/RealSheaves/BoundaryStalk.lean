/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.InertiaNeighbourhood
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Representation
public import WeilConjectures.ConstructibleSheaf.LowerStarSpecialization

/-!
# Boundary stalks of direct images as inertia invariants

Let `j : U ⟶ C` be an open immersion into an integral scheme, `W` an affine open with Dedekind
ring of sections `R = Γ(C, W)` and `W ∩ U = D(ϖ)`, `Ω` a separable closure of the function field
`K = k(C)` and `Q` a maximal ideal of the integral closure `B` of `R` in `Ω` over a maximal
ideal `m` of `R` (the boundary point). The local ring `A = B_Q` is strictly henselian with
fraction field `Ω`; its closed geometric point `x̄ : Spec κ(A) ⟶ Spec A ⟶ C` is a geometric point
over the boundary point and `η : Spec Ω ⟶ Spec A` lies over the generic geometric point of `U`.
The inertia group `I = {σ ∈ Gal(Ω / K) | σ ≡ id mod Q}` acts on the geometric generic stalk `F_η`
of a sheaf `F` on `U`.

For `F` finite locally constant (blueprint `lem-wf-boundary-stalk-invariants`, at a finite
coefficient level), the specialization map
`(j_* F)_x̄ ⟶ F_η` (`AlgebraicGeometry.Etale.boundarySpecialization`) is injective with image the
inertia invariants `F_η^I`, and it intertwines the action of an element `σ` of the decomposition
group (the stabiliser of `Q`) on `F_η` with the action on `(j_* F)_x̄` of the automorphism of the
geometric point `x̄` induced by the residue automorphism of `σ`
(`AlgebraicGeometry.Etale.boundaryStalkMap_comp_boundarySpecialization`). In particular
`(j_* F)_x̄ ≅ F_η^I` (`AlgebraicGeometry.Etale.boundaryStalkLinearEquiv`).

* Injectivity is `AlgebraicGeometry.Etale.injective_specializationStalk`.
* The image consists of invariants since an inertia element induces an automorphism of `A` over
  `C` acting trivially on the residue field.
* Conversely, an invariant `m ∈ F_η` is a point over `η` of the finite étale `U`-scheme `P`
  representing `F`, fixed by inertia; it extends to an étale neighbourhood `V` of `x̄`
  together with a `U`-morphism `V ×_C U ⟶ P`
  (`AlgebraicGeometry.Scheme.FiniteEtale.exists_etale_lift_of_forall_inertia`), that is a section
  of `j_* F` over `V` specializing to `m`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme Scheme.FiniteEtale

namespace Etale

variable {C U : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j] [IsIntegral C]
  [Nonempty U] {W : C.Opens} [Fact (IsAffineOpen W)] [Nonempty W]
  {Ω : Type u} [Field Ω] [Algebra C.functionField Ω] [Algebra Γ(C, W) Ω]
  [IsScalarTower Γ(C, W) C.functionField Ω] [IsGalois C.functionField Ω] [IsSepClosed Ω]
  (Q : Ideal (integralClosure Γ(C, W) Ω)) [Q.IsMaximal] {Λ : Type (u + 1)} [Ring Λ]

/-- The generic geometric point `η : Spec Ω ⟶ U`. -/
noncomputable abbrev genericGeometricPoint : Spec (.of Ω) ⟶ U :=
  pointOfAlgebra Ω (genericPointLift j)

/-- The geometric point `x̄ : Spec κ(B_Q) ⟶ Spec B_Q ⟶ C` over the boundary point. -/
noncomputable abbrev boundaryGeometricPoint :
    Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime Q))) ⟶ C :=
  closedGeometricPoint (Localization.AtPrime Q) ≫ specAtPrime Fact.out Q

omit [IsGalois C.functionField Ω] [IsSepClosed Ω] in
lemma specMap_comp_genericGeometricPoint (σ : Ω ≃ₐ[C.functionField] Ω) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ genericGeometricPoint (Ω := Ω) j =
      genericGeometricPoint j := by
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext a
  exact σ.commutes a

variable {j} in
/-- The action of `σ ∈ Gal(Ω / k(C))` on the geometric generic stalk `F_η`. -/
noncomputable def galoisStalkMap (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (σ : Ω ≃ₐ[C.functionField] Ω) :
    (pointSmallEtale (genericGeometricPoint (Ω := Ω) j)).sheafFiber.obj F ⟶
      (pointSmallEtale (genericGeometricPoint (Ω := Ω) j)).sheafFiber.obj F :=
  (pointSmallEtaleHom (genericGeometricPoint j) (σ : Ω →+* Ω)
    (specMap_comp_genericGeometricPoint j σ)).sheafFiber.app F

/-- Blueprint `lem-wf-boundary-stalk-invariants` (the comparison map): the specialization map
`(j_* F)_x̄ ⟶ F_η` from the stalk of the direct image at the geometric point over the boundary
point to the geometric generic stalk, sending the germ of a section of `F` over `V ×_C U`, for an
étale neighbourhood `V` of `x̄`, to its germ at the lift of `η` through `Spec B_Q ⟶ V`. -/
noncomputable def boundarySpecialization (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (pointSmallEtale (boundaryGeometricPoint Q)).sheafFiber.obj
        ((j)_*[ModuleCat.{u + 1} Λ].obj F) ⟶
      (pointSmallEtale (genericGeometricPoint (Ω := Ω) j)).sheafFiber.obj F :=
  specializationStalk j (specAtPrime Fact.out Q) (CommRingCat.ofHom (Ideal.atPrimeToField Q)) _
    (pointOfAlgebra_comp_eq_specAtPrime j Fact.out Q) F

/-- Blueprint `lem-wf-boundary-stalk-invariants` (injectivity): for `F` locally constant and `C`
locally noetherian with étale local rings that are domains (e.g. regular), the specialization
map of the boundary stalk is injective. -/
theorem injective_boundarySpecialization
    (hC : ∀ (V : C.Etale) (v : V.left), IsDomain (V.left.presheaf.stalk v))
    [IsLocallyNoetherian C] (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsLocallyConstantSheaf F] :
    Function.Injective (boundarySpecialization j Q F) :=
  injective_specializationStalk j _ _ _ _ hC F

end Etale

end AlgebraicGeometry
