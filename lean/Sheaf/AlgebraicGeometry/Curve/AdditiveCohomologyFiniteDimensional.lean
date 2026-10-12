/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Sheaf.AlgebraicGeometry.IsProperOrIsAffine
import Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift
import Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-! # Finite-dimensional scalar model for first additive étale cohomology -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A scalar action on first additive étale cohomology induced by multiplication
on sections is finite-dimensional.
Source: Stacks 0A3N, proof, with 03P2 and 02O6; blueprint
`lem-sc-artin-schreier-dimension`, steps 3--6.
(blueprint: lem-sc-additive-cohomology-finite-dimensional)

Proof: The natural section equivalences identify G with the universe lift of
the associated étale sheaf of O_C. A smooth connected curve is proper or affine
by compactification and affineness of a proper curve minus a nonempty finite
set. If affine, quasi-coherent étale acyclicity makes H^1 zero, so any k-action
on it is finite-dimensional. If proper, the étale/Zariski quasi-coherent
comparison identifies H^1 with H^1(C,O_C), finite-dimensional by proper
coherent cohomology. Naturality for multiplication by c identifies the action
in the hypothesis with the usual k-action: the sectionwise formula uniquely
determines each μ_c, so no arbitrary choice of action is being compared.
Identify derived cohomology with the injective-resolution model naturally
in the sheaf. For the coefficient universe change, use finite affine étale
hypercovers: finite refinements exist in each degree, and ULift identifies
cochains, cocycles, boundaries and scalar maps. The resulting comparison is
an additive equivalence and commutes with every scalar μ_c, hence is k-linear.
This argument does not require ULift to preserve injectives. Transport
finite-dimensionality across the linear equivalence. -/
theorem finiteDimensional_etaleCohomology_one_of_scalar_model
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (ha : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x)) :
    let T := DerivedCategory.singleFunctor
      (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u + 1} C (1 : ℤ)
    ∀ m : Module k (T.obj G),
      letI := m
      (∀ c : k, ∃ μ : G ⟶ G,
        (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
          let ρ : k →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
            (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
          a U (μ.hom.app U x) = a U x * ρ c) ∧
        ∀ x : T.obj G, T.map μ x = c • x) → FiniteDimensional k (T.obj G) := by
  sorry

end AlgebraicGeometry
