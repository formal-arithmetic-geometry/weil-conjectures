/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.Etale.EtaleProjectionSectionNormalization
import WeilConjectures.SixFunctors.NativeExtensionDescentProof.NativeOpenTensorTotalComparison
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorTriangulated

/-!
# Unbounded tensor totalization for arbitrary étale sum extension

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/
sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md, Charts, lines 20--36;
Stacks Project, Tag 0GKF and homology.tex, Section 010V and Tag 012Z.
(blueprint: lem-pur-ordinary-etale-sum-tensor-totalization)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- For an arbitrary étale morphism, the ordinary sheafified sum extension commutes
with the direct-sum total tensor of arbitrary unbounded complexes. The summand map is
exactly the inverse canonical sheaf projection isomorphism, followed by the image of
the target summand inclusion. By `Etale.etaleProjection_section_normalization`, this
sends `(s,m) ⊗ h` to `(s,m ⊗ s^*h)`. The same comparison is natural in both variables
and descends to the canonical homotopy-category bifunctors, with components `Q(Ψ)`.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/
sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md, Charts, lines 20--36;
Stacks Project, Tag 0GKF, homology.tex, Section 010V and Tag 012Z.
(blueprint: lem-pur-ordinary-etale-sum-tensor-totalization)

Proof plan:
1. The exact sum extension is left adjoint to inverse image, hence preserves all
small coproducts, including the empty coproduct. Both functors are additive and
therefore act degreewise on complexes.
2. Invert the canonical jointly natural `Etale.etaleLowerShriekTensorIso`. Its
section normalization is `(s,m) ⊗ h ↦ (s,m ⊗ s^*h)` for every étale morphism.
3. Apply `NativeExtensionDescentProof.native_open_tensor_total_comparison` to the
sheaf tensor bifunctors and these functors. Its summand equation is precisely
`TotalTensorSummandNormalization`. Naturality for the two differentials and
additivity preserve the common sign `(-1)^p`; thus these degree maps form chain
isomorphisms, natural in both complexes. Countable coproducts exist in the
Grothendieck abelian sheaf categories, so unbounded complexes are allowed.
4. Totalization of an additive bifunctor carries homotopies to homotopies in each
variable. Conjugating by the comparison gives the same property for the target.
Quotient the naturality equations to obtain a natural isomorphism on homotopy
categories, whose components are the classes of the same chain isomorphisms.
No boundedness, constructibility, flatness or finiteness hypothesis is used. -/
theorem ordinary_etale_sum_tensor_totalization
    (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (e : U ⟶ X) (he : Etale e) :
    ∃ Ψ : TotalTensorComparison
        (curriedTensor (EtaleModuleSheaf U A)) (curriedTensor (EtaleModuleSheaf X A))
        (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e he)
        (Etale.upperStar (ModuleCat.{u + 1} A) e),
      TotalTensorSummandNormalization
        (curriedTensor (EtaleModuleSheaf U A)) (curriedTensor (EtaleModuleSheaf X A))
        (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e he)
        (Etale.upperStar (ModuleCat.{u + 1} A) e) Ψ
        (fun M N ↦ (Etale.etaleLowerShriekTensorIso (ModuleCat.{u + 1} A) he M N).inv) ∧
      TotalTensorNaturality
        (curriedTensor (EtaleModuleSheaf U A)) (curriedTensor (EtaleModuleSheaf X A))
        (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e he)
        (Etale.upperStar (ModuleCat.{u + 1} A) e) Ψ ∧
      TotalTensorHomotopyIso
        (curriedTensor (EtaleModuleSheaf U A)) (curriedTensor (EtaleModuleSheaf X A))
        (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e he)
        (Etale.upperStar (ModuleCat.{u + 1} A) e) Ψ := by
  sorry

end AlgebraicGeometry
