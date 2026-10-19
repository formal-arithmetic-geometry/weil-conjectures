/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Algebra.Homology.AlgebraicNormalizedDualizing
public import WeilConjectures.Algebra.Homology.IdealPowerTorsionFunctor
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs

public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
import Sheaf.Algebra.Homology.CoherentRHomFiniteInjectiveDimension
import Sheaf.Algebra.Homology.IdealTorsionCechComputation
import Sheaf.Paper.ExtendedCechCompletionModel
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-! # Algebraic local duality with completed Ext

Source: Stacks Project, `dualizing.tex`, Tag 0AAK, lemma-special-case-local-duality
(blueprint: lem-per-algebraic-local-duality).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace DerivedCategory

/-- Algebraic local duality: the completed Ext into a normalized dualizing complex is
the Matlis dual of local cohomology. The injective hull is quantified explicitly, and
the completion is ordinary module completion, without assuming that the ring is complete.
Source: Stacks Project, `dualizing.tex`, Tag 0AAK, lemma-special-case-local-duality;
Tag 08Y3 for injective hulls; Tag 0955 for ideal torsion.
(blueprint: lem-per-algebraic-local-duality).

Proof:
1. By lem-per-algebraic-dualizing-torsion-hull, the torsion of Ω gives one injective
hull E₀, proving existence. For any other hull E, extend the residue-field embedding
along κ → E₀ by injectivity of E (def-sp-injective-resolutions). Essentiality of κ in
E₀ makes the extension u injective. Injectivity of E₀ extends its inverse to v : E → E₀,
with vu = 1. Then E = u(E₀) ⊕ ker(v); essentiality of κ in E forces ker(v) = 0.
Thus u is an isomorphism and derived torsion of Ω is E[0] for every such E.
2. Set K = M[0] and B = RHom(K,Ω). The normalized dualizing conditions give finite
cohomology and a bounded injective representative of Ω. Hence
lem-trf-coherent-rhom-finite-injective-dimension makes every Hʲ(B) finite.
3. Choose generators of the maximal ideal by def-weil-pbc-noetherian-ring. Let C be
the augmented localization complex of lem-per-ideal-torsion-cech-computation and put
Λ(X) = RHom(C,X). The lem-per-algebraic-completion-rhom comparison gives
Λ(B) ≅ RHom(Λ(K),Λ(Ω)). Then lem-per-algebraic-torsion-completion-hom identifies
this with RHom(RΓ(K),RΓ(Ω)), hence RHom(RΓ(K),E[0]) by step 1 and
def-pur-derived-internal-hom.
4. On the one-object site, lem-weil-pbc-extended-cech-completion-model and
lem-weil-pbc-constant-completion-equivalence identify Λ(B) and the derived limit
of B tensor A/mⁿ by their identical reflection property and compatible units.
Uniqueness gives inverse maps. The product-fibre comparison of
lem-weil-pbc-ringed-strict-tower-homotopy-limit, and exactness of products of modules,
identify this limit with the termwise product-fibre model. Apply
lem-per-derived-completion-finite-cohomology using step 2: H⁻ⁱ(Λ(B)) is the ordinary
completion of H⁻ⁱ(B), namely the completed Ext in the conclusion.
5. Compute T = RΓ(M[0]) by applying the ideal-power torsion functor
(def-sbc-ideal-power-torsion-functor) to an injective resolution. The bounded-below
injective resolution and E[0] are K-injective by
lem-weil-pbc-bounded-below-injectives-kinjective; over a Noetherian ring its torsion
terms are injective as in Tag 0955. Thus def-pur-derived-internal-hom computes the
right side of step 3 by the total Hom complex into E[0]. Write Zⁱ = ker(dⁱ) and
Bⁱ = im(dⁱ⁻¹). Degree -i cycles are maps Tⁱ/Bⁱ → E. Restriction to Zⁱ/Bⁱ is
surjective by injectivity. Its kernel consists of maps vanishing on Zⁱ, hence maps
factoring through im(dⁱ), which extend to Tⁱ⁺¹ by injectivity. These are precisely
the boundaries; negate the extension if the Hom differential requires it. Thus
H⁻ⁱ RHom(T,E[0]) ≅ Hom(Hⁱ(T),E).
6. Take degree -i cohomology of step 3 and compose the identifications of steps 4
and 5. This gives the required A-linear isomorphism for any hull, any finite M,
and every i ≥ 0, including i = 0. No step assumes completeness of A.
-/
theorem algebraic_local_duality
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [HasDerivedCategory.{u} (RingSiteModules A)]
    (Ω : DerivedCategory (RingSiteModules A))
    (hΩ : IsNormalizedAlgebraicDualizing A Ω) :
    (∃ (E : ModuleCat.{u} A) (ι : IsLocalRing.ResidueField A →ₗ[A] E),
      Function.Injective ι ∧ Injective E ∧
      ∀ N : Submodule A E, N ≠ ⊥ → N ⊓ LinearMap.range ι ≠ ⊥) ∧
    ∀ (E : ModuleCat.{u} A) (ι : IsLocalRing.ResidueField A →ₗ[A] E),
      Function.Injective ι → Injective E →
      (∀ N : Submodule A E, N ≠ ⊥ → N ⊓ LinearMap.range ι ≠ ⊥) →
      ∀ (M : ModuleCat.{u} A) [Module.Finite A M] (i : ℕ),
        Nonempty
          (AdicCompletion (IsLocalRing.maximalIdeal A)
            (((homologyFunctor (RingSiteModules A) (-(i : ℤ))).obj
              ((derivedInternalHomOfUniverses.{u, u, u, u}
                ⊥ (CochainComplex.onePointRingSheaf A)).obj
                (op ((DerivedCategory.singleFunctor (RingSiteModules A) 0).obj
                  (algebraicDualizingModuleSheaf A M)), Ω))).val.obj
                  (op ⟨PUnit.unit⟩)) ≃ₗ[A]
            ((((ModuleCat.idealPowerTorsion (IsLocalRing.maximalIdeal A)).rightDerived i).obj M)
              →ₗ[A] E)) := by
  sorry

end DerivedCategory
