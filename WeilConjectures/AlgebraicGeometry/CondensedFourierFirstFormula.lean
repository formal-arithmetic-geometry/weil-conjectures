/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Constant.ConstantModuleFiniteTypeReflection
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheaf
public import WeilConjectures.ProEtaleCoefficients.BoundedConstructibleCounterexample.NonFiniteMultiplicationKernel
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.SheafTensor
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.SectionActionInternal
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingPresheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ProEtaleObjectPullbackRestriction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import WeilConjectures.AlgebraicGeometry.CondensedFourierFirstFormulaMembership
import WeilConjectures.AlgebraicGeometry.CondensedFourierFirstFormulaUnitIso
import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # The first Fourier formulas with condensed coefficients

Source: latest blueprint, sec-fourier-transform/sk-thm-inversion/lem-fd-first-formula.md
and lem-fd-first-formula.proof.md (blueprint: lem-fd-first-formula).
The assertions are derived isomorphisms with membership in the full ordinary
bounded constructible category, for finite E and for its algebraic closure.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The constant coefficient unit in degree zero.
Source: latest blueprint, first-formula opening (blueprint: lem-fd-first-formula). -/
def condensedFourierUnit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :=
  (DerivedCategory.singleFunctor _ 0).obj (Mod.regular (condensedRingObj Λ X))

/-- The degree-zero skyscraper at the origin of the affine line. Closed direct
image is exact, so its total derived functor on the degree-zero unit is i₀* E[0].
Source: latest blueprint, delta_0 definition (blueprint: lem-fd-first-formula). -/
def condensedFourierDelta
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] :=
  (CondensedRing.lowerStar Λ (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
    (condensedFourierUnit Λ (Spec (.of k)))

/-- The two first formulas in the full bounded constructible category. Membership
of the inputs, outputs and displayed comparison objects is explicit. Isomorphisms
are computed in its ambient ordinary derived category, as its definition specifies.
L is the existing positive Tate line, not a chosen trivial line.
Source: latest blueprint, two displayed formulas (blueprint: lem-fd-first-formula). -/
def condensedFourierFirstFormulas
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k₀ : Type u) [Field k₀] [Fintype k₀]
    (k : Type u) [Field k] [Algebra k₀ k] (ψ : AddChar k₀ (MonObj.Γ Λ))
    (c : Compactification (pullback.snd
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k))
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k))))
    (L : Mod (Sheaf (Scheme.ProEt.topology (AffineSpace PUnit (Spec (.of k)))) Ab.{u + 1})
      (condensedRingObj Λ (AffineSpace PUnit (Spec (.of k))))) : Prop :=
  boundedConstructible _ (condensedFourierUnit Λ (AffineSpace PUnit (Spec (.of k)))) ∧
  boundedConstructible _ (condensedFourierDelta Λ k) ∧
  boundedConstructible _ ((condensedFieldFourierTransform Λ k₀ k ψ c).obj
    (condensedFourierUnit Λ (AffineSpace PUnit (Spec (.of k))))) ∧
  boundedConstructible _ ((condensedFieldFourierTransform Λ k₀ k ψ c).obj
    (condensedFourierDelta Λ k)) ∧
  boundedConstructible _ ((shiftFunctor _ (-1 : ℤ)).obj
    (spInternalComplexTwist (AffineSpace PUnit (Spec (.of k))) _ L
      (condensedFourierDelta Λ k) (-1))) ∧
  boundedConstructible _ ((shiftFunctor _ (1 : ℤ)).obj
    (condensedFourierUnit Λ (AffineSpace PUnit (Spec (.of k))))) ∧
  Nonempty ((condensedFieldFourierTransform Λ k₀ k ψ c).obj
      (condensedFourierUnit Λ (AffineSpace PUnit (Spec (.of k)))) ≅
    (shiftFunctor _ (-1 : ℤ)).obj
      (spInternalComplexTwist (AffineSpace PUnit (Spec (.of k))) _ L
        (condensedFourierDelta Λ k) (-1))) ∧
  Nonempty ((condensedFieldFourierTransform Λ k₀ k ψ c).obj (condensedFourierDelta Λ k) ≅
    (shiftFunctor _ (1 : ℤ)).obj
      (condensedFourierUnit Λ (AffineSpace PUnit (Spec (.of k)))))

/-- The constant sheaf transforms to delta_0(-1)[-1], and delta_0 transforms to
E[1], with the same formulas after extension to the finite-subextension-valued
condensed algebraic closure.
Source: latest blueprint, lem-fd-first-formula.md and its proof
(blueprint: lem-fd-first-formula).

Proof, following the DAG's eight steps:
1. Over k₀ expand FT(E) as Rp₂! Kψ[1], using the coefficient pullback unit
(sk-prop-sfb-cartesian-coefficients) and thm-fd-transform-well-defined.
2. Off zero, lem-fd-stalk-formula and lem-fd-character-integral give zero at
all geometric fibres. Stability and lem-fd-condensed-geometric-fibre-conservativity
make its restriction to the punctured line zero.
3. The quasi-compact principal complement and the exact ordinary open-closed sequence
(lem-weil-pbc-proetale-ringed-open-closed) yield the derived localization triangle
(lem-sf-exact-localization-triangle), so FT(E) is the zero-section direct image
of its ordinary restriction to zero.
4. Shriek base change at zero (det-thm-sfb-shriek-base-change) and the kernel's
rank-one lissity (prop-kernel-lisse) identify that restriction with Ra! E[1].
The zero-function unit trivialization (lem-wft-as-unit-trivialization) uses pullback
composition (prop-sfb-module-left-derived-upper-star-comp). The rational affine-line
trace (lem-fd-rational-affine-line-trace) gives E(-1)[-2][1]=E(-1)[-1]. The support
projection formula (lem-sfb-condensed-support-projection-formula) moves the Tate line
through i₀*, giving precisely delta_0(-1)[-1].
5. For the skyscraper, compact-support base change (det-prop-sf-cbc) pulls i₀* E
back to the zero-coordinate support in the product. The same support projection
formula restricts the kernel there; its pairing is zero, so the normalized unit
trivialization makes it the coefficient unit.
6. Closed direct image is exact and is shriek for the identity-open compactification
(def-sfb-module-derived-lower-shriek-chosen). Composition, independence and the unit
law (sk-thm-sf-comp-composition), with p₂ on the support equal to the identity,
give E[1].
7. Pull both isomorphisms to k. Clause (b) of det-prop-sf-cbc allows the arbitrary
base map from k to k₀; the original schemes are Noetherian. The monoidal pullback
comparison (lem-sfb-derived-pullback-tensor-comparison-iso), pullback composition,
and sk-prop-sfb-cartesian-coefficients identify integrands, units and Tate lines.
Stability (sk-thm-sf-ctf-stability) and transform well-definedness give all bounded
constructible memberships. No finite-type condition is placed on k/k₀.
8. The scalar comparisons (sk-prop-scalar-six) commute with pullback, tensor,
shriek and closed pushforward. For the kernel they preserve the E-defined projector
on the finite etale torsor pushforward (prop-kernel-lisse), giving the Qbar kernel.
The unit and the Tate line extend to their Qbar counterparts (sk-def-sp-tate-twist).
Field coefficients give finite Tor amplitude (sk-thm-sf-ctf-stability), so this
proves the second coefficient clause without changing the character. -/
theorem condensedFourier_first_formula
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k₀ : Type u) [Field k₀] [Fintype k₀] [CharP k₀ p]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (hμ : ∀ ζ : rootsOfUnity p (PadicAlgCl ℓ), ((ζ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) ∈ E.1)
    (ψ : AddChar k₀ E) (hψ : ψ ≠ 1)
    (k : Type u) [Field k] [Algebra k₀ k] (hk : Finite k ∨ IsAlgClosed k)
    (c : Compactification (pullback.snd
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k))
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k)))) :
    condensedFourierFirstFormulas (Profinite.continuousMapRingObj E.1) k₀ k
      ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) c
      (spRationalTwist (AffineSpace PUnit (Spec (.of k))) ℓ E) ∧
    condensedFourierFirstFormulas (Profinite.padicAlgClRingObj ℓ) k₀ k
      ((Profinite.PadicAlgCl.constRingHom ℓ).toMonoidHom.compAddChar
        (E.1.subtype.toMonoidHom.compAddChar ψ)) c
      (spQbarTwist (AffineSpace PUnit (Spec (.of k))) ℓ) := by
  have hmem := first_formula_membership p ℓ hpℓ k₀ E hμ ψ hψ k hk c
  have hunit := first_formula_unit_iso p ℓ hpℓ k₀ E hμ ψ hψ k hk c
  have hdelta := first_formula_delta_iso p ℓ hpℓ k₀ E hμ ψ hψ k hk c
  rcases hmem with ⟨hmemE, hmemQ⟩
  rcases hunit with ⟨hunitE, hunitQ⟩
  rcases hdelta with ⟨hdeltaE, hdeltaQ⟩
  rcases hmemE with ⟨mE₁, mE₂, mE₃, mE₄, mE₅, mE₆⟩
  rcases hmemQ with ⟨mQ₁, mQ₂, mQ₃, mQ₄, mQ₅, mQ₆⟩
  constructor
  · simpa [condensedFourierFirstFormulas, condensedFourierUnit, condensedFourierDelta] using
      (show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ from
        ⟨mE₁, mE₂, mE₃, mE₄, mE₅, mE₆, hunitE, hdeltaE⟩)
  · simpa [condensedFourierFirstFormulas, condensedFourierUnit, condensedFourierDelta] using
      (show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ from
        ⟨mQ₁, mQ₂, mQ₃, mQ₄, mQ₅, mQ₆, hunitQ, hdeltaQ⟩)

end AlgebraicGeometry.ProEtale
