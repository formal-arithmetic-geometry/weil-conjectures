/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients

import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! # Uniform Ext bound for constructible sheaves

Source: blueprint latest, `sec-six-functors-basics/sk-lem-uniform-constructible-ext`,
node statement and `sk-lem-uniform-constructible-ext.proof.md` (blueprint:
sk-lem-uniform-constructible-ext).

The theorem states the uniform Ext vanishing for every constructible source and target,
and the explicit cutoff for a locally closed lisse source with a lisse integral lattice.
Its proof proceeds by finite
coefficient descent, coefficient-heart dévissage, the formal closed-support formula,
torsion reductions, derived completeness, and the inverse-limit bound. The finite-field
and algebraically closed base cases give finiteness of the cohomological dimensions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped CategoryTheory.Obj

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

/-- Uniform Ext vanishing for constructible pro-étale coefficient modules, with the
explicit locally closed lisse cutoff from the formal closed-support argument.

Source: blueprint latest, `sec-six-functors-basics/sk-lem-uniform-constructible-ext`,
node statement and proof (blueprint: sk-lem-uniform-constructible-ext).
Proof: finite coefficient descent and the rational stratum estimate give a finite bound for
locally closed lisse sources. The coefficient-heart filtration and the covariant and
contravariant Ext exact sequences extend this bound first to targets and then to sources.
For the explicit cutoff, retain the given global lisse lattice and use the formal
closed-support fibre formula, torsion reductions,
derived completeness and the Milnor inverse-limit sequence; the two extra degrees are the
support cone and the derived inverse limit. The base-field cohomological-dimension result
makes the displayed cutoffs finite.
-/
theorem uniformConstructibleExt (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ)
    [Fact ℓ.Prime] (_hℓ : ℓ ≠ D.p)
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (_hΛ :
      (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
        FiniteDimensional ℚ_[ℓ] E ∧
          Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
        Λ = Profinite.padicAlgClCondensedRing ℓ)
    (k : Type u) [Field k]
    (_hk : Nonempty (k ≃+* D.k₀) ∨ Nonempty (k ≃+* D.k))
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    (∀ C : ConstantModelConstructible (coefficientHeartRingObj Λ) X,
      ∃ d : ℕ, ∀ N : ConstantModelConstructible (coefficientHeartRingObj Λ) X,
        ∀ q : ℕ, d < q →
          Subsingleton (Abelian.Ext C.obj N.obj q)) ∧
    (∀ (S Z U : Scheme.{u}) (v : S ⟶ Z) (i : Z ⟶ X) (j : U ⟶ X)
      [IsOpenImmersion v] [IsClosedImmersion i] [IsOpenImmersion j]
      [CompactSpace S] [QuasiSeparatedSpace S] [QuasiCompact j],
      Set.range i.base = (Set.range j.base)ᶜ →
      ∀ L : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (coefficientHeartRingObj Λ) S),
      IsLisseCoefficientModule (coefficientHeartRingObj Λ) L →
      (∃ (E : PadicAlgCl.FiniteIntermediateField ℓ)
        (f : Profinite.continuousMapRingSheaf.{u} E ⟶ Λ),
        ((∃ h : Profinite.continuousMapRingSheaf.{u} E = Λ, f = eqToHom h) ∨
          ∃ h : Profinite.padicAlgClCondensedRing.{u} ℓ = Λ,
            f = Profinite.padicSubfieldCondensedRingToPadicAlgCl ℓ E ≫ eqToHom h) ∧
        ∃ Lmodel : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
          (condensedRingObj (LisseQlbar.fieldRing ℓ E) S),
          IsLisseCoefficientModule (LisseQlbar.fieldRing ℓ E) Lmodel ∧
          LisseQlbar.hasLattice (LisseQlbar.integerRing ℓ E)
            (LisseQlbar.fieldRing ℓ E) (LisseQlbar.integerInclusion ℓ E) S Lmodel ∧
          Nonempty ((CategoryTheory.Mod.extendScalars
            ((upperStarFromPoint S).map
              ((sheafCompose (coherentTopology Profinite.{u})
                (forget₂ RingCat.{u + 1} Ab.{u + 1})).map f))).obj Lmodel ≅ L)) →
      ∃ d : ℕ,
        (d : WithTop ℕ) =
          relativeCohomologicalDimension ℓ (Fact.out : ℓ.Prime) j +
            cohomologicalDimension ℓ (Fact.out : ℓ.Prime) S + 2 ∧
        ∀ N : ConstantModelConstructible (coefficientHeartRingObj Λ) X,
          ∀ q : ℕ, d < q →
            Subsingleton
              (Abelian.Ext
                ((CondensedRing.lowerStar (coefficientHeartRingObj Λ) i).obj
                  ((CondensedRing.openImmersionLowerShriek
                    (coefficientHeartRingObj Λ) v).obj L))
                N.obj q)) := by
  sorry

end AlgebraicGeometry.ProEtale
