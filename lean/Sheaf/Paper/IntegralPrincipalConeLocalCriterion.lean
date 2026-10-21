/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.PrincipalConeTower
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses
public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses

/-! # The local criterion for a principal cone completion

Source: Stacks Tags 0999, 099B and 0A0E.
(blueprint: lem-pur-integral-principal-cone-local-criterion) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralPrincipalCone

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : AlgebraicGeometry.Scheme.{t})

/-- The localization test on the actual slice, with independent coefficient size.
Source: Stacks 0999 (blueprint: lem-pur-integral-principal-cone-local-criterion). -/
def localTest (K : IntegralOnSlice.D l E T none) (U : T.ProEt)
    (s : ((IntegralOnSlice.ring l E T (some U)).obj ⋙ forget CommRingCat).sections) :
    IntegralOnSlice.D l E T (some U) :=
  letI : HasSheafify (IntegralOnSlice.topology T (some U))
      CommRingCat.{max u (t + 1)} :=
    letI : EssentiallySmall.{max u (t + 1)} (IntegralOnSlice.Site T (some U)) :=
      essentiallySmallSelf _
    hasSheafifyEssentiallySmallSite _ _
  letI := HasDerivedCategory.standard
    (SheafOfModules.{max u (t + 1)} ((IntegralOnSlice.rings l E T none).over U))
  (IntegralOnSlice.hom l E T (some U)).obj
    (op ((DerivedCategory.singleFunctor _ 0).obj
      (ringedSectionLocalizationOfUniverses (IntegralOnSlice.ring l E T (some U)) s)),
      ringedSiteDerivedRestrictionOfUniverses (IntegralOnSlice.rings l E T none) U K)

/-- Vanishing for every locally divisible section on every slice.
Source: Stacks 0999 (blueprint: lem-pur-integral-principal-cone-local-criterion). -/
def locallyComplete
    (σ : ∀ U : T.ProEtᵒᵖ, (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)
    (K : IntegralOnSlice.D l E T none) : Prop :=
  ∀ (U : T.ProEt)
    (s : ((IntegralOnSlice.ring l E T (some U)).obj ⋙ forget CommRingCat).sections),
    (∃ S : Sieve U, S ∈ AlgebraicGeometry.Scheme.ProEt.topology T U ∧
      ∀ (V : T.ProEt) (f : V ⟶ U), S f →
        ∃ c : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj (op V),
          s.val (op (Over.mk f)) = σ (op V) * c) →
      IsZero (localTest l E T K U s)

/-- The principal cone completion is locally complete, and its specified unit is
invertible exactly for locally complete inputs. The scalar is any natural section;
no regularity, boundedness or flatness of the input complex is needed.

Source: Stacks Tags 0999, 099B and 0A0E, the singleton Koszul completion reflector.
(blueprint: lem-pur-integral-principal-cone-local-criterion).

Proof: replace the essentially small ringed site by its small model at coefficient
universe max(u,t+1). Exact module restriction is an equivalence, preserving the scalar,
localizations, internal Hom, products and mapping cones. Apply the ringed Koszul
completion reflector to the singleton scalar. Its negative Koszul tensor complex is
canonically the cone of scalar multiplication on P, and its (scalar,1) transitions and
degree-zero unit are those of PrincipalCone. The image ideal of multiplication by the
scalar consists exactly of the sections locally divisible by that scalar; sheaf image
and local lifting give the displayed covering-sieve formulation, including on every
slice. The reflector gives completeness of its output and the unit criterion. Transport
back through the site equivalence and then through e. For a zero scalar localization
at every ideal section is zero, and the same construction still applies. -/
theorem localCriterion
    (σ : ∀ U : T.ProEtᵒᵖ, (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)
    (_hσ : ∀ {U V : T.ProEtᵒᵖ} (f : U ⟶ V),
      (completedIntegralCoefficientSheafUnrestricted l E T).obj.map f (σ U) = σ V)
    (P : IntegralOnSlice.Cx l E T none) (μ : End P)
    (_hμ : ∀ (q : ℤ) (U : T.ProEtᵒᵖ) (x : (P.X q).val.obj U),
      (μ.f q).val.app U x = σ U • x)
    (K : IntegralOnSlice.D l E T none) (e : DerivedCategory.Q.obj P ≅ K) :
    locallyComplete l E T σ (DerivedCategory.Q.obj (CochainComplex.PrincipalCone.completion μ)) ∧
      (locallyComplete l E T σ K ↔
        IsIso (e.inv ≫ DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ))) := by
  sorry

end WeilConjectures.IntegralPrincipalCone
