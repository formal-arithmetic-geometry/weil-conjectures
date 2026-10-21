module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.NumberTheory.Padics.PadicNumbers

import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization
import Sheaf.AlgebraicGeometry.ProEtale.HypercoverExistence
import Sheaf.AlgebraicGeometry.ProEtale.SectionsConservative
import Sheaf.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
import Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic
import Sheaf.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.FiniteTypeConstantExact
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import Sheaf.CategoryTheory.Sites.RGammaDerivedLimit
import Sheaf.Paper.RingedDerivedSliceLocalization
import Sheaf.Topology.SpectralSpace.ClopenComponentHomeomorphism
import WeilConjectures.Algebra.FiniteTorsionExtensionInduction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor

import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Topology.Spectral.Basic

/-!
# The finite torsion open-unit criterion for norm coefficients

Source: blueprint main-20261015, direct-images proof paragraph (3), agent-formulated
analytical input (blueprint: lem-sfb-torsion-acyclic-norm-coefficient-test).
The coefficient rings use all continuous functions, including for the incomplete algebraic
closure. The hypothesis and conclusion concern the actual derived adjunction units.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Pull the initial coordinate into the spectrum of the filtered colimit.
Source: the affine limit in direct-images paragraph (3)
(blueprint: lem-sfb-torsion-acyclic-norm-coefficient-test). -/
def normTestLimitSection {I : Type u} [PartialOrder I] [OrderBot I]
    (R : I ⥤ CommRingCat.{u}) [HasColimit R] (f₀ : R.obj ⊥) :
    Γ(Spec (colimit R), ⊤) :=
  (Scheme.ΓSpecIso (colimit R)).inv ((colimit.ι R ⊥).hom f₀)

/-- The conclusion of the criterion, spelled out on every affine pro-etale object.
The principal open here is the canonical base change of the given principal open.
Source: direct-images paragraph (3), the actual lisse-module open unit
(blueprint: lem-sfb-torsion-acyclic-norm-coefficient-test). -/
def NormTestLisseOpenUnit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (f : Γ(X, ⊤)) : Prop :=
  ∀ (V : Scheme.{u}) (v : V ⟶ X) [WeaklyEtale v] [IsAffine V],
    ∀ N : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V),
      IsLisseCoefficientModule Λ N →
        IsIso ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ
          (V.basicOpen (v.appTop.hom f)).ι).unit.app
            ((DerivedCategory.singleFunctor _ 0).obj N))

/-- Finite torsion open-unit acyclicity implies the actual open-unit isomorphism for
lisse modules over E and its norm-topological algebraic closure.
Source: agent-formulated analytical input, direct-images paragraph (3)
(blueprint: lem-sfb-torsion-acyclic-norm-coefficient-test).

Proof: (1) The internal-module/section-ring equivalence and module/abelian evaluation
comparison identify the finite-coefficient unit on a weakly contractible affine V with
restriction RΓ(V,Z/ell^s) → RΓ(T,Z/ell^s), T = V[1/f]. Slice localization preserves this
actual unit. Exact evaluation makes positive cohomology on V vanish; V and T are qcqs.
(2) Constant sheafification is exact. Short exact sequences give triangles, restriction
respects these triangles, and two-out-of-three makes its isomorphism locus extension
closed. Finite-torsion extension induction gives all finite ell-primary groups.
(3) Every ell^n-torsion group is the filtered union of its finite subgroups. Constant
sheafification preserves this union. Bounded continuity on affine weakly contractible
hypercovers gives the same restriction isomorphism for every such group.
(4) For a complete normed extension B, its unit-ball sheaf L is the inverse limit of
its discrete quotients O/ell^n O. Completeness gives this identification sectionwise;
the transitions are epimorphisms. B-valued continuous functions are the filtered union
of ell^{-n} L, since their images on qcqs affine tests are compact and bounded.
(5) The epimorphic Milnor theorem identifies L with the derived limit of those
quotients. Derived sections commute with derived limits, and bounded continuity handles
rationalization. Thus restriction is a quasi-isomorphism for complete B, including E.
(6) In degree zero, the finite cyclic restriction identifies clopens, hence component
spaces of the spectral schemes. Continuous maps into E or Omega factor through these
component spaces. This proves degree-zero restriction without completion.
(7) Apply (5) to the normed-field completion of Omega. The separate positive-cohomology
completion-monomorphism lemma for this regular finite-locally-free tower injects
H^q(T,C_Omega) into its zero completed counterpart for q > 0. Together with (6) and
negative-degree vanishing this proves the actual scalar restriction isomorphism.
(8) Trivialize the supplied lisse module on a pro-etale cover. The cone of its actual
unit restricts, by unit-compatible slice localization, to finite sums of the scalar
calculation. Exact, conservative weakly contractible affine evaluations make each
restricted cone zero, hence the cone is zero. Rank zero, empty schemes and identity
opens are included. No finite-field descent or completeness of Omega is used. -/
theorem torsionAcyclic_normCoefficient_test
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (E Ω : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] [NormedField Ω] [NormedAlgebra E Ω]
    [IsAlgClosure E Ω]
    (I : Type u) [PartialOrder I] [OrderBot I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [HasColimit R]
    (κ : (Functor.const I).obj (CommRingCat.of k) ⟶ R)
    (hregular : ∀ i : I, IsRegularScheme (Spec (R.obj i)))
    (hfiniteType : ∀ i : I, LocallyOfFiniteType (Spec.map (κ.app i)) ∧
      QuasiCompact (Spec.map (κ.app i)))
    (hfiniteFlat : ∀ (i j : I) (h : i ≤ j),
      IsFinite (Spec.map (R.map (homOfLE h))) ∧ Flat (Spec.map (R.map (homOfLE h))))
    (f₀ : R.obj ⊥)
    (hregularElement : ∀ i : I, (R.map (homOfLE (bot_le : ⊥ ≤ i))).hom f₀ ∈
      nonZeroDivisors (R.obj i))
    (htorsion : ∀ (s : ℕ), 1 ≤ s →
      IsIso ((derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ s))))
        ((Spec (colimit R)).basicOpen (normTestLimitSection R f₀)).ι).unit.app
          ((DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf (Scheme.ProEt.topology (Spec (colimit R)))
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ s))))).obj
                (ModuleCat.of (ULift.{u + 1} (ZMod (ℓ ^ s)))
                  (ULift.{u + 1} (ZMod (ℓ ^ s)))))))) :
    NormTestLisseOpenUnit (Profinite.continuousCoefficientRingObj E)
      (Spec (colimit R)) (normTestLimitSection R f₀) ∧
    NormTestLisseOpenUnit (Profinite.continuousCoefficientRingObj Ω)
      (Spec (colimit R)) (normTestLimitSection R f₀) := by
  sorry

end AlgebraicGeometry.ProEtale
