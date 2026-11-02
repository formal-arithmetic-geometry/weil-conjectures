/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteZerothHypercohomologyOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.IntegralLisseLocalStructureAux
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalSheavesModules
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.AlgebraicGeometry.IntegralConstantCompletion
import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseOrigin
import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportAdjunction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedInverseImageLimits
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.CategoryTheory.TruncationHypercohomology

/-!
# The torsion stratum bound

Source: latest blueprint, sec-six-functors-basics/sk-lem-uniform-constructible-ext,
`sk-lem-uniform-constructible-ext-torsion.md` and its proof; Stacks Tags 099Y,
09AF and 09A6 (blueprint: det-uniform-constructible-ext-torsion).

The coefficients are the continuous condensed integer ring and its actual finite
quotients. The helpers assemble the quotient sheaf, supported complex and dual twist
from the recorded module operations. Cohomological cutoffs belong to `WithTop ℕ`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
  [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]

/-- Ordinary reduction of an integral module, retaining its quotient-ring action.
It is scalar extension along the actual continuous quotient map, so on a locally
free lattice it is precisely M / π^n M, including rank zero.
Source: torsion proof, opening paragraph (blueprint: det-uniform-constructible-ext-torsion). -/
abbrev torsionStratumReduction {Y : Scheme.{u}}
    (M : FormalSupportModules (DerivedNakayama.integerRing ℓ E) Y) (n : ℕ) :
    FormalSupportModules (DerivedNakayama.quotientRing ℓ E n) Y :=
  (Mod.extendScalars (coefficientMap (DerivedNakayama.reductionRing ℓ E n) Y)).obj M

/-- The absolute dimension, with the qcqs structures supplied by the standing setting.
Source: sk-def-cd and the bound in torsion clause (2)
(blueprint: det-uniform-constructible-ext-torsion). -/
def torsionStratumDimension (k : Type u) [Field k]
    (S : Over (Spec (.of k))) [QuasiCompact S.hom] [IsSeparated S.hom] : WithTop ℕ := by
  letI : CompactSpace S.left := QuasiCompact.compactSpace_of_compactSpace S.hom
  letI : QuasiSeparatedSpace S.left := quasiSeparatedSpace_of_quasiSeparated S.hom
  exact cohomologicalDimension ℓ (Fact.out : ℓ.Prime) S.left

/-- The relative dimension of the open complement. Finite type makes its source
Noetherian, so its quasi-compactness and quasi-separatedness are derived, not assumed.
Source: sk-def-cd and the bound in torsion clauses (1)--(2)
(blueprint: det-uniform-constructible-ext-torsion). -/
def torsionStratumRelativeDimension (k : Type u) [Field k]
    {V X : Over (Spec (.of k))} [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    (j : V ⟶ X) : WithTop ℕ := by
  letI : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian V.hom
  letI : CompactSpace V.left := QuasiCompact.compactSpace_of_compactSpace V.hom
  letI : IsNoetherian V.left := ⟨⟩
  exact relativeCohomologicalDimension ℓ (Fact.out : ℓ.Prime) j.left

/-- RΓ_Z of the degree-zero sheaf k_* v_! (M / π^n M), using the canonical
closed-support functor of sk-lem-formal-closed-support.
Source: torsion clause (1) (blueprint: det-uniform-constructible-ext-torsion). -/
abbrev torsionStratumSupport {Z V X T B : Scheme.{u}}
    (i : Z ⟶ X) (j : V ⟶ X) (kb : B ⟶ X) (vb : T ⟶ B)
    [IsOpenImmersion vb]
    (M : FormalSupportModules (DerivedNakayama.integerRing ℓ E) T) (n : ℕ) :
    DerivedCategory (FormalSupportModules (DerivedNakayama.quotientRing ℓ E n) Z) :=
  (closedSupport (DerivedNakayama.quotientRing ℓ E n) i j).rightDerivedFunctor.obj
    ((DerivedCategory.singleFunctor _ 0).obj
      ((lowerStar (DerivedNakayama.quotientRing ℓ E n) kb).obj
        ((openImmersionLowerShriek (DerivedNakayama.quotientRing ℓ E n) vb).obj
          (torsionStratumReduction ℓ E M n))))

/-- The displayed dual twist (L^∨ / π^n) ⊗ u^* RΓ_Z b_!(M / π^n).
The dual is ordinary internal Hom into the coefficient unit. Derived tensor computes
the ordinary termwise tensor here because the reduced dual of a lisse lattice is flat.
Source: torsion clause (2) (blueprint: det-uniform-constructible-ext-torsion). -/
abbrev torsionStratumTwist {S Z V X T B : Scheme.{u}}
    (v : S ⟶ Z) (i : Z ⟶ X) (j : V ⟶ X) (kb : B ⟶ X) (vb : T ⟶ B)
    [IsOpenImmersion vb]
    (L : FormalSupportModules (DerivedNakayama.integerRing ℓ E) S)
    (M : FormalSupportModules (DerivedNakayama.integerRing ℓ E) T) (n : ℕ) :
    DerivedCategory (FormalSupportModules (DerivedNakayama.quotientRing ℓ E n) S) :=
  ((derivedTensor (DerivedNakayama.quotientRing ℓ E n) S).obj
    ((DerivedCategory.singleFunctor _ 0).obj
      (torsionStratumReduction ℓ E
        ((ihom L).obj (𝟙_ (FormalSupportModules (DerivedNakayama.integerRing ℓ E) S))) n))).obj
    ((upperStar (DerivedNakayama.quotientRing ℓ E n) v).mapDerivedCategory.obj
      (torsionStratumSupport ℓ E i j kb vb M n))

/-- Both torsion stratum bounds, including classical cohomology in clause (1).
Source: latest blueprint, sk-lem-uniform-constructible-ext-torsion, clauses (1)--(2);
Stacks Tags 099Y, 09AF, 09A6 (blueprint: det-uniform-constructible-ext-torsion).

Proof: A = O_E / π^n is finite and killed by ℓ^n, since ℓ is in the maximal ideal
(π). In local finite free bases, lattice reduction and dual reduction are finite
locally free A-modules. Standing schemes are Noetherian, hence all maps used for
comparison are qcqs. Their ringed module categories are Grothendieck abelian with
enough injectives. Exact coefficient forgetting, and derived pushforward composition,
identify their derived cohomology bounds with the underlying abelian bounds.
By Tag 099Y the reduced target lattice descends to the etale site; Tags 09AF and
09A6 make open extension by zero and closed direct image commute with comparison.
Thus N = k_*v_!(M/π^n) and j^*N are classical. Tag 09A6 identifies Rj_*j^*N with
its etale counterpart, with classical cohomology, zero in negative degrees and above
c = cd_ℓ(j). The formal support fibre formula gives RΓ_Z N = i^*fib(N → Rj_*j^*N).
The long exact cohomology sequence places this fibre in [0,c+1]. Kernels, cokernels
and inverse image preserve etale origin, proving every part of (1).
For (2), the reduced lattice dual is finite locally free, so tensor is exact and is
computed termwise, as in det-formal-closed-support-ii-limits. Exact inverse image
and this tensor preserve the window [0,c+1] and classical ℓ-power torsion cohomology.
Tensor descent follows locally from a finite A-presentation and exact comparison;
the pure-tensor identifications agree on overlaps. If c or d = cd_ℓ(S) is infinite,
the second assertion is vacuous. Otherwise the bounded hypercohomology spectral
sequence E₂^{p,v} = H^p(S,H^v(G)) converges with finite abutment filtrations. Its
terms vanish unless p ≤ d and 0 ≤ v ≤ c+1. Every term of total degree q > c+d+1
vanishes, so the finite abutment filtration has zero graded pieces and H^q RΓ(S,G)
is zero. Empty schemes, empty strata, and zero-rank lattices are included. -/
theorem uniformConstructibleExtTorsion
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hpℓ : p ≠ ℓ)
    (S Z V X T B : Over (Spec (.of k)))
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    (v : S ⟶ Z) (i : Z ⟶ X) (j : V ⟶ X) (kb : B ⟶ X) (vb : T ⟶ B)
    [IsOpenImmersion v.left] [IsClosedImmersion i.left] [IsOpenImmersion j.left]
    [IsClosedImmersion kb.left] [IsOpenImmersion vb.left]
    (_hij : Set.range i.left.base = (Set.range j.left.base)ᶜ)
    (L₀ : FormalSupportModules (DerivedNakayama.integerRing ℓ E) S.left)
    (M₀ : FormalSupportModules (DerivedNakayama.integerRing ℓ E) T.left)
    (_hL₀ : IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E) L₀)
    (_hM₀ : IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E) M₀)
    (n : ℕ) (_hn : 1 ≤ n) :
    ((∀ q : ℤ, q < 0 ∨ torsionStratumRelativeDimension ℓ k j + 1 <
        (q.toNat : WithTop ℕ) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        (torsionStratumSupport ℓ E i.left j.left kb.left vb.left M₀ n))) ∧
      (∀ q : ℤ, IsClassicalAbelian
        ((DerivedCategory.homologyFunctor _ q).obj
          (torsionStratumSupport ℓ E i.left j.left kb.left vb.left M₀ n)).X)) ∧
    (∀ q : ℤ, torsionStratumRelativeDimension ℓ k j + torsionStratumDimension ℓ k S + 1 <
        (q.toNat : WithTop ℕ) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((formalClosedSupportSections
          (DerivedNakayama.quotientRing ℓ E n) S.left).rightDerivedFunctor.obj
            (torsionStratumTwist ℓ E v.left i.left j.left kb.left vb.left L₀ M₀ n)))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
