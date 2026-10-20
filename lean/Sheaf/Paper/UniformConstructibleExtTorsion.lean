/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.Paper.FormalClosedSupport
public import Sheaf.AlgebraicGeometry.CohomologicalDimension
public import Sheaf.Paper.DerivedNakayamaResolution
public import Sheaf.Paper.CoefficientHeartCommonStratification
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.Paper.ProEtaleLisseOrigin
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Sheaf.AlgebraicGeometry.IntegralConstantCompletion
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.Paper.FormalClosedSupportII

/-!
# The torsion stratum bound

Source: blueprint main-20261015, sec-six-functors-basics,
sk-lem-uniform-constructible-ext/sk-lem-uniform-constructible-ext-torsion.md
(blueprint: det-uniform-constructible-ext-torsion).
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

/-- Commutativity of the existing finite quotient coefficient ring.
Source: the torsion stratum bound, coefficient A = O_E/π^n
(blueprint: det-uniform-constructible-ext-torsion). -/
instance torsionStratum_quotientComm (n : ℕ) :
    IsCommMonObj (DerivedNakayama.quotientRing ℓ E n) :=
  letI := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  Profinite.isCommMonObj_continuousCoefficientRingObj _

/-- The actual ordinary reduction M/π^n, by scalar extension along the quotient map.
Source: the torsion stratum bound, opening coefficient reduction
(blueprint: det-uniform-constructible-ext-torsion). -/
def torsionStratumReduction (Y : Scheme.{u}) (n : ℕ) :
    FormalSupportModules (DerivedNakayama.integerRing ℓ E) Y ⥤
      FormalSupportModules (DerivedNakayama.quotientRing ℓ E n) Y :=
  Mod.extendScalars (coefficientMap (DerivedNakayama.reductionRing ℓ E n) Y)

/-- Cohomological dimension with the qcqs structure supplied by the standing setting.
Source: the torsion stratum bound, cd_ℓ(S) (blueprint: det-uniform-constructible-ext-torsion).
-/
def torsionStratumDimension (k : Type u) [Field k]
    (S : Over (Spec (.of k))) [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] : WithTop ℕ :=
  letI := LocallyOfFiniteType.isLocallyNoetherian S.hom
  letI := QuasiCompact.compactSpace_of_compactSpace S.hom
  cohomologicalDimension ℓ (Fact.out : ℓ.Prime) S.left

/-- Relative dimension with the open immersion's qcqs structure derived from the setting.
Source: the torsion stratum bound, cd_ℓ(j) (blueprint: det-uniform-constructible-ext-torsion).
-/
def torsionStratumRelativeDimension (k : Type u) [Field k]
    {V X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
    (j : V ⟶ X) [IsOpenImmersion j.left] : WithTop ℕ :=
  letI := LocallyOfFiniteType.isLocallyNoetherian X.hom
  relativeCohomologicalDimension ℓ (Fact.out : ℓ.Prime) j.left

/-- The support complex RΓ_Z b_!(M₀/π^n), using the given open-closed factorization.
Source: the torsion stratum bound, clause (1)
(blueprint: det-uniform-constructible-ext-torsion). -/
def torsionStratumSupport {Z V X T B : Scheme.{u}}
    (i : Z ⟶ X) (j : V ⟶ X) (kb : B ⟶ X) (vb : T ⟶ B) [IsOpenImmersion vb]
    (M₀ : FormalSupportModules (DerivedNakayama.integerRing ℓ E) T) (n : ℕ) :
    DerivedCategory (FormalSupportModules (DerivedNakayama.quotientRing ℓ E n) Z) :=
  (formalClosedSupport (DerivedNakayama.quotientRing ℓ E n) i j).rightDerivedFunctor.obj
    ((DerivedCategory.singleFunctor _ 0).obj
      ((lowerStar (DerivedNakayama.quotientRing ℓ E n) kb).obj
        ((openImmersionLowerShriek (DerivedNakayama.quotientRing ℓ E n) vb).obj
          ((torsionStratumReduction ℓ E T n).obj M₀))))

/-- The complex (L₀^∨/π^n) ⊗ u^* RΓ_Z b_!(M₀/π^n).
The dual is internal Hom into the actual integral coefficient ring. Derived tensor is
ordinary tensor here because the reduced dual of the lisse lattice is locally finite free.
Source: the torsion stratum bound, clause (2)
(blueprint: det-uniform-constructible-ext-torsion). -/
def torsionStratumTwist {S Z V X T B : Scheme.{u}}
    (u : S ⟶ Z) (i : Z ⟶ X) (j : V ⟶ X) (kb : B ⟶ X) (vb : T ⟶ B)
    [IsOpenImmersion vb]
    (L₀ : FormalSupportModules (DerivedNakayama.integerRing ℓ E) S)
    (M₀ : FormalSupportModules (DerivedNakayama.integerRing ℓ E) T) (n : ℕ) :
    DerivedCategory (FormalSupportModules (DerivedNakayama.quotientRing ℓ E n) S) :=
  ((derivedTensor (DerivedNakayama.quotientRing ℓ E n) S).obj
    ((DerivedCategory.singleFunctor _ 0).obj
      ((torsionStratumReduction ℓ E S n).obj
        ((ihom L₀).obj (𝟙_ (FormalSupportModules (DerivedNakayama.integerRing ℓ E) S)))))).obj
    ((formalSupportPullback (DerivedNakayama.quotientRing ℓ E n) u).mapDerivedCategory.obj
      (torsionStratumSupport ℓ E i j kb vb M₀ n))

/-- The torsion stratum bound, including classicality of all support cohomology sheaves.
Source: blueprint main-20261015, sec-six-functors-basics,
sk-lem-uniform-constructible-ext/sk-lem-uniform-constructible-ext-torsion.md, clauses (1)--(2)
(blueprint: det-uniform-constructible-ext-torsion).

Proof:
1. Set A = O_E/π^n. The coefficient-extension finiteness theorem gives finite A and
ℓ^n A = 0, since ℓ belongs to the uniformizer ideal. The integral constant-coefficient
criterion identifies the pulled-back quotient with the constant A ring. Local bases
identify both lattice reductions, including the dual, with finite free A modules.
2. Finite-type schemes over the field are Noetherian; their opens are quasi-compact.
Thus S, the open complement j and the closed factor kb satisfy the qcqs hypotheses.
The size convention and ringed-site Grothendieck theorem give enough injectives.
3. Forgetting coefficients is exact, as kernels and sheafified cokernels are unchanged.
Derived pushforward composition identifies module-derived direct image and sections with
the underlying abelian-derived operations to which the cd definitions apply.
4. The lisse-origin theorem (Tag 099Y) descends the reduction of M₀ to the etale site.
Open extension comparison (Tag 09AF) and closed direct-image comparison (Tag 09A6)
then make N = kb_* vb_!(M₀/π^n) classical.
5. Direct-image comparison makes Rj_*j^*N classical. A nonnegative injective resolution
and the relative cd definition put it in [0,cd_ℓ(j)]. Formal closed support identifies
RΓ_Z N with i^* fib(N → Rj_*j^*N).
6. Its long exact sequence gives H^0 = ker, H^1 = coker, and H^r = R^(r-1)j_*j^*N
for r ≥ 2, with no negative cohomology. Exact fully faithful etale comparison preserves
these kernels and cokernels, so they are classical. Exact i^* preserves classicality
and the bound [0,cd_ℓ(j)+1]. Infinite upper endpoints impose no upper vanishing.
7. The reduced dual is locally finite free. The finite-free tensor clause of formal
closed support and exact u^* preserve this interval. Lisse-origin and exact comparison,
using a finite presentation for each finite constant module, preserve classicality
under this tensor. The resulting cohomology is killed by ℓ^n.
8. The truncation hypercohomology spectral sequence has
E₂^(p,v) = H^p(S,H^v(G)) and a finite exhaustive separated filtration in each degree.
The absolute cd definition kills p > cd_ℓ(S), while step 7 kills v outside
[0,cd_ℓ(j)+1]. For q > cd_ℓ(j)+cd_ℓ(S)+1 every term on the total-q diagonal is zero,
so every abutment graded piece, and hence the abutment, vanishes. If either dimension
is infinite, no integer exceeds this endpoint and the assertion is vacuous. -/
theorem uniformConstructibleExtTorsion
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (S Z V X T B : Over (Spec (.of k)))
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    (u : S ⟶ Z) (i : Z ⟶ X) (j : V ⟶ X) (kb : B ⟶ X) (vb : T ⟶ B)
    [IsOpenImmersion u.left] [IsClosedImmersion i.left] [IsOpenImmersion j.left]
    [IsClosedImmersion kb.left] [IsOpenImmersion vb.left]
    (hij : Set.range i.left.base = (Set.range j.left.base)ᶜ)
    (L₀ : FormalSupportModules (DerivedNakayama.integerRing ℓ E) S.left)
    (M₀ : FormalSupportModules (DerivedNakayama.integerRing ℓ E) T.left)
    (hL₀ : IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E) L₀)
    (hM₀ : IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E) M₀)
    (n : ℕ) (hn : 1 ≤ n) :
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
        ((formalClosedSupportSections (DerivedNakayama.quotientRing ℓ E n)
            S.left).rightDerivedFunctor.obj
          (torsionStratumTwist ℓ E u.left i.left j.left kb.left vb.left L₀ M₀ n)))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
