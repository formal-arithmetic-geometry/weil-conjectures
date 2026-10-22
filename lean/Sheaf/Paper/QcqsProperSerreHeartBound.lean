/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.AlgebraicGeometry.DimensionExtension
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.AlgebraicGeometry.BoundedComplexDirectImagePresheaf
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.AlgebraicGeometry.ProEtale.WeaklyContractibleBasis

/-!
# A uniform proper bound on the constructible weak Serre coproduct heart

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md, (2), first paragraph
(blueprint: lem-sfb-qcqs-proper-serre-heart-bound).

The coefficient hypothesis spells out exactly the six norm-topological coefficient families.
The closure uses finite constant scalar models and coproducts indexed in `Type (u + 1)`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Proper direct image is uniformly bounded above on the weak Serre coproduct closure
of finite constant-model constructible heart objects over a qcqs base.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md, (2), first paragraph
(blueprint: lem-sfb-qcqs-proper-serre-heart-bound).

Proof plan (the five steps of the DAG node):
1. Since $q$ is proper it is quasi-compact. Take a finite affine open cover of the quasi-compact
$S$; each inverse image is quasi-compact by the finite-type definition, so their finite union $Y$
is quasi-compact. Properness of $f$ makes it finite type. The finite-type fibre-dimension theorem
supplies $e\in\mathbf N$ such that $\dim X_y\leq e$ for every $y\in Y$. Every fibre is finite type
over $\kappa(y)$, and dimension is unchanged under a field extension. Thus the same $e$ bounds
every geometric fibre of $f$ and of every base change of $f$. Fix $d=2e+2\geq0$ once and for all.

2. For any scheme map $a:T\to X$, $a^*$ sends $\mathcal P_X$ into $\mathcal P_T$. Indeed it is
additive exact, so preserves zero, kernels, cokernels and short exact sequences. Its adjunction to
$a_*$ makes it preserve the small coproducts. The constructible-preimage lemma applies: to check
retrocompactness of the inverse image of a retrocompact open, cover any affine source open by
finitely many affine opens mapping into affine target opens; the target open in each of those is a
finite union of principal opens, whose inverse images are principal. Thus inverse images preserve
the required constructible subsets. Pulling back the finite locally closed strata consequently
gives a finite constructible stratification; on the pullback of a scalar-model trivializing cover
the model is still $\Lambda\otimes_{\Lambda(*)}P$ for the very same finitely presented scalar
module $P$, since the pulled-back coefficient map is an isomorphism. Thus it preserves the
specified constructible generators, not merely arbitrary finite presentations. The class of $M$
such that $a^*M\in\mathcal P_T$ therefore has every closure property in the intersection defining
$\mathcal P_X$. Minimality gives the assertion.

3. Fix $M\in\mathcal P_X$ and an affine w-contractible object $W\to Y$ of the small pro-étale
site. Apply the proper closed-fibre rigidity theorem to $f,M,W$. It supplies the reduced
closed-point scheme $C\hookrightarrow W$: $C$ is affine, zero-dimensional and w-contractible with
separably closed residue fields. With $X_C=X\times_YC$ and $a:X_C\to X$ it supplies the actual
isomorphism in $D(\mathbf{Ab})$ $$R\Gamma(X\times_YW,M)\simeq R\Gamma((X_C)_{\mathrm{pro\acute
et}},a^*M).$$ The left side is derived evaluation on the object $X\times_YW$ of the original
$X$-site. Thus no substitution of ordinary geometric stalks for arbitrary pro-étale module objects
is involved.

4. The morphism $h:X_C\to C$ is proper by base-change stability. A geometric fibre of $h$ is the
base extension of the corresponding fibre of $f$, so Step 1 bounds its dimension by $e$. Step 2
gives $a^*M\in\mathcal P_{X_C}$. Apply the absolute profinite-family cohomological-dimension
estimate with this $C,h,e,a^*M$. It gives $H^rR\Gamma((X_C)_{\mathrm{pro\acute et}},a^*M)=0$ for
$r>2e+2=d$. Taking cohomology of the isomorphism of Step 3 gives
$$H^r(X\times_YW,M)=0\qquad(r>d).$$

5. For each $r>d$ consider the abelian presheaf $V\mapsto H^r(X\times_YV,M)$ on
$Y_{\mathrm{pro\acute et}}$. The bounded-below higher-direct-image presheaf theorem identifies its
sheafification with the underlying abelian sheaf of $H^r(Rf_*(M[0]))$. To apply it to the actual
module-object composite, use the exact internal-to-section-module equivalences. An injective
resolution of $M$ in the source module category computes the actual direct image; before and after
scalar restriction its underlying section complex at $V$ is exactly $I^\bullet(X\times_YV)$.
Scalar restriction changes only the action and is exact, so these give the same underlying
cohomology sheaf as the theorem with target coefficient ring $f_*\Lambda_X$. Every $V$ has a
covering by affine w-contractible $W$; on each such $W$ the presheaf is zero by Step 4. Its
sheafification is therefore zero. A module sheaf with zero underlying abelian sheaf is zero. This
proves the required vanishing for every $M\in\mathcal P_X$ with the fixed $d$ of Step 1.
-/
theorem exists_uniform_serreHeart_bound_of_isProper
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj (PadicAlgCl ℓ))))
    {S Y X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (q : Y ⟶ S) [IsProper q] (f : X ⟶ Y) [IsProper f] :
    ∃ d : ℕ, ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X),
      ObjectProperty.weakSerreCoproductClosure.{u + 1}
        (IsConstantModelConstructible Λ X) M →
      ∀ r : ℤ, (d : ℤ) < r →
        IsZero ((DerivedCategory.homologyFunctor _ r).obj
          ((moduleObjectDerivedPushforward Λ f).obj
            ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
