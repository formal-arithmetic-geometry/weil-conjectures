/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient
public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import Sheaf.AlgebraicGeometry.ProEtalePullbackLocallyConstant
import Sheaf.AlgebraicGeometry.ProEtaleClosedSupportTriangle
import Sheaf.AlgebraicGeometry.ProEtaleModulePullbackComposition
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Finite-field closed-support constructibility

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.7.11,
closed-immersion support-triangle proof, specialized to R = A and m = 0
(blueprint: lem-sfb-finite-field-closed-support).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The ambient closed exceptional inverse image preserves bounded constructible
cohomology for finite-field coefficients prime to the positive characteristic.
The complementary open is the actual open subscheme with underlying set
`(Set.range g)ᶜ`. The ordinary right derived functor is precisely the one in
`sfIntrinsicClosedAmbientAdjunction`; no completed or restricted category is used.
Source: Bhatt--Scholze, Lemma 6.7.11, closed-immersion proof, R = A and m = 0
(blueprint: lem-sfb-finite-field-closed-support).

Proof (the DAG proof plan, with its dependencies):
1. Let $j:U=T\setminus g(Z)\hookrightarrow T$ be the complementary open immersion. The spectrum of
the field $k$ is Noetherian, so [lem-weil-pbc-finite-type-over-noetherian] makes $T$ Noetherian.
By [lem-weil-pbc-noetherian-open-subscheme-noetherian], $U$ is Noetherian and every open subset of
$T$ is quasi-compact. Hence $j$ is quasi-compact: the inverse image of an affine open of $T$ is an
open subset of this Noetherian space. By [lem-weil-pbc-immersion-base-change-lft] it is locally of
finite type, hence finite type by [def-weil-finite-type-morphism]. Applying
[lem-sfb-finite-type-composition-base-change] to $U\to T\to\operatorname{Spec}k$ makes $U$ finite
type over $k$. Thus the support-triangle theorem applies to $(g,j)$, and the finite-field
direct-image theorem applies to $j$.

2. For $h=j$ or $h=g$, [prop-weil-pbc-proetale-constant-ring-map] identifies $h^{-1}A_T$ with the
constant ring on its source. In [def-weil-proetale-inverse-image], extension along this
isomorphism merely identifies scalar actions. The underlying abelian inverse image is exact by
[lem-weil-pbc-site-pullback-abelian-exact]; kernels and cokernels of module sheaves have their
induced scalar actions, so $h^*$ is exact as well. Therefore
[lem-weil-pbc-exact-functor-complex-cohomology] gives $\mathcal H^q(h^*K)\cong h^*\mathcal H^q(K)$
for every complex $K$ and integer $q$, with $h^*$ applied termwise on the ordinary derived
category. In particular, pullback preserves the cohomological vanishing interval.

3. The same pullbacks preserve constructible cohomology. For a finite stratification $T=\coprod
T_a$ as in [def-weil-proetale-constructible-sheaf], put $S_a=S\times_TT_a$ ($S$ the source of
$h$): its projection $i'_a$ to $S$ is an immersion by [lem-weil-pbc-immersion-base-change-lft],
and $h\circ i'_a=i_a\circ h_a$. The $S_a$ partition $S$ into finitely many locally closed subsets,
constructible by [lem-pur-scheme-constructible-preimage]. By
[lem-pur-proetale-module-pullback-composition], $i_a'^*h^*F\cong h_a^*i_a^*F$, and
[lem-exc-proetale-pullback-locally-constant] gives this a covering with the same finite $A$-module
models, hence finite geometric stalks. Finite $A$-modules are finite-dimensional. With step 2,
$h^*\mathcal B_A(T)\subseteq\mathcal B_A(S)$. Empty strata are discarded.

4. Fix $K\in\mathcal B_A(T)$. Step 3 gives $j^*K\in\mathcal B_A(U)$. Apply
[lem-sfb-finite-field-proetale-direct-image] to the finite-type map $j$ of step 1:
$Rj_*j^*K\in\mathcal B_A(T)$. The field and coefficient hypotheses are exactly the ones in this
item; that theorem does not assume a cohomological-dimension bound on $k$.

5. By [lem-exc-proetale-support-triangle], in the ambient ordinary derived category there is a
distinguished triangle $C\to K\to Rj_*j^*K\to C[1]$, where $C=g_*Rg^!K$. Its exceptional inverse
image is the right adjoint of the same closed direct image as in the statement; uniqueness of
right adjoints identifies any choices. By [lem-weil-proetale-dbc-triangulated], $\mathcal B_A(T)$
is invariant under isomorphisms and shifts and is closed under triangle extensions. Rotate the
triangle to $Rj_*j^*K[-1]\to C\to K\to Rj_*j^*K$. Its outer vertices lie in $\mathcal B_A(T)$ by
step 4 and the hypothesis on $K$, so $C\in\mathcal B_A(T)$.

6. Apply $g^*$ to $C$. Step 3 gives $g^*C\in\mathcal B_A(Z)$. The counit $g^*g_*M\to M$ is an
isomorphism for every module sheaf $M$ by [lem-exc-proetale-closed-fully-faithful], and $g_*$ is
exact by [lem-exc-proetale-closed-exact], since its complementary open immersion is quasi-compact
by step 1. Both functors therefore descend termwise to ordinary derived categories; applying the
sheaf counit degree by degree to any representative of $Rg^!K$ yields $g^*g_*Rg^!K\cong Rg^!K$.
Consequently $Rg^!K\in\mathcal B_A(Z)$ by the isomorphism invariance in
[lem-weil-proetale-dbc-triangulated]. When $Z$ is empty the value is zero, and when $Z=T$ the same
counit identifies the value with $K$; these include the boundary cases. No step uses finiteness of
the absolute cohomological dimension of $k$.
-/
theorem finiteFieldClosedSupport_bounded_constructible
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (_hp : 0 < p) (_hpℓ : p ≠ ℓ)
    (A : Type u) [Field A] [Finite A] [CharP A ℓ]
    {Z T : Scheme.{u}} [Z.Over (Spec (.of k))] [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    (g : Z ⟶ T) [IsClosedImmersion g] [g.IsOver (Spec (.of k))]
    (K : proEtaleDerivedCategory T A)
    (_hK : Set.Finite {q : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T A)) q).obj K)} ∧
      ∀ q : ℤ, IsConstructibleProEtaleModuleSheaf T A
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules T (proEtaleConstantRing T A)) q).obj K)) :
    Set.Finite {q : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules Z (proEtaleConstantRing Z A)) q).obj
        ((sfIntrinsicClosedUpperShriek g
          (Scheme.Opens.ι
            (⟨(Set.range g)ᶜ, g.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : T.Opens))
          A).rightDerivedFunctor.obj K))} ∧
    ∀ q : ℤ, IsConstructibleProEtaleModuleSheaf Z A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Z (proEtaleConstantRing Z A)) q).obj
          ((sfIntrinsicClosedUpperShriek g
            (Scheme.Opens.ι
            (⟨(Set.range g)ᶜ, g.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : T.Opens))
            A).rightDerivedFunctor.obj K)) := by
  sorry

end AlgebraicGeometry.Scheme
