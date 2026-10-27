/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Compactification.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Compact-support finiteness over arbitrary finite rings

Source: Stacks Project, More on Etale Cohomology, Tags 0GL0 and 0G2A, clause (3),
with the chosen-compactification convention of section-derived-lower-shriek-compactification
(blueprint: lem-fd-finite-ring-compact-support-finiteness).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Compact support along a supplied compactification preserves bounded constructibility
and admits a uniform nonnegative cohomological bound over any finite commutative ring.
Neither endpoint need be separated over the field, and no Tor-amplitude or invertibility
hypothesis is imposed.
Source: Stacks Project, Tags 0GL0 and 0G2A (3), and the compactification convention in
section-derived-lower-shriek-compactification
(blueprint: lem-fd-finite-ring-compact-support-finiteness).

Proof plan:

1. First check the geometric hypotheses needed below. The field $k$ is Noetherian because its only
ideals are $(0)$ and $(1)$, so $\operatorname{Spec}k$ is Noetherian. Apply
[lem-weil-pbc-finite-type-over-noetherian] successively to $Y\to\operatorname{Spec}k$, $f:X\to Y$,
and $q:\overline X\to Y$; $q$ is of finite type by the definition of properness
[def-weil-proper-morphism]. Thus $Y,X,\overline X$ are Noetherian, hence quasi-compact and, by
[lem-weil-pbc-locally-noetherian-quasi-separated], quasi-separated. The morphisms $f$ and $q$ are
locally of finite presentation by [pqf-lem-lft-fp-locnoeth]. They are quasi-compact by finite type
and quasi-separated by [lem-weil-pbc-qcqs-morphism-permanence](1), since their sources are
quasi-separated. Thus $f$ is of finite presentation. Also $j$ is quasi-compact by that same
permanence lemma, since $X$ is quasi-compact and $\overline X$ is quasi-separated. These arguments
require no separatedness over $k$.

2. The open immersion $j$ identifies $X$ with an open subscheme [def-weil-open-immersion].
Therefore $X\times_{\overline X}X\cong X$ and its diagonal is an isomorphism, hence a closed
immersion. It follows directly from [def-weil-proper-morphism] that $j$ is separated. The proper
map $q$ is separated by the same definition. By the composition clause (e) of
[lem-weil-pbc-proper-fp-permanence], $f=qj$ is separated.

3. Extension by zero is exact by [lem-weil-pbc-extension-by-zero-exact], and exact functors
commute with cohomology by [lem-sp-exact-functor-preserves-homology](c). Hence, for $L=D(j_!)M$,
one has $\mathcal H^r(L)=j_!\mathcal H^r(M)$; in particular $L$ is bounded below and has the same
cohomological interval as $M$. To compare the two derived conventions, the module sheaf categories
are Grothendieck abelian by [lem-weil-pbc-module-sheaves-grothendieck-abelian], have enough
injectives by [lem-weil-pbc-module-sheaves-enough-injectives], and admit K-injective resolutions
by [prop-weil-pbc-kinjective-resolutions-exist]. The functor $q_*$ is additive and left exact by
[lem-weil-pbc-module-direct-image-left-exact]. Therefore
[src-right-derived-functor-plus-compatibility], applied to $q_*$, identifies its bounded-below
derived functor on $L$ with its unbounded total right derived functor on $L$. All subsequent
bounded-below computations consequently compute the functor $Rq_*D(j_!)$ specified in the
statement.

4. By [def-weil-pbc-constructible-complexes], $M$ is bounded below with constructible cohomology.
Apply [lem-weil-pbc-etale-compactification-constructibility] to $f$ and the supplied
compactification $(j,q)$. Its hypotheses are verified in steps 1 and 2: both endpoints are
quasi-compact and quasi-separated, $f$ is separated and finitely presented, and $j$ is
quasi-compact. Its coefficient hypothesis is precisely that $\Lambda$ is a finite commutative
ring. It yields constructibility of every $\mathcal H^r(Rq_*j_!M)$. By step 3 this is the required
unbounded-derived compact-support output.

5. Since $q$ is proper, it is of finite type [def-weil-proper-morphism], and $Y$ is quasi-compact
by step 1. Thus [lem-fin-finite-type-fibre-dimension-bound] supplies $d\geq0$ bounding the
dimensions of every scheme-theoretic fibre of $q$. Fix this $d$ once and for all, and put $N=2d$.
This choice depends on the supplied compactification and not on $M$ or its cohomological interval.

6. Let $F$ be any $\Lambda$-module sheaf on $\overline X_{\mathrm{et}}$. The finiteness of
$\Lambda$ gives a positive integer $m$ with $m1_\Lambda=0$, so $mF=0$ and its underlying abelian
sheaf $U(F)$ is torsion. Apply [lem-kun-proper-torsion-cd-bound] to $q$ and $U(F)$ to obtain $R^p
q_*U(F)=0$ for $p>2d$. By [lem-sbc-higher-direct-image-forget-comparison], this is the underlying
abelian sheaf of the module higher direct image $R^p q_*F$. A module sheaf with zero underlying
abelian sheaf is zero. Hence $R^p q_*F=0$ for $p>2d$, uniformly for all $F$. This uses no
invertibility of $m$ on any scheme.

7. Suppose $\mathcal H^r(M)=0$ for $r\notin[a,b]$. By step 3, $L=D(j_!)M$ has the same vanishing.
Apply [thm-sp-truncation-e2] to the left exact module direct image $q_*$
[lem-weil-pbc-module-direct-image-left-exact] between the Grothendieck abelian module sheaf
categories [lem-weil-pbc-module-sheaves-grothendieck-abelian]. It gives a spectral sequence
$E_2^{p,r}=R^p q_*\mathcal H^r(L)\Longrightarrow\mathcal H^{p+r}(Rq_*L)$, with $E_2^{p,r}=0$ for
$p<0$ and a finite exhaustive separated abutment filtration in every total degree. Step 6 gives
$E_2^{p,r}=0$ for $p>2d$, and the hypothesis gives zero for $r\notin[a,b]$. Thus a nonzero term
must have $a\leq p+r\leq b+2d$. Outside this interval every associated graded of the finite
filtration is zero, so the abutment is zero. By step 3 this proves $\mathcal H^i(Rf_!^cM)=0$ for
$i\notin[a,b+N]$, with the fixed $N=2d\geq0$.

8. For each $M\in D^b_c(X,\Lambda)$ choose a finite cohomological interval $[a,b]$ using
[def-weil-pbc-constructible-complexes]. Step 7 bounds the output in $[a,b+N]$, and step 4 makes
each of its cohomology sheaves constructible. These are exactly the two conditions in that
definition for $Rf_!^cM\in D^b_c(Y,\Lambda)$. The same $N$ works for every input and every
proposed interval. The zero ring and empty schemes cause no exception: their module complexes are
zero and the bound still holds.
-/
theorem finiteRingCompactSupportFiniteness
    (k : Type u) [Field k] {X Y : Scheme.{u}} [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    IsSeparated f ∧
    (∀ M : DerivedCategoryModule Λ X, DerivedCategory.isBoundedConstructible Λ X M →
      DerivedCategory.isBoundedConstructible Λ Y
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj M)) ∧
    ∃ N : ℕ, ∀ M : DerivedCategoryModule Λ X,
      DerivedCategory.isBoundedConstructible Λ X M → ∀ a b : ℤ,
      (∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((_root_.DerivedCategory.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) i).obj M)) →
      ∀ i : ℤ, (i < a ∨ b + (N : ℤ) < i) →
        IsZero ((_root_.DerivedCategory.homologyFunctor
          (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) i).obj
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj M)) := by
  sorry

end AlgebraicGeometry.Etale
