/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedSupport
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact

/-! # Ambient pro-etale adjunction for the actual constant coefficient sheaf

Source: Weil blueprint, smooth purity, order 1859; Stacks Project, Tags 09BM and 09AH
(blueprint: lem-exc-proetale-closed-support).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Closed direct image is exact and its unbounded derived functor is left adjoint to
R i!_0, where i!_0 is the closed inverse image of the kernel of the open adjunction unit.
Exactness makes the displayed derived direct image the direct image applied termwise.
Source: Weil blueprint, order 1859; Stacks Project, Tags 09BM, 09AH and 07A5
(blueprint: lem-exc-proetale-closed-support).

Proof:
1. A Noetherian target makes the complementary open quasi-compact. Apply ringed open-closed
localization to the actual constant coefficient sheaf, identifying its inverse images with
constant coefficients through the canonical constant-section maps. Closed direct image is
exact, fully faithful, and identifies modules on Z with modules vanishing on U.
2. For a map i* M → N the composite with the open adjunction unit is zero by restriction
to U. The kernel universal property factors it uniquely through sections with support.
The supported-category equivalence has inverse i*, giving the sheaf adjunction to i!_0.
3. Choose K-injective resolutions with injective terms among all constant-ring modules.
The sheaf right adjoint preserves K-injectives because closed direct image is exact:
the termwise homotopy adjunction makes maps from acyclic complexes null-homotopic.
4. Compute derived Hom into those resolutions. The termwise adjunction, followed by the
K-injective Hom identification, gives the derived adjunction naturally in both variables.
The total right derived construction is everywhere defined by those same resolutions.
There is no restriction on boundedness, constructibility, or the values of R i!_0.

Complete DAG proof plan:
1. By [lem-weil-pbc-noetherian-open-subscheme-noetherian], $U\cap V$ is quasi-compact for each
affine open $V\subset T$, so $j$ is quasi-compact. The canonical structure maps $i^{-1}A_T\to A_Z$
and $j^{-1}A_T\to A_U$ are isomorphisms by [prop-weil-pbc-proetale-constant-exact], whose
coefficient convention explicitly supplies these maps; hence the ringed coefficient hypotheses of
the essential-image theorem hold. Thus [lem-exc-proetale-closed-exact], [lem-exc-proetale-closed-
fully-faithful], and [lem-exc-proetale-closed-essential-image] give exactness and full
faithfulness of $i_*$, and identify its essential image with the sheaves killed by $j^*$. We make
explicit the open-restriction calculation used below. Under the localized-site identification of
[lem-weil-proetale-weakly-etale-localization], $j^*$ is restriction: in the inverse-image formula
of [def-weil-proetale-inverse-image], for $W\to U$ the indexing category has initial object $W\to
T$ with the identity $W\cong W\times_TU$, so its opposite has a terminal object and the presheaf
inverse image is $N(W)$; this is already a sheaf, with the restricted constant-ring action. By
[def-weil-proetale-module-direct-image], $(j^*j_*G)(W)=G(W\times_TU)=G(W)$, and the counit is this
identity. Consequently $j^*$ of the unit $N\to j_*j^*N$ is an isomorphism, inverse to that counit
by the adjunction triangle identity. Since $j^*$ preserves kernels by [prop-weil-pbc-proetale-
constant-exact], the sheaf $\Gamma_ZN=\ker(N\to j_*j^*N)$ has $j^*\Gamma_ZN=0$.
Dependencies: lem-weil-pbc-noetherian-open-subscheme-noetherian, lem-exc-proetale-closed-exact,
lem-exc-proetale-closed-fully-faithful, lem-exc-proetale-closed-essential-image, lem-weil-
proetale-weakly-etale-localization, def-weil-proetale-inverse-image, def-weil-proetale-module-
direct-image, prop-weil-pbc-proetale-constant-exact.

2. For a sheaf $M$ on $Z$, [lem-exc-proetale-closed-essential-image] gives $j^*i_*M=0$; for
$\Gamma_ZN$ of Step 1 it gives the natural isomorphism $\Gamma_ZN\to i_*i^*\Gamma_ZN$. If
$f:i_*M\to N$, naturality of the open unit $\eta$ gives $\eta_N f=j_*j^*(f)\eta_{i_*M}=0$, because
$j^*i_*M=0$. The kernel property therefore gives a unique factorization through $\Gamma_ZN$.
Composing with its displayed isomorphism and using [lem-exc-proetale-closed-fully-faithful] gives
the natural bijection $\operatorname{Hom}_T(i_*M,N)\cong\operatorname{Hom}_T(i_*M,\Gamma_ZN)\cong
\operatorname{Hom}_Z(M,i^*\Gamma_ZN)=\operatorname{Hom}_Z(M,i^!_0N)$, with the last equality from
[def-exc-proetale-sections-with-support]. Thus $i_*\dashv i^!_0$ on the whole sheaf categories.
These functors are additive: $i_*$ is additive by its sectionwise definition [def-weil-proetale-
module-direct-image], and its right adjoint preserves zero and finite products, hence biproducts
and their diagonal/codiagonal formula for addition.
Dependencies: lem-exc-proetale-closed-essential-image, lem-exc-proetale-closed-fully-faithful,
def-exc-proetale-sections-with-support, def-weil-proetale-module-direct-image.

3. Use the small skeletons in [def-weil-pbc-proetale-site]. The constant coefficient sheaf is a
sheaf of commutative rings, so [prop-pur-kinjective-resolutions-exist] supplies K-injective
resolutions on $T$ and $Z$ for arbitrary unbounded complexes. In [lem-weil-pbc-right-adjoint-
preserves-kinjective] take $\mathcal A=\operatorname{Sh}(T_{\mathrm{proet}},A)$, $\mathcal
B=\operatorname{Sh}(Z_{\mathrm{proet}},A)$, $v=i_*$ and $u=i^!_0$. Step 2 gives $v\dashv u$ and
Step 1 gives exactness of $v$, so $i^!_0$ sends K-injective complexes on $T$ to K-injective
complexes on $Z$. To apply [lem-weil-pbc-kinjective-total-derived], take $F=Q_Z\circ
(i^!_0)^K:K(T)\to D(Z)$, where $Q_Z$ is localization and the superscript $K$ means termwise
application on the homotopy category. This is an exact functor of triangulated categories:
additivity preserves the chain-homotopy equation, shifts and the biproduct differential matrix
defining each cone in [def-weil-abstract-derived-category]. The cited total-derived theorem
constructs $Ri^!_0$ and identifies $Ri^!_0N$ with $Q_Z(i^!_0I)$ whenever $N\to I$ is a K-injective
resolution on $T$.
Dependencies: def-weil-pbc-proetale-site, prop-pur-kinjective-resolutions-exist, lem-weil-pbc-
right-adjoint-preserves-kinjective, lem-weil-pbc-kinjective-total-derived, def-weil-abstract-
derived-category.

4. Exactness of $i_*$ and [lem-sf-exact-functor-derived-triangulated] give its functor on $D(Z)\to
D(T)$ by termwise application (also computing $Ri_*$). Let $K$ be any complex on $Z$, let $N$ be
any complex on $T$, and choose a K-injective resolution $N\to I$. Step 3 makes $i^!_0I$
K-injective and identifies it with $Ri^!_0N$ in $D(Z)$. The homotopy adjunction [lem-weil-pbc-
termwise-adjunction-homotopy] and the two K-injective Hom comparisons [lem-weil-pbc-kinjective-
hom-derived] give $$\operatorname{Hom}_{D(T)}(i_*K,N)\cong\operatorname{Hom}_{K(T)}(i_*K,I)\cong
\operatorname{Hom}_{K(Z)}(K,i^!_0I)\cong\operatorname{Hom}_{D(Z)}(K,Ri^!_0N).$$ The resolution can
be chosen functorially by [prop-pur-kinjective-resolutions-exist]; every displayed comparison is
natural in $K$ and $N$. These bijections therefore exhibit $i_*\dashv Ri^!_0$ on the whole
unbounded derived categories. No bound or constructibility assumption was used.
Dependencies: lem-sf-exact-functor-derived-triangulated, lem-weil-pbc-termwise-adjunction-
homotopy, lem-weil-pbc-kinjective-hom-derived, prop-pur-kinjective-resolutions-exist.
-/
theorem sfIntrinsicClosedAmbientAdjunction
    (A : Type u) [CommRing A] [Finite A]
    {Z U T : Scheme.{u}} [IsNoetherian T]
    (i : Z ⟶ T) [IsClosedImmersion i] (j : U ⟶ T) [IsOpenImmersion j]
    (_hij : IsCompl (Set.range i) (Set.range j)) :
    PreservesFiniteColimits (sfConstantModuleDirectImage i A) ∧
      Nonempty ((sfConstantModuleDirectImage i A).rightDerivedFunctor ⊣
        (sfIntrinsicClosedUpperShriek i j A).rightDerivedFunctor) := by
  sorry

end AlgebraicGeometry.Scheme
