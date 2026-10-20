/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.IntegralScalarExtension

import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Paper.NormalizedDVRTower
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Paper.IntegralScalarExtensionWellDefined
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts

import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Paper.FiniteFieldSheafScalarExtension
import Sheaf.Paper.IntegralScalarExtensionUniverses
import Sheaf.Paper.ProEtaleConstructibleSheaf
/-!
# Integral scalar extension preserves intrinsic bounded constructibility

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace WeilConjectures

/-- Completed integral scalar extension preserves the intrinsic bounded constructible
predicate over arbitrary schemes.
Source: blueprint order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible).
Proof: choose a K-flat representative of the input and use the normalized quotient
filtration of the finite extension. The residue-field layer is a finite direct sum,
so its constructible cohomology and support interval are preserved. Induction through
the powers of the target uniformizer gives the same interval at every finite level.
The normalized tower effectivity comparison identifies these levels with the reductions
of the completed scalar extension, proving derived completeness and constructibility.
The ambient extension is additive and therefore restricts to the full subcategories.

Complete proof plan from the DAG:
1. Write $R=\mathcal O_E$, $S=\mathcal O_L$, $k_E=R/(\varpi_E)$ and $k_L=S/(\varpi_L)$, with
completed coefficient sheaf $\widehat R_Y$. By [lem-weil-l-adic-extension-integers-dvr] the
residue fields are finite and both valuation rings are DVRs. The maps of
[def-weil-integral-scalar-extension] induce $k_E\to k_L$: $\varpi_E\in\varpi_L S$. This is a
unital map of fields, hence injective. Since $k_L$ is a finite set, successively adjoining a
vector outside the span of the vectors already chosen terminates and gives a finite $k_E$-basis,
say of length $d$. By [def-weil-derived-complete-integral-detailed] choose $r\le s$ bounding the
cohomology of all reductions of $K$, in particular $K_1=K\otimes^L_R k_E$; its cohomology sheaves
are constructible. Only this first reduction and its bound will be used in the finite-level
argument.
2. Choose one K-flat resolution $P\to K$ with flat terms as in
[def-weil-integral-scalar-extension]. For $m\ge1$ put $B_m=S/(\varpi_L^m)$ and
$M_m=P\otimes_{\widehat R_Y}(B_m)_Y$, with the strict quotient transition maps. By
[lem-pur-derived-change-of-rings] these complexes compute $K\otimes^L_R B_m$. By
[lem-pur-kflat-change-of-rings], $M_m$ is K-flat with flat terms over $(B_m)_Y$. Consequently, for
$m\ge n$, derived reduction of $M_m$ to $B_n$ is computed by its ordinary tensor, and the map
$$(P\otimes_{\widehat R_Y}(B_m)_Y)\otimes_{(B_m)_Y}(B_n)_Y\longrightarrow P\otimes_{\widehat
R_Y}(B_n)_Y$$ is an isomorphism of complexes. Its local tensor formula is $(p\otimes b)\otimes
c\mapsto p\otimes bc$, with inverse $p\otimes c\mapsto(p\otimes1)\otimes c$; balancing makes the
maps inverse. The maps commute with differentials, and for $m\ge n\ge a$ both composites send
$(p\otimes b)\otimes c\otimes z$ to $p\otimes bcz$. Thus the adjoints of the specified transition
maps are these isomorphisms and satisfy the quotient cocycle. The strict system is a normalized
DVR tower in the sense of [def-coef-normalized-dvr-tower]; this establishes normalization rather
than assuming it.
3. First treat the common layer $Q=P\otimes_{\widehat R_Y}(k_L)_Y$. Put $P_1=P\otimes_{\widehat
R_Y}(k_E)_Y$, representing $K_1$. By [lem-pur-kflat-change-of-rings], $P_1$ is K-flat over
$(k_E)_Y$, so $P_1\otimes_{(k_E)_Y}(k_L)_Y$ computes $K_1\otimes^L_{k_E} k_L$. The coefficient map
$\widehat R_Y\to(k_L)_Y$ factors through $(k_E)_Y$ by the residue map of step 1. The balanced maps
$(p\otimes a)\otimes b\mapsto p\otimes ab$ and $p\otimes b\mapsto(p\otimes1)\otimes b$ are inverse
chain maps identifying this complex with $Q$. The chosen $k_E$-basis identifies $(k_L)_Y$ with
$(k_E)_Y^{\oplus d}$, so tensoring with it is a finite direct sum of the identity functor. It is
exact, and $\mathcal H^i(Q)=\mathcal H^i(K_1)\otimes_{k_E}k_L$; this also follows by computing
cycles and boundaries in the finite direct sum. For the finitely many degrees $r\le i\le s$, take
a common finite refinement of their constructible stratifications: its members are intersections
of the locally closed constructible members, so remain locally closed constructible and partition
$Y$. Pullback to such a stratum is exact and commutes with constants and tensor, by
[def-weil-proetale-inverse-image] and [lem-weil-pbc-left-exact-site-inverse-image-tensor]. On a
cover trivializing $\mathcal H^i(K_1)$ to the constant sheaf of a finite $k_E$-module $V$, the
displayed cohomology of $Q$ is the constant sheaf of $V\otimes_{k_E}k_L$, with its actual
$k_L$-action. For clarity, inverse image takes each constant coefficient ring to the same constant
ring: the constant set sheaf is the copower of the terminal sheaf indexed by the ring, and the
cited inverse-image theorem preserves both terminal objects and colimits; addition and
multiplication are transported because it preserves finite products. Thus module pullback here is
the exact inverse image, not tensor along an unknown ring comparison. The constant tensor
identification is induced by $v\otimes c\mapsto v\otimes c$ in the sheafified tensor presentation.
Exact sheafification [lem-weil-pbc-site-module-presheaf-sheafification-exact] justifies the
constant tensor and cohomology calculation. This module is finite, as a quotient of the finite set
$V\otimes_{k_E}k_E^{\oplus d}\cong V^{\oplus d}$. Therefore $Q$ has constructible $k_L$-cohomology
and support in $[r,s]$. For each $m$, regard $Q$ as a $(B_m)_Y$-complex via $B_m\to k_L$; the same
constant models show constructibility as $B_m$-modules, with the same support.
4. Fix $m$. Filter the $B_m$-module $B_m$ by the ideals $J_j=\varpi_L^j S/\varpi_L^m S$ for $0\le
j\le m$. Thus $J_0=B_m$, $J_m=0$, and multiplication by $\varpi_L^j$ induces a $B_m$-linear
isomorphism $k_L\cong J_j/J_{j+1}$ for $j<m$. It is surjective by the definition of $J_j$; its
kernel is $(\varpi_L)$ since $S$ is a domain and $\varpi_L^m S\subseteq\varpi_L^{j+1}S$, so
cancellation of $\varpi_L^j$ reduces the kernel assertion to membership in $\varpi_L S$
[lem-weil-l-adic-extension-integers-dvr]. In particular each $J_j/J_{j+1}$ is a finite set.
Descending induction using the fibers of $J_j\to J_j/J_{j+1}$ (each a coset of $J_{j+1}$) shows
that $J_j$ is finite, starting with $J_m=0$. Thus $B_m=J_0$ is indeed a finite commutative ring,
as required for the constructible-subcategory theorem below. Exact constant sheafification
[lem-weil-pbc-site-module-presheaf-sheafification-exact] gives short exact coefficient sheaf
sequences $0\to(J_{j+1})_Y\to(J_j)_Y\to(k_L)_Y\to0$. They are sequences of $\widehat R_Y$-modules
as well, through the compatible coefficient maps. Because each $P^q$ is flat, tensoring produces
degreewise short exact sequences of $B_m$-complexes $$0\to P\otimes_{\widehat R_Y}(J_{j+1})_Y\to
P\otimes_{\widehat R_Y}(J_j)_Y\to Q\to0.$$ They yield distinguished triangles by
[lem-weil-pbc-complex-ses-triangle]. Descending induction from $j=m$ now proves that every middle
complex has constructible cohomology and support in $[r,s]$: the base is the zero complex; the
induction step uses the constructible layer $Q$ from step 3 and extension closure
[lem-weil-proetale-dbc-triangulated] for the finite ring $B_m$. For a degree $i$ outside $[r,s]$,
the two outer cohomology objects vanish, so the middle one vanishes by
[lem-sf-derived-homology-long-exact]. At $j=0$ this complex is $M_m$. The interval never changes
during the induction and is independent of $m$; no flatness of $B_m$ over $A_{E,m}$, no finite Tor
hypothesis and no Noetherian hypothesis on $Y$ were used.
5. Let $N=K\otimes_R S$ be the object defined by [def-weil-integral-scalar-extension]. It is the
fixed cone $\operatorname{Cone}(1-s)[-1]$ of the strict tower $\operatorname{Res}^L_mM_m$, and is
a derived limit of that tower by [lem-weil-integral-scalar-extension-well-defined]. Step 2
verified precisely the normalized-tower hypothesis of [lem-coef-normalized-dvr-effectivity], with
the DVR $S$ and quotient rings $B_m=A_{L,m}$. Apply that theorem to obtain compatible isomorphisms
$N\otimes^L_S B_m\cong M_m$ and derived completeness of $N$. This is the same derived limit as the
normalized-tower theorem: the strict tower theorem
[lem-weil-pbc-ringed-strict-tower-homotopy-limit] computes total derived inverse limit by its Roos
triangle. Countable products of completed-coefficient module sheaves are exact by
[lem-weil-proetale-countable-products-exact], so [lem-weil-derived-limit-products-core] identifies
the derived products in that triangle with the termwise products used here. To make the comparison
explicit, take the strict tower resolution $X_\bullet\to I_\bullet$ used by the strict-tower
theorem, where $X_m=\operatorname{Res}^L_mM_m$. Its maps are termwise quasi-isomorphisms and
commute with the transitions. Exact countable products imply that $\prod_mX_m\to\prod_mI_m$ is a
quasi-isomorphism: cohomology of these products is the product of the cohomologies by
[lem-weil-derived-limit-products-core]. The commuting square with $1-s$ therefore induces a
quasi-isomorphism of the shifted mapping-cone complexes. On each evaluation it commutes with
projection to the corresponding tower member, since the square came from a strict tower map. The
Roos model of the strict-tower theorem is consequently identified with the fixed cone defining
$N$, with its evaluations. This supplies the comparison needed for the canonical counit
isomorphisms of the effectivity theorem, without asserting uniqueness of arbitrary cone maps. The
finite-level statement of step 4 therefore supplies constructibility and the single interval
$[r,s]$ for all derived reductions of $N$. These are exactly the conditions of
[def-weil-derived-complete-integral-detailed] for $L$, so $N\in D^b_c(Y,S)$. Finally the ambient
functor is $R$-linear by clause 3 of [lem-weil-integral-scalar-extension-well-defined].
Restricting its objects and morphisms to the full subcategories just proved preserved leaves the
equality $T(af)=aT(f)$ intact, and gives the asserted $R$-linear functor.
-/
theorem sfIntegralScalarExtension_constructible
    (p l : ℕ) [Fact l.Prime] (_hl : l ≠ p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (Y : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (scalarReductionSource.{u, u} l E Y))
    (hK : sfIntegralConstructible l E Y K) :
    sfIntegralConstructible l L Y
      ((integralScalarExtension l E L ι Y).obj K) := by
  sorry

/-- The completed scalar extension restricted to intrinsic bounded constructible
objects. Its object map is the ambient extension and its morphism map is inherited.
Source: blueprint order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible).
-/
noncomputable def sfConstructibleIntegralScalarExtension
    (p l : ℕ) [Fact l.Prime] (_hl : l ≠ p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (Y : AlgebraicGeometry.Scheme.{u}) :
    sfIntegralConstructibleCategory l E Y ⥤
      sfIntegralConstructibleCategory l L Y :=
  (sfIntegralConstructible l L Y).lift
    ((sfIntegralConstructible l E Y).ι ⋙ integralScalarExtension l E L ι Y)
    (fun X ↦ sfIntegralScalarExtension_constructible p l _hl E L ι Y X.obj X.property)

/-- The restricted functor is linear for the integral coefficient action.
Source: blueprint order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible).
Proof: the ambient completed extension is linear on morphisms; the full-subcategory
restriction preserves the same equality.
-/
theorem sfConstructibleIntegralScalarExtension_smul
    (p l : ℕ) [Fact l.Prime] (_hl : l ≠ p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (Y : AlgebraicGeometry.Scheme.{u})
    (K K' : sfIntegralConstructibleCategory l E Y)
    (f : K ⟶ K') (a : Padic.coefficientExtensionIntegers l E) :
    (integralScalarExtension l E L ι Y).map
        ((integralScalarDerivedAction l E Y a).app K.obj ≫ f.hom) =
      (integralScalarDerivedAction l L Y
          (integralScalarIntegerInclusion l E L ι a)).app
          ((sfConstructibleIntegralScalarExtension p l _hl E L ι Y).obj K).obj ≫
        ((sfConstructibleIntegralScalarExtension p l _hl E L ι Y).map f).hom := by
  exact (integralScalarExtensionWellDefined l E L ι Y).2.choose_spec.choose_spec.2.2.2.2
    a K.obj K'.obj f.hom

end WeilConjectures
