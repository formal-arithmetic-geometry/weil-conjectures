/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.IntegralScalarExtension
public import Sheaf.Paper.IntegralConstructibleLinear

import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.DerivedCompleteIntegralDetailed
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Sheaf.Paper.IntegralScalarExtensionWellDefined
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
/-! # Constructibility under completed integral scalar extension

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible).
-/

@[expose] public section

set_option autoImplicit false

universe d u

open CategoryTheory

namespace WeilConjectures

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

/-- Completed integral extension preserves the actual integral constructible property.
Source: blueprint order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible).
Proof: the strict quotient tower is normalized by the balanced tensor associator.
Its first layer is scalar extension to the finite residue field. Filter each
higher target quotient by powers of its uniformizer, with that residue field
as each layer. Extension closure preserves constructibility and the same
cohomological interval through this finite filtration. Normalized DVR effectivity
identifies all these levels with reductions of the completed extension and gives
its derived completeness. The constant-section balancing identity gives linearity.

Complete DAG proof plan:
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
[lem-pur-kflat-change-of-rings], $M_m$ is K-flat with flat terms over $(B_m)_Y$. Consequently,
for $m\ge n$, derived reduction of $M_m$ to $B_n$ is computed by its ordinary tensor, and the map
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
$(k_E)_Y$, so $P_1\otimes_{(k_E)_Y}(k_L)_Y$ computes $K_1\otimes^L_{k_E} k_L$. The coefficient
map $\widehat R_Y\to(k_L)_Y$ factors through $(k_E)_Y$ by the residue map of step 1. The balanced
maps $(p\otimes a)\otimes b\mapsto p\otimes ab$ and $p\otimes b\mapsto(p\otimes1)\otimes b$ are
inverse chain maps identifying this complex with $Q$. The chosen $k_E$-basis identifies $(k_L)_Y$
with $(k_E)_Y^{\oplus d}$, so tensoring with it is a finite direct sum of the identity functor.
It is exact, and $\mathcal H^i(Q)=\mathcal H^i(K_1)\otimes_{k_E}k_L$; this also follows by
computing cycles and boundaries in the finite direct sum. For the finitely many degrees $r\le
i\le s$, take a common finite refinement of their constructible stratifications: its members are
intersections of the locally closed constructible members, so remain locally closed constructible
and partition $Y$. Pullback to such a stratum is exact and commutes with constants and tensor, by
[def-weil-proetale-inverse-image] and [lem-weil-pbc-left-exact-site-inverse-image-tensor]. On a
cover trivializing $\mathcal H^i(K_1)$ to the constant sheaf of a finite $k_E$-module $V$, the
displayed cohomology of $Q$ is the constant sheaf of $V\otimes_{k_E}k_L$, with its actual
$k_L$-action. For clarity, inverse image takes each constant coefficient ring to the same
constant ring: the constant set sheaf is the copower of the terminal sheaf indexed by the ring,
and the cited inverse-image theorem preserves both terminal objects and colimits; addition and
multiplication are transported because it preserves finite products. Thus module pullback here is
the exact inverse image, not tensor along an unknown ring comparison. The constant tensor
identification is induced by $v\otimes c\mapsto v\otimes c$ in the sheafified tensor
presentation. Exact sheafification [lem-weil-pbc-site-module-presheaf-sheafification-exact]
justifies the constant tensor and cohomology calculation. This module is finite, as a quotient of
the finite set $V\otimes_{k_E}k_E^{\oplus d}\cong V^{\oplus d}$. Therefore $Q$ has constructible
$k_L$-cohomology and support in $[r,s]$. For each $m$, regard $Q$ as a $(B_m)_Y$-complex via
$B_m\to k_L$; the same constant models show constructibility as $B_m$-modules, with the same
support.
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
during the induction and is independent of $m$; no flatness of $B_m$ over $A_{E,m}$, no finite
Tor hypothesis and no Noetherian hypothesis on $Y$ were used.
5. Let $N=K\otimes_R S$ be the object defined by [def-weil-integral-scalar-extension]. It is the
fixed cone $\operatorname{Cone}(1-s)[-1]$ of the strict tower $\operatorname{Res}^L_mM_m$, and is
a derived limit of that tower by [lem-weil-integral-scalar-extension-well-defined]. Step 2
verified precisely the normalized-tower hypothesis of [lem-coef-normalized-dvr-effectivity], with
the DVR $S$ and quotient rings $B_m=A_{L,m}$. Apply that theorem to obtain compatible
isomorphisms $N\otimes^L_S B_m\cong M_m$ and derived completeness of $N$. This is the same
derived limit as the normalized-tower theorem: the strict tower theorem
[lem-weil-pbc-ringed-strict-tower-homotopy-limit] computes total derived inverse limit by its
Roos triangle. Countable products of completed-coefficient module sheaves are exact by
[lem-weil-proetale-countable-products-exact], so [lem-weil-derived-limit-products-core]
identifies the derived products in that triangle with the termwise products used here. To make
the comparison explicit, take the strict tower resolution $X_\bullet\to I_\bullet$ used by the
strict-tower theorem, where $X_m=\operatorname{Res}^L_mM_m$. Its maps are termwise
quasi-isomorphisms and commute with the transitions. Exact countable products imply that
$\prod_mX_m\to\prod_mI_m$ is a quasi-isomorphism: cohomology of these products is the product of
the cohomologies by [lem-weil-derived-limit-products-core]. The commuting square with $1-s$
therefore induces a quasi-isomorphism of the shifted mapping-cone complexes. On each evaluation
it commutes with projection to the corresponding tower member, since the square came from a
strict tower map. The Roos model of the strict-tower theorem is consequently identified with the
fixed cone defining $N$, with its evaluations. This supplies the comparison needed for the
canonical counit isomorphisms of the effectivity theorem, without asserting uniqueness of
arbitrary cone maps. The finite-level statement of step 4 therefore supplies constructibility and
the single interval $[r,s]$ for all derived reductions of $N$. These are exactly the conditions
of [def-weil-derived-complete-integral-detailed] for $L$, so $N\in D^b_c(Y,S)$. Finally the
ambient functor is $R$-linear by clause 3 of [lem-weil-integral-scalar-extension-well-defined].
Restricting its objects and morphisms to the full subcategories just proved preserved leaves the
equality $T(af)=aT(f)$ intact, and gives the asserted $R$-linear functor.
-/
theorem integralScalarExtension_constructible
    (K : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :
    boundedConstructibleDerivedCompleteIntegral D l hl L Y
      ((integralScalarExtension l E L ι Y).obj K.obj) := by
  sorry

/-- The restricted functor uses the original completed extension on objects and maps.
Source: blueprint order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible). -/
noncomputable def constructibleIntegralScalarExtension :
    boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y ⥤
      boundedConstructibleDerivedCompleteIntegralCategory D l hl L Y :=
  (boundedConstructibleDerivedCompleteIntegral D l hl L Y).lift
    ((boundedConstructibleDerivedCompleteIntegral D l hl E Y).ι ⋙
      integralScalarExtension l E L ι Y)
    (integralScalarExtension_constructible D l hl E L ι Y)

/-- Integer-linearity of the restricted completed coefficient functor.
Source: blueprint order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible).
Proof: the ambient integralScalarExtensionWellDefined equality is the balancing
identity for the actual constant sections. Restriction to full subcategories
preserves that equality and their inherited Hom module structures. -/
theorem constructibleIntegralScalarExtension_smul
    (K K' : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y)
    (f : K ⟶ K') (a : Padic.coefficientExtensionIntegers l E) :
    (constructibleIntegralScalarExtension D l hl E L ι Y).map (a • f) =
      integralScalarIntegerInclusion l E L ι a •
        (constructibleIntegralScalarExtension D l hl E L ι Y).map f := by
  sorry

end WeilConjectures


namespace WeilConjectures

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

/-- Finite free completed extension preserves bounded constructibility and completeness.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-weil-integral-scalar-extension-constructible).
Proof: finite freeness makes termwise tensor exact and commutes with all products in
the reduction Roos complex. Tensor associativity identifies the target reductions with
the extended source reductions after cofinal reindexing of the two uniformizer powers.
Thus completeness and the uniform support interval are preserved. At residue level,
finite coefficient extension preserves finite locally constant stalks on each stratum;
induction over the uniformizer filtration gives every finite target level. -/
theorem integralOrdinaryDerivedScalar_constructible
    (K : completedIntegralDerivedCategory l E Y D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E Y K) :
    boundedConstructibleDerivedCompleteIntegral D l hl L Y
      ((integralOrdinaryDerivedScalar l E L ι Y).obj K) := by
  sorry

/-- Restriction of finite free completed tensor to the integral full subcategories.
On complete objects its ordinary exact tensor model computes completed derived tensor.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-weil-integral-scalar-extension-constructible). -/
noncomputable def integralConstructibleScalarExtension :
    boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y ⥤
      boundedConstructibleDerivedCompleteIntegralCategory D l hl L Y :=
  (boundedConstructibleDerivedCompleteIntegral D l hl L Y).lift
    ((boundedConstructibleDerivedCompleteIntegral D l hl E Y).ι ⋙
      integralOrdinaryDerivedScalar l E L ι Y)
    (fun K ↦ integralOrdinaryDerivedScalar_constructible D l hl E L ι Y K.obj K.property)


/-- The actual boundary 1-s of the fixed scalar tower, used for both cone coordinates.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-weil-integral-scalar-extension-constructible). -/
noncomputable abbrev integralScalarRoosBoundary
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n))
    (integralOperationsTowerStep ((integralScalarTowerFunctor l E L ι Y).obj P))

/-- The completion chain map is fixed by the quotient maps and zero shifted coordinate.
Source: Bhatt--Scholze, Proposition 3.5.1; blueprint finite-free comparison
(blueprint: lem-weil-integral-scalar-extension-constructible).
Proof: the quotient tensor maps commute with the tower transitions. Their product is
therefore killed by 1-s. Lift this map to the mapping cocone with zero degree-minus-one
coordinate. The two displayed cone coordinates determine every component uniquely.
Balanced tensor generation proves naturality in P and the quotient formula on sections. -/
theorem integralScalarCompletionChain_existsUnique :
    ∃! χ : (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
        integralScalarComplexFunctor l E L ι Y,
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (n : ℕ)
        (U : Y.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
        (x : (P.X i).val.obj U),
        (((χ.app P ≫ CochainComplex.mappingCocone.fst
          (integralScalarRoosBoundary l E L ι Y P) ≫
          Pi.π (fun n ↦ (integralScalarLevel l E L ι Y n).obj P) n).f i).val.app U)
            ((eqToHom ((integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose
              (P.X i)).symm).val.app U
              ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
                (SheafOfModules.changeOfRingsPresheaf
                  (integralCompletedScalarMap l E L ι Y) (P.X i)).presheaf).app U
                (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
                  ((integralCompletedScalarMap l E L ι Y).hom.app U).hom] x))) =
          integralScalarTensorSection l E L ι Y n (P.X i) U
            ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app U s) x) ∧
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i j : ℤ)
        (h : i + -1 = j),
        (χ.app P).f i ≫ (CochainComplex.mappingCocone.snd
          (integralScalarRoosBoundary l E L ι Y P)).v i j h = 0) := by
  sorry

/-- The quotient completion map, with both cone coordinates specified.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-weil-integral-scalar-extension-constructible). -/
noncomputable def integralScalarCompletionChain :=
  (integralScalarCompletionChain_existsUnique l E L ι Y).exists.choose

/-- The canonical finite-free comparison is uniquely fixed on good representatives.
Source: Bhatt--Scholze, Proposition 3.5.1 and Lemma 6.8.2
(blueprint: lem-weil-integral-scalar-extension-constructible).
Proof: finite freeness identifies ordinary extension with a finite sum on underlying
source modules. It commutes with products and the signed Roos differential. The source
completeness unit is invertible, and cofinality of the two uniformizer filtrations gives
invertibility of exactly the displayed quotient completion map. Its zero shifted
coordinate is retained. The localization of good complexes gives naturality and uniqueness
on the full complete constructible subcategory. No arbitrary lift to a cone is used. -/
theorem integralConstructibleScalarComparison_existsUnique :
    ∃! c : integralConstructibleScalarExtension D l hl E L ι Y ≅
        constructibleIntegralScalarExtension D l hl E L ι Y,
      ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (hP : boundedConstructibleDerivedCompleteIntegral D l hl E Y
          (DerivedCategory.Q.obj P.obj)),
        (c.hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩).hom ≫
            (integralScalarExtensionComparison l E L ι Y).hom.app P =
          (integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app P.obj ≫
            DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι Y).app P.obj) := by
  sorry

/-- The finite-free comparison with the canonical quotient completion normalization.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-weil-integral-scalar-extension-constructible). -/
noncomputable def integralConstructibleScalarComparison :=
  (integralConstructibleScalarComparison_existsUnique D l hl E L ι Y).exists.choose

end WeilConjectures
