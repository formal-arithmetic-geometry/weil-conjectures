/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.ClosedImmersionProducts
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.RingedTopoiCanonicalTensorPullback
import Sheaf.Paper.FiniteFieldDerivedTensorSummand
import Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
import Sheaf.Algebra.Homology.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.AlgebraicGeometry.KunnethGlobalSections
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Ordinary Kunneth for a finite p-adic coefficient ring

Source: Weil conjectures blueprint, sec-smooth-purity/sk-prop-a1-kummer,
node lem-pur-ordinary-kunneth-finite-ring, order 1937
(blueprint: lem-pur-ordinary-kunneth-finite-ring).

## Main definitions

- `derivedConstantPullbackIso`: the canonical comparison for constant derived complexes.
- `ordinaryKunnethPulledCounit`: the global-sections counit pulled back to the product.
- `ordinaryKunnethTensorMate`: the abstract tensor-of-counits adjunct.
- `ordinaryGlobalKunnethMap`: the canonical absolute exterior-product arrow.

## Main statements

- `isIso_ordinaryGlobalKunnethMap_finiteCoefficientRing`: invertibility at positive finite level.
-/

@[expose] public section

universe u uA uC vC uB vB

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section AbsoluteMap

variable (A : Type uA) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The canonical comparison from a constant derived complex on the source to the pullback
of its constant derived complex on the target. It is the inverse of the ordinary
constant-sheaf comparison, derived and then split by the exact-functor composition iso.
Source: blueprint order 1740, terminal-topos specialization
(blueprint: lem-pur-ordinary-kunneth-finite-ring). -/
noncomputable def derivedConstantPullbackIso {X Z : Scheme.{u}} (p : Z ⟶ X) :
    (constantSheaf Z.smallEtaleTopology A).leftDerivedFunctor ≅
      (constantSheaf X.smallEtaleTopology A).leftDerivedFunctor ⋙
        L((p)^*[A]) :=
  (Functor.leftDerivedFunctorNatIso (constantSheaf Z.smallEtaleTopology A)
    (Scheme.upperStarConstantSheafIso A p).symm) ≪≫
      Functor.leftDerivedFunctorCompIso (constantSheaf X.smallEtaleTopology A) (upperStar A p)

/-- Pull the global-sections counit back to `Z`, identifying the pulled-back constant
complex with the constant complex on `Z` by `derivedConstantPullbackIso`.
Source: blueprint order 1740, terminal-topos specialization
(blueprint: lem-pur-ordinary-kunneth-finite-ring). -/
noncomputable def ordinaryKunnethPulledCounit {X Z : Scheme.{u}} (p : Z ⟶ X)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (constantSheaf Z.smallEtaleTopology A).leftDerivedFunctor.obj
      ((rightDerivedGlobalSections A X).obj K) ⟶
        (L((p)^*[A])).obj K :=
  (derivedConstantPullbackIso A p).hom.app _ ≫
    (L((p)^*[A])).map
      ((derivedConstantGlobalSectionsAdjunction A X).counit.app K)

/-- The tensor-of-counits adjunct construction, with its categories left abstract.
Source: blueprint order 1740, the displayed adjunct formula
(blueprint: lem-pur-ordinary-kunneth-finite-ring). This helper keeps the same tensor structures as
explicit parameters when specializing to the terminal geometric morphism. -/
noncomputable def ordinaryKunnethTensorMate
    {C : Type uC} [Category.{vC} C] {B : Type uB} [Category.{vB} B]
    (T : C ⥤ C ⥤ C) (T' : B ⥤ B ⥤ B)
    (F : C ⥤ B) (G : B ⥤ C) (adj : F ⊣ G)
    (δ : (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ B).obj F).obj F).obj T')
    {P Q : C} {V W : B} (a : F.obj P ⟶ V) (b : F.obj Q ⟶ W) :
    (T.obj P).obj Q ⟶ G.obj ((T'.obj V).obj W) :=
  adj.homEquiv _ _ ((δ.app P).app Q ≫ (T'.map a).app _ ≫ (T'.obj _).map b)

/-- The absolute exterior-product arrow in the derived category of modules, adjoint to
the derived constant-sheaf tensor comparison followed by the tensor of the two
pulled-back global-sections counits. Its target is the derived sections of the ordinary
uncompleted derived external tensor product.
Source: blueprint order 1740 and Stacks Tag 0F1E (blueprint: lem-pur-ordinary-kunneth-finite-ring).
This is the terminal-topos form of the upstream `kunnethMap`, using the constant-complex
versus sections adjunction. No equivalence for the etale point is chosen. -/
noncomputable def ordinaryGlobalKunnethMap {X Y Z : Scheme.{u}}
    (p : Z ⟶ X) (q : Z ⟶ Y)
    [(constantSheaf Z.smallEtaleTopology A).Monoidal]
    [(constantSheaf Z.smallEtaleTopology A).PreservesFlat]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (rightDerivedGlobalSections A X).obj K ⊗
        (rightDerivedGlobalSections A Y).obj M ⟶
      (rightDerivedGlobalSections A Z).obj
        (((curriedTensor (DerivedCategory (Sheaf Z.smallEtaleTopology A))).obj
          ((L((p)^*[A])).obj K)).obj
            ((L((q)^*[A])).obj M)) :=
  ordinaryKunnethTensorMate (curriedTensor (DerivedCategory A))
    (curriedTensor (DerivedCategory (Sheaf Z.smallEtaleTopology A)))
    (constantSheaf Z.smallEtaleTopology A).leftDerivedFunctor
    (rightDerivedGlobalSections A Z) (derivedConstantGlobalSectionsAdjunction A Z)
    (constantSheaf Z.smallEtaleTopology A).leftDerivedTensorComparison
    (ordinaryKunnethPulledCounit A p K) (ordinaryKunnethPulledCounit A q M)


end AbsoluteMap

/-- The canonical exterior-product arrow is invertible for arbitrary unbounded complexes
on separated finite-type schemes over the fixed algebraic closure of a finite field,
with coefficients in the positive-level quotient of a finite p-adic extension.

Source: blueprint order 1937, lem-pur-ordinary-kunneth-finite-ring.md
(blueprint: lem-pur-ordinary-kunneth-finite-ring).

Proof plan from the DAG:

1. Fix the coefficient data of [def-weil-l-adic-coefficient-extension]. Thus $\mathcal O_E$ is a
DVR, $A$ is finite, and $\kappa=\mathcal O_E/(\varpi_E)=A/(\varpi_E)$ is a finite field. Its
characteristic is $\ell$: the extended absolute value has $|\ell|_E=\ell^{-1}<1$, so
$\ell\in(\varpi_E)$. In particular $A$ is a torsion ring. The schemes $X,Y,Z=X\times_kY$ are qcqs
and finite type over the separably closed field $k$. For the product, on finite affine covers its
coordinate algebras are $B_i\otimes_k C_j$, generated by the generators of $B_i$ and $C_j$; The
diagonal of $Z$ is the product of the two closed diagonals (after permuting the factors), so
[lem-weil-pbc-closed-immersion-products] makes it a closed immersion. Apply
[lem-pc-separated-quasi-separated] to the three structure morphisms. Over the affine base
$\operatorname{Spec}k$, this gives quasi-separated sources: for affine opens $U,V$, their
intersection is the inverse image of the affine open $U\times_kV$ under the quasi-compact relative
diagonal and is quasi-compact. These observations check all geometric and coefficient hypotheses
used below.

2. We will use coefficient restriction without changing derived sections. For any ring map $R\to
S$ and scheme $T$, restriction of scalars is exact and conservative: kernels, cokernels and
cohomology have the same underlying abelian sheaves. Its derived functor is therefore termwise
restriction. Apply [lem-weil-pbc-ringed-topoi-derived-pushforward-composition] to the two
factorizations of the ringed-topos morphism $(T_{\mathrm{et}},S_T)\to(*,R)$, through
$(T_{\mathrm{et}},R_T)$ and through $(*,S)$. Their equality gives the canonical natural
isomorphism $$R\Gamma_R(T,\operatorname{Res}H)\cong\operatorname{Res}R\Gamma_S(T,H).$$ The
resolution normalization in that node identifies this with the comparison induced by the identity
of underlying section complexes. Thus it respects coefficient endomorphisms. A termwise splitting
$M=eM\oplus(1-e)M$ remains a splitting under $R\Gamma$: finite sums of K-injective complexes are
K-injective, since Hom into their sum is the finite sum of the acyclic Hom complexes. Consequently
$R\Gamma(eM)=eR\Gamma(M)$. No claim that restriction preserves K-injectivity is needed.

3. First let $B$ be any finite field of characteristic $\ell$ and let $P\in D(X_{\mathrm{et}},B)$,
$Q\in D(Y_{\mathrm{et}},B)$. Apply [thm-kun-0f1p] with $n=\ell$ to their restrictions to
$F=\mathbf F_\ell$. Its arrow is $B\otimes_F B$-linear: naturality for multiplication on $P$ and
on $Q$ gives the two commuting actions. Apply the diagonal projector of
[lem-pur-finite-field-derived-tensor-summand] to this isomorphism. On the source its image is
$\operatorname{Res}(R\Gamma_B(X,P)\otimes_B^{\mathbf L}R\Gamma_B(Y,Q))$ by that lemma and step 2.
On the target it is $\operatorname{Res}R\Gamma_B(Z,p_X^{-1}P\otimes_B^{\mathbf L}p_Y^{-1}Q)$,
using the same lemma on $Z$ and step 2. These identifications give the $B$-Kunneth arrow itself:
under [def-kun-kunneth-map] its adjunct is the tensor of the two counits; the balanced tensor
quotient sends the $F$-linear adjunct to the $B$-linear adjunct. Restriction is conservative by
step 2, so this arrow is an isomorphism for arbitrary unbounded $P,Q$.

4. By [lem-kun-0f10] each of $X,Y,Z$ has finite cohomological dimension. For $H\in
D(T_{\mathrm{et}},A)$ put $H_\kappa=H\otimes_A^{\mathbf L}\kappa_T$ as an object of
$D(T_{\mathrm{et}},\kappa)$ using [lem-pur-derived-change-of-rings]. Construct the canonical
scalar comparison as a morphism in $D(\kappa)$: $$c_{T,H}:R\Gamma_A(T,H)\otimes_A^{\mathbf
L}\kappa\longrightarrow R\Gamma_\kappa(T,H_\kappa).$$ Precisely, its adjunct under constant
$\kappa$-complex versus derived sections is the scalar extension of the $A$-counit
$\underline{R\Gamma_A(T,H)}\to H$. The identification of its pulled-back source with the scalar
extension of that constant complex is the pullback-tensor comparison
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. Under step 2, the restriction of this
morphism to $D(A)$ is the constant-tensor comparison [def-kun-projection-formula-map]: both
adjuncts are the same $A$-counit tensor $1_\kappa$. Apply [lem-kun-0f12] at the torsion ring $A$
with the coefficient complex $\kappa[0]$ to conclude that this underlying comparison is an
isomorphism. Since restriction is conservative, $c_{T,H}$ is an isomorphism in $D(\kappa)$. This
constructs the $\kappa$-linear morphism itself; no lifting of an arbitrary $A$-derived morphism
from a commuting coefficient action is asserted.

5. Write $S_T=-\otimes_A^{\mathbf L}\kappa_T$ and $S_*=-\otimes_A^{\mathbf L}\kappa$. The monoidal
scalar-extension isomorphism in [lem-weil-pbc-ringed-topoi-derived-tensor-pullback], applied to
the identity topos with ring map $A_T\to\kappa_T$, identifies $S_T(H\otimes_A^{\mathbf L}J)$ with
$S_TH\otimes_\kappa^{\mathbf L}S_TJ$; the same applies on the point site. Inverse image commutes
with this coefficient extension by [lem-kun-inverse-image-monoidal] applied over $A$ with the
second factor $\underline\kappa$. Hence, with $a_A$ the item’s arrow and $a_\kappa$ the arrow for
$K_\kappa,L_\kappa$, the comparisons of step 4 give the square $$c_{Z,K\boxtimes_A^LL}\circ
S_*(a_A)=a_\kappa\circ(c_{X,K}\otimes_\kappa^{\mathbf L}c_{Y,L}),$$ where the target is identified
with $R\Gamma_\kappa(Z,K_\kappa\boxtimes_\kappa^LL_\kappa)$ by the preceding tensor isomorphisms.
To check this equality, use [def-kun-projection-formula-map] to expand each $c$ as the adjunct of
counit tensor identity and [def-kun-kunneth-map] to expand $a$ as the adjunct of the two counits.
Pull both composites back to $Z$ and take their adjuncts. After the canonical tensor rebracketing
both are $$(p_X^{-1}\varepsilon_X\otimes p_Y^{-1}\varepsilon_Y)\otimes1_{\kappa_Z},$$ from
$p_X^{-1}\underline{R\Gamma_A(X,K)}\otimes_A^{\mathbf
L}p_Y^{-1}\underline{R\Gamma_A(Y,L)}\otimes_A^{\mathbf L}\kappa_Z$ to
$K\boxtimes_A^LL\otimes_A^{\mathbf L}\kappa_Z$. Here $\varepsilon_X:\underline{R\Gamma_A(X,K)}\to
K$ and $\varepsilon_Y:\underline{R\Gamma_A(Y,L)}\to L$ are the counits for constant sheaf versus
global sections, and the pullbacks of the constant complexes to $Z$ are identified. Equality of
adjuncts proves the square. Thus this is an equality of the canonical maps, not merely an
isomorphism of their endpoints.

6. Step 3 with $B=\kappa$ proves that $a_\kappa$ is an isomorphism; its arguments
$K_\kappa,L_\kappa$ need not be bounded. Step 4 and the square in step 5 imply that $S_*(a_A)$ is
an isomorphism. Let $D$ be a cone of $a_A$ in $D(A)$. By the exactness of derived scalar extension
in [lem-pur-derived-change-of-rings], its reduction is a cone of $S_*(a_A)$, hence
$D\otimes_A^{\mathbf L}\kappa=0$.

7. Put $I_i=\varpi_E^iA$ for $0\leq i\leq n$, so $I_0=A$, $I_n=0$. For $i<n$, multiplication by
$\varpi_E^i$ identifies $\kappa$ with $I_i/I_{i+1}$ as $A$-modules: it is surjective, and if
$\varpi_E^iu\in\varpi_E^{i+1}\mathcal O_E$ then cancellation in the DVR gives
$u\in\varpi_E\mathcal O_E$. Choose a K-flat resolution $P$ of $D$ with flat terms by
[lem-pc-kflat-resolution] on the one-point site. For any $A$-module $M$, $P\otimes_A M$ computes
$D\otimes_A^{\mathbf L}M$: choose a K-flat resolution $Q\to M$, use
[lem-weil-pbc-site-derived-tensor-descent] for $P\otimes_AQ$, and use the K-flat condition
[def-pc-kflat-complex] to see that $P\otimes_A\operatorname{Cone}(Q\to M)$ is acyclic. Flatness of
every $P^r$ makes $0\to P\otimes_AI_{i+1}\to P\otimes_AI_i\to P\otimes_A\kappa\to0$ a degreewise
exact sequence of complexes. By [lem-weil-pbc-complex-ses-triangle] this is a distinguished
triangle after localization. Downward induction starts with $P\otimes_AI_n=0$; if
$P\otimes_AI_{i+1}$ is acyclic, its triangle and step 6 imply $P\otimes_AI_i$ is acyclic. At
$i=0$, $P\otimes_AA\cong P$ by the chain isomorphism $p\otimes a\mapsto ap$, with inverse
$p\mapsto p\otimes1$. Hence $D=0$ and $a_A$ is an isomorphism. This proves the stated canonical
arrow without any boundedness assumption.
-/
theorem isIso_ordinaryGlobalKunnethMap_finiteCoefficientRing
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ ringChar D.k)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n)
    (X Y : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (K : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X.left)
    (M : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) Y.left) :
    IsIso (ordinaryGlobalKunnethMap (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
      (pullback.fst X.hom Y.hom) (pullback.snd X.hom Y.hom) K M) := by
  sorry

end AlgebraicGeometry.Etale
