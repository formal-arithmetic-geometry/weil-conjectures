/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.Blowup.AdmissibleBlowup
import Sheaf.AlgebraicGeometry.NagataBoundaryDivisorCartier
import WeilConjectures.Blowup.BlowupUniversal
import WeilConjectures.Blowup.Complement
import WeilConjectures.Blowup.Proper
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import Sheaf.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood
import WeilConjectures.AlgebraicGeometry.LocalizedSeparablePolynomialModel
import WeilConjectures.AlgebraicGeometry.SpreadPurelyInseparableFactors
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Etale.StandardEtale

/-!
# Regular alterations adapted to nested opens

Source: ILO, Travaux de Gabber, Exposé X, Theorem 2.1, printed p.149,
with normalization, two boundary blowups and generic finite-algebra spreading
(blueprint: lem-sfb-nested-open-regular-alteration).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- A regular alteration adapted to two nested dense opens and a prescribed finite étale cover.
The finite family is indexed by `Fin n` and enumerates exactly the irreducible components
of the reduced boundary. The generic field map is the canonical map on generic stalks.
The final shrinking is independent of the normal crossings assertion.
Source: ILO, Exposé X, Theorem 2.1, printed p.149, and the normalization, blowup and
finite-algebra arguments in the DAG (blueprint: lem-sfb-nested-open-regular-alteration).

Proof plan:
1. Put $K=k(T)$. Choose a point of the nonempty finite etale generic fibre $H_K$ and let $F$ be
its residue field; $F/K$ is finite. Let $q:X\to T$ be the normalization of $T$ in $F$. By the
normalization-in-a-residue-field node, $X$ is normal integral with function field $F$; by
finiteness of normalization over a field, $q$ is finite. It is proper by finite-proper, and its
image is closed and contains the generic point, hence it is surjective. Over an affine open of
$S$, the integral-closure description of normalization is unchanged on localization. Thus $X_S$ is
the normalization of $S$ in $\operatorname{Spec}F$. Apply the relative-normalization universal
property to $\operatorname{Spec}F\to H\to S$, whose second arrow is integral: this supplies
$X_S\to H$ over $S$. This argument uses a field factor of $H_K$, not an unsupported assertion that
connected $H$ is integral.
   Uses: def-weil-finite-integral-morphism, lem-weil-pbc-normalization-in-residue-field-extension,
def-fin-normalization-extension, lem-fin-normalization-extension-finite,
lem-weil-pbc-finite-proper, lem-weil-pbc-proper-closed-image,
lem-sbc-relative-normalization-universal-property.
2. The scheme $X$ is separated finite type over $k$, hence Noetherian. Set $U=q^{-1}S\subseteq
U^\circ=q^{-1}T^\circ$; both are dense quasi-compact opens. Choose finite-type quasi-coherent
ideals $\mathcal I,\mathcal J$ with $V(\mathcal I)=X\setminus U$, $V(\mathcal J)=X\setminus
U^\circ$. Let $b_1:B_1=\operatorname{Bl}_{\mathcal I}(X)\to X$, $b_2:B=\operatorname{Bl}_{\mathcal
J\mathcal O_{B_1}}(B_1)\to B_1$, $b=b_1b_2$. As $\mathcal J|_U=\mathcal O_U$, $b_2$ is a
$b_1^{-1}(U)$-admissible blowup. The boundary-divisor lemma, with its clause on a further
admissible blowup, makes $I_B=\mathcal I\mathcal O_B$ effective Cartier with support $B\setminus
b^{-1}U$ and $b^{-1}U$ scheme-theoretically dense in $B$; the Cartier-total-transform lemma gives
the same Cartier property. Applied to $B_1$, $b_1^{-1}U^\circ$ and $\mathcal J\mathcal O_{B_1}$,
it makes $J_B=\mathcal J\mathcal O_B$ effective Cartier with support $B\setminus b^{-1}U^\circ$.
The blowup-complement theorem makes $b_1$ an isomorphism over $U$ and $b_2$ one over $B_1\setminus
V(\mathcal J\mathcal O_{B_1})\supseteq b_1^{-1}U$, so $b^{-1}U\to U$ is an isomorphism and
$b^{-1}U$ is integral with function field $F$. Hence $B$ is integral: it is nonempty, and for a
nonempty affine open $V\subseteq B$ density makes $\mathcal O_B(V)\to\mathcal O_B(V\cap b^{-1}U)$
injective, so $V\cap b^{-1}U\neq\varnothing$; sections of the integral $b^{-1}U$ over a nonempty
open inject into $F$, because they do on each nonempty affine of a cover (affine-fraction lemma),
so $\mathcal O_B(V)$ is a domain. Thus $k(B)=F$ and $b$ is dominant. Blowup properness and proper
composition make $b$ proper. Empty complements give unit ideals and identity blowups.
   Uses: lem-weil-pbc-finite-type-over-noetherian, lemma-nagata-qc-open-complement-ideal-exists,
def-nagata-admissible-blowup, det-nagata-boundary-divisor-cartier,
def-nagata-scheme-theoretically-dense-open, lemma-nagata-cartier-total-transform-blowup,
thm-nagata-global-blowup-complement, def-pc-integral-scheme,
lem-sc-integral-function-field-affine-fraction, lemma-nagata-blowup-proper,
lem-weil-pbc-proper-composition.
3. Choose a prime $\ell\ne p$ and apply the global Gabber theorem to $B$ and $Z=B\setminus
b^{-1}U$. It gives $a:P\to B$ with $P$ smooth over a finite extension $k'/k$ and reduced inverse-
image boundary relative strict normal crossings. Smooth-over-a-field regularity makes $P$ regular.
The regular-normal-components node decomposes this Noetherian scheme into finitely many open-and-
closed integral components. Choose one component $Y$; by the maximal-domination clause of Gabber's
theorem its generic point maps to the generic point of $B$. Restrict $a$ and its boundary to $Y$.
This remains proper (restriction to an open-and-closed component is a closed inclusion followed by
$a$), dominant and generically finite. The restricted boundary $D=\bigcup_{a\in A}D_a$ has
finitely many components and is strict normal crossings; it is regular in the sense of the
regular-scheme boundary definition [def-trf-strict-normal-crossings-boundary] because all the
relative intersections are smooth over $k'$. Set $h=qba|_Y$. By proper composition $h$ is proper.
It is dominant, and $k(Y)/k(T)$ is finite, since $k(Y)/F$ and $F/K$ are finite. All schemes used
are separated finite type over $k$.
   Uses: lem-sfb-gabber-global-snc-alteration, lem-weil-pbc-smooth-scheme-over-field-regular,
rem-pc-regular-normal, lem-weil-pbc-proper-composition, def-weil-proper-morphism,
def-trf-strict-normal-crossings-boundary.
4. Pull back $I_B,J_B$ to $Y$. Both extended ideals are still effective Cartier: a local generator
is nonzero in the function field of $B$, hence remains nonzero in $k(Y)$ by dominance, and every
local ring of $Y$ is a domain. Their supports are $Y\setminus h^{-1}S$ and $Y\setminus
h^{-1}T^\circ$; the first is exactly $|D|$. To check that the second is a union of whole
components, work locally at $y\in Y$. The Gabber boundary has parameter equations $t_1,\ldots,t_r$
there. A generator $f$ of the second ideal becomes a unit off $D$, because its zero set is
contained in $|D|$. In $\mathcal O_{Y,y}[1/(t_1\cdots t_r)]$ it is therefore a unit. The regular-
local-UFD boundary-factorization node gives $f=v\prod t_i^{n_i}$ with $v$ a unit and $n_i\ge0$.
Consequently its support is locally a union of the branches of $D$. At every point of this support
at least one branch through the point is selected, and its generic point also lies in the support.
Since the support is closed, it contains that whole $D_a$. Conversely every selected component
lies in the support. Thus, with $A_{\rm out}$ the components whose generic points lie in it, the
support is $\bigcup_{a\in A_{\rm out}}D_a$. This proves both required open identities without
asserting normal crossings for any later shrinking.
   Uses: lem-trf-regular-local-ufd-boundary-factorization, lem-sfb-gabber-global-snc-alteration,
def-nagata-effective-cartier-ideal.
5. Put $W=h^{-1}S$. The morphism $r:W\to S$ is proper by base change. It is surjective: the proper
image of $h$ is closed and contains the generic point of integral $T$, hence is all of $T$, so its
restriction over $S$ is onto. The composite $W\to X_S\to H$ from step 1 factors $r$ through $c$.
The open $W$ is nonempty integral. The affine-fraction-field lemma identifies every nonempty
affine chart of the generic fibre with a finitely generated $K$-subalgebra of $L=k(Y)$. Its
generators are algebraic over $K$, so it is a finite-dimensional domain, hence a field,
necessarily $L$. These charts all contain the generic point; consequently the whole generic fibre
is $\operatorname{Spec}L$. Apply the generic-finiteness lemma to obtain a nonempty affine open
$\operatorname{Spec}A\subseteq S$ on which $r$ is finite. Write its inverse image as
$\operatorname{Spec}E$, with $E$ a finite $A$-algebra domain and $E\otimes_AK=L$.
   Uses: lem-weil-pbc-proper-base-change, lem-weil-pbc-proper-closed-image,
def-weil-finite-integral-morphism, def-sc-function-field,
lem-sc-integral-function-field-affine-fraction,
lem-weil-pbc-generic-finite-morphism-open-neighborhood.
6. Let $K'\subseteq L$ be the separable closure of $K$ in $L$. The separable-first lemma gives
$K'/K$ finite separable and $L/K'$ finite purely inseparable. Choose a primitive element
$\alpha\in K'$ and write its monic separable minimal polynomial as $g\in K[T]$. Apply the
localized separable-polynomial model lemma and replace $A$ by the resulting nonzero principal
localization, so $g\in A[T]$ and $g$ is coprime to $g'$. Put $A'=A[T]/(g)$. Division by the monic
polynomial shows that $1,T,\ldots,T^{d-1}$ is an $A$-basis, where $d=\deg g=[K':K]\ge1$, and the
map $A'\to K'$ sending $T$ to $\alpha$ is injective: a representative of degree less than $d$
which vanishes at $\alpha$ is zero over $K$, hence over the domain $A$. Thus $A'$ is a domain with
fraction field $K'$. The Bezout relation makes $g'$ a unit in $A'$, so the standard-etale monic-
derivative lemma says $\operatorname{Spec}A'\to\operatorname{Spec}A$ is etale. Its displayed free
basis makes it finite and surjective of constant degree $d$.
   Uses: lem-weil-pbc-separable-first-purely-inseparable,
lem-weil-pbc-finite-separable-extension-primitive-element,
lem-weil-pbc-localized-separable-polynomial-model, lem-weil-pbc-standard-etale-monic-derivative.
7. As $E\otimes_AK=L$, write $\alpha=z/s$ with $z\in E$ and $0\ne s\in A$. After replacing $A$ by
$A[1/s]$ and $E,A'$ by their corresponding base localizations, $\alpha\in E$, and evaluation
defines an injective $A$-algebra map $A'\hookrightarrow E$ compatible with the embeddings in $L$.
The finite $A$-module generators of $E$ also generate $E$ as an $A'$-module: their $A'$-span
contains their $A$-span, which is already all of $E$. Hence $E$ is finite over $A'$. Apply the
spreading-purely-inseparable-factors lemma to the Noetherian domain $A$, the finite etale domain
$A'$, and the finite domain $E$, with fraction fields $K,K',L$. It gives a further nonzero base
localization on which $\operatorname{Spec}E\to\operatorname{Spec}A'$ is surjective radicial and a
universal homeomorphism; it is finite by the preceding module argument. Let $S_0$ be this final
principal open in $S$, $T_0=\operatorname{Spec}A'$ over it, and $W_0=\operatorname{Spec}E$. The
maps $u:W_0\to T_0$ and $e:T_0\to S_0$ have all the asserted properties. The rank-$d$ free
polynomial basis persists under each localization. All localizations are by nonzero elements, so
$S_0$ remains nonempty dense.
   Uses: lem-weil-pbc-spread-purely-inseparable-factors, def-weil-finite-integral-morphism.
-/
theorem exists_nestedOpen_regular_alteration
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p)
    (T : Scheme.{u}) [T.Over (Spec (.of k))] [IsIntegral T]
    [IsSeparated (T ↘ Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))]
    (S Tcirc : T.Opens) (hST : S ≤ Tcirc)
    (hS : Dense (S : Set T)) (hTcirc : Dense (Tcirc : Set T))
    (H : Scheme.{u}) [ConnectedSpace H] (c : H ⟶ S.toScheme)
    [IsFinite c] [Etale c] [Surjective c] :
    ∃ (Y : Over (Spec (.of k))) (_ : IsIntegral Y.left),
      IsRegularScheme Y.left ∧ IsSeparated Y.hom ∧
      LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom ∧
      ∃ (h : Y.left ⟶ T) (_ : IsProper h) (_ : IsDominant h),
        h ≫ (T ↘ Spec (.of k)) = Y.hom ∧
        (∃ hη : h (genericPoint Y.left) = genericPoint T,
          (T.presheaf.stalkSpecializes (specializes_of_eq hη) ≫
            h.stalkMap (genericPoint Y.left)).hom.Finite) ∧
        ∃ (D : Y.left.IdealSheafData), IsStrictNormalCrossingsBoundary D ∧
          ∃ (n : ℕ)
            (C : Fin n ≃ {Z : Set (D.support : Set Y.left) //
              Z ∈ irreducibleComponents (D.support : Set Y.left)})
            (Aout : Finset (Fin n)),
            (h ⁻¹ᵁ S : Set Y.left) = (D.support : Set Y.left)ᶜ ∧
            (h ⁻¹ᵁ Tcirc : Set Y.left) =
              (⋃ a ∈ Aout, Subtype.val '' (C a).val)ᶜ ∧
            IsProper (h ∣_ S) ∧ Surjective (h ∣_ S) ∧
            (∃ b : (h ⁻¹ᵁ S).toScheme ⟶ H, b ≫ c = h ∣_ S) ∧
            ∃ S0 : S.toScheme.Opens,
              Nonempty S0 ∧ Dense (S0 : Set S.toScheme) ∧
              IsFinite (pullback.snd (h ∣_ S) S0.ι) ∧
              ∃ (T0 : Scheme.{u}) (u : pullback (h ∣_ S) S0.ι ⟶ T0)
                (e : T0 ⟶ S0.toScheme) (d : ℕ),
                u ≫ e = pullback.snd (h ∣_ S) S0.ι ∧
                IsFinite u ∧ (topologically IsHomeomorph).universally u ∧
                IsFinite e ∧ Etale e ∧ Surjective e ∧ 1 ≤ d ∧
                ∀ s : S0.toScheme, e.finrank s = d := by
  sorry

end AlgebraicGeometry
