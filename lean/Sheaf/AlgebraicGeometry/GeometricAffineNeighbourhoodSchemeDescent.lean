/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineAtlasOpenCover
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteAffineSubatlas
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.RingTheory.Jacobson.Ring
import Sheaf.AlgebraicGeometry.DecentSpaceFiniteFieldMap
import Mathlib.RingTheory.Artinian.Module
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Sheaf.AlgebraicGeometry.FiniteFreeAlgebraSpectrum
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability

/-!
# Schemeness from affine neighbourhoods after algebraic closure

Source: Stacks Project, Spaces over Fields, Tag 0B88,
`lemma-scheme-over-algebraic-closure-enough-affines`; Decent Spaces, Tag 088J,
`lemma-locally-separated-decent`
(blueprint: lem-sfb-geometric-affine-neighbourhood-scheme-descent).

Restriction along `Over.map` computes the base-change functor of points: on a scheme
`T → Spec Ω` its sections are the sections of `X` on `T → Spec Ω → Spec k`.
Thus the representing isomorphism below specifies the sheaf fibre product over `k`.
The diagonal is relative to `Spec k`, since all presheaves are on `Over (Spec k)`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally separated algebraic space locally of finite type over a field is a scheme
if its base change to an algebraic closure is a scheme in which every finite list of
rational points factors through an affine open, including the empty list.
Source: Stacks Project, Spaces over Fields, Tag 0B88, and Decent Spaces, Tag 088J
(blueprint: lem-sfb-geometric-affine-neighbourhood-scheme-descent).

Proof (the node's finite-fibre descent argument, without a perfection assumption):

1. The structure map $\operatorname{Spec}k\to\operatorname{Spec}\mathbf Z$ is a map of schemes,
hence locally separated. Composition with $X/k$ makes $X$ absolutely locally separated. Thus $X$
is decent. Every etale scheme chart of $X$ is locally of finite type over the Noetherian scheme
$\operatorname{Spec}k$ (a field has only the ideals $0,k$), hence locally Noetherian. Apply the
locally-Noetherian decent-space lemma to conclude that $X$ is quasi-separated.
Dependencies: lem-sfb-space-locally-separated-base-change, lem-sfb-locally-separated-space-decent,
pqf-lem-locnoeth-lft, lem-sfb-locally-noetherian-decent-quasiseparated.

2. Cover $X$ by open subspaces $O$ admitting a surjective etale affine scheme atlas. Each $O$ is
quasi-compact, is quasi-separated by quasi-compact-open permanence, and is still locally of finite
type over $k$, since a scheme chart of $O$ is a scheme chart of $X$. Fix such an $O$ and an affine
atlas $q:U\to O$. Write $O_{\overline k}=Y\times_XO$, an open subscheme of $Y$. We will give
scheme neighbourhoods in $O$ for the images of all finite type points of $U$.
Dependencies: lem-a1-space-affine-atlas-open-cover, lem-a1-space-finite-affine-subatlas,
lem-sfb-space-integral-qcqs-permanence, def-a1-space-open-subspace.

3. Let $u$ be a finite type point of $U$, and put $L=\kappa(u)$. By definition
$\operatorname{Spec}L\to U$ is of finite type. The affine scheme $U$ is quasi-compact and locally
of finite type over $k$, hence of finite type. Composition gives
$\operatorname{Spec}L\to\operatorname{Spec}k$ of finite type, so $L$ is a finitely generated
$k$-algebra. Zariski\textquotesingle s lemma makes $L/k$ finite. Let $a:\operatorname{Spec}L\to X$
be the composite and $x$ its point image, which lies in $O$. Decency and the finite-field-map
lemma imply that $a$ is representable and finite.
Dependencies: lem-sfb-finite-type-points-detect-open, lem-weil-pbc-affine-scheme-qcqs,
lem-sfb-finite-type-composition-base-change, lem-weil-pbc-zariski-lemma,
lem-sfb-decent-space-finite-field-map.

4. Its base change to $\overline k$ is the finite map $a_{\overline
k}:Z=\operatorname{Spec}(L\otimes_k\overline k)\to Y$. The tensor algebra has finite dimension
over $\overline k$ (tensor a finite $k$-basis of $L$: the maps $\overline k^d\to
L\otimes_k\overline k$, $(c_i)\mapsto\sum_i e_i\otimes c_i$, and $l\otimes
c\mapsto(\lambda_i(l)c)_i$ for dual coordinate functions $\lambda_i$ are inverse), hence is
Artinian and has finite spectrum. For a prime $\mathfrak p$ its quotient is a finite-dimensional
domain over $\overline k$, hence a field: multiplication by any nonzero element is an injective
endomorphism of a finite-dimensional vector space, thus is surjective. This field is $\overline
k$: each of its elements is algebraic, and a split polynomial over $\overline k$ annihilating it
forces it to equal a root in $\overline k$. Thus every point of $Z$ gives a $\overline k$-rational
point of $Y$. Point fibre-product calculus shows that the image $F$ of $|Z|$ is exactly the
inverse image of $x$ in $|Y|$. The same calculus shows $F\subseteq |O_{\overline k}|$. Choose an
affine open $W\subseteq Y$ containing $F$ using the hypothesis.
Dependencies: lem-sfb-finite-space-morphism-topology, lem-weil-pbc-finite-dim-algebra-artinian,
lem-sfb-artinian-spectrum-finite, def-weil-algebraic-closure, lem-a1-space-point-open-calculus.

5. Shrink $W=\operatorname{Spec}A$ into $O_{\overline k}$ while retaining $F$. Write its closed
complement $W\setminus O_{\overline k}=V(J)$. For every prime $\mathfrak p$ representing a member
of $F$, $J\not\subseteq\mathfrak p$. Prime avoidance yields $f\in J$ outside all these primes.
Then $F\subseteq D(f)\subseteq W\cap O_{\overline k}$, and $D(f)$ is affine. If $F$ is empty take
the empty affine open. Replace $W$ by this $D(f)$. This also proves precisely the finite-point
shrinking needed when restricting the hypothesis to an open subspace.
Dependencies: lem-weil-pbc-prime-avoidance, lem-weil-pbc-affine-open-section-vanishing-prime.

6. Index the finite intermediate extensions $k\subseteq K\subseteq\overline k$ by inclusion. This
is a small nonempty directed set: any finitely many algebraic elements generate a finite
extension, giving common upper bounds; its union is $\overline k$. Put
$O_K=O\times_k\operatorname{Spec}K$. On an affine scheme test $T=\operatorname{Spec}A\to O$, its
pullback is $\operatorname{Spec}(A\otimes_kK)$. Thus the transition maps are affine. The same
affine test formula makes $O_K\to O$ affine. Hence every stage is qcqs by affine-morphism
permanence. On affine tests, the ring colimit is $A\otimes_k\overline k$; the affine-spectrum
limit formula and etale sheaf descent identify the sheaf limit with $O_{\overline k}$.
Equivalently this is the base-change-compatible limit asserted by the algebraic-space affine-limit
lemma.
Dependencies: lem-sfb-space-affine-limits-schematic-stages, lem-sfb-space-affine-locality,
lem-weil-pbc-limit-affine-transition, def-trf-algebraic-space.

7. Since the limit $O_{\overline k}$ is a scheme, schematic-stage descent gives a finite
intermediate field $K_0$ with $O_{K_0}$ a scheme. Every later $O_K$ is a scheme by the same lemma.
Pass to the directed tail $K\supseteq K_0$, whose limit remains $O_{\overline k}$. Its transition
morphisms are affine and its stages quasi-separated. Affine-open limit descent applied to the
affine $W\subseteq O_{\overline k}$ gives a finite $K\supseteq K_0$ and an affine open
$W_K\subseteq O_K$ whose inverse image is exactly $W$.
Dependencies: lem-sfb-space-affine-limits-schematic-stages, lem-trf-affine-open-limit-descent.

8. The map $O_{\overline k}\to O_K$ is surjective on points: given any field-valued representative
over $K$, the tensor product with $\overline k$ is a nonzero algebra over that field and has a
prime, producing a lift after a residue-field extension. Nonzeroness follows by extending
$1\in\overline k$ to a $K$-basis. For any point of $O_K$ above $x$, such a lift belongs to $F$,
hence to $W$; the equality $W=W_K\times_K\overline k$ therefore puts the original point in $W_K$.
Thus $W_K$ contains the entire fibre of $p:O_K\to O$ over $x$.
Dependencies: lem-a1-space-point-open-calculus, lem-weil-common-extension-fields-maximal-ideal,
def-weil-algebraic-closure.

9. The projection $p:O_K\to O$ is representable surjective finite locally free. Indeed on a scheme
test $T=\operatorname{Spec}A\to O$ its source is $\operatorname{Spec}(A\otimes_kK)$. A $k$-basis
of $K$ gives a finite $A$-basis, so the finite-free spectrum lemma gives finite local freeness;
these affine tests cover every scheme test. Every point lifts, since its residue-field tensor
product with the nonzero finite field extension $K$ is nonzero and has a prime (use a basis
containing $1$). Apply the finite-locally-free fibre-neighbourhood criterion to $p$ and the affine
$W_K$. It gives an open scheme subspace $N_u\subseteq O$ containing $x$.
Dependencies: lem-weil-pbc-finite-free-algebra-spectrum,
lem-weil-common-extension-fields-maximal-ideal,
lem-sfb-finite-locally-free-fibre-scheme-neighbourhood.

10. Let $N\subseteq O$ be the union of these open scheme subspaces $N_u$, one for each finite type
point $u$ of $U$. Open subsets correspond to open subspaces. On any scheme test $T\to N$, their
inverse images are open subschemes covering $T$, so these representable open subfunctors cover
$N$. Since $N$ is an fppf sheaf it is a Zariski sheaf; the schemes criterion therefore makes $N$ a
scheme. The inverse image $q^{-1}N$ is an open subset of $U$ containing every finite type point,
so point detection gives $q^{-1}N=U$. Surjectivity of the atlas and point calculus imply $N=O$.
Hence $O$ is a scheme.
Dependencies: lem-a1-space-etale-open-image, lem-pc-schemes-criterion, def-trf-algebraic-space,
lem-sfb-finite-type-points-detect-open, lem-a1-space-point-open-calculus.

11. The open subspaces $O$ of step 2 cover $X$ and are now represented by schemes. On every scheme
test their pullbacks are open subschemes covering that test. The algebraic space $X$ is a Zariski
sheaf, and the schemes criterion applied to this representable open cover gives a representing
scheme. Its structure map to $\operatorname{Spec}k$ is the natural transformation corresponding
under Yoneda to the given structure map of $X$, so it is a representing $k$-scheme. This includes
empty $X$ and needs no global quasi-compactness.
Dependencies: lem-pc-schemes-criterion, def-trf-algebraic-space.
-/
theorem isRepresentable_of_geometric_affine_neighbourhoods
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    (hlft : ∀ (U : Over (Spec (CommRingCat.of k)))
      (a : yoneda.obj U ⟶ X.obj.obj), IsEtale a → LocallyOfFiniteType U.hom)
    (hlsep : IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left)
      (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj)))
    (Y : Over (Spec (CommRingCat.of Ω)))
    (hY : Nonempty (yoneda.obj Y ≅
      (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).op ⋙ X.obj.obj))
    (haff : ∀ (n : ℕ)
      (y : Fin n → (Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶ Y)),
      ∃ V : Y.left.Opens, IsAffineOpen V ∧
        ∀ i : Fin n, ∃ z : Spec (CommRingCat.of Ω) ⟶ V.toScheme,
          z ≫ V.ι = (y i).left) :
    ∃ Z : Over (Spec (CommRingCat.of k)), Nonempty (yoneda.obj Z ≅ X.obj.obj) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
