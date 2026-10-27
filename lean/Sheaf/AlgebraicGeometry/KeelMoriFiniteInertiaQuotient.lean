/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.AlgebraicGeometry.ModuliInertia
public import Sheaf.AlgebraicGeometry.FiniteStackSchemeTests
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.EtaleSmoothAtlasFppfDescent
import Sheaf.AlgebraicGeometry.AffineStackStabilizerEtaleComparison
import Sheaf.AlgebraicGeometry.EtaleRelationQuotient
import Mathlib.AlgebraicGeometry.Limits

/-! # Keel--Mori quotient of a DM stack with finite inertia

Source: Stacks Project, Tag 0DUT, theorem-keel-mori; Tag 0DUG,
definition-categorical-quotient
(blueprint: lem-sfb-keel-mori-finite-inertia-quotient).

The base is arbitrary. Inertia and every point map are the existing canonical
constructions; no finite-type or reductivity condition is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u v w v' w'

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- A DM stack with finite inertia has a categorical algebraic-space quotient,
separated, quasi-compact, and a homeomorphism after every algebraic-stack base change.
Source: Stacks Project, Tag 0DUT, theorem-keel-mori, restricted to DM stacks over S;
Tag 0DUG, definition-categorical-quotient
(blueprint: lem-sfb-keel-mori-finite-inertia-quotient).

Scheme-test properness of the relative diagonal expresses separatedness: this diagonal
is unramified for a DM stack, so a proper algebraic-space base change is finite and
is a scheme. Quasi-compactness uses the equivalent affine-test, quasi-compact-atlas
criterion. The final clause uses the actual first projection of Z ×_M X and the
smooth-atlas topology on its field-object quotient, for arbitrary algebraic stacks Z.
The test universes include the scheme and source universes and admit further enlargement.

Proof:
1. The etale atlas of $\mathcal X$ is smooth by [lem-sfb-stack-chartwise-smooth-etale-calculus],
so [lem-sfb-etale-smooth-atlas-fppf-descent] applies to the given etale stack and makes it an
algebraic stack in the fppf convention of the source. Apply
[lem-sfb-finite-inertia-local-affine-covers] to obtain a set-indexed covering $g_i:\mathcal
X_i\to\mathcal X$ of separated, representable, etale maps preserving all automorphism sheaves;
each $\mathcal X_i$ has a finite flat affine cover. The inertia hypothesis is exactly the finite
inertia projection assumed in the statement. Keep the family within the size universe in
[def-weil-size-convention].

2. For every $i$ apply [lem-sfb-finite-flat-affine-stack-invariant-quotient] to the chosen finite
flat affine cover. This constructs $f_i:\mathcal X_i\to M_i$, with $M_i$ an affine $S$-scheme, by
the equalizer ring of the two maps on functions. It is a uniform categorical morphism for all
algebraic-space targets, and is separated, quasi-compact and a universal homeomorphism. In
particular we use the all-algebraic-spaces assertion of the lemma, not just categoricality for
affine targets.

3. Put $\mathcal X_{ij}=\mathcal X_i\times_{\mathcal X}\mathcal X_j$. It is DM by
[lem-sfb-dm-etale-atlas-calculus]; its projections are representable etale by
[lem-sfb-stack-chartwise-smooth-etale-calculus] and separated by
[lem-sfb-stack-coarse-properties-etale-locality]. They preserve automorphism sheaves: an
automorphism of $(x_i,x_j,\phi)$ is a pair $(a_i,a_j)$ with $\phi g_i(a_i)=g_j(a_j)\phi$ by
[def-sfb-stable-pointed-moduli-groupoids]. Given $a_i$, the isomorphism of automorphism sheaves
for $g_j$ gives exactly one $a_j$ solving that equation. The same argument with $i,j$ interchanged
works for the other projection, over every scheme and compatibly with pullback. Thus the
hypotheses of the etale comparison lemma hold for both projections.

4. Apply [lem-sfb-affine-stack-stabilizer-etale-comparison] to $\mathcal X_{ij}\to\mathcal X_i$.
It gives a scheme $N_i$ separated etale over $M_i$, with $\mathcal X_{ij}\simeq
N_i\times_{M_i}\mathcal X_i$. Etale maps are flat by
[lem-sfb-stack-chartwise-smooth-etale-calculus], so the uniform categoricality of $f_i$ in
[lem-sfb-finite-flat-affine-stack-invariant-quotient] makes $\mathcal X_{ij}\to N_i$ uniform
categorical. Do the same over $j$, obtaining $N_j$. These are categorical moduli spaces of the
same stack, so unique factorization gives inverse maps $N_i\rightleftarrows N_j$; their composites
are identities because this is true after precomposition from $\mathcal X_{ij}$. Denote the
identified scheme by $M_{ij}$ and the map by $f_{ij}$. We have both cartesian squares and
separated etale maps $M_{ij}\to M_i,M_j$.

5. For $\mathcal X_{ijk}=\mathcal X_{ij}\times_{\mathcal X_j}\mathcal X_{jk}$ the already obtained
squares identify its map to $M_{ij}\times_{M_j}M_{jk}$ with a flat base change of $f_j$, so it is
categorical by [lem-sfb-finite-flat-affine-stack-invariant-quotient]. The map to $\mathcal X_{ik}$
forgetting the middle object, followed by $f_{ik}$, therefore descends uniquely to
$M_{ij}\times_{M_j}M_{jk}\to M_{ik}$. Likewise the diagonal $\mathcal X_i\to\mathcal X_{ii}$
descends to $M_i\to M_{ii}$, and swapping the factors descends to $M_{ij}\to M_{ji}$. Their source
and target identities hold after precomposition with the categorical maps, hence hold by
uniqueness. Form the schemes $U=\coprod_i M_i$ and $R=\coprod_{i,j}M_{ij}$ using
[lem-weil-pbc-scheme-coproduct-family]. These operations define identity, inverse and composition
on the pre-relation $R\to U\times_SU$. The maps $s,t$ are etale, as this holds on each disjoint
open component by [lem-sfb-stack-chartwise-smooth-etale-calculus].

6. Fix an algebraically closed field $K$ over $S$. By
[lem-sfb-stack-universal-homeomorphism-geometric-points] applied to $f_i$ and its base changes,
$M_i(K)=\pi_0\mathcal X_i(K)$ and $M_{ij}(K)=\pi_0\mathcal X_{ij}(K)$. For the latter, use that
$f_{ij}$ is a base change of $f_i$ by step 4 and
[lem-sfb-finite-flat-affine-stack-invariant-quotient]. The 2-fibre product formula of
[def-sfb-stable-pointed-moduli-groupoids] gives a surjection $\pi_0\mathcal
X_{ij}(K)\to\pi_0\mathcal X_i(K)\times_{\pi_0\mathcal X(K)}\pi_0\mathcal X_j(K)$: choose an
isomorphism between the two images. It is injective because, after choosing isomorphisms of the
endpoints, the discrepancy between the chosen comparison isomorphisms is an automorphism of their
image in $\mathcal X(K)$, and the automorphism-sheaf isomorphism for $g_i$ uniquely lifts it and
corrects one endpoint isomorphism. Consequently $R(K)\to U(K)^2$ is precisely the kernel
equivalence relation of $U(K)\to\pi_0\mathcal X(K)$. Applying
[lem-sfb-unramified-geometric-equivalence-relation] with the operations of step 5 makes $R\to
U\times_SU$ a monomorphic etale equivalence relation on all test schemes.

7. Apply [lem-trf-etale-relation-quotient] to the schemes $R,U$ of steps 5--6. Define $M$ as the
big-fppf sheafification of $T\mapsto U(T)/R(T)$, rather than the presheaf quotient itself. The
cited theorem makes $M$ an algebraic space over $S$, gives a surjective etale map $U\to M$, and
identifies $R\simeq U\times_MU$. In particular, its sections over schemes lift to $U$ etale
locally. By [lem-weil-pbc-scheme-coproduct-family] the maps $M_i\to U$ identify disjoint open
components. Restricting the kernel-pair equality to the components $M_i,M_j$ gives $M_{ij}\simeq
M_i\times_M M_j$. Hence the two composites $M_{ij}\to M_i\to M$ and $M_{ij}\to M_j\to M$ agree,
supplying the overlap equality used in the next step. The family $\{M_i\to M\}$ is therefore a
jointly surjective etale scheme cover.

8. Construct $p:\mathcal X\to M$ on $x\in\mathcal X(T)$. Put $T_i=T\times_{\mathcal X}\mathcal
X_i$; these are algebraic spaces etale over $T$. Their images cover $T$: for a field-valued point
of $T$, the covering of $|\mathcal X|$ supplies a lift to some $\mathcal X_i$ after common field
extension and an isomorphism to the pullback of $x$. This is an object of the 2-fibre product by
[def-sfb-stable-pointed-moduli-groupoids]. The field-extension lifting clause of
[lem-sfb-stack-chartwise-smooth-etale-calculus] thus gives joint surjectivity after base change.
Refine the $T_i$ by etale scheme atlases using [lem-sfb-dm-etale-atlas-calculus]; compositions are
etale by the chartwise calculus. On these refinements use $T_i\to\mathcal
X_i\xrightarrow{f_i}M_i\to M$. The two maps agree on overlaps through $M_{ij}\to M$ by steps 4 and
7. Since $M$ is a sheaf by [def-trf-algebraic-space], they glue uniquely to $p(x):T\to M$.
Pullback along $T'\to T$ has the same restrictions, so uniqueness proves base-change
compatibility. An isomorphism $x\simeq x'$ also gives identical restrictions, hence identical
maps. This defines an $S$-morphism of stacks restricting to $f_i$ followed by $M_i\to M$.

9. The square for $\mathcal X_i\to\mathcal X$ above $M_i\to M$ is cartesian. Indeed, pull the
comparison $h_i:\mathcal X_i\to M_i\times_M\mathcal X$ back along $\mathcal X_j\to\mathcal X$. Its
source is $\mathcal X_{ij}$, and its target is $M_i\times_M\mathcal
X_j\simeq(M_i\times_MM_j)\times_{M_j}\mathcal X_j\simeq M_{ij}\times_{M_j}\mathcal X_j$, which is
$\mathcal X_{ij}$ by [lem-sfb-affine-stack-stabilizer-etale-comparison] and
[lem-trf-etale-relation-quotient]. The resulting functor is the canonical equivalence from that
square. These equivalences imply that $h_i$ is fully faithful: on each scheme test, arrows lift
uniquely on the covering refinements from step 8 and glue uniquely because isomorphisms form
sheaves. For any object of its target, the local preimages have unique overlap isomorphisms
inducing its descent isomorphisms; full faithfulness forces the cocycle, and effective object
descent in [def-sfb-stable-pointed-moduli-groupoids] glues them to a preimage. Thus $h_i$ is an
equivalence. This establishes the square without a geometric isomorphism criterion.

10. Under the cartesian identifications of step 9, the base change of $p$ by $M_i\to M$ is $f_i$.
Each $f_i$ is separated, quasi-compact, and a universal homeomorphism by
[lem-sfb-finite-flat-affine-stack-invariant-quotient]. The target-cover criterion
[lem-sfb-stack-coarse-properties-etale-locality] therefore gives all three properties for $p$. Its
universal-homeomorphism conclusion is tested after arbitrary algebraic-stack base change, exactly
as required in the item, not merely on schemes or geometric points.

11. Let $Z/S$ be any algebraic space and $a:\mathcal X\to Z$ an $S$-map. The categoricality of
each $f_i$ gives a unique $b_i:M_i\to Z$ with $b_if_i=a g_i$. Over $M_{ij}$, the two restrictions
of $b_i,b_j$ have the same composite with $f_{ij}$, namely the restriction of $a$ to $\mathcal
X_{ij}$. By its categoricality from the flat-base-change clause of
[lem-sfb-finite-flat-affine-stack-invariant-quotient], these restrictions are equal. They
therefore glue uniquely over the etale cover $\{M_i\to M\}$ to $b:M\to Z$, since an algebraic
space is an etale sheaf [def-trf-algebraic-space]. On the covering refinements of step 8, $bp=a$
by construction, so equality follows from the same sheaf condition.

12. If $b^\prime:M\to Z$ is another $S$-map with $b^\prime p=a$, its restriction to $M_i$ has
composite $a g_i$ with $f_i$, hence equals $b_i$ by
[lem-sfb-finite-flat-affine-stack-invariant-quotient]. The sheaf condition of
[def-trf-algebraic-space] on $\{M_i\to M\}$ gives $b^\prime=b$. Thus composition with $p$ is the
stated bijection. All constructions and gluings were over $S$, and no finite-type, Noetherian, or
stabilizer reductivity assumption was used. -/
theorem exists_keelMori_finiteInertia_quotient {S : Scheme.{u}}
    (X : BasedCategory.{v, w} (Over S)) (hX : IsDeligneMumfordModuliStack X)
    (hfinite : IsRepresentableFiniteModuliMap (moduliInertiaProjection X)) :
    ∃ (M : AlgebraicSpace S) (p : BasedFunctor X (discreteModuli M.obj.obj)),
      (∀ Z : AlgebraicSpace S,
        Function.Bijective (fun a : M.obj.obj ⟶ Z.obj.obj ↦ p.comp (discreteModuliMap a))) ∧
      ModuliSchemeTest @IsProper (moduliRelativeDiagonal p) ∧
      IsQuasiCompactModuliMap p ∧
      (∀ (Z : BasedCategory.{max u v v', max (u + 1) w w'} (Over S))
        (a : BasedFunctor Z (discreteModuli M.obj.obj)),
        IsAlgebraicModuliStack Z → IsHomeomorph (moduliPointMap (moduliTwoFiberFst a p))) := by
  sorry

end CategoryTheory
