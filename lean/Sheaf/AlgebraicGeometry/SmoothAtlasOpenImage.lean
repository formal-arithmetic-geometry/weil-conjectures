/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatLfpUniversallyOpen
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Open images of restricted smooth atlases

Source: Stacks Project, stacks-properties.tex, Tag 05UP (lemma-open-image-substack);
morphisms.tex, Tag 01VC; criteria.tex, Tag 076V
(blueprint: lem-sfb-smooth-atlas-open-image).

The range formula uses all representable étale scheme charts of the actual space
base change. Their scheme-point images form precisely its image in the test scheme.
The representing equivalence retains the projection to that scheme.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- Restricting a smooth atlas to an open subscheme gives a smooth map whose image
is an algebraic open substack, and a smooth surjective atlas of that substack.
Source: Stacks Project, stacks-properties.tex, Tag 05UP; morphisms.tex, Tag 01VC;
criteria.tex, Tag 076V (blueprint: lem-sfb-smooth-atlas-open-image).

Proof:
1. Put $g=p\circ j$. The open immersion $j$ is etale by
[lem-weil-pbc-etale-composition-cancellation](1), hence smooth by
[lem-sfb-stack-chartwise-smooth-etale-calculus]. It is representable by schemes: its scheme
pullbacks are the inverse-image open subschemes. The composition assertion of the same calculus
node, applied to $j$ and $p$, makes $g$ representable by algebraic spaces and smooth.
2. For a scheme $T$ and $x:T\to\mathcal X$, let $E_x=V\times_{\mathcal X,x}T$ and $a_x:E_x\to T$.
Representability of $g$ makes $E_x$ an algebraic space. Base change in
[lem-sfb-stack-chartwise-smooth-etale-calculus] makes $a_x$ smooth, hence flat and locally of
finite presentation. Thus [lem-sfb-flat-lfp-space-universally-open] shows that
$I_x=\operatorname{im}(|E_x|\to|T|)$ is open. Endow $I_x\subseteq T$ with its open subscheme
structure [def-weil-open-immersion].
3. For $h:T\prime\to T$, reassociating the triples in the 2-fibre product
[def-sfb-stable-pointed-moduli-groupoids] gives $E_{x h}\simeq E_x\times_TT\prime$, compatibly
with projection to $T\prime$. The point-image formula of [lem-a1-space-point-open-calculus] gives
$I_{x h}=h^{-1}(I_x)$ as subsets, hence as open subschemes. An isomorphism $x\simeq y$ induces an
isomorphism $E_x\simeq E_y$ over $T$, so $I_x=I_y$. These equalities hold for arbitrary scheme
maps, not just etale ones.
4. Define $\mathcal W(T)$ as the full subgroupoid of $\mathcal X(T)$ on objects $x$ with $I_x=T$,
equivalently $a_x$ surjective on points. Step 3 makes this predicate invariant under isomorphism
and stable under pullback, so it defines a strictly full fibred subcategory. It is an etale
substack: isomorphism sheaves are those of $\mathcal X$; a descent datum descends in $\mathcal X$
to $x$, and its restrictions lie in $\mathcal W$ exactly when the inverse images of $I_x$ on the
jointly surjective etale cover are the whole cover members. This forces $I_x=T$. These are
precisely the stack conditions of [def-sfb-stable-pointed-moduli-groupoids].
5. For a scheme test $x:T\to\mathcal X$, an object of $T\times_{\mathcal X}\mathcal W$ over
$T\prime$ is $(h:T\prime\to T,w,\alpha:xh\simeq w)$. Step 3 makes its existence equivalent to
$h^{-1}(I_x)=T\prime$, or $h(T\prime)\subseteq I_x$. By
[lem-weil-pbc-morphism-factors-through-open-subscheme], this is equivalent to a unique
factorization through $I_x$. For fixed $h$, any two pairs $(w,\alpha)$ have exactly one arrow
respecting their comparison maps, namely $\alpha\prime\alpha^{-1}$, because $\mathcal W$ is full.
Taking $w=xh$ gives a preferred pair whenever the predicate holds. This identifies the fibre
product with the discrete fibred groupoid of $I_x$, compatibly with pullbacks. Thus $\mathcal
W\to\mathcal X$ is representable by open immersions, and its scheme pullback is exactly the
asserted open image.
6. The diagonal section of $V\times_{\mathcal X}V\to V$, given by $(v,v,\mathrm{id}_{g(v)})$,
proves $I_g=V$. Thus the object $g\in\mathcal X(V)$ belongs to $\mathcal W(V)$ and supplies
$q:V\to\mathcal W$ with composite $g$. For any scheme $T\to\mathcal W$ with underlying object $x$,
full faithfulness identifies $V\times_{\mathcal W}T$ with $E_x$: the isomorphism of images in
$\mathcal X$ is already an isomorphism in $\mathcal W$. Hence this is an algebraic space and its
projection is the smooth $a_x$ of step 2. It is surjective since $x\in\mathcal W(T)$ means
$I_x=T$. Therefore $q$ is representable, smooth and surjective by the scheme-test definitions.
7. For schemes $A,B\to\mathcal W$, full faithfulness also identifies $A\times_{\mathcal W}B$ with
$A\times_{\mathcal X}B$. The latter is an algebraic space: it is a scheme pullback of the
representable diagonal of $\mathcal X$. Thus the diagonal of $\mathcal W$ is representable by
algebraic spaces. Together with the etale-stack condition from step 4 and the smooth surjective
scheme atlas $q$ from step 6, this proves algebraicity in the statement's convention. If $V$ is
empty, every $E_x$ and $I_x$ is empty; consequently $\mathcal W$ is the empty open substack and
$q$ is the empty atlas. If $V=U$, the atlas hypothesis gives $I_x=T$ for every $x$, so $\mathcal
W=\mathcal X$. No nonemptiness or quasi-compactness was used.
-/
theorem smooth_atlas_open_image
    {S : Scheme.{u}} (X : BasedCategory.{v, w} (Over S))
    (hX : IsAlgebraicModuliStack X) (U V : Over S)
    (p : BasedFunctor (discreteModuli (yoneda.obj U)) X)
    (hp : IsSmoothModuliAtlas X U p) (j : V ⟶ U) (hj : IsOpenImmersion j.left) :
    IsRepresentableByAlgebraicSpaces ((discreteModuliMap (yoneda.map j)).comp p) ∧
      ModuliSpaceTest @Smooth ((discreteModuliMap (yoneda.map j)).comp p) ∧
      ∃ (W : OpenModuliSubstack X)
        (q : BasedFunctor (discreteModuli (yoneda.obj V)) W.category),
        IsAlgebraicModuliStack W.category ∧ IsSmoothModuliAtlas W.category V q ∧
        Nonempty (ModuliTwoIso (q.comp (fullModuliInclusion X W.property))
          ((discreteModuliMap (yoneda.map j)).comp p)) ∧
        ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) X),
          ∃ (Z : AlgebraicSpace S) (a : Z.obj.obj ⟶ yoneda.obj T)
            (O : Over S) (i : O ⟶ T)
            (e : BasedFunctor (discreteModuli (yoneda.obj O))
              (moduliTwoFiberProduct t (fullModuliInclusion X W.property))),
            HasSpaceBaseChange ((discreteModuliMap (yoneda.map j)).comp p) T t Z a ∧
            IsOpenImmersion i.left ∧ e.toFunctor.IsEquivalence ∧
            Nonempty (ModuliTwoIso
              (e.comp (moduliTwoFiberFst t (fullModuliInclusion X W.property)))
              (discreteModuliMap (yoneda.map i))) ∧
            Set.range i.left = {x : T.left | ∃ (A : Over S)
              (b : yoneda.obj A ⟶ Z.obj.obj), AlgebraicSpace.IsEtale b ∧
                ∃ y : A.left, (yoneda.preimage (b ≫ a)).left y = x} := by
  sorry

end CategoryTheory
