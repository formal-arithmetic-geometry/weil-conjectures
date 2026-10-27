/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q143
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus

/-! # A finite-type field representative with étale self-relation

Source: Stacks Project, stacks-morphisms.tex, Tags 06G3, 06MZ and 06N0,
as combined in the first construction paragraph of Tag 06N3; relative diagonal
convention: Tag 050N(1)
(blueprint: lem-sfb-finite-type-point-etale-self-relation).

The finite-type hypothesis retains a representative of the specified quotient point.
The conclusion retains the algebraic-space self-product, an equivalence with the
actual 2-fibre product, and comparisons with both projections.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- The point class of a field representative is its value on the identity of the
representing field scheme. No choice of a field object or point is made.
Source: Stacks, stacks-properties.tex, underlying points; stacks-morphisms.tex,
Tag 06N3 (blueprint: lem-sfb-finite-type-point-etale-self-relation). -/
def moduliFieldRepresentativePoint {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (K : Type u) [Field K]
    (b : Spec (.of K) ⟶ S)
    (a : BasedFunctor (discreteModuli (yoneda.obj (Over.mk b))) F) : ModuliPoints F :=
  Quot.mk (ModuliFieldRelation F)
    ⟨a.obj (CostructuredArrow.mk (𝟙 (yoneda.obj (Over.mk b)))),
      K, inferInstance, ⟨eqToIso (congrArg Over.left
        (a.w_obj (CostructuredArrow.mk (𝟙 (yoneda.obj (Over.mk b))))))⟩⟩

/-- Every finite-type point of an algebraic stack with unramified relative diagonal
has a locally finite type field representative with two étale self-product projections.
Source: Stacks, stacks-morphisms.tex, Tags 06G3, 06MZ, 06N0 and the first construction
paragraph of Tag 06N3; Tag 050N(1) for the relative convention
(blueprint: lem-sfb-finite-type-point-etale-self-relation).

Proof:
1. Apply the finite-type-point residual-substack lemma to $x$. Obtain a reduced locally
Noetherian algebraic stack $\mathcal Z$ and a representable fully faithful locally finite type
map $i:\mathcal Z\to\mathcal X$, with $|\mathcal Z|$ a singleton mapping to $x$. This
application requires no finiteness condition on the base scheme.
Uses: lem-sfb-finite-type-point-residual-substack.
2. The relative diagonal of $\mathcal Z$ is unramified. Indeed, a map $T\to\mathcal
Z\times_S\mathcal Z$ specifies two objects $u,v\in\mathcal Z(T)$. Its base change of the
diagonal is the sheaf of isomorphisms from $u$ to $v$. Full faithfulness of $i$ on every
$T$-scheme identifies this sheaf, over $T$, with the sheaf of isomorphisms from $i(u)$ to
$i(v)$. The identification sends an isomorphism to its image under $i$; full faithfulness gives
its unique inverse, and pullback compatibility follows because $i$ is a functor over the base.
Thus it is an isomorphism of sheaves over $T$. The latter sheaf is exactly the base change of
$\Delta_{\mathcal X/S}$ by $(i(u),i(v))$, so it is an algebraic space unramified over $T$ by the
assumed meaning of unramified relative diagonal. Thus every scheme test of $\Delta_{\mathcal
Z/S}$ is unramified. This is the test-scheme form of the cartesian diagonal square for a fully
faithful map.
Uses: lem-sfb-finite-type-point-residual-substack, def-sfb-stable-pointed-moduli-groupoids.
3. The stack $\mathcal Z$ now has all hypotheses of the singleton-stack field-cover lemma: it is
algebraic, reduced, locally Noetherian, and has one point, and its relative diagonal is
unramified by step 2. Choose the resulting field $k$ and representable surjective etale morphism
$z:U=\operatorname{Spec}k\to\mathcal Z$. In particular its unique point maps to the unique point
of $|\mathcal Z|$.
Uses: lem-sfb-unramified-diagonal-singleton-field-cover.
4. Put $a=i\circ z:U\to\mathcal X$. It represents $x$, since the only point of $\mathcal Z$ maps
to $x$. The chartwise calculus says etale maps are smooth, smooth maps are locally of finite
presentation, and local finite presentation implies local finite type. Thus $z$ is locally of
finite type. The same calculus gives stability under composition for representable locally
finite type maps, so $a$ is representable and locally of finite type, as required.
Uses: lem-sfb-finite-type-point-residual-substack,
lem-sfb-unramified-diagonal-singleton-field-cover, lem-sfb-stack-chartwise-smooth-etale-calculus.
5. For any $S$-scheme $T$, a $T$-point of $U\times_{\mathcal X}U$ consists of maps $p,q:T\to U$
and an isomorphism $i(zp)\simeq i(zq)$. Full faithfulness of $i$ gives a unique isomorphism
$zp\simeq zq$ in $\mathcal Z(T)$. The same correspondence on arrows is inverse to applying $i$
and commutes with pullback in $T$. It therefore identifies $U\times_{\mathcal X}U$ with
$U\times_{\mathcal Z}U$, preserving both maps to $U$. Both fibre products are algebraic spaces,
by the representable diagonals of $\mathcal X$ and $\mathcal Z$. The inverse correspondence just
constructed therefore gives an isomorphism of algebraic spaces over $U\times_S U$. Each
projection $U\times_{\mathcal Z}U\to U$ is a base change of the etale map $z$. The chartwise
base-change calculus makes both projections etale. Under the displayed identification they are
exactly the two projections asserted in the item. No separability or perfectness assumption on
the chosen field has entered the argument.
Uses: lem-sfb-finite-type-point-residual-substack,
lem-sfb-unramified-diagonal-singleton-field-cover, def-sfb-stable-pointed-moduli-groupoids,
lem-sfb-stack-chartwise-smooth-etale-calculus.
-/
theorem finite_type_point_etale_self_relation {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsAlgebraicModuliStack F)
    (x : ModuliPoints F)
    (hx : ∃ (L : Type u) (_ : Field L) (b : Spec (.of L) ⟶ S)
      (a : BasedFunctor (discreteModuli (yoneda.obj (Over.mk b))) F),
      ModuliSpaceTest @LocallyOfFiniteType a ∧ moduliFieldRepresentativePoint L b a = x)
    (hΔ : HasUnramifiedModuliDiagonal F) :
    ∃ (K : Type u) (_ : Field K) (b : Spec (.of K) ⟶ S)
      (a : BasedFunctor (discreteModuli (yoneda.obj (Over.mk b))) F),
      moduliFieldRepresentativePoint K b a = x ∧ ModuliSpaceTest @LocallyOfFiniteType a ∧
        ∃ (R : AlgebraicSpace S)
          (p q : R.obj.obj ⟶ yoneda.obj (Over.mk b))
          (e : BasedFunctor (discreteModuli R.obj.obj) (moduliTwoFiberProduct a a)),
          e.toFunctor.IsEquivalence ∧
            Nonempty (ModuliTwoIso (e.comp (moduliTwoFiberFst a a)) (discreteModuliMap p)) ∧
            Nonempty (ModuliTwoIso (e.comp (moduliTwoFiberSnd a a)) (discreteModuliMap q)) ∧
            SpaceMapIsEtale R (Over.mk b) p ∧ SpaceMapIsEtale R (Over.mk b) q := by
  sorry

end CategoryTheory
