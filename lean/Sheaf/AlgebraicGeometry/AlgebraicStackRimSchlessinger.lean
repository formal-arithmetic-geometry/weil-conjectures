/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Sheaf.AlgebraicGeometry.SpaceAffineThickeningPushout
import Sheaf.AlgebraicGeometry.EtaleSmoothAtlasFppfDescent
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Rim--Schlessinger gluing for algebraic stacks

Source: Stacks Project, artin.tex, Tags 07WQ, 07WP and 07WN
(blueprint: lem-sfb-algebraic-stack-rim-schlessinger).

We use the total-category formulation of the equivalence on fibre groupoids.
An object on the overlap with its two lifted arrows encodes the specified gluing
isomorphism. A pushout of these arrows encodes gluing and its full universal property,
including the unique gluing of compatible isomorphisms. No cleavage is chosen.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- An algebraic stack satisfies Rim--Schlessinger gluing over a Noetherian affine base.
The spectra of `A`, `B`, `C`, `D` are respectively `Z`, `T`, `Z'`, `T'`.
The surjective map `q` with nilpotent kernel presents the specified nilpotent closed
immersion `j`. The four structure maps are arbitrary finite-type scheme morphisms.

The conclusion is the total-category form of the canonical restriction equivalence:
`x`, `a`, `b` encode the triple with its specified overlap isomorphism. Every arrow
in a fibred groupoid is cartesian, so such spans represent exactly all these triples.
The equations and universal property in `IsPushout a b c d` retain that isomorphism
and give unique gluing of arrows, including all automorphisms. Conversely equivalence
of the fibre restriction functor gives this universal property: for a target over
any base `Q`, glue the two base maps using the base pushout, pull the target back to
`T'`, and apply full faithfulness in that fibre. Thus the formulation neither chooses
an unrelated equivalence nor asserts only existence of isomorphism classes.

Source: Stacks Project, artin.tex, Tag 07WQ (lemma-algebraic-stack-RS), using condition
(RS) of Tag 07WP and Tag 07WN (lemma-pushout)
(blueprint: lem-sfb-algebraic-stack-rim-schlessinger).

Proof:
1. Put $P=T'$. The map $Z\to T$ is affine, since both schemes are affine. Write
$Z'=\operatorname{Spec}A'$ and $Z=\operatorname{Spec}(A'/I)$, with $I^N=0$. Every prime of $A'$
contains $I$: if $x\in I$, then $x^N=0$ lies in the prime, so primality gives $x$ in it. The
quotient-spectrum homeomorphism therefore makes $Z\to Z'$ a thickening. The geometric pushout
theorem identifies the given scheme pushout $P$ with the algebraic-space pushout of $T$ and $Z'$
along $Z$, and makes $T\to P$ a thickening. All identifications fix the original cocone maps, by
uniqueness of pushouts. Uses: lem-weil-pbc-morphism-affine-schemes-affine, def-weil-closed-
immersion, lem-weil-pbc-spec-quotient-homeomorphism-zero-locus, lem-sfb-space-affine-thickening-
pushout.

2. We will also use this universal property after every flat scheme map $B\to P$. Set
$T_B=B\times_PT$, $Z'_B=B\times_PZ'$, $Z_B=B\times_PZ$. The flat counit of scheme pushout
patching says exactly that $B$ is the scheme pushout $T_B\amalg_{Z_B}Z'_B$. The map $Z_B\to
Z'_B$ is a thickening by base change, and $Z_B\to T_B$ is affine by affine base change. Thus the
geometric pushout theorem makes this square a pushout for algebraic-space targets too. This
argument requires no finite-presentation hypothesis on $B\to P$. Uses: lem-sfb-scheme-pushout-
flat-patching, lem-sfb-space-thickening-base-change, lem-weil-pbc-affine-morphism-permanence,
lem-sfb-space-affine-thickening-pushout.

3. The etale-stack convention for $\mathcal X$ has fppf descent by the smooth-atlas descent
theorem. For any flat $B\to P$ and $c,d\in\mathcal X(B)$, that theorem also identifies
$I=\operatorname{Isom}_B(c,d)$ as an algebraic space over $B$. Compatible isomorphisms on $T_B$
and $Z'_B$ are compatible sections of $I$ on those schemes. Step 2 glues their underlying maps
uniquely to $s:B\to I$. Its composite to $B$ restricts to the original cocone maps, so the same
pushout uniqueness, now with target $B$, gives $s$ a section. This establishes bijectivity on
every isomorphism set, hence full faithfulness of the restriction functor for every flat $B\to
P$, including $B=P$. Uses: def-sfb-algebraic-moduli-stack, lem-sfb-etale-smooth-atlas-fppf-
descent.

4. Fix a triple $(a,b,\phi)$ as in the statement and choose a smooth surjective scheme atlas
$U\to\mathcal X$. By its definition, $V=T\times_{a,\mathcal X}U$ and $W=Z'\times_{b,\mathcal
X}U$ are algebraic spaces smooth and surjective over $T,Z'$. Their objects over a test scheme
consist of a base map, a map to $U$, and an isomorphism to the pulled-back object $a$ or $b$.
Composing that isomorphism with $\phi$ identifies $V\times_TZ$ with $W\times_{Z'}Z$; call this
common space $H$. This identification retains the map to $U$, so the two projections $H\to U$
agree. Smoothness gives flatness and local finite presentation of both $V\to T$ and $W\to Z'$.
Uses: def-sfb-algebraic-moduli-stack, def-sfb-stable-pointed-moduli-groupoids, lem-sfb-stack-
chartwise-smooth-etale-calculus.

5. Form the geometric pushout $V'=V\amalg_HW$. Its canonical restrictions to $T,Z'$ recover
$V,W$, with precisely the chosen identification over $Z$. The theorem also makes $V\to V'$ a
thickening. Since the maps $V\to U$ and $W\to U$ agree on $H$, the pushout universal property
produces a unique map $V'\to U$. Only these stated geometric properties of the pushout are used
here; the flat scheme chart in the next step will provide the covering needed for descent. Uses:
lem-sfb-space-affine-thickening-pushout.

6. Choose a surjective etale scheme chart $V_1\to V$. The compatible-chart theorem supplies a
surjective etale scheme chart $W_1\to W$, an identified overlap $H_1=V_1\times_TZ\cong
W_1\times_{Z'}Z$, and a scheme $E=V_1\amalg_{H_1}W_1$ with a surjective etale map $E\to V'$. The
maps $V_1\to T$ and $W_1\to Z'$ are smooth by composition of an etale map with a smooth map;
hence they are flat and locally finitely presented. Scheme pushout patching therefore says $E\to
P$ is flat and locally finitely presented. The maps $T\to P$ and $V\to V'$ are thickenings, so
their maps on point spaces are onto; since $V\to T$ is surjective, $V'\to P$ is surjective.
Consequently $E\to P$ is surjective as well and is an fppf covering. This is why no additional
smooth-pushout lemma is needed. Uses: def-trf-algebraic-space, lem-sfb-space-pushout-compatible-
etale-charts, lem-sfb-stack-chartwise-smooth-etale-calculus, lem-sfb-scheme-pushout-flat-
patching, def-pc-fppf-site.

7. Pull the atlas object in $\mathcal X(U)$ back along $E\to V'\to U$, obtaining $c\in\mathcal
X(E)$. By the defining triple description of $V,W$, their tautological isomorphisms identify the
restrictions of $c$ to $E\times_PT$ and $E\times_PZ'$ with the restrictions of $a,b$. On
$E\times_PZ$ those identifications commute with $\phi$, because the identification of $H$ was
defined by composition with $\phi$ and the pushout recovery maps preserve it. Thus $c$ maps to
the specified triple over $E$, with an isomorphism of triples, not just equality of isomorphism
classes. Uses: def-sfb-stable-pointed-moduli-groupoids, lem-sfb-space-affine-thickening-pushout.

8. On $E_2=E\times_PE$, the two pullbacks of $c$ have images canonically isomorphic through the
fixed triple $(a,b,\phi)$. The map $E_2\to P$ is flat, and likewise $E_3=E\times_PE\times_PE\to
P$ is flat, by base change and composition of flat maps. Step 3 therefore lifts the isomorphism
on $E_2$ uniquely to an isomorphism between those pullbacks of $c$. Its inverse and its cocycle
equality on $E_3$ follow by faithfulness, since their images are the inverse and cocycle of the
fixed triple. Effective fppf descent yields $c_0\in\mathcal X(P)$. The compatible
identifications with $a$ and $b$ descend along the base changes of the fppf cover $E\to P$,
using the fppf sheaf property for isomorphisms. Their compatibility with $\phi$ is an equality
of sections and holds after that cover, hence holds globally. Thus $c_0$ maps to the given
triple. Essential surjectivity together with Step 3 proves the equivalence. No finiteness or
separation of $\mathcal X\to S$ was used. Uses: lem-sfb-stack-chartwise-smooth-etale-calculus,
lem-sfb-etale-smooth-atlas-fppf-descent. -/
theorem algebraicModuliStack_rimSchlessinger
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (F : BasedCategory.{v, w} (Over (Spec (.of R)))) (hF : IsAlgebraicModuliStack F)
    (A B C D : CommRingCat.{u})
    [IsLocalRing A] [IsArtinianRing A] [IsLocalRing B] [IsArtinianRing B]
    [IsLocalRing C] [IsArtinianRing C] [IsLocalRing D] [IsArtinianRing D]
    (sA : Spec A ⟶ Spec (.of R)) (sB : Spec B ⟶ Spec (.of R))
    (sC : Spec C ⟶ Spec (.of R)) (sD : Spec D ⟶ Spec (.of R))
    [LocallyOfFiniteType sA] [QuasiCompact sA] [LocallyOfFiniteType sB] [QuasiCompact sB]
    [LocallyOfFiniteType sC] [QuasiCompact sC] [LocallyOfFiniteType sD] [QuasiCompact sD]
    (q : C ⟶ A) (hq : Function.Surjective q.hom) (hn : IsNilpotent (RingHom.ker q.hom))
    (i : Over.mk sA ⟶ Over.mk sB) (j : Over.mk sA ⟶ Over.mk sC)
    (hj : j.left = Spec.map q)
    (k : Over.mk sB ⟶ Over.mk sD) (l : Over.mk sC ⟶ Over.mk sD)
    (hsq : IsPushout i j k l)
    (x : Functor.Fiber F.p (Over.mk sA)) (y : Functor.Fiber F.p (Over.mk sB))
    (z : Functor.Fiber F.p (Over.mk sC))
    (a : x.val ⟶ y.val) (b : x.val ⟶ z.val)
    (ha : F.p.IsHomLift i a) (hb : F.p.IsHomLift j b) :
    ∃ (t : Functor.Fiber F.p (Over.mk sD)) (c : y.val ⟶ t.val) (d : z.val ⟶ t.val),
      F.p.IsHomLift k c ∧ F.p.IsHomLift l d ∧ IsPushout a b c d := by
  sorry

end CategoryTheory
