/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil SHEAF project
-/
module

public import Mathlib.Algebra.Category.Ring.Under.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import WeilConjectures.RingTheory.IntegralOverHenselianPair
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Elkik equivalence for finite algebras étale away from an ideal

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé V, Theorem 1.2.4,
printed p.64 (Elkik, Théorème 5)
(blueprint: lem-per-elkik-finite-etale-away-completion).

The categories are full subcategories of commutative algebras, represented by `Under`.
The base-change functor is Mathlib's `CommRingCat.tensorProd`, restricted by
`ObjectProperty.lift`; its landing proof and equivalence are asserted together.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace CommRingCat

/-- Finite commutative algebras whose spectrum is étale over the complement of `V(I)`.
Source: ILO, Exposé V, Theorem 1.2.4, printed p.64
(blueprint: lem-per-elkik-finite-etale-away-completion).
This predicate defines the full subcategory, retaining all algebra homomorphisms. -/
def finiteEtaleAwayProperty (B : CommRingCat.{u}) (I : Ideal B) :
    ObjectProperty (Under B) :=
  fun C => Module.Finite B C ∧
    Etale (morphismRestrict (Spec.map C.hom)
      ⟨(PrimeSpectrum.zeroLocus (I : Set B))ᶜ,
        (PrimeSpectrum.isClosed_zeroLocus (I : Set B)).isOpen_compl⟩)

/-- Completion induces an equivalence on finite algebras étale away from `V(I)`,
and every such completed algebra is a scalar extension of one over `B`.
Source: ILO, Exposé V, Theorem 1.2.4, printed p.64 (Elkik, Théorème 5)
(blueprint: lem-per-elkik-finite-etale-away-completion).

Proof:
1. For every finite $B$-algebra $C$ in the source category, tensoring a finite list of module
generators with $\widehat B$ gives generators of $\widehat B\otimes_B C$. Apply
[lem-weil-pbc-etale-scheme-base-change] to the etale restriction over the complement of $V(I)$;
its inverse image is the complement of $V(I\widehat B)$. Thus base change defines the stated
functor on objects and algebra homomorphisms. By [lem-weil-pbc-completion-finite-module-tensor]
its value is canonically $C^\wedge$. This is an algebra isomorphism: on pure tensors the
comparison is $a\otimes c\mapsto a\iota_C(c)$, which preserves units and products, and it is
natural in $C$.
2. Let $C_1,C_2$ be objects of the source category. A finite module generating set also
generates the algebra, so each $C_i$ is of finite type over $B$ and is Noetherian by
[lem-weil-pbc-finite-type-algebra-noetherian]. It is integral over $B$ by
[lem-weil-pbc-finite-algebra-is-integral]; hence $(C_2,IC_2)$ is henselian by
[lem-weil-pbc-integral-over-henselian-pair]. Apply [lem-per-etale-away-completion-hom-lifting]
with $A=B,D=C_1,C=C_2$. Every map $C_1^\wedge\to C_2^\wedge$ lifts uniquely to $C_1\to C_2$. In
particular this holds for the $\widehat B$-linear maps in the target category, and the
completion of the lift is the given map. Conversely every completed $B$-algebra map is $\widehat
B$-linear, as is seen coordinatewise modulo $I^n$. The identifications in Step 1 therefore give
bijections on the required Hom sets; the functor is fully faithful.
3. Let $E$ be an object of the target category. The ring $\widehat B$ is Noetherian by
[lem-weil-pbc-adic-completion-noetherian] and is $I$-adically complete by
[lem-weil-pbc-module-completion-complete] applied to $M=B$. Apply
[lem-per-completed-etale-jacobian-torsion] over $A=\widehat B$ and ideal $I\widehat B$. This
gives a completed polynomial presentation of $E$ whose conormal differential has kernel and
cokernel annihilated by a fixed power of $I$, as well as completeness of $E$. The same
presentation is over $B[x_1,\ldots,x_r]^\wedge$: [lem-weil-pbc-adic-completion-mod-power] gives
$B/I^n=\widehat B/I^n\widehat B$, hence the polynomial quotient rings at every level agree.
Taking their inverse limits identifies the two completed polynomial rings, their continuous
partial derivatives, the kernel ideal $J$, and the displayed conormal differential. Thus its
torsion bound is the one needed over $B$.
4. Apply [lem-per-rig-etale-jacobian-algebraization] to the completed presentation over $B$ from
Step 3. It gives a finite type $B$-algebra $D$, etale away from $V(I)$, and a $B$-algebra
isomorphism $D^\wedge\cong E$. By [lem-weil-pbc-module-completion-complete] for the Noetherian
ring $D$ (Noetherian by [lem-weil-pbc-finite-type-algebra-noetherian]), reduction of this
isomorphism gives $D/ID\cong E/IE$. This is finite as a $B/I$-module: reduce module generators
for $E$ over $\widehat B$ and use $\widehat B/I\widehat B=B/I$ from Step 3.
5. Put $X=\operatorname{Spec}D$. Its map to $\operatorname{Spec}B$ is affine, hence separated by
[lem-weil-pbc-affine-morphism-permanence], and of finite type. The whole closed fibre
$X_0=\operatorname{Spec}(D/ID)$ is finite over $B/I$ by Step 4, hence proper by
[lem-per-affine-proper-finite]. Apply [lem-per-henselian-pair-proper-clopen-lift] with $Y=X_0$.
It produces an open and closed $W\subseteq X$, proper over $B$, with $W_0=X_0$. The inclusion
$W\to X$ is a homeomorphism onto a closed subset, so is affine by
[lem-trf-closed-embedding-affine]; since $X$ is affine, $W$ is affine by
[lem-weil-pbc-affine-morphism-permanence]. Write $W=\operatorname{Spec}C$. A morphism between
affine schemes is affine by the inverse-image description on basic affine opens. Since $W$ is
proper over $B$, [lem-per-affine-proper-finite] shows that $C$ is a finite $B$-module. Over the
complement of $V(I)$ the inclusion of $W$ is an open immersion and the structure map of $X$ is
etale. Parts (1) and (2) of [lem-weil-pbc-etale-composition-cancellation] therefore show that
their composite, the structure map of $W$ there, is etale.
6. For each $n\geq1$, every prime of $D$ containing $I^nD$ contains $ID$. Since $W$ contains all
of $X_0$, the inverse image of $W$ in $\operatorname{Spec}(D/I^nD)$ is its whole underlying
space. As $W\to X$ is an open immersion with restricted structure sheaf, this inverse image is
the whole scheme. Thus restriction gives compatible ring isomorphisms $D/I^nD\cong C/I^nC$.
Their inverse limit identifies $D^\wedge\cong C^\wedge$ as $B$-algebras. Step 1 identifies
$C^\wedge$ with $\widehat B\otimes_B C$; the composite with Step 4 gives the desired isomorphism
to $E$. All these maps are $\widehat B$-linear: modulo $I^n$ their scalar action is through
$B/I^n$, and equality in the inverse limit is coordinatewise. This proves essential
surjectivity. Together with Step 2 it yields the equivalence: choose a representative $C$ and
such an isomorphism for each $E$, and lift morphisms by the Hom bijections; uniqueness enforces
identities and composition. The stated particular conclusion is the object assertion just
established. -/
theorem elkik_finiteEtaleAway_completion
    (B : CommRingCat.{u}) [IsNoetherianRing B] (I : Ideal B) [HenselianRing B I] :
    ∃ h : ∀ C : (finiteEtaleAwayProperty B I).FullSubcategory,
      finiteEtaleAwayProperty (CommRingCat.of (AdicCompletion I B))
        (I.map (algebraMap B (AdicCompletion I B)))
        ((tensorProd B (CommRingCat.of (AdicCompletion I B))).obj C.obj),
      ((finiteEtaleAwayProperty (CommRingCat.of (AdicCompletion I B))
          (I.map (algebraMap B (AdicCompletion I B)))).lift
        ((finiteEtaleAwayProperty B I).ι ⋙
          tensorProd B (CommRingCat.of (AdicCompletion I B))) h).IsEquivalence ∧
      ∀ E : (finiteEtaleAwayProperty (CommRingCat.of (AdicCompletion I B))
          (I.map (algebraMap B (AdicCompletion I B)))).FullSubcategory,
        ∃ C : (finiteEtaleAwayProperty B I).FullSubcategory,
          Nonempty ((tensorProd B (CommRingCat.of (AdicCompletion I B))).obj C.obj ≅ E.obj) := by
  sorry

end CommRingCat
