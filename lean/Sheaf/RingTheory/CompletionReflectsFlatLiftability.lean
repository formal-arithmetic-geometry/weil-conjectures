module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.RingHom.Smooth
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness
import WeilConjectures.RingTheory.SmoothLocalCompleteIntersection
import WeilConjectures.RingTheory.NakayamaNilpotent
import WeilConjectures.Algebra.FiniteTypeLiftNilpotent

/-!
# Completion detects existence of flat algebra lifts

Source: Stacks Project, Tag 0DZ3, `examples-defos.tex`, lemma-lift-equivalence,
with the Artinian deformation specialization and the 0DZ4--0DZ5 small-extension route.
(blueprint: lem-sfb-completion-reflects-flat-liftability)
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Algebra

/-- A marked finite-type flat deformation has a flat algebra lift exactly when its
completion along the inverse image of the special-fibre ideal has one. Base changes are
written with the coefficient algebra on the left, using commutativity of tensor products.
The existential witnesses on the two sides are independent.

Source: Stacks Project, Tag 0DZ3, lemma-lift-equivalence; Tags 0DZ4 and 0DZ5 for
passage from square-zero kernels to general Artinian surjections.
(blueprint: lem-sfb-completion-reflects-flat-liftability)

Proof plan (the reviewed DAG proof):

1. Put $I=\ker(A'\to A)$. By [lem-weil-pbc-artinian-local-noetherian-nilpotent], $A',A$ are
Noetherian and their maximal ideals are nilpotent. Since $I\subseteq\mathfrak m_{A'}$, $I$ is
nilpotent. A field is Noetherian (its only ideals are $0,k$); [lem-weil-pbc-finite-type-algebra-
noetherian] makes $P,Q$ and all finite-variable polynomial rings over $k,A,A'$ Noetherian. Take
a surjection $S=A[x_1,\ldots,x_d]\twoheadrightarrow Q$ and put $S'=A'[x_1,\ldots,x_d]$. These
polynomial algebras are flat over their coefficient rings: tensoring an injection with their
monomial basis gives a direct sum of copies of that injection. Let $K\subset S$ be the inverse
image of $J_Q$, and $K'\subset S'$ its inverse image. Let $K_0$ be their common image in
$k[x_1,\ldots,x_d]$. Thus $K,K'$ are exactly the inverse images of $K_0$ under reduction to $k$.
First prove reverse liftability under the additional assumption $I^2=0$ (steps 4–8); step 3
proves forward liftability without that assumption. Steps 9–10 then treat arbitrary kernels.
Dependencies: lem-weil-pbc-artinian-local-noetherian-nilpotent, lem-weil-pbc-finite-type-
algebra-noetherian.

2. Write $C=\widehat Q$, $T=\widehat S_K$, $T'=\widehat {S'}_{K'}$. Apply [lem-sfb-adic-
completion-flat-deformation-functor] first to $P,J,Q$, and then to the marked polynomial
deformations of $k[x_1,\ldots,x_d]$ along $K_0$. It gives Noetherianity and coefficient-flatness
of $C,T,T'$, the marked special fibre $C\otimes_Ak\cong\widehat P_J$, and the canonical
reduction $T'\otimes_{A'}A\cong T$. Also $S'\to T'$ is flat by [lem-weil-pbc-noetherian-
completion-flat]. Since $S'$ is Noetherian, $K'$ is finitely generated; [lem-weil-pbc-adic-
completion-mod-ideal] gives $S'/K'\cong T'/K'T'$. The finite $S$-module $Q$ is cyclic; [lem-
weil-pbc-completion-finite-module-tensor] identifies $Q\otimes_ST\cong C$. On pure tensors this
map is $q\otimes t\mapsto q t$ in the completion, so it respects products and units. In
particular $T\to C$ is surjective, as extension of the surjection $S\to Q$ (equivalently, every
tensor reduces to $1\otimes t$ after lifting $q$ to $S$).
Dependencies: lem-sfb-adic-completion-flat-deformation-functor, lem-weil-pbc-noetherian-
completion-flat, lem-weil-pbc-adic-completion-mod-ideal, lem-weil-pbc-completion-finite-module-
tensor.

3. The forward implication already follows by completing a given flat lift $Q'/A'$. Its special
fibre is $P$, so [lem-sfb-adic-completion-flat-deformation-functor], applied to $P,J$, supplies
a flat completion $D$ and the canonical marked reduction $D\otimes_{A'}A\cong C$. This uses an
arbitrary flat lift; no finite-type condition on the given $Q'$ is needed for that cited
statement.
Dependencies: lem-sfb-adic-completion-flat-deformation-functor.

4. For each $g\in K'$, let $h$ be its image in $Q$, and $\bar h\in J\subset P$ its special-fibre
image. Set $Q_g=Q[1/h]$. It is $A$-flat by [lem-pc-affine-flat-module-localization-preserves-
flatness]. It is finite type over $A$: adjoin one generator $z$ and the relation $hz=1$ to a
finite presentation by generators. Thus [lem-weil-pbc-finite-type-noetherian-finite-
presentation] makes it finitely presented. Its only fibre over $\operatorname{Spec}A$ is
$P[1/\bar h]$, since every prime of $A$ contains its nilpotent maximal ideal. This fibre is
smooth: its spectrum is $D(\bar h)\subseteq\operatorname{Spec}P\setminus V(J)$, and smoothness
restricts to opens by the affine-local characterization in [def-sbc-smooth-morphisms]. The same
characterization, with [lem-weil-pbc-smooth-ring-map-local-on-cover], identifies its ring map as
smooth; an affine cover by principal opens has a finite subcover because their elements generate
the unit ideal. Hence [lem-weil-pbc-smooth-over-field-local-complete-intersection] makes this
fibre a local complete intersection. These are exactly flatness, finite presentation and
fibrewise complete-intersection hypotheses in [lem-sfb-syntomic-algebra-surjection-lift].
Applied to $A'\twoheadrightarrow A$, it gives an $A'$-flat algebra $E_g$ with $E_g/IE_g\cong
Q_g$.
Dependencies: lem-pc-affine-flat-module-localization-preserves-flatness, lem-weil-pbc-finite-
type-noetherian-finite-presentation, def-sbc-smooth-morphisms, lem-weil-pbc-smooth-ring-map-
local-on-cover, lem-weil-pbc-smooth-over-field-local-complete-intersection, lem-sfb-syntomic-
algebra-surjection-lift.

5. Lift the images of $x_1,\ldots,x_d$ under $S\to Q_g$ to arbitrary elements of $E_g$.
Evaluation gives an $A'$-algebra map $S'\to E_g$. The image of $g$ reduces to a unit. It is
therefore a unit: lift its inverse modulo $IE_g$; their product is $1+u$ with $u$ nilpotent,
inverted by $1-u+\cdots+(-u)^{N-1}$. Evaluation consequently extends to $S'_g\to E_g$. Its
reduction is the prescribed map $S_g\to Q_g$, so $E_g$ as an $S'_g$-module is an $A'$-flat lift
of the localized $S$-module $Q_g$. This verifies every local-lift hypothesis needed below,
including $g$ with nilpotent image, when $Q_g=0$.

6. For the reverse implication, take the given flat $A'$-algebra $D$ with its specified
reduction $D/ID\cong C$. The special fibre is $\widehat P_J$. By [lem-sfb-adic-completion-flat-
deformation-functor], $\widehat P_J$ is Noetherian and complete along $J\widehat P_J$; its
automatic-completeness assertion, now applied to this complete special-fibre algebra, makes $D$
Noetherian and complete along the inverse image $L\subset D$ of $J\widehat P_J$. Lift the
variable images of $S\to Q\to C$ to $D$, obtaining $f:S'\to D$. The ideal $K'$ maps into $L$, so
$f$ extends to $\widehat f:T'\to D$: at level $n$ use $S'/K'^n\to D/L^n$, then take compatible
sequences and the completeness identification $D\cong\varprojlim D/L^n$. Reduction of this map
agrees with $T\to C$ because both maps are the continuous extension of $S\to C$; agreement
follows at each quotient and hence in the separated complete ring $C$. Thus $D$, regarded as a
$T'$-module, is an $A'$-flat lift of $Q\otimes_ST=C$.
Dependencies: lem-sfb-adic-completion-flat-deformation-functor.

7. Under the temporary assumption $I^2=0$, apply [lem-sfb-flat-module-lift-formal-neighbourhood]
to $A'\to S'\to T'$, $K'$, and $M=Q$. Step 1 gives Noetherian polynomial rings, coefficient-
flatness and square-zero $I$; step 2 gives Noetherian $T'$, flat $S'\to T'$, its canonical
scalar reduction, and the required quotient isomorphism modulo $K'$. The module $Q$ is finite
over $S$ because it is a quotient, and is $A$-flat by hypothesis. Steps 4–5 give every localized
lift. The $T'$-module lift from step 6 therefore yields an $A'$-flat $S'$-module $M'$ and a
specified $S$-linear isomorphism $M'/IM'\cong Q$.
Dependencies: lem-sfb-flat-module-lift-formal-neighbourhood.

8. Choose $e\in M'$ mapping to $1\in Q$. The $S'$-linear map $S'\to M'$, $s\mapsto se$, is
surjective modulo $I$, since $S\to Q$ is surjective. By [lem-weil-pbc-nakayama-nilpotent] it is
surjective. Its kernel $H$ is an ideal, since $S'$ is a commutative ring and this is a map out
of its rank-one free module. Hence $S'/H\cong M'$ as $S'$-modules. Give $Q'=S'/H$ its quotient
algebra structure. It is $A'$-flat because $M'$ is. The specified reduction identifies $Q'/IQ'$
with $Q$: the composite $S\to Q'/IQ'\to Q$ sends $s$ to its original image in $Q$, since $e$
maps to $1$. Consequently that bijective module map is an algebra isomorphism, proving the
reverse implication for square-zero kernels with the required marking. If $J=P$, the completions
are zero and the same argument uses local lifts on the whole smooth spectrum; if $J=0$, $J_Q$ is
nilpotent and $C=Q$. If $P=0$, nilpotence forces $Q=0$, and the zero lift works. No step
identifies the originally chosen $D$ with the completion of the constructed $Q'$.
Dependencies: lem-weil-pbc-nakayama-nilpotent.

9. Consider the completion functor $F:\mathrm{Def}_P\to\mathrm{Def}_{\widehat P_J}$ of [lem-sfb-
adic-completion-flat-deformation-functor]; $P$ is Noetherian by step 1, so that node applies and
supplies its compatibility with every Artinian base change. By [lem-sfb-ring-deformation-
smoothness-test], the source and target tangent spaces identify with
$\operatorname{Exal}_k(P,P)$ and $\operatorname{Exal}_k(\widehat P_J,\widehat P_J)$. Under these
identifications the tangent map is completion: both send the middle algebra of a marked dual-
number extension to its completion, and its kernel map $p\mapsto\epsilon\widetilde p$ is
preserved by this operation. Apply [lem-sfb-exal-completion-smooth-complement] with $B=P$ and
$N=P$, finite as a module over itself. Its hypotheses are exactly finite type of $P$ and
smoothness off $V(J)$. Since $\widehat N=\widehat P_J$, it says precisely that this tangent map
is an isomorphism, in particular surjective.
Dependencies: lem-sfb-adic-completion-flat-deformation-functor, lem-sfb-ring-deformation-
smoothness-test, lem-sfb-exal-completion-smooth-complement.

10. We now discharge the temporary square-zero restriction. For every object
$B\in\mathrm{Def}_P(R)$, the maximal ideal of $R$ is nilpotent by [lem-weil-pbc-artinian-local-
noetherian-nilpotent], and [lem-weil-pbc-finite-type-lift-nilpotent] applied to $B/\mathfrak
m_RB=P$ makes $B$ finite type over $R$. Consequently steps 1–8 apply to every such object and
every small extension $R'\twoheadrightarrow R$: its kernel, being annihilated by $\mathfrak
m_{R'}$ and contained in that ideal, is square zero. They give exactly condition (ii) of [lem-
sfb-ring-deformation-smoothness-test], existence of a source lift whenever the completed object
lifts. Step 9 gives condition (i). The cited criterion therefore gives compatible marked lifts
over arbitrary Artinian surjections. Apply it to the original $A'\twoheadrightarrow A$, $Q$ and
supplied $D$: the output includes a flat algebra $Q'$ with $Q'\otimes_{A'}A\cong Q$, as
required. The criterion preserves the target marking at each small-extension step; no arbitrary
intermediate lift is assumed to retain formal liftability. This proves the reverse implication
for the original unchanged statement; combine with step 3.
Dependencies: lem-weil-pbc-artinian-local-noetherian-nilpotent, lem-weil-pbc-finite-type-lift-
nilpotent, lem-sfb-ring-deformation-smoothness-test.
-/
theorem completion_reflects_flat_liftability
    (k P : Type u) [Field k] [CommRing P] [Algebra k P] [FiniteType k P]
    (J : Ideal P)
    (hsmooth : ∀ p : Spec (CommRingCat.of P),
      p ∉ PrimeSpectrum.zeroLocus (J : Set P) →
      ∃ U : (Spec (CommRingCat.of P)).Opens, p ∈ U ∧
        AlgebraicGeometry.Smooth (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k P))))
    (A' A : Type u) [CommRing A'] [CommRing A]
    [IsLocalRing A'] [IsLocalRing A] [IsArtinianRing A'] [IsArtinianRing A]
    [Algebra k A'] [Algebra k A] [Algebra A' A] [IsScalarTower k A' A]
    [IsLocalHom (algebraMap A' A)]
    (hsurj : Function.Surjective (algebraMap A' A))
    (eA' : IsLocalRing.ResidueField A' ≃ₐ[k] k)
    (eA : IsLocalRing.ResidueField A ≃ₐ[k] k)
    (hres : ∀ a' : A',
      eA (IsLocalRing.residue A (algebraMap A' A a')) = eA' (IsLocalRing.residue A' a'))
    (Q : Type u) [CommRing Q] [Algebra A Q] [Algebra k Q] [IsScalarTower k A Q]
    [Module.Flat A Q] [FiniteType A Q]
    (eP : (Q ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A Q)) ≃ₐ[k] P) :
    (∃ (Q' : Type u) (_ : CommRing Q') (_ : Algebra A' Q'),
      Module.Flat A' Q' ∧ Nonempty ((A ⊗[A'] Q') ≃ₐ[A] Q)) ↔
    (∃ (D : Type u) (_ : CommRing D) (_ : Algebra A' D),
      Module.Flat A' D ∧
        Nonempty ((A ⊗[A'] D) ≃ₐ[A]
          AdicCompletion (J.comap (eP.toRingHom.comp
            (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map (algebraMap A Q))))) Q)) := by
  sorry

end Algebra
