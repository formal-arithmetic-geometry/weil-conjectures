/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularImmersionClassSystem
public import WeilConjectures.AlgebraicGeometry.RegularSupportedLocalContinuity
import WeilConjectures.AlgebraicGeometry.ClosedSupportHom
import WeilConjectures.Blowup.InvertibleCenter
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Regular.RegularSequence
import WeilConjectures.AlgebraicGeometry.ConormalAlgebraFlatBaseChange
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyContinuity
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.RingTheory.StrictHenselizationNoetherian
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat

/-! # Regular-immersion fundamental-class calculus

Source: ILO, Expose XVI, Definition 2.3.1, Theorem 2.3.2 and sections 3.2--3.3;
Stacks Project, Tag 03Q6 (blueprint: lem-per-regular-immersion-class-calculus).

## Main statement

* `regular_immersion_class_calculus`: a simultaneous normalized supported class family,
  with composition, flat restriction, coefficient reduction and supported continuity.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.Etale

/-- There is a normalized system of supported fundamental classes for all Noetherian
regular closed immersions, including codimension zero, and all positive prime-power
levels. The supported realization is transposed under Ri_* adjoint to i^! to give eta.
On any regular-sequence chart, repeated transitivity gives the ordered Cartier Kummer
composite. Normalization identifies every factor, including its +c_1(O(D)) sign.
Consequently all regular generating sequences and regular orders compute the same
chosen global class. The class is constructed globally, not glued from equal derived
morphisms on open charts. Flat compatibility includes open restriction and localization;
the second conjunct gives the supported continuity identification for actual local and
strict-local ind-etale presentations, with the same canonical restriction equations.
Coefficient compatibility uses the power map on roots and evaluation on signed twists.

Source: ILO, Expose XVI, Definition 2.3.1, Theorem 2.3.2, Proposition 2.2.3.1,
section 3.2 before Definition 3.2.2, Propositions 3.3.1--3.3.2; Stacks Project, Tag 03Q6
(blueprint: lem-per-regular-immersion-class-calculus).

Proof (the reviewed one-level reconstruction):
1. Construct the class globally, before choosing regular generators. Work on a component where
   the codimension is the constant c>0. By [lem-per-regular-flag-blowup-geometry] the conormal
   C=I/I^2 is finite locally free of rank c. Apply [lem-per-modified-blowup-generalized-class]
   to the identity presentation C -> I/I^2 and define gamma_i=gamma_(i,C). This is an actual
   element of H_Z^{2c}(X,Lambda_n(c)), characterized by its injective blowup pullback G(Q_C).
   The supported-Hom isomorphism of [lem-amb-closed-support-hom] realizes it as Ri_*Lambda_Z ->
   Lambda_X(c)[2c]. Transpose under the right adjoint of [thm-amb-etale-exceptional-adjoint] to
   define eta_(i,n). This construction is global and canonical: it does not assume that
   arbitrary derived morphisms glue from equality on open charts. Components of different
   codimension use this same construction with their respective c.
2. For c=0, a length-zero regular presentation means I=0 in a neighbourhood of Z. Thus the image
   of the closed immersion is also open. Define the supported morphism by inclusion of the
   corresponding constant-sheaf summand; its transpose is restriction to that summand, and the
   identity immersion gives 1. For c=1, I=O_X(-D) is invertible, so its blowup is X by [cor-
   nagata-blowup-cartier-iso]. The construction has Q_C=-1, hence gamma_i=-e_D(I,1). The dual-
   line identity in [lem-per-noetherian-supported-product-calculus] gives
   -e_D(I,1)=e_D(O_X(D),1), and identifies this with c_(D,Lambda_n). Its composite with the unit
   is +c_1(O_X(D)) by [lem-asd-ordinary-supported-kummer]. Thus the construction has precisely
   the required Cartier Kummer sign.
3. Use the nested supported action of [lem-per-noetherian-supported-product-calculus] to write
   gamma_i gamma_j for the class in H_Z^{2(m+d)}(X,Lambda_n(m+d)) associated to Z -i-> Y -j-> X
   of codimensions m,d. Its statement identifies this product with composition of supported
   morphisms and, after adjunction, with exceptional composition. More explicitly the two
   successive transposes use the composite Hom bijection in [def-weil-pbc-composite-adjunction];
   its unit and counit formulas give i^!(eta_j)(m)[2m] composed with eta_i. Here ji is again a
   regular immersion, so gamma_(ji) is defined: near a point of Z choose an affine open Spec A
   of X on which Y=V(s_1,...,s_d) with s regular, and, principal opens forming a base, shrink it
   to D(g) so that Z is cut out in Y by the images of a regular sequence t_1,...,t_m.
   Localization is flat [lem-weil-pbc-localization-flat], so tensoring the injective
   multiplication maps with A_g keeps s regular [def-weil-pbc-flat-ring-map] (the final quotient
   is nonzero as it contains a point of Z); then s_1,...,s_d followed by lifts of the t_k is a
   regular sequence in A_g with quotient the ring of Z, directly by [def-weil-pbc-regular-
   sequence]. Consequently it suffices to prove gamma_(ji)=gamma_i gamma_j. Codimension-zero
   factors are restrictions of constant-sheaf summands, so the equality is the
   identity/restriction identity. In the remaining argument m,d>0.
4. First take d=1. Put E=C_(Z/Y), F=C_(Z/X), K=C_(Y/X)|Z, k=c_1(K), and xi=c_1(O_P(1)); write
   S_E=sum_(s=0)^(m-1)(-1)^s c_s(E) xi^(m-1-s). All coefficients are pulled from Z when used on
   P. Apply [lem-per-regular-flag-blowup-geometry] to pi:B=Bl_Z X -> X: its exceptional divisor
   is P=P(F), its other Cartier divisor is Ytilde=Bl_Z Y, and P'=P(E)=P intersection Ytilde.
   They meet transversely; pi^*I_Y=I_P tensor I_Ytilde as framed invertible ideals; the ideal of
   P' in P is K tensor O_P(-1). These are exactly the hypotheses needed for supported ideal
   additivity and transverse Cartier interchange. Pullback on H_Z^*(X) is injective by [lem-per-
   modified-blowup-generalized-class] applied to the regular immersion ji.
5. Let G_P denote the ideal-normalized exceptional operator on B. The identity
   pi^*gamma_j=-e(I_P,1)-e(I_Ytilde,1) follows from Step 2 and framed-ideal additivity. Multiply
   by pi^*gamma_i, using naturality and the projection formula in [lem-per-noetherian-supported-
   product-calculus]. The first term is G_P((-1)^(m+1)c_m(E)): indeed the restriction of gamma_i
   to Z is (-1)^m c_m(E) by [lem-per-modified-blowup-generalized-class]. For the second, the
   blowup formula for i gives the inner argument Q_E=-S_E on P'. Transverse Cartier interchange
   moves G_P outside G_(P' in P); the extra minus from gamma_j cancels the minus in Q_E. On P
   the latter operator is multiplication by c_1(K tensor O_P(-1))=k-xi. Here supported-Hom
   identifies a class supported on the Cartier divisor with its operator, so the projection
   formula applies to each polynomial term, which restricts from P. Thus pi^*(gamma_i
   gamma_j)=G_P((-1)^(m+1)c_m(E)+(k-xi)S_E). This computation uses the actual operator domains
   on the common support P', followed by enlargement to P; it does not equate classes having
   different supports.
6. The same blowup construction gives pi^*gamma_(ji)=G_P(Q_F), where Q_F=-sum_(s=0)^m(-1)^s
   c_s(F)xi^(m-s). The exact conormal sequence 0 -> K -> F -> E -> 0 is supplied by [lem-per-
   regular-flag-blowup-geometry]. Whitney's formula of [lem-per-noetherian-etale-chern-
   identities] says c_s(F)=c_s(E)+k c_(s-1)(E), with c_0(E)=1 and c_s(E)=0 outside 0<=s<=m.
   Substitute these coefficients: sum_(s=0)^m(-1)^s c_s(F)xi^(m-s)=(xi-k)S_E+(-1)^m c_m(E).
   Negating shows that Q_F is the argument obtained in Step 5. Apply G_P and the injectivity in
   Step 4 to obtain gamma_(ji)=gamma_i gamma_j when j is Cartier.
7. For arbitrary d>0, blow up Y in X. In the notation of [lem-per-regular-flag-blowup-geometry],
   P=P(C_(Y/X)), P'=P times_Y Z, i':P' -> P, and j':P -> B. The conormal-presentation kernels K
   and K' have rank d-1 and K'=i'^*K. Write z=c_(d-1)(K^vee), z'=i'^*z. Base change and excess
   in [lem-per-modified-blowup-generalized-class], with the dual-bundle sign from [lem-per-
   noetherian-etale-chern-identities], give pi^*gamma_(ji)=z' gamma_(j'i') and pi^*gamma_j=z
   gamma_(j'). Generalized-class base change and the stated isomorphism C_(P'/P)=p'^*C_(Z/Y)
   give p^*gamma_i=gamma_(i'). The hypotheses of Steps 4-6 hold for i',j': over an affine open
   of Y on which C_(Y/X) is free, P is covered by spectra of polynomial rings, which are free
   and hence flat modules, so p is flat; tensoring the injective multiplication maps of a local
   regular sequence for Z in Y with these flat algebras [def-weil-pbc-flat-ring-map] shows that
   i' is a regular immersion of codimension m, cut out by the same equations; j' is an effective
   Cartier divisor, and j'i' is regular of codimension m+1 by the lifting argument of Step 3.
   Step 6 applies because j' is Cartier, so gamma_(j'i')=gamma_(i')gamma_(j'). Associativity and
   the projection formula now yield z' gamma_(i')gamma_(j')=gamma_(i')z gamma_(j')=pi^*(gamma_i
   gamma_j). Injectivity with support Z, not merely support Y, in the generalized-class
   statement proves the equality on X. Step 3 converts it into the claimed exceptional
   composition.
8. Let t_1,...,t_c be regular generators on an affine chart, with the successive quotients Z_k
   of the statement. By [def-weil-pbc-regular-sequence], multiplication by t_k is injective
   modulo the preceding generators; hence each Z_k -> Z_(k-1) is the indicated effective Cartier
   divisor. Induct on c. The empty flag gives Step 2's identity; for c>0, apply Step 7 to the
   first Cartier inclusion Z_1 -> X and the suffix regular immersion Z_c -> Z_1. The suffix has
   c-1 regular generators, so the induction hypothesis identifies its class with the
   corresponding suffix composite. Step 2 identifies the first class with the supported Cartier
   Kummer map; associativity gives the entire flag composite. Every flag therefore computes the
   globally constructed gamma_i. A different set or order of generators which is a regular
   generating sequence computes that same class. No assertion that every permutation is regular
   in an arbitrary nonlocal ring, and no derived gluing principle, is used.
9. For a flat base change, check at stalks: if A -> B is flat and multiplication by t_k is
   injective on A/(t_1,...,t_(k-1)), tensoring this injection with B is injective by [def-weil-
   pbc-flat-ring-map]. Its tensor quotient is B/(t_1,...,t_(k-1)); thus the pulled sequence
   remains regular wherever its final support is nonempty. Empty pulled supports give the zero
   class. The degree-one isomorphism in [lem-pur-conormal-algebra-flat-base-change] identifies
   the pulled conormal with the new conormal. The arbitrary-base-change formula for generalized
   classes therefore identifies gamma_i pulled back with gamma_(i'). The codimension-zero
   summand map has the same restriction identity. Open restriction is also immediate from that
   formula, since restricting I/I^2 to an open is the conormal of the restricted ideal. Via
   supported-Hom these are compatibilities of the normalized supported classes, not a claim of
   exceptional base change for every complex.
10. For N>=n the geometric blowup and its conormal presentation are unchanged. The coefficient
   naturality in [lem-per-modified-blowup-generalized-class] carries its defining pullback
   G(Q_C) at level N to the level-n pullback G(Q_C). Injectivity at level n then forces the
   reduced class gamma_(i,N) to be gamma_(i,n). For c=0 the summand map has this compatibility
   directly. The Chern coefficients and Kummer products have the same comparisons by [lem-per-
   noetherian-etale-chern-identities] and [lem-per-noetherian-supported-product-calculus]. The
   roots comparison is u -> u^(ell^(N-n)); [lem-asd-etale-finite-twist-pullback] identifies its
   tensor powers, and the dual/evaluation identifications give negative twists. Supported-Hom
   and transposition carry precisely this supported-class comparison to the eta notation.
11. For continuity take a small directed affine system X_a over an affine chart of X,
   representing a localization or strict localization, and set Z_a=Z times_X X_a, U_a=X_a-Z_a.
   Its limiting pair is (X_infty,Z_infty), and X_infty is Noetherian: a localization S^{-1}A of
   a Noetherian ring is Noetherian, every ideal being extended from A; for the strict
   localization at a geometric point over a prime p of the chart A, [lem-weil-pbc-etale-local-
   ring-triples] and [lem-weil-pbc-strict-henselization-triples] identify the neighbourhood
   colimit with the strict henselization of the Noetherian local ring A_p, which is Noetherian
   by [lem-sc-strict-henselization-noetherian]. Each U_a is qcqs because the ideal of Z_a is
   finitely generated; transitions on U_a are affine base changes of those on X_a. Apply [lemma-
   weil-pbc-etale-cohomology-continuity] to X_a and U_a with the pulled torsion Tate sheaf
   Lambda_n(c); [lem-asd-etale-finite-twist-pullback] supplies its pullback identification. The
   supported-Hom mapping fibre of [lem-amb-closed-support-hom] gives the natural sequences
   H^{q-1}(X_a) -> H^{q-1}(U_a) -> H^q_(Z_a)(X_a) -> H^q(X_a) -> H^q(U_a). Their filtered
   colimit is exact by [lem-weil-pbc-filtered-colimit-abelian-groups-exact]. In the comparison
   with the limit sequence the four ordinary-cohomology maps are isomorphisms. Exactness gives
   the middle isomorphism: lift a target supported element's image in H^q(X_infty), correct its
   difference by a lift from H^{q-1}(U_infty), and use the same argument for a kernel element.
   This is precisely the canonical supported continuity map, being induced by restriction of the
   mapping fibres. Thus the supported groups, with their actual comparison maps, have the
   asserted continuity identifications.
12. Finally identify the class under that continuity map. On a nonempty constant-codimension
   part with c>0, restriction of I/I^2 to a localization or a strict localization is the
   conormal presentation of the restricted immersion: the canonical localization is flat by
   [lem-weil-pbc-localization-flat], and the strict-henselization structural map is flat by
   [lem-sbc-affine-strict-henselization-structural-flat], so Step 9 applies to the limit.
   Alternatively on an affine regular-generating chart the ideal and its conormal basis are the
   same finite equations after passing to every neighbourhood and to the limit. Apply
   generalized-class naturality in [lem-per-modified-blowup-generalized-class] both to the
   stages and to the Noetherian limit, with these identity conormal presentations. It says that
   the images of the original gamma_i are gamma_(i_a) and gamma_(i_infty); these equalities are
   compatible with every transition. Since Step 11's map is induced by those very restriction
   maps, it carries the represented class to gamma_(i_infty). The summand construction gives the
   same assertion for c=0, including an empty support. Step 8 identifies these classes with the
   actual Kummer flag composites. Hence localization and strict localization preserve the
   required normalized class under the canonical supported continuity identification.
-/
theorem regular_immersion_class_calculus (ell : ℕ) (h : ell.Prime) :
    (∃ g : RegularClassFamily.{u} ell, IsRegularImmersionClassSystem ell h g) ∧
      RegularClassLocalContinuity.{u} ell h := by
  sorry

end AlgebraicGeometry.Etale
