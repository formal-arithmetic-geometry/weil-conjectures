/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Sheaf.RingTheory.StrictHenselizationPresentationIn
public import Sheaf.Paper.StrictLocalKummerTameModule
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic

import Mathlib.RingTheory.AdjoinRoot
import Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.SNCFiniteRootRegularRing
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import WeilConjectures.RingTheory.HypersurfaceDerivationRegular
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.RegularRingNormal
import Sheaf.AlgebraicGeometry.NormalTopologicallyNoetherianComponents
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleOpenIntegralClosure
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalDenseOpenIntegralSection
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalPresentation
import WeilConjectures.RingTheory.StrictHenselizationNoetherian
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Mathlib.RingTheory.FiniteType
import WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent
import Sheaf.RingTheory.IndEtaleStability
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Precoverage
import WeilConjectures.AlgebraicGeometry.FpqcDescentEtale
import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull
import WeilConjectures.AlgebraicGeometry.FiniteEtaleDescent

/-! # A finite root level extending a tame cover across an SNC boundary

Source: ILO, Travaux de Gabber, Expose IX, Proposition 2.1 and proof, pp.133--134.
(blueprint: lem-sfb-snc-tame-root-etale-extension).

The local tower uses only the labels vanishing at the selected prime. Its puncture
is formed by base change from the original boundary complement. The strict henselization
is specified by the recorded pointed-etale colimit presentation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.SNCTameExtension

/-- The ordered subtuple of labels vanishing at a prime; no irreducibility is required.
Source: ILO IX Proposition 2.1, local branch parameters
(blueprint: lem-sfb-snc-tame-root-etale-extension). -/
def active {B : Type u} [CommRing B] {r : ℕ} (t : Fin r → B)
    (q : PrimeSpectrum B) : List B :=
  (List.ofFn t).filter (fun z ↦ @decide (z ∈ q.asIdeal) (Classical.propDecidable _))

/-- The coefficient map from the affine base to a specified strict local algebra.
Source: ILO IX Proposition 2.1, localization followed by strict henselization
(blueprint: lem-sfb-snc-tame-root-etale-extension). -/
def coefficient {B : Type u} [CommRing B] (q : PrimeSpectrum B)
    (H : Type u) [CommRing H] [Algebra (Localization.AtPrime q.asIdeal) H] : B →+* H :=
  (algebraMap (Localization.AtPrime q.asIdeal) H).comp
    (algebraMap B (Localization.AtPrime q.asIdeal))

/-- The active parameter tuple in the specified strict henselization.
Source: ILO IX Proposition 2.1, local branch parameters
(blueprint: lem-sfb-snc-tame-root-etale-extension). -/
def localParameters {B : Type u} [CommRing B] {r : ℕ} (t : Fin r → B)
    (q : PrimeSpectrum B) (H : Type u) [CommRing H]
    [Algebra (Localization.AtPrime q.asIdeal) H] : Fin (active t q).length → H :=
  fun i ↦ coefficient q H ((active t q).get i)

/-- The canonical projection of the full local active-root tower to the affine base.
Source: ILO IX Proposition 2.1, strict-local parameter roots
(blueprint: lem-sfb-snc-tame-root-etale-extension). -/
def localProjection (p : ℕ) {B : Type u} [CommRing B] {r : ℕ} (t : Fin r → B)
    (q : PrimeSpectrum B) (H : Type u) [CommRing H]
    [Algebra (Localization.AtPrime q.asIdeal) H] :
    Spec (.of (tameRootAlgebra p (localParameters t q H))) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom
    ((algebraMap H (tameRootAlgebra p (localParameters t q H))).comp (coefficient q H)))

/-- The actual open complement, including the product-one case of no labels.
Source: ILO IX Proposition 2.1, boundary complement
(blueprint: lem-sfb-snc-tame-root-etale-extension). -/
def puncture {B : Type u} [CommRing B] {r : ℕ} (t : Fin r → B) :
    Spec (.of (Localization.Away (∏ i, t i))) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (∏ i, t i))))

/-- The full active-root tower restricted to the prescribed boundary complement.
Inactive parameters are units in the strict local ring, so this is exactly the displayed
local puncture, with no extra parameter roots adjoined.
Source: ILO IX Proposition 2.1, punctured strict-local tower
(blueprint: lem-sfb-snc-tame-root-etale-extension). -/
def localPuncture (p : ℕ) {B : Type u} [CommRing B] {r : ℕ} (t : Fin r → B)
    (q : PrimeSpectrum B) (H : Type u) [CommRing H]
    [Algebra (Localization.AtPrime q.asIdeal) H] :
    pullback (puncture t) (localProjection p t q H) ⟶
      Spec (.of (Localization.Away (∏ i, t i))) :=
  pullback.fst _ _

/-- The finite simultaneous root projection, defined by the literal polynomial quotient.
Source: ILO IX Proposition 2.1, finite Kummer base change
(blueprint: lem-sfb-snc-tame-root-etale-extension). -/
def finiteProjection {B : Type u} [CommRing B] {r : ℕ} (t : Fin r → B) (n : ℕ) :
    Spec (.of (MvPolynomial (Fin r) B ⧸ Ideal.span (Set.range
      (fun i ↦ MvPolynomial.X i ^ n - MvPolynomial.C (t i))))) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom (algebraMap B _))

/-- A finite etale cover split by every strict-local full prime-to-p active-root tower
extends etale after one common finite simultaneous root base change.
Source: ILO IX Proposition 2.1 and proof, printed pp.133--134.
(blueprint: lem-sfb-snc-tame-root-etale-extension).

Proof (the complete stage-1 proof, with its dependencies):
1. If $V$ is empty, take $n=1$ and $Z=\varnothing$. If $r=0$, then $V^\circ=V$, and $n=1$, $Z=P$
   works without using the tower hypothesis. If $P=\varnothing$, take $n=1$, $Z=\varnothing$. In
   the remaining argument allow degree zero locally. For every positive $a$ prime to $p$ put
   $C_a=B[x_1,\ldots,x_r]/(x_i^a-t_i)_i$ and $X_a=\operatorname{Spec}C_a$. Iterating the
   monic-quotient basis gives the finite free $B$-basis $\prod_i x_i^{e_i}$, $0\le e_i<a$. The
   same presentation represents roots after any scalar extension: both directions fix coefficients
   and send each root to its named coordinate. For $a\mid b$ the transition $X_b\to X_a$ is
   defined by $x_{i,a}\mapsto x_{i,b}^{b/a}$; the relations and composition law follow by exponent
   multiplication.

   Uses: lem-weil-pbc-monic-quotient-free.

2. We first check regularity of every $C_a$ despite the possibly disconnected labels. At a point
   $v\in V$, the active $t_i$ are distinct regular parameters, so each is prime in $\mathcal
   O_{V,v}$ by the regular-local UFD boundary lemma. At every point the same assertion shows that
   $V(t_i)$ is reduced and locally has at most one irreducible component through the point. There
   are finitely many boundary components. Delete the components not passing through $v$ and invert
   the inactive $t_i$; shrink to an affine neighbourhood $W$ of $v$. There each remaining
   $V(t_i)\cap W$ is precisely one reduced integral boundary component, and these components are
   pairwise distinct. Indeed two components through $v$ cannot belong to one $(t_i)$, because its
   localized ideal is prime; two active labels cannot name the same component, because associated
   parameters would make a generator redundant in the full parameter list, contradicting the
   dimension bound for a generating set of the maximal ideal. The restricted SNC intersection
   conditions are unchanged. Apply the existing finite-root regularity theorem to these active
   labels on $W$. It gives a regular Noetherian algebra after adjoining their $a$th roots.

   Uses: lem-trf-regular-local-ufd-boundary-factorization,
   lem-weil-pbc-noetherian-local-dimension-le-generators,
   def-trf-strict-normal-crossings-boundary, lem-weil-pbc-noetherian-finite-components,
   lem-sfb-snc-finite-root-regular-ring.

3. Adjoin the roots of the inactive labels successively to the algebra just obtained. If $u$ is a
   unit in a regular ring $D$, then in $D[T]/(T^a-u)$ the class of $T$ is a unit, with inverse
   $T^{a-1}/u$. The image of the derivative $aT^{a-1}$ is a unit, since $a$ is prime to $p$. The
   polynomial ring $D[T]$ is regular, so the hypersurface-derivation criterion makes its quotient
   regular. Induction over the inactive labels proves that $C_a$ is regular on the inverse image
   of $W$. These opens cover $X_a$, proving its regularity everywhere; $C_a$ is Noetherian also
   directly from its finite $B$-basis. Thus $C_a$ is normal. At each stalk of $B$, $f$ is a unit
   times a product of nonzero parameters in a domain, so multiplication by $f$ is injective on
   $B$. The monic basis then makes multiplication by $f$ injective on $C_a$ as well. Decompose
   $X_a$ into its finitely many clopen normal integral components. None is contained in $V(f)$: in
   that product decomposition injectivity excludes the zero component of $f$. Consequently
   $X_a^\circ=D(f)$ contains every generic point and is dense in every component.

   Uses: lem-trf-polynomial-ring-regular-base, lem-weil-pbc-hypersurface-derivation-regular,
   lem-weil-pbc-finite-algebra-noetherian, lem-weil-pbc-regular-ring-normal,
   lem-trf-regular-local-ufd-boundary-factorization,
   lem-trf-normal-topologically-noetherian-components.

4. Write $P=\operatorname{Spec}D$ over $B[1/f]$, and $D_a=D\otimes_{B[1/f]}C_a[1/f]$. Finiteness
   is preserved here by the elementary tensor argument: images of any finite module generating set
   generate the tensor product. Etaleness is preserved by the etale base-change theorem. Let $E_a$
   be the integral closure of $C_a$ in $D_a$. On each normal integral component of $X_a$, apply
   finite-etale-open integral-closure finiteness to $D(f)$ and this finite etale cover. Its
   conclusion makes the integral closure a finite module on that component. The finite clopen
   component decomposition therefore makes $E_a$ a finite $C_a$-module. As $C_a$ is Noetherian,
   the resulting finite-type algebra $E_a$ is of finite presentation. Put
   $N_a=\operatorname{Spec}E_a$ with its finite map to $X_a$. No Galois closure or degree bound
   has been introduced.

   Uses: lem-weil-pbc-etale-scheme-base-change, lem-sbc-finite-etale-open-integral-closure,
   lem-trf-normal-topologically-noetherian-components,
   lem-weil-pbc-finite-type-noetherian-finite-presentation.

5. The open restriction of $N_a$ is the prescribed cover: apply integral-closure ind-etale base
   change to $C_a\to C_a[1/f]$. This localization is ind-etale since it is an open immersion and
   is etale. It identifies $E_a[1/f]$ with the integral closure of $C_a[1/f]$ in $D_a$. Every
   element of the finite $C_a[1/f]$-algebra $D_a$ is integral, so this closure is all of $D_a$.
   Also the integral closure of $C_a$ in $C_a[1/f]$ is exactly $C_a$: an integral section on the
   dense open $D(f)$ extends by the normal dense-open integral-section theorem, and the injection
   $C_a\hookrightarrow C_a[1/f]$ from Step 3 makes the extension unique. Both assertions use the
   actual structural maps, not merely abstract isomorphisms.

   Uses: lem-sfb-integral-closure-ind-etale-base-change,
   lem-weil-pbc-etale-composition-cancellation, lem-weil-pbc-finite-algebra-is-integral,
   lem-sbc-normal-dense-open-integral-section.

6. Fix a geometric point $\bar v$ with image $v$ and put $A=\mathcal O_{V,\bar v}^{\rm sh}$ and
   $I=\{i:t_i(v)=0\}$. The geometric strict-henselization presentation identifies $A$ with the
   algebraic strict henselization of $B_v$. It is Noetherian and is a filtered colimit of etale
   $B$-algebras. For $(m,p)=1$, put $T_m=A[z_i:i\in I]/(z_i^m-t_i)_{i\in I}$. The active puncture
   $T_m[1/\prod_{i\in I}t_i]$ equals $T_m[1/f]$, since all inactive $t_j$ are units in $A$. These
   affine punctures form a directed inverse system under divisibility with affine transitions. The
   limit is the tower in the hypothesis, by the affine-transition limit theorem. Each $T_m$ and
   $T_m[1/f]$ is Noetherian, by the monic finite basis and Noetherian finite-type permanence. The
   pullbacks of $P$ are etale and of finite presentation: etaleness is base change, and finite
   module generators give finite-type algebras over these Noetherian bases.

   Uses: lem-sbc-geometric-strict-henselization-local-presentation,
   lem-sc-strict-henselization-noetherian, lem-weil-pbc-strict-henselization-triples,
   lem-weil-pbc-limit-affine-transition, lem-weil-pbc-finite-type-algebra-noetherian,
   lem-weil-pbc-finite-type-noetherian-finite-presentation, lem-weil-pbc-etale-scheme-base-change.

7. By the hypothesis, over that punctured limit there is an isomorphism from the pullback of $P$
   to $d$ copies of the base for some finite $d\ge0$. Apply the morphism and equality clauses of
   finite-data descent to this isomorphism and its inverse between the pullbacks of $P_A$ and the
   fixed trivial $d$-sheeted cover, both defined at $m=1$. Descend the two arrows and the two
   inverse identities, and enlarge to a common prime-to-$p$ index $m$. This gives an isomorphism
   over $T_m[1/f]$ between $P_A$ pulled back there and $\coprod_d\operatorname{Spec}T_m[1/f]$. All
   objects at the starting stage are etale of finite presentation, as checked in Step 6; the index
   is the directed set of positive prime-to-$p$ integers with divisibility. Thus the cited
   morphism and equality clauses apply to the specified objects, rather than descending an
   unrelated model of them.

   Uses: lem-weil-pbc-etale-finite-data-descent.

8. Let $S=A\otimes_B C_m=A[x_1,\ldots,x_r]/(x_i^m-t_i)_i$. There is a $T_m$-algebra structure on
   $S$ sending $z_i$ to $x_i$ for active $i$. Base change of the preceding splitting gives the
   actual $S[1/f]$-algebra isomorphism $D_m\otimes_{C_m}S\simeq S[1/f]^d$. The map $C_m\to S$ is
   ind-etale: it is the base change of the filtered etale presentation $B\to A$, by ind-etale
   stability. This argument merely adjoins the roots of the inactive units as additional
   coordinates; it neither chooses those roots in $A$ nor assumes any roots of unity in $B$.

   Uses: lem-weil-pbc-ind-etale-stability.

9. Apply integral-closure ind-etale base change twice along $C_m\to S$. For the algebra
   $C_m[1/f]$, Step 5 says its integral closure is $C_m$, so the theorem identifies the integral
   closure of $S$ in $S[1/f]$ with $S$, via the structural inclusion. For the algebra $D_m$, it
   identifies $S\otimes_{C_m}E_m$ with the integral closure of $S$ in $S[1/f]^d$, using Step 8.
   This last closure is $S^d$: projection shows that an integral tuple has every coordinate
   integral, hence in $S$ by the first application; conversely every tuple of elements of $S$ is
   integral over diagonal $S$, since for $s=(s_1,\ldots,s_d)$ the monic polynomial
   $\prod_{j=1}^d(T-s_j)$ vanishes coordinatewise. For $d=0$ the target ring is the zero ring and
   both closures are zero. Hence $N_m\times_V\operatorname{Spec}A$ is a disjoint union of $d$
   copies of $X_m\times_V\operatorname{Spec}A$. It is therefore finite etale over that base.

   Uses: lem-sfb-integral-closure-ind-etale-base-change.

10. The map $B_v\to A$ is faithfully flat by strict-henselization faithful flatness; its spectrum
   is surjective by faithful-flat surjectivity and flat, hence is an fpqc cover (an affine
   surjective flat map meets the defining affine-cover condition). Fpqc base-change stability
   makes $\operatorname{Spec}(A\otimes_B C_m)\to\operatorname{Spec}(B_v\otimes_B C_m)$ an fpqc
   cover. Etaleness thus descends by fpqc descent from Step 9:
   $N_m\times_V\operatorname{Spec}B_v\to X_m\times_V\operatorname{Spec}B_v$ is etale. Now write
   $B_v$ as the directed colimit of $B[1/h]$ for $h\notin v$ (the index can be finite subsets of
   $B\setminus v$, inverting their product). Apply etale-property descent to the fixed finitely
   presented morphism $N_m\to X_m$ over $V$. All schemes at the starting stage are affine, hence
   qcqs; the transitions are affine localizations. There is $h_v\notin v$ such that $N_m\to X_m$
   is etale after base change from $V$ to $W_v=D(h_v)$. It is still finite there, because a finite
   module generating set remains generating after localization. Thus a finite root level $m_v=m$
   works on an entire Zariski neighbourhood of $v$, including every point of $X_m$ above it.

   Uses: lem-sc-strict-henselization-faithfully-flat,
   lem-weil-pbc-faithfully-flat-surjective-spectrum, def-weil-pbc-fpqc-covering,
   lem-galois-fpqc-covering-base-change, lem-galois-fpqc-descend-etale,
   lem-weil-pbc-descend-etale.

11. The opens $W_v$ cover the quasi-compact affine $V$. Choose a finite subcover $W_1,\ldots,W_s$,
   with corresponding levels $m_1,\ldots,m_s$. Set $n=\prod_{j=1}^s m_j$, a positive integer prime
   to $p$. For every $j$ the power substitutions from Step 1 give $X_n\to X_{m_j}$. Pull the
   finite etale cover $N_{m_j}|_{X_{m_j}\times_VW_j}$ back along this map, obtaining $Z_j\to
   X_n\times_VW_j$. Etaleness is stable under base change, and tensoring module generators proves
   finiteness. Its restriction to $X_n^\circ\times_VW_j$ is identified with the pullback of $P$ by
   Step 5. These identifications use the same power substitution for every root and therefore give
   actual identifications with one fixed cover $P\times_{V^\circ}X_n^\circ$.

   Uses: lem-weil-pbc-etale-scheme-base-change.

12. For completeness construct the overlap identifications rather than assuming normalization
   commutes with the ramified transition $X_n\to X_{m_j}$. The base $X_n$ is normal Noetherian by
   Steps 2-3. On an overlap $H_{ij}=X_n\times_V(W_i\cap W_j)$, its clopen integral components are
   normal, and $H_{ij}\cap X_n^\circ$ is dense in each nonempty component, by Step 3 and
   restriction. The two covers $Z_i,Z_j$ have a specified isomorphism on that dense open through
   their identifications with the same pullback of $P$. On each integral component restrict this
   isomorphism to its generic point and apply generic-point full faithfulness for finite etale
   covers to extend that morphism and its inverse. Their composites are identities by uniqueness
   at the generic point. These extensions agree with the original isomorphism on the entire
   punctured overlap: apply uniqueness again on the integral dense open, which is normal.
   Combining the clopen components gives an isomorphism $\alpha_{ij}:Z_i|_{H_{ij}}\simeq
   Z_j|_{H_{ij}}$ extending exactly the specified puncture identification.

   Uses: lem-trf-normal-topologically-noetherian-components,
   lem-sbc-normal-integral-generic-hom-full.

13. On each integral component of a triple overlap, the two composites $\alpha_{jk}\alpha_{ij}$
   and $\alpha_{ik}$ agree at the generic point, since all puncture identifications factor through
   the single cover pulled back from $P$. Uniqueness in generic-point full faithfulness makes them
   equal everywhere. The same uniqueness gives the identity and inverse conditions. Hence
   $(Z_j,\alpha_{ij})$ is a finite etale descent datum for the surjective etale morphism
   $\coprod_j(X_n\times_VW_j)\to X_n$ (each summand is an open immersion). Effective finite-etale
   descent supplies a finite etale $Z\to X_n$ and compatible identifications with the $Z_j$.
   Restricting to the puncture, their specified identifications with $P\times_{V^\circ}X_n^\circ$
   satisfy the same datum. Full faithfulness of the descent equivalence therefore gives the
   required isomorphism $Z\times_{X_n}X_n^\circ\simeq P\times_{V^\circ}X_n^\circ$. Since $X_n=V_n$
   by its presentation, this is the assertion.

   Uses: lem-sbc-normal-integral-generic-hom-full, lem-weil-pbc-etale-composition-cancellation,
   lem-galois-descent.
-/
theorem exists_finite_root_etale_extension
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    (B : Type u) [CommRing B] (b : Spec (.of B) ⟶ Spec (.of k))
    [LocallyOfFiniteType b] [QuasiCompact b] [IsSeparated b]
    (_hB : IsRegularScheme (Spec (.of B)))
    (r : ℕ) (t : Fin r → B) (D : (Spec (.of B)).IdealSheafData)
    (_hD : IsStrictNormalCrossingsBoundary D)
    (_hproduct : D = Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of B)).inv (∏ i, t i)}))
    (_hparameters : ∀ q : PrimeSpectrum B,
      ∃ (_hnoeth : IsNoetherianRing (Localization.AtPrime q.asIdeal))
        (s : List (Localization.AtPrime q.asIdeal)),
        IsLocalRing.IsRegularSystemOfParameters s ∧
          ((active t q).map (algebraMap B (Localization.AtPrime q.asIdeal))).Sublist s)
    (P : Scheme.{u}) (π : P ⟶ Spec (.of (Localization.Away (∏ i, t i))))
    [IsFinite π] [Etale π]
    (_hsplit : ∀ (q : PrimeSpectrum B) (K H : Type u) [Field K]
      [Algebra (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) K]
      [IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) K]
      [Algebra (Localization.AtPrime q.asIdeal) K]
      [IsScalarTower (Localization.AtPrime q.asIdeal)
        (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) K]
      [CommRing H] [Algebra (Localization.AtPrime q.asIdeal) H],
      Algebra.StrictHenselizationPresentationIn (Localization.AtPrime q.asIdeal) K H →
        ∃ d : ℕ, ∃ e : pullback π (localPuncture p t q H) ≅
          ∐ (fun _ : Fin d ↦ pullback (puncture t) (localProjection p t q H)),
          e.hom ≫ Sigma.desc (fun _ ↦ 𝟙 _) = pullback.snd _ _) :
    ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧
      ∃ (Z : Scheme.{u}) (ζ : Z ⟶ Spec (.of (MvPolynomial (Fin r) B ⧸
        Ideal.span (Set.range (fun i ↦ MvPolynomial.X i ^ n - MvPolynomial.C (t i)))))),
        IsFinite ζ ∧ Etale ζ ∧
          ∃ e : pullback ζ (pullback.snd (puncture t) (finiteProjection t n)) ≅
            pullback π (pullback.fst (puncture t) (finiteProjection t n)),
            e.hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
  sorry

end AlgebraicGeometry.ProEtale.SNCTameExtension
