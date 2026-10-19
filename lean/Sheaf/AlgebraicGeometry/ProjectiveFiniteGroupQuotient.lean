/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Endomorphism
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import WeilConjectures.RingTheory.GradedPrimeAvoidance
import Sheaf.AlgebraicGeometry.ProjStandardOpenBasis
import Sheaf.AlgebraicGeometry.AffineGroupoidOrbitFibres
import Sheaf.TraceFormula.ProjQcOpenTwistAmple
import WeilConjectures.AlgebraicGeometry.AmpleImmersionAffineBase
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.AdmissibleQuotientAffineIntegralCharts
import Sheaf.AlgebraicGeometry.EquivariantProjectiveEnvelope
import Sheaf.AlgebraicGeometry.FiniteGradedProjMorphism
import Sheaf.AlgebraicGeometry.QuasiprojectiveAffineComposition

/-!
# Finite group quotients preserve relative projectivity

Source: Rydh, Existence and properties of geometric quotients, Theorem 4.4,
Proposition 4.7 and Remark 4.9, pp. 20--23; the finite homogeneous-coordinate proof
in the DAG (blueprint: lem-per-projective-finite-group-quotient).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- A finite group quotient of a finite-type relatively quasi-projective scheme over an
ample Noetherian base is quasi-projective, and is projective when the source is projective.
The quotient is categorical in schemes, finite, surjective, has geometric orbit fibres,
and its structure sheaf consists of invariant sections. Invariant opens descend to opens
and their restricted maps are categorical quotients.

Source: Rydh, Theorem 4.4, Proposition 4.7 and Remark 4.9, pp. 20--23;
finite homogeneous-coordinate construction in the DAG
(blueprint: lem-per-projective-finite-group-quotient).

Proof plan (the numbered DAG proof steps, with their dependencies):
1. Choose an affine Noetherian scheme $S=\operatorname{Spec}R$ over which $B$ has the stated
finite projective-space immersion $B\hookrightarrow\mathbf P^m_S$. This immersion is locally of
finite type by [lem-weil-pbc-immersion-base-change-lft]; it is quasi-compact because every open of
the Noetherian scheme $B$ is quasi-compact [lem-weil-pbc-noetherian-open-subscheme-noetherian], so
it is of finite type [def-weil-finite-type-morphism]. The projection $\mathbf P^m_S\to S$ is
proper [lem-kun-projective-implies-proper], hence of finite type, so $B\to S$ is of finite type by
[lem-sfb-finite-type-composition-base-change], and so is $V\to S$. By
[lem-per-quasiprojective-affine-composition], the composite $V\to S$ has such an immersion too.
Apply [lem-per-equivariant-projective-envelope] to obtain an equivariant open immersion $V\subset
M=\operatorname{Proj}(A)$ with $A$ a graded quotient of a polynomial ring over $R$, generated in
degree one. Put $R_0=A_0$; this is a quotient of $R$, and $H$ fixes it. Write
$C=A^H=\bigoplus_{n\geq0}(A_n)^H$, so $C_0=R_0$. The equality of graded components follows by
applying each $h$ to the unique homogeneous decomposition of an invariant element. Uses:
lem-weil-pbc-immersion-base-change-lft, lem-weil-pbc-noetherian-open-subscheme-noetherian,
def-weil-finite-type-morphism, lem-kun-projective-implies-proper,
lem-sfb-finite-type-composition-base-change, lem-per-quasiprojective-affine-composition,
lem-per-equivariant-projective-envelope.

2. For each degree-one generator $a_i$ of $A$ over $R$, the orbit polynomial $\prod_{h\in
H}(T-h(a_i))$ is monic with coefficients in $C$ and vanishes at $a_i$. Let $e=|H|\geq1$. Reducing
powers with these monic relations shows that the finitely many monomials $\prod_i a_i^{j_i}$,
$0\leq j_i<e$, span $A$ over $C$: induction on the total degree of a monomial reduces any exponent
at least $e$. Apply [lem-per-artin-tate-subalgebra-finite-type] to $R\to C\subseteq A$. It gives
that $C$ is of finite type over $R$, hence over $C_0=R_0$. Replacing a finite generating family by
its finitely many homogeneous components gives homogeneous generators: all those components are
invariant because the action preserves degrees. The injective graded extension $C\subseteq A$ is
therefore module finite and satisfies every hypothesis of [lem-per-finite-graded-proj-morphism].
Obtain a finite surjective map $r:M\to P=\operatorname{Proj}(C)$ with the stated standard-open
chart maps. Uses: lem-per-artin-tate-subalgebra-finite-type, lem-per-finite-graded-proj-morphism.

3. Both $M$ and its invariant open $V$ have admissible actions. Here is the affine-neighbourhood
argument. For a finite orbit $E\subset V$, let $J$ be the homogeneous ideal generated by the
positive-degree homogeneous $u$ with $D_+(u)\subset V$. The standard-open basis covers $V$, so $J$
cuts out its complement. The graded ideal $J\cap A_+$ is not contained in any of the finitely many
homogeneous primes belonging to $E$: for each such prime take an element of $J$ outside it and
multiply by a positive-degree element outside it. By [lem-sc-graded-prime-avoidance], choose a
positive-degree homogeneous $t\in J$ avoiding all of $E$. Then $f=\prod_{h\in H}h(t)$ is
homogeneous invariant, avoids all of $E$, and $D_+(f)=\bigcap_h D_+(h(t))\subset V$. It is affine
by [lem-sc-proj-standard-open-basis]. These opens cover $V$. The same argument with $J=A_+$ covers
$M$ by invariant affine standard opens. Thus [lem-per-admissible-quotient-affine-integral-charts]
gives categorical quotients for $M$ and $V$, with geometric orbit fibres, invariant structure
sheaf, and compatibility with invariant open restrictions. Uses: lem-sc-graded-prime-avoidance,
lem-sc-proj-standard-open-basis, lem-per-admissible-quotient-affine-integral-charts.

4. For a positive-degree homogeneous $f\in C$, the inverse image of $D_+(f)\subset P$ under $r$ is
$D_+(f)\subset M$, with coordinate ring $A_{(f),0}$, by [lem-per-finite-graded-proj-morphism]. One
has $(A_{(f),0})^H=C_{(f),0}$. To prove this even with zero divisors, write an invariant element
as $a/f^m$. Each $h(a)-a$ is killed by a power of $f$; a common exponent $k$ exists since $H$ is
finite. Then $af^k$ is invariant and $a/f^m=(af^k)/f^{m+k}$ lies in $C_{(f),0}$. Localization
preserves the inclusion $C\subseteq A$, proving the reverse injection. This equality is compatible
with further homogeneous localization since both restriction maps send a fraction to that same
fraction. The standard affine basis of [lem-sc-proj-standard-open-basis] therefore gives $\mathcal
O_P=(r_*\mathcal O_M)^H$ as sheaves. Uses: lem-per-finite-graded-proj-morphism,
lem-sc-proj-standard-open-basis.

5. On each affine chart above, apply [lem-a1-affine-groupoid-orbit-fibres] to $\coprod_{h\in
H}D_+(f)\rightrightarrows D_+(f)$. The source is the fold map, the target restricts to the
automorphism $h$ on its copy, and multiplication and inverse in $H$ give the groupoid structure.
Both projections are finite locally free: on coordinate modules they are a finite free sum of
copies of the chart ring, with the second sum identified by the automorphisms. Its equalizer is
exactly $(A_{(f),0})^H=C_{(f),0}$. Thus the fibres of $r$ on points and on algebraically closed
field-valued points are exactly $H$-orbits. The finite map $r$ is proper by
[lem-weil-pbc-finite-proper], hence closed; together with surjectivity this makes its topology the
quotient topology. The quotient $q_M:M\to Y$ supplied in Step 3 has that same orbit topology and
invariant structure sheaf, by [lem-per-admissible-quotient-affine-integral-charts]. The unique
homeomorphism $Y\cong P$ induced by the common orbit set identifies their sheaves, since both are
the sheaf of invariant sections of $\mathcal O_M$ on the same inverse-image opens. It is therefore
an isomorphism of schemes commuting with the quotient maps. In particular $r$ is categorical. The
invariant-open restriction clause of the same node now shows that $Q=r(V)$ is open, $r^{-1}Q=V$,
and $q=r|_V:V\to Q$ is its categorical geometric quotient. It is finite by restriction of the
finite affine chart maps of $r$, and surjective. This restriction clause also proves the assertion
for every invariant open of $V$. Uses: lem-a1-affine-groupoid-orbit-fibres,
lem-weil-pbc-finite-proper, lem-per-admissible-quotient-affine-integral-charts.

6. The scheme $P=\operatorname{Proj}(C)$ is proper over $\operatorname{Spec}R_0$ by
[lem-per-finite-type-graded-proj-proper], since Step 2 proved the required finite generation. In
particular it is quasi-compact and locally of finite type. By [lem-trf-proj-qc-open-twist-ample]
applied with the whole open $P$, a positive twist is an ample invertible module on $P$. Apply
[lem-weil-pbc-ample-very-ample-immersion-affine-base] over $R_0$ to obtain an immersion
$P\hookrightarrow\mathbf P^n_{R_0}$. This immersion is proper by
[lemma-nagata-proper-to-separated-target], since $P$ is proper over $R_0$ and projective space is
separated (its properness follows from [lem-kun-projective-implies-proper]). It is a closed
immersion by [lem-weil-pbc-proper-immersion-closed]. Because $R\twoheadrightarrow R_0$, the map
$\operatorname{Spec}R_0\hookrightarrow\operatorname{Spec}R$ is a closed immersion by
[lem-weil-pbc-spec-quotient-closed-immersion], and so is its base change $\mathbf
P^n_{R_0}=\mathbf P^n_R\times_{\operatorname{Spec}R}\operatorname{Spec}R_0\hookrightarrow\mathbf
P^n_R$ by [lem-weil-pbc-closed-immersion-base-change]. The composite $P\hookrightarrow\mathbf
P^n_R$ is a closed immersion by [lem-weil-pbc-closed-immersion-comp]. The open $Q\subset P$ is
$P\cap W$ for the open $W=\mathbf P^n_R\setminus(P\setminus Q)$, and $Q\to W$ is a closed
immersion by [lem-weil-pbc-closed-immersion-base-change]; so $Q\to\mathbf P^n_R$ is an immersion.
Uses: lem-per-finite-type-graded-proj-proper, lem-trf-proj-qc-open-twist-ample,
lem-weil-pbc-ample-very-ample-immersion-affine-base, lemma-nagata-proper-to-separated-target,
lem-kun-projective-implies-proper, lem-weil-pbc-proper-immersion-closed,
lem-weil-pbc-spec-quotient-closed-immersion, lem-weil-pbc-closed-immersion-base-change,
lem-weil-pbc-closed-immersion-comp.

7. The invariant map $V\to B$ descends uniquely to $Q\to B$ by the categorical property proved in
Step 5. Since $B\to S$ is quasi-projective, it is separated: a locally closed subscheme of
projective space has closed diagonal, by restricting the diagonal of that separated projective
space. The graph $Q\to Q\times_S B$ is consequently closed, as the pullback of this diagonal. The
immersion $Q\hookrightarrow\mathbf P^n_S$ from Step 6 base changes to an immersion $Q\times_S
B\hookrightarrow\mathbf P^n_B$ by [lem-weil-pbc-immersion-base-change-lft]; it is a closed
immersion into an open $U\subseteq\mathbf P^n_B$, and composing with the closed graph gives a
closed immersion $Q\to U$ [lem-weil-pbc-closed-immersion-comp], i.e. the desired finite
projective-space immersion over $B$. The scheme $P$ is Noetherian by
[lem-weil-pbc-finite-type-over-noetherian], applied over $\operatorname{Spec}R_0$; that base is
Noetherian: ideals of $R_0$ are quotients of ideals of $R$, hence finitely generated, and
[pqf-def-locnoeth] applies to its one affine chart. Its open $Q$ is Noetherian by
[lem-weil-pbc-noetherian-open-subscheme-noetherian]. Every inverse image of an affine open of $B$
is therefore quasi-compact. The immersion $Q\to\mathbf P^n_B$ is locally of finite type by
[lem-weil-pbc-immersion-base-change-lft] and quasi-compact since $Q$ is Noetherian, so of finite
type [def-weil-finite-type-morphism]; $\mathbf P^n_B\to B$ is proper
[lem-kun-projective-implies-proper], hence separated and of finite type. Thus $Q\to B$ is of
finite type by [lem-sfb-finite-type-composition-base-change]. It is separated: the immersion is a
monomorphism, so its diagonal is an isomorphism, and the diagonal of $Q$ over $B$ is the inverse
image of the closed diagonal of $\mathbf P^n_B$. Uses: lem-weil-pbc-immersion-base-change-lft,
lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-noetherian-open-subscheme-noetherian,
def-weil-finite-type-morphism, pqf-def-locnoeth, lem-kun-projective-implies-proper,
lem-weil-pbc-closed-immersion-comp, lem-sfb-finite-type-composition-base-change.

8. If $V\to B$ is projective, it is proper by [lem-kun-projective-implies-proper]. We check
universal closedness of $Q\to B$ directly. After any base change $B^\prime\to B$, the map
$q^\prime:V\times_B B^\prime\to Q\times_B B^\prime$ is surjective by
[lem-weil-pbc-surjective-base-change]. For any closed subset $Z$ of $Q\times_B B^\prime$, its
inverse image under $q^\prime$ is closed, and its image in $B^\prime$ is closed since $V\to B$ is
universally closed. Surjectivity makes this image precisely the image of $Z$. Thus $Q\to B$ is
universally closed; it is separated and of finite type by Step 7, so proper by
[def-weil-proper-morphism]. The immersion $Q\hookrightarrow\mathbf P^n_B$ of Step 7 is proper by
[lemma-nagata-proper-to-separated-target] and [lem-kun-projective-implies-proper]. Apply
[lem-weil-pbc-proper-immersion-closed] to make it a closed immersion. This is exactly projectivity
in [def-kun-projective], with a finite number of coordinates. Uses:
lem-kun-projective-implies-proper, lem-weil-pbc-surjective-base-change, def-weil-proper-morphism,
lemma-nagata-proper-to-separated-target, lem-weil-pbc-proper-immersion-closed, def-kun-projective.

9. If $V$ is integral, the continuous surjection $q$ implies that $Q$ is nonempty and irreducible:
two nonempty opens of $Q$ have nonempty inverse images in the irreducible space $V$, hence
intersect. For an affine open $W\subset Q$, Step 5 identifies $q^{-1}W$ with an affine open of
$V$, and $\mathcal O_Q(W)$ with the invariant subring of its coordinate ring. When $W$ is
nonempty, that coordinate ring is a domain because $V$ is integral, and its invariant subring is a
domain as well. Thus every nonempty affine open of $Q$ has a domain as its ring of functions, so
$Q$ is integral in [def-pc-integral-scheme]. This proves the remaining clause without assuming
that the action is faithful or tame. Uses: def-pc-integral-scheme,
lem-per-admissible-quotient-affine-integral-charts. -/
theorem exists_finiteGroup_quotient_of_quasiProjective
    (B V : Scheme.{u}) [IsNoetherian B]
    (hB : ∃ (R : Type u) (_ : CommRing R) (_ : IsNoetherianRing R)
      (b : B ⟶ Spec (.of R)) (ι : Type u) (_ : Finite ι)
      (j : B ⟶ ℙ(ι; Spec (.of R))),
      IsImmersion j ∧ j ≫ ℙ(ι; Spec (.of R)) ↘ Spec (.of R) = b)
    (f : V ⟶ B) [LocallyOfFiniteType f] [QuasiCompact f]
    (hV : ∃ (ι : Type u) (_ : Finite ι) (j : V ⟶ ℙ(ι; B)),
      IsImmersion j ∧ j ≫ ℙ(ι; B) ↘ B = f)
    (H : Type v) [Group H] [Finite H] (a : H →* Aut V)
    (ha : ∀ h : H, (a h).hom ≫ f = f) :
    ∃ (Q : Scheme.{u}) (q : V ⟶ Q) (g : Q ⟶ B),
      q ≫ g = f ∧ IsFinite q ∧ Surjective q ∧
      (∀ h : H, (a h).hom ≫ q = q) ∧
      Topology.IsQuotientMap q ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
        Function.Surjective (fun x : Spec (.of Ω) ⟶ V ↦ x ≫ q) ∧
        ∀ x y : Spec (.of Ω) ⟶ V,
          x ≫ q = y ≫ q ↔ ∃ h : H, x ≫ (a h).hom = y) ∧
      (∀ W : Q.Opens, Function.Injective (q.app W).hom ∧
        ∀ s : Γ(V, q ⁻¹ᵁ W),
          s ∈ Set.range (q.app W).hom ↔
            ∀ (h : H) (T : V.Opens) (hT : T ≤ q ⁻¹ᵁ W)
              (hTh : T ≤ (a h).hom ⁻¹ᵁ (q ⁻¹ᵁ W)),
              ((a h).hom.appLE (q ⁻¹ᵁ W) T hTh).hom s =
                (V.presheaf.map (homOfLE hT).op).hom s) ∧
      (∀ (Z : Scheme.{u}) (t : V ⟶ Z),
        (∀ h : H, (a h).hom ≫ t = t) → ∃! d : Q ⟶ Z, q ≫ d = t) ∧
      (∃ (ι : Type u) (_ : Finite ι) (j : Q ⟶ ℙ(ι; B)),
        IsImmersion j ∧ j ≫ ℙ(ι; B) ↘ B = g) ∧
      LocallyOfFiniteType g ∧ QuasiCompact g ∧
      (IsHProjective f → IsHProjective g) ∧ (IsIntegral V → IsIntegral Q) ∧
      ∀ (U : V.Opens) (hU : ∀ h : H, U ≤ (a h).hom ⁻¹ᵁ U),
        ∃ (W : Q.Opens) (qU : U.toScheme ⟶ W.toScheme),
          q ⁻¹ᵁ W = U ∧ qU ≫ W.ι = U.ι ≫ q ∧
          IsFinite qU ∧ Surjective qU ∧
          ∀ (Z : Scheme.{u}) (t : U.toScheme ⟶ Z),
            (∀ h : H, (a h).hom.resLE U U (hU h) ≫ t = t) →
              ∃! d : W.toScheme ⟶ Z, qU ≫ d = t := by
  sorry

end AlgebraicGeometry
