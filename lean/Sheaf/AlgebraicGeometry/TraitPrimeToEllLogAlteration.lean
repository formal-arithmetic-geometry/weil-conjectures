module

public import Sheaf.AlgebraicGeometry.GabberModificationData
public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.LogRegularPair
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective

import WeilConjectures.AlgebraicGeometry.NormalScheme
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product
import WeilConjectures.AlgebraicGeometry.FpqcDescentEtale
import Sheaf.AlgebraicGeometry.AdmissibleFreeFiniteQuotient
import Sheaf.AlgebraicGeometry.BirationalIsomorphismDenseOpen
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.RingTheory.FinitePresentation
import Mathlib.GroupTheory.Sylow

/-!
# Prime-to-ell logarithmic alteration over a trait

Source: ILO, Travaux de Gabber, Exposé XVI 3.7, printed pp.254--255
(blueprint: lem-per-trait-prime-to-ell-log-alteration).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A projective generically finite étale alteration of degree prime to ell, whose regular
source is fs log smooth over a finite extension of the original trait.

The base log structure is identified, over its structural map, with the prescribed
functions invertible on the generic open D(pi). Charts use the multiplicative form
of N, the actual monoid-ring comparison, injective group map and invertible finite
torsion cokernel. The residue degree at the generic point is the function-field degree.

Source: ILO XVI 3.7, printed pp.254--255
(blueprint: lem-per-trait-prime-to-ell-log-alteration).

Proof (the accepted Q108 DAG split; the five geometric inputs remain unsplit):

1. Apply [lem-per-trait-semistable-galois-alteration] to the given $X/S$. Obtain $G$,
$S^{\prime}$, $a:X^{\prime}\to X$, and a nonempty open $U\subset X$ with $E=a^{-1}U\to U$ a
connected finite etale $G$-torsor. Retain its $G$-stable divisorial fs log structure: $X^{\prime}$
is integral, regular, log regular, and log smooth over $S^{\prime}$. This input already includes
normalization of the constants; we do not make an additional arbitrary-degree base change of $X$.
Schemes finite type over the Noetherian traits are Noetherian by
[lem-weil-pbc-finite-type-over-noetherian].
Uses: lem-per-trait-semistable-galois-alteration, lem-weil-pbc-finite-type-over-noetherian.

2. Choose an $\ell$-Sylow subgroup $H\le G$ using [lem-weil-pbc-sylow-subgroup-prime-index]. Thus
$\#H=\ell^r$ and $d=[G:H]>0$ is prime to $\ell$. Put
$T=\operatorname{Spec}(\Gamma(S^{\prime},\mathcal O)^H)$. The order of $H$ is invertible on $S$,
so [lem-per-tame-trait-quotient-log-etale] makes $T$ a complete strictly henselian trait finite
dominant over $S$, and makes $X^{\prime}\to T$ log smooth. It is again of mixed characteristic:
$\operatorname{Frac}((R^{\prime})^H)\subset\operatorname{Frac}R^{\prime}$ has characteristic zero,
and the local inclusion $(R^{\prime})^H\subset R^{\prime}$ embeds the residue field of $T$ into
that of $S^{\prime}$, of characteristic $p>0$. Only the degree of $S^{\prime}\to T$ divides $\#H$;
the action on the trait need not be faithful.
Uses: lem-weil-pbc-sylow-subgroup-prime-index, lem-per-tame-trait-quotient-log-etale.

3. The following explicit embeddings supply the quasi-projective hypotheses used below. Since
$T\to S$ is finite, it is proper and separated by [lem-weil-pbc-finite-proper]. The graph
$X^{\prime}\to X^{\prime}\times_S T$ is a section of the separated projection, hence a closed
immersion by [lem-weil-pbc-separated-base-change] and
[lem-weil-pbc-section-separated-closed-immersion]. Base-changing $X^{\prime}\hookrightarrow\mathbf
P^n_S$ and composing gives $X^{\prime}\hookrightarrow\mathbf P^n_T$. It is of finite type over $T$
by [lemma-nagata-finite-type-to-separated-target]. More generally, in every composition below of a
projective map $Z\hookrightarrow\mathbf P^m_B$ with an immersion $B\hookrightarrow\mathbf P^n_D$,
base change gives an immersion $\mathbf P^m_B\hookrightarrow\mathbf P^m_D\times_D\mathbf P^n_D$,
and the Segre embedding gives $Z\hookrightarrow\mathbf P^{(m+1)(n+1)-1}_D$. These are just
compositions of the cited immersions; [lem-weil-pbc-immersion-base-change-lft],
[lem-weil-pbc-proper-fp-permanence](e), and [lem-chow-segre] justify each arrow. In particular the
resulting quasi-projectivity has the finite-projective-space meaning of the item.
Uses: lem-weil-pbc-finite-proper, lem-weil-pbc-separated-base-change,
lem-weil-pbc-section-separated-closed-immersion, lemma-nagata-finite-type-to-separated-target,
lem-weil-pbc-immersion-base-change-lft, lem-weil-pbc-proper-fp-permanence, lem-chow-segre.

4. For every geometric point of $X^{\prime}$, its $H$-stabilizer has order dividing $\ell^r$. The
residue characteristic is zero or the residue characteristic of $S$, different from $\ell$; the
action is therefore tame. It is generically free since it is free on $E$. All hypotheses of
[lem-per-gabber-log-smooth-equivariant-modification] now hold over $T$: integrality and log
regularity come from Step 1, relative log smoothness from Step 2, and quasi-projectivity from Step
3. Obtain an $H$-equivariant projective birational $h:W\to X^{\prime}$ and the quotient $Q=W/H$
with its fs invariant log structure, log regular and log smooth over $T$. In particular $W$ is
integral and quasi-projective of finite type over $T$.
Uses: lem-per-gabber-log-smooth-equivariant-modification.

5. The composite $W\xrightarrow h X^{\prime}\xrightarrow a X$ is projective by
[lem-trf-h-projective-composition]. Apply [lem-per-projective-finite-group-quotient] with base
$X$: $X$ is Noetherian and quasi-projective over the affine Noetherian $S$, and $W\to X$ is
projective, hence quasi-projective. It gives a finite surjective quotient $q:W\to Q$, an integral
$Q$, and a projective $v:Q\to X$. The categorical quotient is the same $Q$ as in Step 4 by the two
universal properties. Applying the same theorem with base $T$ gives $Q/T$ quasi-projective of
finite type. Step 3 makes $W/S$ quasi-projective from $h$ and $X^{\prime}/S$, so applying the
quotient theorem with base $S$ gives $Q/S$ quasi-projective of finite type as well. These are the
same scheme quotient and the induced structure maps, by uniqueness of categorical quotients.
Uses: lem-trf-h-projective-composition, lem-per-projective-finite-group-quotient.

6. Write $T=\operatorname{Spec}A$. It is a mixed-characteristic discrete valuation ring, so
$\operatorname{Frac}A$ has characteristic zero. Apply the DVR clause of
[lem-per-characteristic-zero-dedekind-excellent] to obtain excellence of $A$. This uses the
characteristic-zero Dedekind theorem, not the excluded complete-local excellence interface. The
integral fs log-regular $Q$, quasi-projective of finite type over $T$, now meets every hypothesis
of [lem-per-log-regular-projective-log-resolution]. Obtain a projective birational saturated
log-blowup tower $b:(Y,M_Y)\to Q$ with $Y$ integral and regular. That statement also says that the
composite $Y\to Q\to T$ is log smooth. No purity assertion is invoked.
Uses: lem-per-characteristic-zero-dedekind-excellent,
lem-per-log-regular-projective-log-resolution.

7. Set $f=v\circ b:Y\to X$. It is projective by [lem-trf-h-projective-composition]. Step 3 applied
to $b$ and each of $Q/T$, $Q/S$ gives finite-projective-space immersions of $Y$ over both $T$ and
$S$. Finite type follows from [lem-sfb-finite-type-composition-base-change], since a projective
embedding over a Noetherian base is finite type. All maps commute over $S$. To use proper images
below, projective maps are proper: the projective-space projections are proper by
[lemma-nagata-projective-space-base-change-proper], closed immersions are proper and proper maps
compose by [lem-weil-pbc-proper-fp-permanence].
Uses: lem-trf-h-projective-composition, lem-sfb-finite-type-composition-base-change,
lemma-nagata-projective-space-base-change-proper, lem-weil-pbc-proper-fp-permanence.

8. Apply [lem-sfb-birational-isomorphism-dense-open] to $h$. Its projectivity gives separatedness,
and finite type over the Noetherian models gives local finite presentation by
[lem-weil-pbc-finite-type-noetherian-finite-presentation] on affines. Intersect the isomorphism
open in $X^{\prime}$ with its finitely many $H$-translates. Inside the original torsor open, the
complement has closed image under the finite $a$ and that image misses the generic point. Remove
it and choose a nonempty affine subopen $U_1\subset U$. Then $W_{U_1}=X^{\prime}_{U_1}=E_1$ is the
connected finite etale $G$-torsor. Quotient restriction in
[lem-per-projective-finite-group-quotient] identifies $Q_{U_1}$ with its categorical $H$-quotient.
Since $E_1$ is affine, its free $H$-action meets the affine-orbit hypothesis of
[lem-sfb-admissible-free-finite-quotient]; that theorem identifies this same quotient with the
fppf sheaf $E_1/H$.
Uses: lem-sfb-birational-isomorphism-dense-open,
lem-weil-pbc-finite-type-noetherian-finite-presentation, lem-per-projective-finite-group-quotient,
lem-sfb-admissible-free-finite-quotient.

9. Apply [lem-sfb-admissible-free-finite-quotient] also to the $G$-action on the torsor
$E=a^{-1}U$ itself. Its hypotheses hold: $E$ is open in $X^{\prime}$, which is quasi-projective
over the affine $S$, hence separated; the action is free since it is simply transitive on
geometric fibres of $E\to U$; and $E\to U$ is finite, hence affine
[def-weil-finite-integral-morphism], so the orbit of a point over $u\in U$ lies in the affine
inverse image of an affine neighbourhood of $u$. The theorem's quotient is categorical, so by the
Galois-cover definition [def-sbc-normal-dominant-galois] and uniqueness of categorical quotients
it is $U$, and its action-map clause gives $G\times E\cong E\times_UE$. Pulling back along the
open $U_1\subset U$ gives $G\times E_1\cong E_1\times_{U_1}E_1$. Here is an explicit
identification after this base change, rather than an assumption that arbitrary categorical
quotients commute with it. In the fppf sheaf quotient description from Step 8, write a pair over
$U_1$ uniquely as $(ge,e)$. Send its $H$-orbit to $(Hg,e)$. Conversely $(Hg,e)$ gives the class of
$(ge,e)$; changing the representative $g$ changes only the $H$-orbit. These formulas are inverse
on local sections and glue, so the representing schemes satisfy
$Q_{U_1}\times_{U_1}E_1\cong(H\backslash G)\times E_1$. This has $d=[G:H]$ sheets over $E_1$. The
cover $E_1\to U_1$ is fpqc by [def-weil-pbc-fpqc-covering]: it is finite affine, surjective and
flat, with flatness part of [def-weil-etale-morphism]. Apply [lem-weil-pbc-fpqc-descend-finite]
and [lem-galois-fpqc-descend-etale] to conclude that $Q_{U_1}\to U_1$ is finite etale. At the
generic point set $K=k(U_1)$ and $L=k(E_1)$. The finite generic $K$-algebra $B$ satisfies
$B\otimes_K L\cong L^d$. A $K$-basis of $B$ tensors to an $L$-basis, so $\dim_K B=d$.
Uses: lem-sfb-admissible-free-finite-quotient, def-sbc-normal-dominant-galois,
def-weil-pbc-fpqc-covering, def-weil-etale-morphism, lem-weil-pbc-fpqc-descend-finite,
lem-galois-fpqc-descend-etale, def-weil-finite-integral-morphism.

10. Apply [lem-sfb-birational-isomorphism-dense-open] to $b$, with local finite presentation
checked on the same Noetherian affine charts as in Step 8. Obtain a dense open $V\subset Q$ over
which $b$ is an isomorphism. The projective map $v$ is closed, so $v(Q\setminus V)$ is closed. It
misses the generic point of $X$: Step 9 identifies the generic fibre of $Q/X$ with the spectrum of
its function field, so its only point is the generic point of $Q$, which lies in $V$. Remove this
closed image from $U_1$ to obtain a nonempty open $U_2$. Then $Y_{U_2}=Q_{U_2}$, so $f$ is finite
etale of degree $d$ over $U_2$. Since $Y$ and $X$ are integral, its generic finite algebra is the
field $k(Y)$, and its dimension over $k(X)$ is $d$: after the faithfully flat torsor extension in
Step 9 it becomes $d$ copies of the base field. Hence $[k(Y):k(X)]=d>0$, $f$ is dominant, and
$\ell\nmid d$ by Step 2. Together with Steps 6--7 this gives every clause of the item, without
asserting punctual purity.
Uses: lem-sfb-birational-isomorphism-dense-open,
lem-weil-pbc-finite-type-noetherian-finite-presentation, def-weil-proper-morphism.
-/
theorem exists_trait_primeToEll_log_alteration
    (ell : ℕ) [Fact ell.Prime]
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] [CharZero (FractionRing R)]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    (hell : IsUnit (ell : R))
    (X : Scheme.{u}) [IsIntegral X] (hregular : IsRegularScheme X)
    (s : X ⟶ Spec (.of R)) [Flat s] [LocallyOfFiniteType s] [QuasiCompact s]
    (hqp : GabberModification.QuasiProjective s) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
      (t : Spec (.of A) ⟶ Spec (.of R)),
      IsFinite t ∧ IsDominant t ∧
      ∃ (π : A), IsLocalRing.maximalIdeal A = Ideal.span {π} ∧
      ∃ (M : EtaleLogStructure (Spec (.of A))) (hfs : M.IsFineSaturated),
        (∃ e : M.monoidSheaf.obj ≅ divisorialLogPresheaf
            ((Spec (.of A)).basicOpen ((Scheme.ΓSpecIso (.of A)).inv π)).ι,
          e.hom ≫ divisorialStructuralMap
            ((Spec (.of A)).basicOpen ((Scheme.ΓSpecIso (.of A)).inv π)).ι = M.alpha) ∧
        ∃ (Y : FineSaturatedLogScheme.{u}) (_ : IsIntegral Y.scheme)
          (g : EtaleLogHom Y ⟨Spec (.of A), inferInstance, M, hfs⟩)
          (f : Y.scheme ⟶ X),
          IsRegularScheme Y.scheme ∧
          LocallyOfFiniteType g.base ∧ QuasiCompact g.base ∧
          LocallyOfFiniteType (g.base ≫ t) ∧ QuasiCompact (g.base ≫ t) ∧
          GabberModification.QuasiProjective g.base ∧
          GabberModification.QuasiProjective (g.base ≫ t) ∧
          f ≫ s = g.base ≫ t ∧ IsHProjective f ∧ IsDominant f ∧
          (∀ y : Y.scheme, ∃ c : FSLogChart g,
            y ∈ Set.range c.V.hom ∧
            ∃ e : c.P ≃* Multiplicative (ULift.{u} ℕ),
              (∀ a : c.P, M.alpha.app (op c.W) (c.chartY a) =
                c.W.hom.appTop ((Scheme.ΓSpecIso (.of A)).inv π) ^ (e a).toAdd.down) ∧
              Function.Injective c.groupMap ∧ Finite (CommGroup.torsion c.cokernel) ∧
              (∀ v : c.V.left,
                IsUnit (Nat.card (CommGroup.torsion c.cokernel) : c.V.left.presheaf.stalk v)) ∧
              Smooth c.comparison) ∧
          ∃ (U : X.Opens) (d : ℕ), Nonempty U ∧
            IsFinite (f ∣_ U) ∧ Etale (f ∣_ U) ∧
            0 < d ∧ ¬ ell ∣ d ∧ f.residueDegree (genericPoint Y.scheme) = d := by
  sorry

end AlgebraicGeometry
