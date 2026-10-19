/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.CommAlgCat.Basic
import WeilConjectures.RingTheory.CohenRingsExist
import WeilConjectures.RingTheory.CohenRingLiftToCompleteLocal
import Mathlib.RingTheory.Henselian
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.RegularLocalQuotientKernelParameters
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients
import Sheaf.RingTheory.CompleteLocalExcellent
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.RingTheory.ExcellentRing
import WeilConjectures.RingTheory.GRingCompletionRegular
import Sheaf.RingTheory.PopescuSmoothing
import WeilConjectures.CategoryTheory.ExistsDirectedReindexing
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Sheaf.RingTheory.FilteredColimitFiniteData
import WeilConjectures.RingTheory.SmoothFibreRegularLocal
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.FiniteType
import WeilConjectures.RingTheory.LocalizationOfRegularRing
import Sheaf.RingTheory.RegularLocalLiftRegularSequenceQuotient
import Sheaf.RingTheory.RegularSequencePrincipalNeighbourhood
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Blowup.BlowupUniversal
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Sheaf.AlgebraicGeometry.LimitAffineTransition

/-!
# Simultaneous approximation of a complete mixed-characteristic regular local pair

Source: ILO, Travaux de Gabber, Expose XVI §3.7, first paragraph (printed p.254), with
Cohen's structure theorem (I 2.9, p.9) and Popescu smoothing (I 10.3(i), p.17).
The precise simultaneous formulation is the agent-formulated algebraic input of
(blueprint: lem-per-complete-mixed-regular-pair-approximation).

The affine inverse system is expressed contravariantly by a directed diagram `B` of
`C`-algebras and its compatible quotient diagram `G`. The two ring-colimit cocones,
and their square with the residue map, specify the limit of pairs. No arbitrary
identification of the limiting closed immersion is substituted for that square.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace RingTheory

/-- Simultaneously approximate the complete regular local ring and its closed point, keeping
its ordered parameters. Source: ILO XVI §3.7, first paragraph, printed p.254; I 2.9 and I 10.3(i).
(blueprint: lem-per-complete-mixed-regular-pair-approximation)

Here `k` is `IsLocalRing.ResidueField R`, `Vᵢ = Spec (B.obj i)` and `Zᵢ = Spec (G.obj i)`.
The kernel and surjectivity conditions identify `Zᵢ` with the zero scheme of `s i`.
`CharP (G.obj i) p` gives its canonical F_p-scheme structure. Spectra are affine and
all their transition morphisms are affine. Finite type affine schemes over `Spec C`
are quasi-projective: algebra generators embed them into affine space over `C`,
and affine space is open in projective space. `CharZero R` expresses the characteristic
zero of its fraction field, since a regular local ring is a domain.

Proof (the twelve steps of the DAG node):
1. Choose a Cohen ring $C$ with $C/pC\simeq k$ by [lem-weil-pbc-cohen-rings-exist], and lift this
residue isomorphism to $C\to R$ by [lem-weil-pbc-cohen-ring-lift-complete-local]. The regular
local ring $R$ is a domain by [lem-sc-regular-local-domain]. This map is local: an element outside
$pC$ has nonzero residue in $k$ and hence is a unit in $R$. It is injective: every nonzero element
of the DVR $C$ is a unit times $p^n$, and $p^n\ne0$ in the characteristic-zero domain $R$.
Completeness makes $C$ henselian by [lem-weil-pbc-complete-pair-henselian], and $k$ is separably
closed, so $\operatorname{Spec}C$ is a complete strictly henselian mixed-characteristic trait.
Since $\ell$ is invertible in the local ring $R$, $\ell\ne p$; its residue in $C/pC$ is nonzero,
so $\ell$ is invertible in $C$.

2. Put $P=C[[X_1,\ldots,X_d]]$, with maximal ideal $\mathfrak n=(p,X_1,\ldots,X_d)$. The
power-series structure theorem [lem-weil-pbc-power-series-field-cohen-regular-complete] makes $P$
complete regular local of dimension $d+1$. The continuous map $\pi:P\to R$, $X_a\mapsto t_a$,
exists by summing power series in the complete ring $R$. It is surjective by the following
explicit expansion. For $r\in R$, lift its residue to $c_0\in C$. If a polynomial approximation
has error in $\mathfrak m^N$, write that error modulo $\mathfrak m^{N+1}$ as a finite sum of
degree-$N$ monomials in the $t_a$ with coefficients in $k$, and lift these coefficients to $C$.
Adding the corresponding degree-$N$ polynomial improves the error to $\mathfrak m^{N+1}$. The
successive homogeneous polynomials define a series in $P$ mapping to $r$. The map is local, with
the prescribed residue identification and prescribed ordered parameters.

3. By [lem-weil-pbc-regular-local-quotient-kernel-parameters], $\ker\pi$ is generated by an
initial part of a parameter system of $P$. By
[lem-weil-pbc-regular-local-generators-regular-sequence], quotienting by $c$ such parameters has
dimension $d+1-c$. Since $P/\ker\pi\simeq R$ has dimension $d$, $c=1$; write $\ker\pi=(h)$ with
$h\notin\mathfrak n^2$. Express $p=\sum_a t_a r_a$ in $R$, lift $r_a$ to $b_a\in P$, and set
$f=p-\sum_aX_ab_a$. Then $f\in\ker\pi$ and its image in $\mathfrak n/\mathfrak n^2$ has
coefficient $1$ on the basis vector $p$. In particular $f\notin\mathfrak n^2$. Writing $f=uh$
forces $u$ to be a unit, since otherwise $uh\in\mathfrak n^2$. Thus $R=P/(f)$, compatibly with
$t_a=X_a\bmod f$, and $f\bmod(X_1,\ldots,X_d)=p$.

4. Let $A=C[X_1,\ldots,X_d]$ and $J=(p,X_1,\ldots,X_d)$. Its $J$-adic completion is $P$: at level
$N$, both $A/J^N$ and $P/(JP)^N$ consist uniquely of the finitely many monomials $X^E$ with
$|E|<N$, their coefficients taken modulo $p^{N-|E|}$. The criterion in
[lem-weil-pbc-power-series-combined-ideal-coefficients] gives this description on $P$; on
polynomials it is the expansion of the generators of $J^N$. Hence the compatible finite quotient
maps are isomorphisms. Taking their inverse limits and using the completeness of $P$ from
[lem-weil-pbc-power-series-field-cohen-regular-complete] identifies $\widehat A_J$ with $P$, as
$A$-algebras. This argument also checks that the map is the canonical completion map, not an
unspecified isomorphism.

5. The complete Noetherian local ring $C$ is excellent by [lem-per-complete-local-excellence].
Thus $A$ is excellent by [lem-exc-finite-type-localization-excellent], and is a G-ring by the
definition [def-exc-excellent-ring]. Apply [lem-weil-pbc-g-ring-completion-regular] to $A,J$ and
the canonical identification of Step 4: $A\to P$ is regular. Both rings are Noetherian. By
[lem-weil-pbc-popescu-smoothing], $P$ is a small filtered colimit of smooth $A$-algebras. Popescu
gives smooth morphisms $\operatorname{Spec}B\to\operatorname{Spec}A$; by
[lem-weil-pbc-smooth-ring-map-iff-smooth-affine] each $A\to B$ is a smooth ring map, so it is
finitely presented by [def-weil-pbc-smooth-ring-map]. By
[lem-weil-pbc-filtered-category-directed-cofinal], reindex this diagram by a small nonempty
directed set $I_0$, writing $P=\operatorname{colim}_iB_i$. The same lemma preserves the colimit
cocone, so the maps to $P$ remain $A$-algebra maps.

6. By finite-data descent [lemma-nagata-filtered-colimit-finite-data], all $b_a$ lift to one
$B_{i_0}$. Restrict to $i\ge i_0$ and let $b_{i,a}$ be their compatible images. Define
$f_i=p-\sum_aX_ab_{i,a}$ and $E_i=B_i/(f_i)$. The $E_i$ form a compatible system with colimit
$P/(f)=R$. Indeed a compatible family of ring maps out of the $E_i$ is exactly a compatible family
out of the $B_i$ killing all $f_i$, equivalently a map out of $P$ killing $f$. Also
$E_i/(X_1,\ldots,X_d)=B_i/(p,X_1,\ldots,X_d)$. This is a smooth $k$-algebra by
[lem-weil-pbc-smooth-ring-map-base-change-composition], hence regular by
[lem-weil-pbc-smooth-fibre-regular-local]. The structural map $E_i\to R\to k$ is surjective
because it contains the surjection $C\to k$; denote its maximal kernel by $q_i$.

7. We check the local sequence at $q_i$, without assuming regularity has descended. Let
$Q_i\subset B_i$ be the inverse image of $q_i$ and $T=(B_i)_{Q_i}$. Smoothness makes $B_i$ flat
over $A$ by [lem-weil-pbc-smooth-ring-map-flat]. The sequence $X_1,\ldots,X_d,p$ is regular on
$A$: successive quotients by the variables are polynomial rings over the domain $C$, and the final
quotient by $p$ is $k$. Tensoring the injective multiplication maps of this sequence with the flat
module $B_i$, using [lem-weil-pbc-flat-tensor-exact], preserves their injectivity. Localization at
$Q_i$ preserves each injection: if $x(y/s)=0$, some $v$ outside $Q_i$ satisfies $vxy=0$ in the
relevant quotient, hence $vy=0$ by injectivity there, and $y/s=0$. Every resulting quotient in $T$
is nonzero because all these elements lie in $Q_i$. Since $f_i=p$ modulo the variables,
$X_1,\ldots,X_d,f_i$ is a regular sequence in $T$. The Noetherian local permutation lemma
[lem-weil-pbc-regular-sequence-permutation-noetherian-local] makes $f_i,X_1,\ldots,X_d$ regular.
Consequently the ordered variables are a regular sequence in $(E_i)_{q_i}=T/(f_i)$. Here $T$ is
Noetherian: $B_i$ is finite type over the Noetherian ring $A$, by
[lem-weil-pbc-finite-type-algebra-noetherian].

8. The quotient of $(E_i)_{q_i}$ by the variables is a localization of the regular ring of Step 6,
so is regular local by [lem-weil-pbc-localization-of-regular-ring]. Together with Step 7,
[lem-exc-regular-local-lift-regular-sequence-quotient] makes $(E_i)_{q_i}$ regular local. The ring
$E_i$ is finite type over $C$, hence excellent by [lem-exc-finite-type-localization-excellent].
Its regular locus is open by the J-2 clause of [def-exc-excellent-ring], applied to $E_i$ as a
finite type algebra over itself. Choose a principal open containing $q_i$ inside that locus. By
[lem-exc-regular-sequence-principal-neighbourhood], shrink once more around $q_i$ so that the
prescribed ordered variables form a regular sequence on the whole affine ring. Every inverted
element has nonzero image in $k$, hence maps to a unit in $R$; therefore $E_i\to R$ extends across
each shrink.

9. The resulting regular affine Noetherian scheme has finitely many irreducible components by
[lem-weil-pbc-noetherian-finitely-many-components]. Its local rings are domains by
[lem-sc-regular-local-domain]; hence different irreducible components cannot meet, since a local
domain has a unique minimal prime. Remove all components except the one through $q_i$, and choose
a principal open still containing $q_i$ in this complement. Its ring $F_i$ is a domain. To see
reducedness explicitly, a nilpotent element becomes zero in each local domain; if it were nonzero
its proper annihilator would lie in a maximal ideal and its localization there would be nonzero.
Thus the ring is reduced, and having just one minimal prime makes it a domain. This shrink
preserves the regular sequence: all multiplication injections remain injective under localization
by [lem-pc-localization-preserves-nonzerodivisor], and the final quotient is nonzero because $q_i$
remains. The composite of the successive principal shrinks is itself a principal shrink of $E_i$.

10. Use all good principal shrinks, not independently chosen unrelated models. An index is
$(i,g)$, $i\ge i_0$, where $g\in E_i\setminus q_i$ and $(E_i)_g$ is integral regular with the
ordered variables a regular sequence. Step 9 supplies such an index over every $i$. Put
$(i,g)\preceq(j,h)$ if $i\le j$ and the image of $g$ is a unit in $(E_j)_h$; the transition is the
unique map induced by $E_i\to E_j$. Any two indices have an upper bound: first choose $j$ above
both stages, then take a good principal shrink at $j$ and also invert the images of both
denominators. These images avoid $q_j$, so the shrink remains nonempty and good. This is a small
directed preorder; apply [lem-weil-pbc-filtered-category-directed-cofinal] to its thin filtered
category to obtain a directed set $I$. The colimit is still $R$: every element of $R$ lifts to
some $E_i$ and hence to a good shrink; a fraction mapping to zero has numerator zero in $R$, thus
that numerator vanishes at a later $E_j$ by [lem-weil-pbc-filtered-colimit-rings-zero] and then in
a common good upper shrink. Denominators map to units in $R$, so all maps to $R$ exist.

11. For an index of the final directed set write $F_i$ for its ring. It is a finite type
$C$-algebra, as $B_j$ is finite presentation over $A=C[X_1,\ldots,X_d]$ and the construction uses
one quotient and one principal localization. The map $C\to F_i\to R$ is injective on $C$. Since
$F_i$ is a domain, this makes it torsion free over the PID $C$, hence flat by
[lem-weil-pbc-pid-torsion-free-module-flat]. Thus $V_i=\operatorname{Spec}F_i$ is integral regular
affine, flat and finite type over $S$. Set $Z_i=\operatorname{Spec}(F_i/(X_1,\ldots,X_d))$. Its
ring is a principal localization of $B_j/(p,X_1,\ldots,X_d)$, so it is regular by
[lem-weil-pbc-localization-of-regular-ring] and Step 6, and it is an $\mathbf F_p$-algebra. The
closed immersion is cut out by the displayed regular sequence of length $d$. All transition maps
preserve the variables because the original diagram is over $A$; therefore these closed immersions
and their equations are compatible.

12. By Step 10, $\operatorname{colim}_iF_i=R$. Quotienting the compatible variables gives
$\operatorname{colim}_iF_i/(X_1,\ldots,X_d)=R/(t_1,\ldots,t_d)=k$: a map from the left-hand
colimit is exactly a compatible family of maps from $F_i$ killing the variables, equivalently a
map from $R$ killing the $t_a$. By [lem-weil-pbc-limit-affine-transition-core] and
[lem-weil-pbc-limit-affine-transition-affine-comparison], taking spectra identifies the limits of
the two affine systems with $\operatorname{Spec}R$ and $\operatorname{Spec}k$, compatibly with the
closed immersion and with the functions $t_a$. All transitions between affine schemes are affine.
Finally choose finitely many algebra generators of each $F_i$ over $C$; the resulting surjection
from a polynomial algebra gives a closed immersion $V_i\hookrightarrow\mathbf A^n_S\subset\mathbf
P^n_S$, verifying quasi-projectivity as claimed.
-/
theorem exists_complete_mixed_regular_pair_approximation
    (R : Type u) [CommRing R] [IsRegularLocalRing R] [CharZero R]
    [IsStrictlyHenselianLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (p ℓ d : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField R) p]
    (hℓ : ℓ.Prime) (hℓR : IsUnit (ℓ : R)) (hd : 1 ≤ d)
    (hdim : ringKrullDim R = (d : WithBot ℕ∞)) (t : Fin d → R)
    (ht : IsLocalRing.IsRegularSystemOfParameters (List.ofFn t))
    (htreg : RingTheory.Sequence.IsRegular R (List.ofFn t)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsDomain C) (_ : IsDiscreteValuationRing C)
      (_ : CharZero C) (_ : IsStrictlyHenselianLocalRing C)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal C) C)
      (_ : CharP (IsLocalRing.ResidueField C) p)
      (e : IsLocalRing.ResidueField C ≃+* IsLocalRing.ResidueField R) (_ : Algebra C R),
      IsUnit (ℓ : C) ∧
      (∀ c : C, e (IsLocalRing.residue C c) =
        IsLocalRing.residue R (algebraMap C R c)) ∧
      ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
        (B : I ⥤ CommAlgCat.{u} C) (G : I ⥤ CommRingCat.{u})
        (q : B ⋙ forget₂ (CommAlgCat.{u} C) CommRingCat.{u} ⟶ G)
        (s : (i : I) → Fin d → B.obj i)
        (ι : B ⟶ (Functor.const I).obj (CommAlgCat.of C R))
        (ν : G ⟶ (Functor.const I).obj (CommRingCat.of (IsLocalRing.ResidueField R))),
        (∀ (i j : I) (f : i ⟶ j) (a : Fin d), B.map f (s i a) = s j a) ∧
        (∀ i : I,
          IsIntegral (Spec (CommRingCat.of (B.obj i))) ∧
          IsRegularScheme (Spec (CommRingCat.of (B.obj i))) ∧
          Flat (Spec.map (CommRingCat.ofHom (algebraMap C (B.obj i)))) ∧
          LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap C (B.obj i)))) ∧
          QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap C (B.obj i))))) ∧
        (∀ i : I,
          IsRegularScheme (Spec (G.obj i)) ∧ CharP (G.obj i) p ∧
          IsClosedImmersion (Spec.map (q.app i)) ∧ Function.Surjective (q.app i) ∧
          RingHom.ker (q.app i).hom = Ideal.ofList (List.ofFn (s i)) ∧
          RingTheory.Sequence.IsRegular (B.obj i) (List.ofFn (s i))) ∧
        Nonempty (IsColimit ((forget₂ (CommAlgCat.{u} C) CommRingCat.{u}).mapCocone
          { pt := CommAlgCat.of C R, ι := ι })) ∧
        Nonempty (IsColimit { pt := CommRingCat.of (IsLocalRing.ResidueField R), ι := ν }) ∧
        (∀ (i : I) (a : Fin d), ι.app i (s i a) = t a) ∧
        (∀ i : I, (ν.app i).hom.comp (q.app i).hom =
          (IsLocalRing.residue R).comp (ι.app i).hom.toRingHom) := by
  sorry

end RingTheory
