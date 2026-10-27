/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q113
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Sheaf.RingTheory.StrictHenselizationPresentationIn
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.RingTheory.StrictHenselizationTriplesPresentation
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import Sheaf.AlgebraicGeometry.StrictHenselizationDVR
import WeilConjectures.RingTheory.PointedEtaleSmallFiltered
import WeilConjectures.RingTheory.StrictHenselizationLocalMaximalIdeal
import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTraitStalk

/-!
# Approximation of strict-local generic points by etale trait neighbourhoods

Source: Stacks Project, Limits, Tag 01ZM, finite-coordinate specialization, and Algebra,
Tag 04GW, the defining pointed-etale colimit of a strict henselization
(blueprint: lem-sfb-strict-local-generic-point-etale-approximation).

The fraction-field maps in the conclusion are specified by their restrictions to the
rings. These restrictions determine them uniquely, so the displayed equality of points
is base change along the embedding induced by the local ring map.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory

namespace AlgebraicGeometry

/-- A point of a finite-type scheme over the fraction field of a DVR, valued in the
fraction field of its chosen strict henselization, descends to an etale local DVR
neighbourhood of finite presentation.

Source: Stacks Project, Tag 01ZM, affine finite-coordinate specialization, together with
Tag 04GW and the local-refinement argument below
(blueprint: lem-sfb-strict-local-generic-point-etale-approximation).

Proof:
1. First identify the two strict-henselization conventions. Apply
[lem-sc-strict-henselization-triples-presentation] to the given pointed-algebra colimit $D$. For
$Y=\operatorname{Spec}R$ and its closed point, [lem-weil-pbc-etale-local-ring-triples](3)
identifies this residue-triple diagram with the opposite of the affine pointed-neighbourhood
diagram. Thus $D$ is the scheme strict henselization at the corresponding geometric point,
compatibly with $R\to D$: both are colimits of that same diagram, so the mutually inverse
comparison maps are forced by their coprojections. The base stalk is $R$ by
[lem-weil-pbc-affine-open-stalk-localization](c), since every element outside the maximal ideal of
a local ring is already invertible. A DVR is Noetherian because each ideal has one generator.
Hence [lem-sc-strict-henselization-dvr] applies and shows that $D$ is a DVR and $R\to D$ is
injective and local. Choose a uniformizer $\pi$ of $R$; its image in $D$ is nonzero.

2. By the finite-type definition [def-weil-finite-type-morphism], choose from a finite affine
cover a chart $W=\operatorname{Spec}C\subset V$ containing the image of the unique point of
$\operatorname{Spec}F$, where $C$ is generated over $K$ by $c_1,\ldots,c_n$. The inverse image of
$W$ is the entire one-point scheme, so $v$ factors through $W$. Under the affine spectrum
correspondence [def-weil-affine-spectrum] it gives a $K$-algebra map $\varphi:C\to F$. Write
$\varphi(c_j)=a_j/b_j$ with $a_j,b_j\in D$ and $b_j\ne0$. This includes $n=0$.

3. Use a small representative category of pointed etale $R$-algebras: it is filtered by
[lem-sc-pointed-etale-small-filtered], and its colimit is $D$ by
[def-sc-ring-strict-henselization]. By [lem-pc-filtered-colimit-commrings-elementwise](1), each of
the finitely many $a_j,b_j$ has a representative at a stage. Repeated use of filteredness gives
one stage $(B,\chi)$ and elements $\alpha_j,\beta_j\in B$ whose images under the structural
coprojection $h:B\to D$ are $a_j,b_j$. If $n=0$, use nonemptiness to choose a stage. Compose $h$
with $D\to k_R^{\mathrm{sep}}$; this is $\chi$ by uniqueness of the colimit map. The map $D\to
k_R^{\mathrm{sep}}$ kills $\mathfrak m_RD=\mathfrak m_D$ by
[lem-sc-ring-strict-henselization-local-maximal-ideal], and its kernel is proper because $1$ maps
to $1$; its kernel is therefore exactly $\mathfrak m_D$. Consequently $\ker\chi=q=h^{-1}(\mathfrak
m_D)$. Thus $q$ lies over $\mathfrak m_R$, because the structural map of step 1 is local. In
particular $B$ is nonzero.

4. There are only two primes of $R$: $(0)$ and $\mathfrak m_R$. Indeed, $R$ is a local domain of
dimension one by [lem-sc-dvr-dimension-one], so any other prime would give the strict chain
$(0)\subsetneq p\subsetneq\mathfrak m_R$. For each of these two base primes $p$,
[lem-weil-pbc-etale-ring-base-change] makes $B\otimes_R\kappa(p)$ etale over the field
$\kappa(p)$. By [lem-weil-pbc-etale-algebra-over-field-product] this fibre is a finite product of
fields and therefore has finitely many primes. The fibre-ring description
[def-weil-pbc-localization-at-prime] and the localization spectrum correspondence
[lem-weil-pbc-localization-spectrum-embedding] identify its primes with the primes of $B$
contracting to $p$: first invert $R\setminus p$, then quotient by $p$; prime ideals of a quotient
are exactly preimages of primes containing the quotient ideal. Consequently $\operatorname{Spec}B$
is finite.

5. Set $A=B_q$. It is canonically the stalk of $\operatorname{Spec}B$ at $q$, with its actual map
from $R$, by [lem-weil-pbc-affine-open-stalk-localization](c). The point $q$ lies over the closed
point of $\operatorname{Spec}R$, so [lem-sbc-etale-trait-stalk] shows that $A$ is a domain DVR,
$R\to A$ is injective, and $\mathfrak m_A=\pi A$. Since $h(s)\notin\mathfrak m_D$ for every
$s\notin q$, the formula $h_q(b/s)=h(b)h(s)^{-1}$ defines a map $h_q:A\to D$ extending $h$. Its
inverse image of $\mathfrak m_D$ is $qA$, by the same formula. Hence $h_q$ is local and its
composite with $R\to A$ is the prescribed $R\to D$.

6. We now show that this particular prime localization is principal. For each of the finitely many
primes $P\subset B$ not contained in $q$, choose $s_P\in P\setminus q$ and put $f=\prod_Ps_P$
(empty product $1$). Then $f\notin q$. A prime containing no power of $f$ cannot be one of those
$P$, hence is contained in $q$. By [lem-weil-pbc-localization-spectrum-embedding], every prime of
$B_f$ is therefore contained in $qB_f$, and $qB_f$ itself is prime. Thus $B_f$ is local with
maximal ideal $qB_f$. Every $s\in B\setminus q$ has invertible image in $B_f$. The universal
properties now give inverse $B$-algebra maps $B_f\rightleftarrows B_q$: both composites fix every
fraction. We obtain $A=B_q\cong B_f$. This explicitly isolates the local neighbourhood; it does
not assume that an arbitrary prime localization of a finitely presented algebra is finitely
presented.

7. Apply [lem-weil-pbc-etale-algebra-finite-presentation-localization](2) to $R\to B$ and $f$. It
shows that $\operatorname{Spec}B_f\to\operatorname{Spec}R$ is etale, hence the identified morphism
$\operatorname{Spec}A\to\operatorname{Spec}R$ is etale. Part (1), applied to $R\to A$, also
supplies finite presentation. For completeness the scheme morphism is of finite presentation in
[def-weil-pbc-scheme-conventions]: etaleness supplies local finite presentation, and
$\operatorname{Spec}A$ has two points by [lem-sc-dvr-dimension-one]. The preimage of any affine
open is finite, hence quasi-compact. The diagonal also has this finite scheme as its domain, so
its affine-open preimages are finite and quasi-compact as well. Thus the morphism is quasi-compact
and quasi-separated.

8. The map $h_q:A\to D$ is injective. Its kernel is prime since $D$ is a domain. A local domain
DVR has just the primes $(0)$ and $\mathfrak m_A$, by the same dimension-one chain argument used
in step 4, using [lem-sc-dvr-dimension-one] for $A$. But $h_q(\pi)$ is the nonzero image of $\pi$
from step 1, whereas $\pi\in\mathfrak m_A$. Thus the kernel cannot be $\mathfrak m_A$ and must be
zero. This also proves that each $\beta_j$ has nonzero image in $A$, since its image $b_j$ in $D$
is nonzero.

9. As $A\hookrightarrow D$ is an injection of domains, $D$ is torsion free over $A$: if $0\ne a\in
A$ and $h_q(a)d=0$, the domain property of $D$ forces $d=0$. A DVR is a principal ideal domain
[def-sc-discrete-valuation-ring], so [lem-weil-pbc-pid-torsion-free-module-flat] makes $D$ flat
over $A$. The map is local between local rings by step 5. Therefore
[lem-pc-local-flat-faithful-flat-reflects-surjective] makes it faithfully flat.

10. Put $L=\operatorname{Frac}A$. The injections $R\hookrightarrow A$ and $A\hookrightarrow
D\hookrightarrow F$ extend uniquely to $K\hookrightarrow L\hookrightarrow F$ by
[lem-weil-pbc-fraction-field-lift], compatibly with the given map $K\to F$. In $L$ set
$x_j=\alpha_j/\beta_j$, using the images in $A$. Their images in $F$ are $\varphi(c_j)$. Let $I$
be the kernel of the surjection $K[T_1,\ldots,T_n]\to C$ defined by the chosen generators. For
every $P\in I$, the image of $P(x_1,\ldots,x_n)$ in $F$ is
$P(\varphi(c_1),\ldots,\varphi(c_n))=0$. Since $L\hookrightarrow F$ is injective,
$P(x_1,\ldots,x_n)=0$ in $L$. Thus evaluation factors through $C$ and defines a $K$-algebra map
$\varphi_A:C\to L$. By [def-weil-affine-spectrum] this gives $v_A:\operatorname{Spec}L\to W\subset
V$. After pullback to $F$, its coordinate map agrees with $\varphi$ on $K$ and all generators,
hence on $C$; therefore its pullback is exactly $v$. Together with steps 5, 7, 8 and 9, these are
all the required clauses.
-/
theorem strictLocalGenericPoint_etale_approximation
    (R D κsep K F : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field κsep] [Algebra (IsLocalRing.ResidueField R) κsep]
    [IsSepClosure (IsLocalRing.ResidueField R) κsep]
    [Algebra R κsep] [IsScalarTower R (IsLocalRing.ResidueField R) κsep]
    [CommRing D] [IsDomain D] [Algebra R D]
    (P : Algebra.StrictHenselizationPresentationIn.{u, u} R κsep D)
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field F] [Algebra D F] [IsFractionRing D F]
    [Algebra R F] [IsScalarTower R D F]
    [Algebra K F] [IsScalarTower R K F]
    (V : Scheme.{u}) (sV : V ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType sV] [QuasiCompact sV]
    (v : Spec (CommRingCat.of F) ⟶ V)
    (hv : v ≫ sV = Spec.map (CommRingCat.ofHom (algebraMap K F))) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
      (i : R →+* A) (j : A →+* D)
      (k : K →+* FractionRing A) (l : FractionRing A →+* F)
      (vA : Spec (CommRingCat.of (FractionRing A)) ⟶ V),
      j.comp i = algebraMap R D ∧
      Etale (Spec.map (CommRingCat.ofHom i)) ∧
      LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom i)) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom i)) ∧
      QuasiSeparated (Spec.map (CommRingCat.ofHom i)) ∧
      Function.Injective j ∧ IsLocalHom j ∧ j.FaithfullyFlat ∧
      k.comp (algebraMap R K) = (algebraMap A (FractionRing A)).comp i ∧
      l.comp (algebraMap A (FractionRing A)) = (algebraMap D F).comp j ∧
      vA ≫ sV = Spec.map (CommRingCat.ofHom k) ∧
      Spec.map (CommRingCat.ofHom l) ≫ vA = v :=
  sorry

end AlgebraicGeometry
