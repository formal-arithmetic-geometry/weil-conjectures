module

public import Sheaf.AlgebraicGeometry.StrictlySemistableCurve
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.KrullDimension

import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Flat
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Sheaf.AlgebraicGeometry.FiniteBirationalNormalIso
import Sheaf.RingTheory.QuasiFiniteAtPrimeZeroFibreDimension
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.RingTheory.QuasiFiniteAtPrime
import Sheaf.RingTheory.ValuationDomainFibreDimensions
import Sheaf.TraceFormula.ValuationHorizontalCurveModels
import Sheaf.TraceFormula.ValuationStrictSemistableCofinality
import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.EtaleAlgebraFilteredColimitDescent
import Sheaf.AlgebraicGeometry.BirationalRiemannZariskiNeighbourhoods
import Sheaf.FieldTheory.ValuedCurveEtaleParameter

/-! # Strictly semistable local uniformization along centred valuations

Source: Temkin, Stable Modification, Proposition 4.3.3, pp. 29--30
(blueprint: lem-trf-valuation-strict-semistable-local-uniformization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Strictly semistable local uniformization of a relative curve along all centred valuations.

Source: Temkin, Stable Modification, §1.2, §4.3 and Proposition 4.3.3, pp. 29--30
(blueprint: lem-trf-valuation-strict-semistable-local-uniformization).

Finite presentation includes quasi-compactness and quasi-separatedness. The shared
`IsStrictlySemistableCurve` predicate imposes the relative chart equations. Both projection
identities characterize the generic map induced by the specified `y i`.

Proof plan, retaining all twelve DAG steps and their dependencies:

1. Apply [lem-trf-valuation-horizontal-curve-models] with empty marking: $X$ is reduced with
finitely many components. Take a finite affine cover $U=\operatorname{Spec}A$ of $X$. By
[lem-weil-pbc-lfp-affine-opens-finite-presentation], each $A$ is finitely presented over $V$.
Each component is horizontal. Indeed $V$-flatness makes multiplication by every nonzero $v\in V$
injective on $A$. If $v$ lay in a minimal prime $\mathfrak p$, choose, for every other minimal
prime $\mathfrak q$, an element of $\mathfrak q\setminus\mathfrak p$ and multiply them. The
resulting $b\notin\mathfrak p$ satisfies $vb=0$, since $A$ is reduced, a contradiction. Thus the
function field $L$ of each component contains $K$ and is the function field of a smooth generic
curve. It has transcendence degree one by [lem-sc-closed-irreducible-dimension-trdeg]. There are
finitely many affine components to consider. A centred valuation whose closed centre is in $U$
factors through $U$: the inverse image of $U$ contains the closed point of the local spectrum
and therefore all its generalizations.

2. Fix one affine component with field $L$ and a centred valuation $W\subset L$. Put $R=W\cap
K$. This is a valuation overring of $V$, and $R=V_{\mathfrak p}$ for $\mathfrak p=V\cap\mathfrak
m_R$: every $s\in V\setminus\mathfrak p$ is invertible in $R$, while for $r\in R\setminus V$,
the element $r^{-1}\in V$ is invertible in $R$, so belongs to $V\setminus\mathfrak p$. In
particular $R$ has finite height. Localizing $\operatorname{Spec}W\to U$ by nonzero elements of
$V$ gives a centre on $U_\eta$. This localization is $KW$ as in
[lem-trf-valued-curve-etale-parameter]; inverting $V\setminus\{0\}$ or $R\setminus\{0\}$ gives
the same subring of $L$, since both yield all of $K$. The morphism lands in the component of the
smooth generic curve with field $L$. Apply that parameter theorem to obtain $t\in W$, $F=K(t)$
and $O=W\cap F$ such that $O\to W$ is etale and $L/F$ is finite. Thus $\operatorname{Spec}O$ has
its prescribed centre on $P=\operatorname{Spec}V[t]$.

3. Use [lem-trf-birational-riemann-zariski-neighbourhoods](iii) for $P$ and $O$: write
$O=\varinjlim A_j$, where $D_j=\operatorname{Spec}A_j$ is an affine neighbourhood of the centre
on an integral proper birational model $P_j\to P$, with $A_j\subset O\subset F$ and
$\operatorname{Frac}A_j=F$. The index category is small and filtered on rings, as required in
the subsequent descent statements. The morphism $P_j\to P$ is a reduced modification: a finite
set of algebra generators on affine charts gives a dense isomorphism open after clearing their
denominators in $F$. By [lem-trf-valuation-horizontal-curve-models], $P_j$ is a $T$-curve and
its generic fibre is $P_\eta$. Consequently $(D_j)_\eta$ is an open of the affine line, and
$A_j$ is finitely presented over $V$ by [lem-weil-pbc-lfp-affine-opens-finite-presentation].
Here $P$ itself is the affine-line strictly semistable model, with smooth generic fibre and
empty marking.

4. Since $O\to W$ is etale, [lem-weil-pbc-etale-algebra-filtered-colimit-descent] gives an etale
$A_j$-algebra $B_j$ and an identification $O\otimes_{A_j}B_j=W$. For each later index replace
$B_j$ by its base change; these remain etale by [lem-weil-pbc-etale-scheme-base-change] and
their filtered colimit is $W$. For every such index, $B_j\otimes_{A_j}F=W\otimes_OF=L$. To check
the last equality, the left localization is a domain algebraic over the field $F$, and every
nonzero algebraic element has its inverse in the same algebra by its minimal polynomial; its
fraction field is $L$. Moreover $B_j$ is $A_j$-flat by [lem-weil-pbc-etale-algebra-flat]. Tensor
the injection $A_j\hookrightarrow F$ with $B_j$ to see that $B_j\hookrightarrow L$. Thus $B_j$
is a domain. Its fraction field is exactly $L$, since its localization by the nonzero elements
of $A_j$ already equals $L$. This also verifies that no unwanted generic factor has been
introduced by descent.

5. The given centre determines a $V$-algebra map $A\to W$. Since $A$ is finitely presented over
$V$, apply [lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit] to $W=\varinjlim
B_j$. After increasing $j$ this map factors through $A\to B_j\to W$. Under the inclusions into
$L$ from Step 4 its generic map is the original component map $A\to L$. In particular the kernel
is precisely the prime defining that component of $U$.

6. Apply [lem-trf-valuation-strict-semistable-cofinality] to the modification $P_j\to P$. It
supplies an integral strictly semistable model $Z\to P$ dominating $P_j$, with the same generic
fibre. Integrality follows as well from the dense integral isomorphism open in a modification:
schematic density kills any sections vanishing there, so every nonempty affine chart embeds into
its function field. By [lem-trf-birational-riemann-zariski-neighbourhoods], $O$ has a unique
lift to $Z$. Choose an affine neighbourhood $E=\operatorname{Spec}C$ of its centre contained in
the inverse image of $D_j$. The whole morphism $\operatorname{Spec}O\to Z$ factors through $E$,
since its closed point does. We have $A_j\subset C\subset O$, $\operatorname{Frac}C=F$, and
$E_\eta$ is an open of the affine line. Also $C$ is finitely presented over $V$ by
[lem-weil-pbc-lfp-affine-opens-finite-presentation].

7. Set $B=B_j\otimes_{A_j}C$ and $Y=\operatorname{Spec}B$. The map $Y\to E$ is etale by
[lem-weil-pbc-etale-scheme-base-change]. The maps $B_j\to W$ and $C\to O\to W$ agree on $A_j$,
so give $B\to W$ and a factorization of the original centre through $Y$. Since $B$ is $C$-flat
by [lem-weil-pbc-etale-algebra-flat], tensoring $C\hookrightarrow F$ embeds $B$ into
$B\otimes_CF=L$. Hence $B$ is a domain with fraction field $L$. The ring $C$ is $V$-flat because
$E$ is an open of the $T$-curve $Z$, by [lem-weil-pbc-flat-morphism-affine-criterion]. Flatness
of $V\to B$ follows from [lem-weil-pbc-flat-ring-map-comp]. The etale map $C\to B$ is of finite
presentation by [lem-weil-pbc-lfp-affine-opens-finite-presentation], as is $V\to C$; their
composite is of finite presentation by
[lem-weil-pbc-finite-presentation-base-change-composition]. Thus $Y\to T$ is flat and finitely
presented, with a genuine valuation lift.

8. The integral finite-type $K$-scheme $Y_\eta$ has field $L$, so
[lem-sc-closed-irreducible-dimension-trdeg] gives $\dim Y_\eta=1$. For any prime $\mathfrak
p\subset V$, apply [lem-trf-valuation-domain-fibre-dimensions] to the finite-type domain
$B\otimes_VV_{\mathfrak p}$ over the valuation ring $V_{\mathfrak p}$. Its generic fibre is
$B\otimes_VK$ and has dimension one. Every nonempty fibre over $\mathfrak p$ is therefore
equidimensional of dimension one; the same holds at the generic point by the preceding dimension
computation. This proves the required pure relative dimension. Finally $Y_\eta\to E_\eta$ is
etale by [lem-weil-pbc-etale-scheme-base-change]; its source is smooth of relative dimension one
over $K$ by [lem-weil-pbc-etale-smooth-zero-dimensional-fibres] and
[lem-sbc-smooth-relative-dimension-permanence], since $E_\eta$ is an open of the smooth affine
line.

9. Restrict the strictly semistable charts of $Z$ to $E$. Compose these with $Y\to E$; the
composites are etale by [lem-weil-pbc-etale-composition-cancellation]. Thus $Y$ has exactly the
affine-line or $uv-a$ charts in the stated definition of strict semistability, so is strictly
semistable. The map $A\to B$ from Steps 5 and 7 defines an affine morphism $Y\to U$. It is of
finite type: a finite set of $V$-algebra generators of $B$ also generates it as an $A$-algebra.
Since $U$ is a quasi-compact open of the quasi-separated $X$, the composition $Y\to U\to X$ is
separated and of finite type. It identifies its function field with the chosen component field
$L$ and lifts $W$, as required for a birational quasi-modification.

10. For completeness verify the whole generic map is an open immersion. Its image is in the
component $H$ of $U_\eta$ with function field $L$; the components of a smooth curve are disjoint
and open, since their local rings are normal by [lem-sc-smooth-normal], hence domains, and there
are finitely many components. The morphism $Y_\eta\to H$ is affine, finite type and birational.
Both source and target are integral one-dimensional finite-type $K$-schemes. The generic fibre
is a single point. Over a closed point of $H$, a nonzero element of its prime ideal stays
nonzero in the domain of $Y_\eta$, so every prime in that fibre is nonzero and hence maximal.
The fibre has dimension zero. By [lem-weil-pbc-ring-quasifinite-zero-fibre-dimension] this is an
everywhere quasi-finite morphism. The affine target $H$ is qcqs, so [thm-pqf-zmt-factorization]
gives a quasi-compact open immersion $Y_\eta\hookrightarrow M$ with $M\to H$ finite.

11. Let $N$ be the scheme-theoretic image of $Y_\eta\hookrightarrow M$, using
[lem-weil-pbc-scheme-image-qc-kernel]. On an affine of $M$ meeting $Y_\eta$, its coordinate ring
modulo the kernel embeds into the function field $L$, so is a domain; these affine images have
the same generic point. Hence $N$ is integral, finite over $H$, and has function field $L$. Its
intersection with the open $Y_\eta$ is all of $Y_\eta$ with its original structure, because the
kernel ideal restricts to zero there. Thus $Y_\eta\to N$ is an open immersion. The target $H$ is
normal by [lem-sc-smooth-normal]. Apply [lem-trf-finite-birational-normal-iso] to $N\to H$: it
is an isomorphism. Therefore $Y_\eta\to H\hookrightarrow X_\eta$ is an open immersion, proving
the additional generic clause rather than merely birationality.

12. For each affine component $U_\alpha=\operatorname{Spec}(A/\mathfrak p_\alpha)$, Steps 2--11
construct a suitable $Y\to U_\alpha$ around each of its centred valuations. The factorization
through $U_\alpha$ is scheme-theoretic: $A\to B\hookrightarrow L$ has kernel $\mathfrak
p_\alpha$. Apply [lem-trf-birational-riemann-zariski-neighbourhoods](ii): the valuations which
lift to this $Y$ form an open subspace of $\operatorname{Val}_L(U_\alpha)$. These opens cover
that space by construction, and clause (i) makes it quasi-compact. Choose finitely many such $Y$
for each affine component, and take their union as a finite list over the finite affine cover of
$X$. Every centred valuation factors through an affine containing its closed centre and through
its component, so lifts to one entry of the list. Each entry is integral, strictly semistable,
and has the generic-open property from Step 11. If $X$ is empty, the empty list works. This
proves all clauses without changing $T$ or its fraction field.
-/
theorem valuation_strict_semistable_local_uniformization
    {V K : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] [IsSepClosed K]
    (hchain : ∀ p q : PrimeSpectrum V, p ≤ q ∨ q ≤ p)
    (hfinite : Finite (PrimeSpectrum V))
    (X : Scheme.{u}) (c : X ⟶ Spec (CommRingCat.of V))
    [Flat c] [LocallyOfFinitePresentation c] [QuasiCompact c] [QuasiSeparated c]
    (hcurve : ∀ s : Spec (CommRingCat.of V),
      ∀ Z ∈ irreducibleComponents (c.fiber s),
        topologicalKrullDim Z = (1 : WithBot ℕ∞))
    [Smooth
      (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap V K))))] :
    ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (y : ∀ i, Y i ⟶ X),
      (∀ i, IsIntegral (Y i)) ∧
      (∀ i, IsStrictlySemistableCurve (y i ≫ c)) ∧
      (∀ i, IsSeparated (y i) ∧ LocallyOfFiniteType (y i) ∧ QuasiCompact (y i)) ∧
      (∀ i, ∃ C : Set X, ∃ ξ : X,
        C ∈ irreducibleComponents (X : Type u) ∧
        IsGenericPoint ξ C ∧
        (∀ z : Y i, (y i).base z ∈ C) ∧
        ∃ ηᵢ : Y i, IsGenericPoint ηᵢ (Set.univ : Set (Y i)) ∧
          (y i).base ηᵢ = ξ ∧
          Function.Bijective ((y i).residueFieldMap ηᵢ).hom) ∧
      (∀ i, ∃ j : pullback (y i ≫ c)
          (Spec.map (CommRingCat.ofHom (algebraMap V K))) ⟶
          pullback c (Spec.map (CommRingCat.ofHom (algebraMap V K))),
        j ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap V K))) =
            pullback.fst (y i ≫ c) (Spec.map (CommRingCat.ofHom (algebraMap V K))) ≫ y i ∧
        j ≫ pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap V K))) =
            pullback.snd (y i ≫ c) (Spec.map (CommRingCat.ofHom (algebraMap V K))) ∧
        IsOpenImmersion j) ∧
      (∀ (C : Set X) (hC : C ∈ irreducibleComponents (X : Type u))
        (ξ : X) (hξ : IsGenericPoint ξ C)
        (W : ValuationSubring (X.residueField ξ))
        (z : Spec (CommRingCat.of W) ⟶ X),
        z.base (⊥ : PrimeSpectrum W) = ξ →
        ∃ i : Fin n, ∃ l : Spec (CommRingCat.of W) ⟶ Y i,
          l ≫ y i = z) := by
  sorry

end AlgebraicGeometry
