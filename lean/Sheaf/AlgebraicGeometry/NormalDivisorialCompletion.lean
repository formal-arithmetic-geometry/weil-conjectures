module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Connected.Basic
public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Sheaf.TraceFormula.SmoothGeometricallyNormal
import Sheaf.AlgebraicGeometry.NormalTopologicallyNoetherianComponents
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Defs
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Blowup.AdmissibleBlowup
import Sheaf.AlgebraicGeometry.NagataBoundaryDivisorCartier
import Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry
import WeilConjectures.Blowup.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Sheaf.AlgebraicGeometry.ReducedNormalization
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.RingTheory.DimensionAtPointLocalRingTrdeg
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Height

/-! # Normal proper completion with divisorial boundary

Source: Milne, Algebraic Groups (2017), Proposition 8.25, printed p.154, referring to
Milne (2013), Proposition 4.1, first paragraph of the proof, and Aside 5.4
(blueprint: lem-sfb-normal-divisorial-completion).

The boundary is the actual reduced closed subscheme defined by the vanishing ideal of
its closed support. The positive natural number `d` records the finite Krull dimension;
thus the natural subtraction `d - 1` is the ordinary dimension minus one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth connected nonproper separated finite-type scheme over an algebraically closed
field is integral and admits a normal integral proper completion with nonempty divisorial
boundary.
Source: Milne, Algebraic Groups (2017), Proposition 8.25, printed p.154, referring to
Milne (2013), Proposition 4.1, first paragraph of the proof, and Aside 5.4
(blueprint: lem-sfb-normal-divisorial-completion).

Proof (the reviewed DAG proof, step by step):
1. For every finite-type $k$-scheme $Z$ used below, choose a finite affine cover
$\operatorname{Spec}A_i$ with $A_i$ finitely generated over $k$ [def-weil-finite-type-morphism].
By [lem-wf-affine-noetherian-components], each $A_i$ is Noetherian and each affine space is
topologically Noetherian. A descending chain of closed subsets of $Z$ stabilizes on each member of
this finite cover, hence stabilizes on $Z$. Thus $Z$ is locally Noetherian and its topology is
Noetherian. In particular every open in $Z$ is quasi-compact: otherwise finite unions of members
of an open cover would have no maximal member, contradicting stabilization of ascending chains of
opens.

2. Apply [lem-trf-smooth-geometrically-normal] to the smooth structure morphism of $Y$, using the
trivial field extension: $Y$ is normal and reduced. By
[lem-trf-normal-topologically-noetherian-components] and step 1, its irreducible components are a
finite disjoint union of open and closed integral schemes. Since $Y$ is connected and nonempty,
exactly one component occurs. Hence $Y$ is integral.

3. Apply [thm-nagata-compactification] to $Y\to\operatorname{Spec}k$. Its separatedness and finite
type are hypotheses, and $\operatorname{Spec}k$ is affine, hence quasi-compact and
quasi-separated. By [def-nagata-compactifiable] and [def-nagata-compactification], obtain an open
immersion $Y\hookrightarrow P$ with $P$ proper over $k$. No quasi-projectivity of $Y$ is required.

4. Let $T$ be the reduced induced closed subscheme on $\overline{|Y|}\subseteq P$, supplied by
[lem-weil-pbc-reduced-induced-closed-subscheme]. Its topology is irreducible, being the closure of
the irreducible set $|Y|$, and it is reduced, so $T$ is integral. Over the open subscheme $Y$ its
defining ideal is zero: the affine description in that node gives the nilradical on every affine
open of $Y$, which is zero by step 2. Therefore $Y\hookrightarrow P$ factors as a dense open
immersion into $T$, with its original scheme structure. By [lem-weil-pbc-closed-immersion-proper],
$T$ is proper over $k$, hence finite type. Step 1 applies to $T$.

5. Use [lemma-nagata-qc-open-complement-ideal-exists] on the qcqs scheme $T$ and its quasi-compact
open $Y$, obtaining a finite-type quasi-coherent ideal $\mathcal I$ with $V(\mathcal I)=T\setminus
Y$. Apply [det-nagata-boundary-divisor-cartier]: the blowup $b:B=\operatorname{Bl}_{\mathcal
I}T\to T$ is a $Y$-admissible blow-up [def-nagata-admissible-blowup], so by
[lemma-nagata-admissible-blowup-over-open] the induced morphism $b^{-1}(Y)=B\times_TY\to Y$ is an
isomorphism and $Y$ is identified with the open $b^{-1}(Y)\subseteq B$; moreover $\mathcal
I\mathcal O_B$ defines an effective Cartier divisor $D$ with support $B\setminus Y$. The ideal is
nonzero since it is the unit ideal over nonempty $Y$. Thus
[lem-sfb-integral-blowup-projective-geometry] gives integrality of $B$. By
[lemma-nagata-blowup-proper] and [lem-weil-pbc-proper-composition], $B$ is proper over $k$. In
particular $B$ is finite type, so step 1 applies.

6. Let $\nu:X_0=B^\nu\to B$ be the function-field normalization [def-sc-normalization]. Since $B$
is integral, this is also its componentwise normalization [def-weil-pbc-reduced-normalization]. By
[lem-sfb-componentwise-normalization-generic-properties], $X_0$ is normal and has exactly one
irreducible-component generic point. By [lem-sc-normalization-exists], $\nu$ is finite and
birational, and $X_0$ is proper over $k$, hence finite type. Step 1 and
[lem-trf-normal-topologically-noetherian-components] then make $X_0$ a finite disjoint union of
integral components; exactly one occurs, so it is integral. Since the open $Y\subseteq B$ is
normal, [lem-sc-normalization-over-normal-locus] identifies $\nu^{-1}Y$ with $Y$. This gives an
open immersion $j_0:Y\hookrightarrow X_0$, dense because a nonempty open subset of an irreducible
space is dense.

7. The extended ideal $\mathcal I\mathcal O_{X_0}$ is effective Cartier. Indeed, on an affine open
of $B$ where $D$ has equation $t$, the element $t$ is nonzero in the common function field. The
normalization [def-sc-normalization] is built from subrings of that field, so the image of $t$
remains nonzero. Since $X_0$ is integral, multiplication by this image is injective on each local
ring; this is precisely [def-nagata-effective-cartier-ideal]. These local equations generate the
extended ideal and have vanishing set $\nu^{-1}|D|$: a local ring homomorphism sends a local
equation into the target maximal ideal exactly when it belongs to the source maximal ideal. Hence
the resulting divisor $D_0$ has support $X_0\setminus j_0(Y)$.

8. Give $E_0=X_0\setminus j_0(Y)$ its reduced induced closed structure using
[lem-weil-pbc-reduced-induced-closed-subscheme]. Its support equals $|D_0|$ by step 7. It is
nonempty: otherwise the open immersion $j_0$ would be surjective and therefore an isomorphism
[def-weil-open-immersion], making $Y$ proper, contrary to hypothesis. By
[lem-sc-dimension-locally-algebraic], $\dim X_0=\dim Y=:d$, and every nonempty affine open of
$X_0$ has dimension $d$ and dimension $d$ at each of its points. By
[lem-kun-dimension-finite-type], $d$ is finite; it is nonnegative since $Y$ is nonempty.

9. Let $C$ be any irreducible component of $E_0$ and $\xi$ its generic point. Choose an affine
neighbourhood $\operatorname{Spec}A\subseteq X_0$ of $\xi$ on which $D_0$ has a single equation
$t$. It can be chosen as a principal refinement of a finite-type affine chart, so $A$ is a
finitely generated $k$-algebra and is Noetherian by step 1. It is a domain since $X_0$ is
integral, and $t\ne0$ by step 7. The prime $\mathfrak p$ of $\xi$ is minimal over $(t)$: otherwise
a smaller prime containing $t$ would give a proper irreducible closed subset inclusion
$C\subsetneq C'\subseteq |D_0|$ after taking closure, contradicting maximality of $C$. By
[lem-sfb-krull-principal-ideal-height-bound], $\operatorname{ht}\mathfrak p\le1$. Since
$t\in\mathfrak p$ is nonzero, the strict chain $(0)\subsetneq\mathfrak p$ gives the opposite
bound. By [lem-weil-pbc-localization-dimension-chains-below-prime], $\dim A_{\mathfrak p}=1$.

10. Apply [lem-weil-pbc-dimension-at-point-local-ring-trdeg] to the finite-type algebra $A$ and
prime $\mathfrak p$ of step 9. Step 8 gives $\dim_{\mathfrak p}(\operatorname{Spec}A)=d$, and step
9 gives $\dim A_{\mathfrak p}=1$, so $d=1+\operatorname{trdeg}_k\kappa(\mathfrak p)$. The residue
field is the residue field of $X_0$ at $\xi$, since open restriction preserves the local ring. By
[lem-sc-closed-irreducible-dimension-trdeg] applied to the nonempty irreducible closed subset
$C\subseteq X_0$, its dimension is that same transcendence degree. Thus $\dim C=d-1$. This holds
for every component. Since $E_0$ is nonempty it has such a component, whose dimension is
nonnegative. Therefore $d\ge1$, proving the positive-dimension assertion as well.
-/
theorem exists_normal_proper_completion_divisorial_boundary
    {k : Type u} [Field k] [IsAlgClosed k] (Y : Scheme.{u})
    (f : Y ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [Smooth f] [ConnectedSpace Y] (hnotproper : ¬ IsProper f) :
    IsIntegral Y ∧
      ∃ (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) (j : Y ⟶ X) (_ : IsOpenImmersion j),
        IsNormalScheme X ∧ IsProper p ∧ j ≫ p = f ∧ DenseRange j.base ∧
          Nonempty (Scheme.IdealSheafData.vanishingIdeal
            ⟨(j.opensRange : Set X)ᶜ, j.opensRange.isOpen.isClosed_compl⟩).subscheme ∧
          ∃ d : ℕ, 0 < d ∧ topologicalKrullDim Y = (d : WithBot ℕ∞) ∧
            topologicalKrullDim X = (d : WithBot ℕ∞) ∧
            ∀ C ∈ irreducibleComponents
              (Scheme.IdealSheafData.vanishingIdeal
                ⟨(j.opensRange : Set X)ᶜ, j.opensRange.isOpen.isClosed_compl⟩).subscheme,
              topologicalKrullDim C = ((d - 1 : ℕ) : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
