module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.TraceFormula.Modification
import Sheaf.AlgebraicGeometry.ClosedDominantDimension
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.AlgebraicGeometry.ConnectedPointGeometricallyConnected
import Sheaf.AlgebraicGeometry.FiniteDominantFibrePurity
import Sheaf.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree
import Sheaf.AlgebraicGeometry.GeometricReducedFiniteTypePerfectField
import Sheaf.AlgebraicGeometry.LocallyNoetherianComponentsLocallyFinite
import Sheaf.AlgebraicGeometry.ProperFiniteFibreFiniteNeighbourhood
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.SteinFactorizationAffine
import WeilConjectures.FieldTheory.CommonExtensionFields
import Sheaf.TraceFormula.FlatFibreComponentClosureDimension
import Sheaf.TraceFormula.RelativeDimensionBaseChange
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Rigidity
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Finite image of a projection fibre under a proper comparison after modifying the base

Source: Temkin, *Stable modification of relative curves*, Proposition 5.2,
printed p. 35, fibre-image subclaim (blueprint: lem-trf-base-modification-comparison-fibre-image).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Canonical map from a base-modification fibre to the corresponding target fibre: for
`hy : Y` with image `s` in `S`, the composite `F = Y' ×_Y Spec κ(y) ⟶ Y' ⟶ X' ⟶ X`
through `g`, lifted to the fibre `X_s = X ×_S Spec κ(s)` by the canonical map
`Spec κ(y) ⟶ Spec κ(s)`.

Source: Temkin, *Stable modification of relative curves*, Proposition 5.2, printed p. 35,
fibre-image subclaim: the map `F → Y' → X' → X` whose image is asserted finite
(blueprint: lem-trf-base-modification-comparison-fibre-image). -/
noncomputable def baseModificationFibreMap
    {S C X Y S' : Scheme.{u}}
    (c : C ⟶ S) (x : X ⟶ S) (y : Y ⟶ S) (a : X ⟶ C) (b : Y ⟶ C)
    (hac : a ≫ c = x) (hbc : b ≫ c = y)
    (q : S' ⟶ S) (g : pullback y q ⟶ pullback x q)
    (hgc : g ≫ pullback.fst x q ≫ a = pullback.fst y q ≫ b)
    (hy : Y) : (pullback.fst y q).fiber hy ⟶ x.fiber (y hy) := by
  have hgs : (g ≫ pullback.fst x q) ≫ x = pullback.fst y q ≫ y := by
    calc
      (g ≫ pullback.fst x q) ≫ x =
          (g ≫ pullback.fst x q) ≫ (a ≫ c) :=
        congrArg (fun k : X ⟶ S => (g ≫ pullback.fst x q) ≫ k) hac.symm
      _ = (pullback.fst y q ≫ b) ≫ c := by
        simpa only [Category.assoc] using congrArg (fun k : pullback y q ⟶ C => k ≫ c) hgc
      _ = pullback.fst y q ≫ y := by
        simpa only [Category.assoc] using congrArg (fun k : Y ⟶ S => (pullback.fst y q) ≫ k) hbc
  let p : (pullback.fst y q).fiber hy ⟶ Spec (S.residueField (y hy)) :=
    (pullback.fst y q).fiberToSpecResidueField hy ≫
      Spec.map (y.residueFieldMap hy)
  change (pullback.fst y q).fiber hy ⟶ pullback x (S.fromSpecResidueField (y hy))
  exact pullback.lift ((pullback.fst y q).fiberι hy ≫ g ≫ pullback.fst x q) p (by
    simp only [Category.assoc]
    rw [← Category.assoc g (pullback.fst x q) x]
    rw [hgs]
    simpa only [p, Category.assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] using
      congrArg (fun k : (pullback.fst y q).fiber hy ⟶ Y => k ≫ y)
        (Scheme.Hom.fiber_fac (pullback.fst y q) hy))

/-- Finite image of a projection fibre after a proper birational base modification.

Source: Temkin, *Stable modification of relative curves*, Proposition 5.2, printed p. 35,
fibre-image subclaim before the connectedness argument
(blueprint: lem-trf-base-modification-comparison-fibre-image).

The hypotheses encode the source's reduced flat finite-type families, proper comparisons
that are isomorphisms on the generic fibre and on schematically dense opens, eta-normality
of `Y`, and the proper birational base modification.  For a closed point `y`, the
canonical fibre product `F = Y' ×_Y Spec κ(y)` has finite image in the fibre `X_s`.
The dense-open isomorphism canonically identifies the two function fields; no equality
of their underlying Lean types is imposed. The equations `hgq` and `hgc` together mean
that `g` is a morphism over `C'`.
Proof (the componentwise repair of Temkin's fibre-image argument):

1. Fix the given closed point $y$ and its image $s$. Choose an affine neighbourhood of $s$ in $S$,
   then an affine neighbourhood $C_0$ of $b(y)$ inside its inverse image. Replace $C,X,Y$ by
   $C_0,a^{-1}(C_0),b^{-1}(C_0)$ and restrict $g$ accordingly. The entire fibre $F$ is retained,
   since its composite to $C$ is constantly $b(y)$. These restrictions remain reduced, flat and
   finite type; all opens involved are quasi-compact because finite-type schemes over the
   Noetherian base are Noetherian. Properness of $a,b$ survives the open base change. We may
   therefore assume $S=\operatorname{Spec}R$ and $C=\operatorname{Spec}A$ affine. In particular
   $X_s,Y_s$ are separated finite-type schemes over $\kappa(s)$, since they are proper over the
   affine scheme $C_s$.
   Uses: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-proper-fp-permanence, def-weil-
   flat-morphism, def-weil-proper-morphism.

2. We will use schematic generic density explicitly. For a flat scheme over an integral base, on
   an affine chart over a domain every nonzero base element acts injectively on sections: apply
   the torsion-free sections lemma with the invertible module $\mathcal O$. Localization in these
   elements is therefore injective. This proves schematic density of the generic fibre. The same
   assertion holds after base change to $S'$: on affine charts, $(B\otimes_R
   R')\otimes_{R'}M=B\otimes_R M$ proves that base change preserves flatness, by applying the
   definition to injections of $R'$-modules. The affine criterion translates this back to schemes.
   We may also restrict to any open of the source. Consequently an ideal pulled back to one of
   these flat schemes is zero if its restriction to the generic fibre is zero.
   Uses: lem-sc-flat-invertible-sections-torsion-free, lem-weil-pbc-flat-morphism-affine-
   criterion, def-weil-pbc-flat-ring-map.

3. Index the irreducible components of $C_\eta$ by $i$, and put $n_i=\dim C_{i,\eta}$. The generic
   isomorphisms give corresponding components of $X_\eta$ and $Y_\eta$. Let $C_i,X_i,Y_i$ denote
   their reduced closures in the respective total spaces. Generic density from Step 2 and
   finiteness of the total component sets show that these are all total-space components: a
   component disjoint from the generic fibre would have a nonempty open away from the other
   finitely many components, contradicting density. Properness and the generic identifications
   give surjections $X_i\to C_i$ and $Y_i\to C_i$, since their closed images contain the generic
   point of $C_i$. The flat fibre-component-closure dimension theorem gives pure dimension $n_i$
   for every nonempty fibre of each of $C_i,X_i,Y_i$. Its hypothesis concerns the ambient flat
   scheme, so no flatness of these reduced closures is asserted. Relative-dimension base change
   gives the same purity after every residue-field extension.
   Uses: lem-trf-flat-fibre-component-closure-dimension, lem-trf-relative-dimension-base-change,
   lem-sc-locnoeth-components-locally-finite, lem-sc-scheme-sober, def-weil-proper-morphism, lem-
   weil-pbc-reduced-induced-closed-subscheme.

4. Take the affine Stein factorization $Y\xrightarrow{p}D=\operatorname{Spec}B\xrightarrow{r}C$,
   where $B=\Gamma(Y,\mathcal O_Y)$. The affine Stein theorem makes $p$ proper, surjective, with
   geometrically connected fibres. Since $Y$ is locally Noetherian, $\mathcal O_Y$ is coherent;
   proper coherent cohomology over the Noetherian affine $C$ makes $B$ finite over $A$. Thus $r$
   is finite. The ring $B$ is reduced, since sections on a reduced scheme have no nonzero
   nilpotents. Flat base change of global sections along
   $\operatorname{Spec}K\to\operatorname{Spec}R$ and $Y_\eta\simeq C_\eta$ give $B\otimes_RK\simeq
   A\otimes_RK$, with its canonical algebra map. Also $B\hookrightarrow B\otimes_RK$ by Step 2.
   Hence $D_\eta$ is dense in $D$: if $D(b)$ misses it, some power of $b$ is killed by a nonzero
   element of $R$, so $b$ is nilpotent and $D(b)$ is empty. Therefore the integral components
   $D_i$ of $D$ correspond to the same generic components, $D_i\to C_i$ is finite surjective, and
   $p(Y_i)=D_i$.
   Uses: lem-weil-pbc-stein-factorization-affine, pqf-lem-coherent-ft-locnoeth, lem-pc-coherent-
   hi, def-weil-finite-integral-morphism, lem-weil-pbc-flat-base-change-global-sections-qcqs.

5. The finite-dominant fibre-purity lemma applies to the finite dominant map r:D_i\to C_i. Since
   every nonempty fibre of C_i is pure of dimension n_i by Step 3, it gives that every nonempty
   fibre of D_i is pure of dimension n_i. Its proof uses the going-up description of components
   under an integral extension and the finite-surjective dimension theorem, so it does not infer a
   lower bound from openness of the bounded-dimension locus. The relative-dimension base-change
   theorem then gives the same purity after every field extension \Omega/\kappa(s).
   Uses: lem-trf-finite-dominant-fibre-purity, lem-trf-relative-dimension-base-change.

6. Choose an algebraic closure $\Omega$ of $\kappa(s)$ and write
   $T=S'\times_S\operatorname{Spec}\Omega$. It is proper and finite type over $\Omega$. The fibre
   of $g$ gives $H:T\times_\Omega Y_\Omega\to X_\Omega$, over $C_\Omega$, by forgetting its $T$
   coordinate. Here the subscript $\Omega$ means base change from $S$ through $s$. All these
   schemes are Noetherian. If $T$ is empty the required image is empty. Otherwise let $W$ be any
   connected component of $Y_\Omega$; it is open and closed, since a Noetherian scheme has
   finitely many irreducible components and its connected components are their disjoint maximal
   connected unions. We will prove finiteness of the image of $T\times\{z\}$ for every
   $\Omega$-rational point $z\in W$.
   Uses: lem-pc-algebraic-closure-exists-unique, lem-weil-pbc-proper-fp-permanence, lem-weil-pbc-
   finite-type-over-noetherian, lem-sc-locnoeth-components-locally-finite, def-pc-fibre-product.

7. Under $p_\Omega$, the component $W$ is exactly the inverse image of a connected component $V$
   of $D_\Omega$. Indeed $p_\Omega$ is a closed surjection with connected nonempty fibres. It is a
   quotient map, and the connected-preimage theorem makes the inverse image of each closed
   connected component of $D_\Omega$ connected; maximality of connected components gives the
   assertion. Since $p:Y_i\to D_i$ is proper surjective, so is its base change to $\Omega$. Thus
   $W$ meets $(Y_i)_\Omega$ exactly when $V$ meets $(D_i)_\Omega$. Choose $n$ maximal among the
   $n_i$ with this property, and choose one such $i$. A component $E$ of $(D_i)_\Omega$ meeting
   $V$ lies entirely in $V$, since $V$ is open and closed. It has dimension $n$ by Step 5. Its
   finite image $B_0\subseteq (C_i)_\Omega$, with reduced structure, is integral and has dimension
   $n$.
   Uses: lem-weil-pbc-stein-factorization-affine, lem-weil-pbc-connected-fibres-quotient-preimage-
   connected, lem-weil-pbc-proper-fp-permanence, lem-sc-finite-surjective-dimension, lem-weil-pbc-
   reduced-induced-closed-subscheme.

8. Let $X_{\leq n}\subseteq X$ be the reduced union of the $X_j$ with $n_j\leq n$, and let
   $Y^0=Y\setminus\bigcup_{n_j>n}Y_j$. By the maximality defining $n$, $W\subseteq Y^0_\Omega$. On
   the generic fibre the comparison $g$ is forced to equal $a_\eta^{-1}b_\eta$, so its restriction
   to $(Y^0)'$ lands in $(X_{\leq n})'$. This holds scheme-theoretically on the entire $(Y^0)'$:
   pull back the ideal of $(X_{\leq n})'$; it is zero generically, and Step 2 makes it zero
   everywhere because $(Y^0)'$ is flat over the integral $S'$. Hence $H|_{T\times W}$ lands in
   $(X_{\leq n})_\Omega$. This step only uses the displayed ideal argument; it does not infer
   factorization through a closed subscheme from pointwise containment.
   Uses: lem-sc-flat-invertible-sections-torsion-free, lem-weil-pbc-flat-morphism-affine-
   criterion, def-weil-pbc-flat-ring-map, lem-weil-pbc-reduced-induced-closed-subscheme.

9. Put $P=(X_{\leq n})_\Omega\times_{C_\Omega}B_0$. It is proper over the integral $B_0$ and has
   dimension at most $n$: it is closed in $(X_{\leq n})_\Omega$, because $B_0$ is closed in
   $C_\Omega$, and Step 3 bounds every component of the latter scheme by $n$. If an integral
   component $L$ of $P$ dominates $B_0$, the closed-dominant dimension formula gives $\dim L=\dim
   B_0+\operatorname{trdeg}_{\kappa(B_0)}\kappa(L)$. Thus $\dim L=n$ and this transcendence degree
   is zero. The generic fibre of $L\to B_0$ is integral, proper and finite type over
   $\kappa(B_0)$, and applying that same dimension formula over this field makes it zero-
   dimensional. It is a finite set by the zero-dimensional closed-subset lemma. A nondominating
   component of $P$ has closed image missing the generic point of $B_0$. There are finitely many
   components, so the whole generic fibre of $P\to B_0$ is finite.
   Uses: lem-weil-pbc-proper-fp-permanence, lem-trf-closed-dominant-dimension, lem-sc-dim0-finite.

10. The proper finite-fibre neighbourhood theorem, applied to $P\to B_0$ at the generic point of
   the Noetherian $B_0$, supplies a nonempty open $U\subseteq B_0$ over which $P$ is finite.
   Choose a closed point $e$ of the nonempty open $E\times_{B_0}U$ and then a closed point $z_0$
   of its nonempty inverse image in $(Y_i)_\Omega$. Such points exist by choosing a maximal ideal
   on a nonempty affine chart; their residue fields are $\Omega$ by the closed-point field
   theorem, and the same theorem makes them closed in the ambient finite-type schemes. They lie in
   $V$ and $W$ respectively. Put $c_0=b(z_0)\in U$. Finite morphisms have finite fibres by the
   finite-closed-map theorem. Step 8 implies that $H(T\times\{z_0\})$ is contained in the finite
   fibre $P_{c_0}$, viewed in $X_\Omega$. We have therefore found an actual rational seed point of
   $W$ with finite image.
   Uses: thm-sc-proper-finite-fibre-finite-neighbourhood, lem-kun-closed-point-field, def-weil-
   finite-integral-morphism, lem-weil-pbc-finite-closed-map-finite-fibres.

11. Cover $T$ by the reduced closed subschemes $T_1,\ldots,T_m$ underlying its irreducible
   components. Each is integral, nonempty, proper and finite type over $\Omega$. It has a rational
   closed point by the closed-point field theorem, so the connected-point geometric-connectedness
   criterion makes it geometrically connected. It is geometrically reduced by the perfect-field
   reducedness theorem: an algebraically closed field is perfect, since in positive characteristic
   every $a$ has a root of $t^p-a$. The finite image of $T_r\times\{z_0\}$ in Step 10 is
   connected. Its points are closed: each has residue field algebraic over $\Omega$, because the
   image lies in the finite fibre over the rational $c_0$. The closed-point field theorem
   therefore makes that image a finite discrete set. A nonempty connected finite discrete set is a
   singleton.
   Uses: lem-kun-closed-point-field, lem-trf-connected-point-geometrically-connected, lem-kun-
   geometric-reduced-perfect, lem-weil-pbc-reduced-induced-closed-subscheme.

12. Apply the rigidity lemma to the proper geometrically connected geometrically reduced
   $\Omega$-scheme $T_r$, the connected $\Omega$-scheme $W$, and the separated finite-type target
   $X_\Omega$, using the morphism $H|_{T_r\times W}$ and the rational point $z_0\in W$. Step 11
   supplies its singleton-image hypothesis. It follows that $H|_{T_r\times W}$ factors through
   $W$. Consequently for every rational $z\in W$, the image of $T_r\times\{z\}$ is a single
   rational point of $X_\Omega$; rationality follows by evaluating at a rational point of $T_r$.
   The finite component cover remains surjective after product with $W$, so $H(T\times\{z\})$ is
   the union of at most $m$ such points. This proves the assertion for every rational point on
   every connected component of $Y_\Omega$. Nilpotents in $T$ do not affect the argument: the
   component cover by the reductions is universally surjective and covers all points of this
   product.
   Uses: lem-sc-rigidity, lem-kun-closed-point-field, def-pc-fibre-product.

13. Since $y$ is closed in the finite-type $\kappa(s)$-scheme $Y_s$, the field $\kappa(y)$ is
   finite over $\kappa(s)$. Thus $\operatorname{Spec}(\kappa(y)\otimes_{\kappa(s)}\Omega)$ has
   finitely many points, all with residue field $\Omega$: indeed for any prime its quotient is a
   finite-dimensional domain, hence a field (multiplication by a nonzero element is injective and
   therefore surjective); so the spectrum is zero-dimensional and the zero-dimensional closed-
   subset lemma makes it finite. Its residue fields are finite over the algebraically closed
   $\Omega$. The corresponding rational points of $Y_\Omega$ lie on finitely many components $W$.
   The geometric base change of $F$ is
   $T\times_\Omega\operatorname{Spec}(\kappa(y)\otimes_{\kappa(s)}\Omega)$. Its underlying space
   is covered by the finitely many products $T\times\{z\}$ above those rational points. Step 12
   therefore gives a finite set of rational points as its image in $X_\Omega$. Surjectivity of
   field extension (on a fibre-product point choose a prime in the nonzero tensor product of the
   two residue fields) implies that this image projects onto the original image in $X_s$. Each
   projected point has residue field algebraic over $\kappa(s)$, since it embeds into its rational
   lifting's field $\Omega$. The closed-point field theorem makes every such point closed in
   $X_s$. This proves exactly the required finite set of closed points.
   Uses: lem-kun-closed-point-field, lem-weil-common-extension-fields, def-pc-fibre-product, lem-
   sc-dim0-finite.
-/
theorem base_modification_comparison_fibre_image
    {S : Scheme.{u}} [IsIntegral S] [IsNoetherian S]
    (η : S) (hη : IsGenericPoint η Set.univ)
    {C X Y : Scheme.{u}}
    (c : C ⟶ S) (x : X ⟶ S) (y : Y ⟶ S)
    [Flat c] [Flat x] [Flat y]
    [LocallyOfFiniteType c] [QuasiCompact c]
    [LocallyOfFiniteType x] [QuasiCompact x]
    [LocallyOfFiniteType y] [QuasiCompact y]
    [IsReduced C] [IsReduced X] [IsReduced Y]
    (a : X ⟶ C) (b : Y ⟶ C)
    (hac : a ≫ c = x) (hbc : b ≫ c = y)
    (ha : EtaModification (S.fromSpecStalk η) a c)
    (hb : EtaModification (S.fromSpecStalk η) b c)
    (hnormal : ∀ {Z : Scheme.{u}} (f : Z ⟶ Y),
      IsFinite f → EtaModification (S.fromSpecStalk η) f (b ≫ c) → IsIso f)
    {S' : Scheme.{u}} (q : S' ⟶ S) [IsIntegral S']
    (hq : IsProper q)
    (hbirational : ∃ U : S.Opens, Dense (U : Set S) ∧ IsIso (q ∣_ U))
    (g : pullback y q ⟶ pullback x q)
    (hgq : g ≫ pullback.snd x q = pullback.snd y q)
    (hgc : g ≫ pullback.fst x q ≫ a = pullback.fst y q ≫ b)
    (hy : Y) (hyclosed : IsClosed ({y.asFiber hy} : Set (y.fiber (y hy)))) :
    (Set.range (baseModificationFibreMap c x y a b hac hbc q g hgc hy)).Finite ∧
      ∀ z ∈ Set.range (baseModificationFibreMap c x y a b hac hbc q g hgc hy),
        IsClosed ({z} : Set (x.fiber (y hy))) := by
  sorry


end AlgebraicGeometry

