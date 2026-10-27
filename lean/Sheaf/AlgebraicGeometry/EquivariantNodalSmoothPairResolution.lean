module

public import Sheaf.AlgebraicGeometry.SplitMarkedNodalAction
public import Sheaf.AlgebraicGeometry.SmoothStrictNormalCrossingsDivisor
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.Blowup.FlatBaseChange
import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Sheaf.AlgebraicGeometry.SmoothPairLocalCoordinates
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle
import Sheaf.AlgebraicGeometry.FreeCharacteristicRegularBoundary
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.AlgebraicGeometry.LogBlowupNormalization
import Sheaf.AlgebraicGeometry.LogSmoothLogRegular
import Sheaf.AlgebraicGeometry.NCMaximalBranchBlowup
import Sheaf.TraceFormula.NodalDivisorialChart
import Sheaf.SixFunctors.TraceFormula.NodalEtaleChart
import Sheaf.SixFunctors.TraceFormula.NodalLogRegularity
import Sheaf.AlgebraicGeometry.PermissibleBoundaryPreservation
import Sheaf.TraceFormula.ProjectiveBundleProper
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization
import Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import WeilConjectures.Blowup.FiniteDegree.Algebra
import WeilConjectures.Blowup.Complement

/-! # Equivariant resolution of a marked nodal curve over a smooth pair

Source: ILO, Travaux de Gabber, X Lemma 2.2 proof, pp.149--150, the smooth-pair
variant of Vidal 4.4.4 (blueprint: lem-sfb-equivariant-nodal-smooth-pair-resolution).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- The one-curve equivariant projective resolution over an arbitrary field, including
semilinear actions. The closed set `B` is the marked boundary on `T`, not an additional
exceptional set. Dense-open isomorphisms commuting with the morphisms express
birationality; on integral schemes they also identify the function fields by the induced
map. Equivariance of `r` is specified on both fibre-product projections and therefore
is equivariance for the diagonal action. The final component equations are in ordinary
local rings, with distinct members of one regular system of parameters.
Source: ILO X Lemma 2.2 proof, pp.149--150, relative smooth-pair variant of Vidal 4.4.4
(blueprint: lem-sfb-equivariant-nodal-smooth-pair-resolution).

Proof (the fifteen steps of the DAG):

1. Put $W=T\times_SS_0$, $g:W\to S_0$, $M_0=M\times_SS_0$, and $B=|M_0|\cup g^{-1}|E|$. The
semistable marked base-change statement gives flatness, finite presentation, the one-dimensional
nodal fibres, and the smooth-locus condition for $(W,M_0)$. Its geometric generic fibre is the
original generic curve, since $t$ is birational. Projective-bundle properness gives finite type
of $t$. Finite-type composition and base change, followed by the finite-type-over-Noetherian
theorem, make $S,S_0,T,W$ Noetherian and finite type over $F$; a field is Noetherian since its
only ideals are $0$ and $F$. In particular all later bases are quasi-compact and
quasi-separated. The diagonal action of $J$ on the fibre product preserves $M_0$ and $B$.
Uses: lem-trf-semistable-marked-base-change, lem-sfb-finite-type-composition-base-change,
lem-weil-pbc-finite-type-over-noetherian, lem-trf-projective-bundle-proper,
def-weil-proper-morphism.

2. The projective-bundle convention is preserved by the base changes used here. Indeed, on
affine charts $A\to A'$, for a finite-type module $N$ the canonical graded identity
$A'\otimes_A\operatorname{Sym}_A N=\operatorname{Sym}_{A'}(A'\otimes_A N)$ identifies the
corresponding projective bundles: their standard charts are the degree-zero parts after
localization at a degree-one generator, and these same presentations commute with
$A'\otimes_A-$. Finitely many generators of $N$ pull back to generators, and these chart
identifications agree on intersections. Pull back the closed immersion defining a projective
morphism and apply the cited closed-immersion base-change theorem. Thus both $g:W\to S_0$ and
$q:W\to T$ are projective in precisely the required convention. In particular $g$ is proper by
the projective-bundle properness theorem.
Uses: def-trf-projective-bundle-morphism, lem-weil-pbc-closed-immersion-base-change,
lem-trf-projective-bundle-proper.

3. Both $T$ and $W$ are integral. Here is the flatness argument, applied with base $S$ and then
$S_0$. For an affine open $\operatorname{Spec}A$ of the integral base, let
$\operatorname{Spec}C$ be a nonempty affine open of its inverse image and
$K=\operatorname{Frac}(A)$. Flatness makes $C\to C\otimes_AK$ injective: multiplication by every
nonzero $a\in A$ is injective on $C$. The localization is nonzero and is the ring of a nonempty
affine open of the integral generic curve, hence is a domain; therefore $C$ is a domain. Every
nonempty open meets the generic fibre by the same localization argument. Two such opens meet
because their intersections with the generic fibre meet. Thus the total space is reduced and
irreducible. This also proves density of every inverse image of a dense open of the base. No
reduction or choice of a main component of $W$ is needed.

4. Apply the relative normal-crossings chart criterion to $(S_0,E)$: its divisorial log
structure is fs, log regular and log smooth over the trivial log scheme $\operatorname{Spec}F$.
The marking $M_0$ is an effective Cartier divisor, finite etale over $S_0$. To check the only
additional assertion, work in the relative smooth locus of $g$ and apply the smooth-pair
coordinate theorem to one section $S_0\hookrightarrow W_{\mathrm{sm}}$ over $S_0$. Relative
dimension one makes its equation a single coordinate $z=0$, a nonzerodivisor. Near that section
avoid the other disjoint closed sections; off all sections the ideal is the unit ideal. Hence
the finite union is Cartier. These arguments include empty $E$ or $M_0$.
Uses: lem-sfb-free-characteristic-relative-nc-criterion, lem-pur-smooth-pair-local-coordinates.

5. The hypotheses of the nodal log-regularity theorem now hold for $g$, base boundary $|E|$, and
Cartier marking $M_0$: Step 2 supplies properness and Step 1 supplies flat finite presentation
and the nodal fibres. It follows that $B$ is nowhere dense and $(W,B)$ is log regular, with its
divisorial log structure. In particular its open complement $U=W\setminus B$ is dense. Notice
that $B$ is exactly the pullback support of $|M|\cup f^{-1}D$, because $|E|=t^{-1}D$.
Uses: lem-trf-nodal-log-regularity.

6. We also need relative log smoothness, which is not a clause of the preceding cited node. Use
the nodal-chart theorem: at a node the etale local equation is $uv=h$, with
$h=\varepsilon\alpha(a)$ in an fs base chart $P$, and away from nodes the map is smooth or has
the marked coordinate $z=0$. For a node use the divisorial-chart theorem with $R=\mathbf Z\oplus
P$ and $Q=\mathbf N^2\amalg_{\mathbf N}R$. It identifies the comparison scheme with
$uv=\varepsilon\alpha(a)$ and gives injective $R^{\rm gp}\to Q^{\rm gp}$ with cokernel $\mathbf
Z$. The comparison from the nodal neighbourhood is etale, so the definition of log smoothness
applies. At smooth unmarked points use $P\to P$; at marked points use $P\to P\oplus\mathbf N$
and the coordinate $z$. The log structure in each case is the divisorial one: log regularity and
the recovery assertion of the injective-chart theorem identify it from the same triviality locus
$U$. Thus $(W,B)\to(S_0,E)$ is log smooth. The composition theorem and Step 4 give log
smoothness over the trivial log field $F$.
Uses: lem-trf-nodal-etale-chart, lem-trf-nodal-divisorial-chart, def-per-fs-log-smooth-etale,
lem-trf-log-smooth-log-regular, lem-sfb-log-smooth-composition-strict-base-change.

7. Construct the regularization tower directly from fan charts, without a separatedness
assumption on $W$. Its sharp saturated characteristic monoids have torsion-free group
completions: if $na=0$, saturation puts both $a$ and $-a$ in the monoid, so $a$ is a unit and
hence zero. The fan-chart theorem gives strict etale neighbourhoods with saturated torsion-free
fan charts. On any such chart $c:V\to F$, pull back the functorial saturated fan
desingularization using the fan-chart blowup theorem. Its last characteristic monoids are free.
For two charts of a strict comparison, the local-comparison theorem identifies the localized
fans by an isomorphism. Fan functoriality for these localizations and isomorphisms identifies
their contracted towers, retaining ordered centers. These comparisons respect composition and
finite disjoint unions. Thus the hypotheses of log-blowup etale descent hold, and it gives a
finite global tower $W_1\to W$ with free final characteristic monoids. Applying these
comparisons to each automorphism of $(W,B)$ lifts $J$ to the tower; composition compatibility
gives the group law. Everything here concerns log schemes and their automorphisms, so it also
applies when $J$ acts nontrivially on $F$.
Uses: lem-trf-log-fan-chart-blowup, lem-trf-functorial-fan-desingularization,
lem-trf-strict-fan-chart-local-comparison, lem-trf-functorial-log-blowup-etale-descent.

8. Each global step of this tower is a normalized ordinary blowup along the finite-type nonzero
ideal generated by its coherent log center, by the log-blowup normalization theorem. The
ordinary blowup is integral and projective in the projective-bundle sense. It is finite type
over $F$; its normalization in its function field is finite, surjective and birational by the
finite-type normalization theorem. The finite map is projective in the projective-bundle sense,
and projective-bundle composition applies because every base is Noetherian. Inductively the
global composite $W_1\to W$ is projective and birational, and all its stages are integral
finite-type schemes. This proves global projectivity from the actual descended ideals, rather
than from local projectivity. The log-blowup theorem identifies its triviality locus with the
inverse image of $U$ and gives an isomorphism there.
Uses: lem-trf-log-blowup-normalization, lem-sfb-integral-blowup-projective-geometry,
lem-sfb-finite-type-composition-base-change, lem-sc-normalization-exists,
lem-trf-finite-projective-bundle, lem-sfb-projective-bundle-composition.

9. Saturated log blowups are log etale, so Step 6 and log-smooth composition show that $W_1$ is
still log smooth over the trivial log field $F$. Step 8 preserves log regularity and Step 7
gives free characteristic monoids; the free-characteristic criterion for a log regular scheme
therefore gives regularity of $W_1$. Applying the new relative chart criterion shows that $W_1$
is smooth over $F$ and that $B_1=(W_1\times_WB)_{\mathrm{red}}$ has smooth relative
normal-crossings charts. This is the point where mere regularity would be insufficient over an
imperfect field. We have not yet asserted strictness of the global components.
Uses: lem-sfb-log-smooth-composition-strict-base-change,
lem-trf-free-characteristic-regular-boundary, lem-sfb-free-characteristic-relative-nc-criterion.

10. Strictify by the maximal-branch algorithm, retaining $D_i$, the strict transform of the
original $B_1$, and $H_i$, the accumulated reduced exceptional boundary. Start with $D_0=B_1$,
$H_0=\varnothing$. Inductively the full boundary is $D_i\cup H_i$, is normal crossings, and
$H_i$ is strict normal crossings. If $D_i$ is nonempty, its geometric branch count has a finite
positive maximum $m_i$. The maximal-branch blowup theorem gives the reduced closed locus $Z_i$
where this maximum is reached; it is regular and, in boundary coordinates, is
$z_1=\cdots=z_{m_i}=0$, with $D_i$ given by $z_1\cdots z_{m_i}=0$. Its blowup has strict
transform $D_{i+1}$ with branch count at most $m_i-1$. The center is invariant under every
automorphism preserving $D_i$, since its definition uses only this intrinsic branch count.
Consequently it is $J$-invariant.
Uses: lem-trf-nc-maximal-branch-blowup.

11. These ordinary blowups preserve the relative smooth charts. In a chart of Step 9 the center
is the inverse image of the coordinate ideal $(z_1,\ldots,z_m)$ under a smooth map to $\mathbf
A^r_F$. Smooth maps are flat, so the flat blowup base-change theorem applies. Its standard
$z_i$-chart has coordinates $z_i$, $v_j=z_j/z_i$ for $1\leq j\leq m$, $j\ne i$, and $z_k$ for
$k>m$. The reduced full boundary is $$z_i\prod_{1\leq j\leq m,\ j\ne i}v_j\prod_{m<k\leq
r}z_k=0.$$ This chart is affine space over $F$ with its coordinate boundary, and the pulled-back
chart maps smoothly to it. Every coordinate intersection remains smooth of the expected
codimension. The affine blowup charts cover, and smoothness is preserved by their base changes
and composition, so the assertion holds globally at every stage. Thus the relative smoothness is
checked over $F$ itself, without descending regularity from an algebraic closure.
Uses: lem-pc-smooth-flat, def-nagata-blowup-flat-base-change-map,
thm-nagata-blowup-flat-base-change, prop-nagata-affine-blowup-chart-cover,
lem-sbc-smooth-relative-dimension-permanence, lem-sfb-free-characteristic-relative-nc-criterion.

12. Apply permissible-boundary preservation at each step to $B_i=D_i\cup H_i$, $H_i$ and $Z_i$.
Its exact conclusions give the normal-crossings full boundary and strictness of
$H_{i+1}=(b_i^{-1}(H_i\cup Z_i))_{\mathrm{red}}$, together with $B_{i+1}=D_{i+1}\cup H_{i+1}$.
This closes the induction in Step 10; the relative charts in Step 11 make all its regular strata
smooth over $F$. After at most $m_0$ iterations $D_i$ is empty, since the positive maximum
strictly decreases. The final reduced full boundary is therefore $H_i$, a relative strict normal
crossings divisor: locally each of its distinct global components is a single coordinate branch,
and their intersections are precisely coordinate intersections. If $m_i=1$, the center is
Cartier and its blowup can be the identity, but its old strict transform is empty and that
divisor is included in $H_{i+1}$; the same decrease still holds. If $B_1$ is empty, the tower
has length zero. Each blowup is integral and projective by the ordinary-blowup theorem, and is
an isomorphism off its center. Its action is induced on the Rees algebra by the invariant
center, with group multiplication inherited degreewise. Hence the whole strictification tower is
$J$-equivariant.
Uses: lem-trf-permissible-boundary-preservation, lem-sfb-integral-blowup-projective-geometry,
thm-nagata-global-blowup-complement.

13. Let $T'$ be the last scheme and $r:T'\to W$ the composite of both towers. Projective-bundle
composition makes $r$ projective, and projective-bundle properness makes it closed. It is
birational because each step is an isomorphism over the same dense $U$, with unchanged function
field; it is surjective because its closed image contains dense $U$. It is $J$-equivariant by
Steps 7 and 12, and Step 11 gives smoothness over $F$. Every step changes the boundary to its
reduced total inverse image, so the final boundary $E'$ is exactly $(r^{-1}B)_{\mathrm{red}}$.
The log-blowup and ordinary-blowup complement statements show that $r$ is an isomorphism outside
$B$. These prove the asserted support and complement clauses, including when both markings and
boundary are empty.
Uses: lem-sfb-projective-bundle-composition, lem-trf-projective-bundle-proper,
def-weil-proper-morphism.

14. The regularity already obtained and the strict boundary supplied by Step 12 satisfy the
strict-boundary parameter criterion. At $x\in T'$ its ideal is $(t_1\cdots t_s)$ for distinct
members of a regular system of parameters of $\mathcal O_{T',x}$. The regular-local
factorization theorem makes each $t_i$ prime. Consequently the reduced union defined by this
product has as its components through $x$ exactly the distinct height-one ideals $(t_i)$; thus
each component has the required individual local equation. This is an assertion in the ordinary
local ring, not only the strict henselization. All local rings are regular by the earlier
regularization and permissible-boundary preservation conclusions.
Uses: lem-sfb-snc-boundary-parameter-criterion,
lem-trf-regular-local-ufd-boundary-factorization.

15. Finally $q:W\to T$ is the base change of the projective birational surjection $t$. By Step 2
it is projective. Choose a dense open $V\subseteq S$ over which $t$ is an isomorphism; $f^{-1}V$
is dense in integral $T$ by Step 3. Over this open $q$ is an isomorphism, so it is birational;
its image is closed by projective-bundle properness and contains this dense open, hence it is
surjective. Composition with $r$ gives all three assertions for $T'\to T$, with the same
function field. If $S_0$ embeds into finite-dimensional projective space over $F$, the cited
ample-sheaf theorem gives an ample invertible sheaf on $S_0$. The projective-bundle morphism
$T'\to S_0$ is then H-projective by the conversion theorem. Its composite with the H-projective
structure map $S_0\to\operatorname{Spec}F$ is H-projective by H-projective composition. This
proves the final finite-projective-space clause, without conflating the two projectivity
conventions.
Uses: lem-trf-projective-bundle-proper, def-weil-proper-morphism,
lem-sfb-projective-bundle-composition, lem-weil-pbc-projective-ample-invertible,
lem-trf-projective-bundle-to-h-projective, lem-trf-h-projective-composition.
-/
theorem exists_equivariant_nodal_smooth_pair_resolution
    (F : Type u) [Field F] (S T : Scheme.{u}) (s : S ⟶ Spec (.of F))
    [IsIntegral S] [LocallyOfFiniteType s] [QuasiCompact s]
    (D : Closeds S) (f : T ⟶ S) (hf : IsProjectiveBundle f)
    [Flat f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (hfib : HasNodalGeometricFibres f) [GeometricallyReduced f]
    (η : S) (hη : IsGenericPoint η Set.univ)
    [Smooth (f.fiberToSpecResidueField η)]
    [GeometricallyIntegral (f.fiberToSpecResidueField η)]
    (hsmooth : ∀ x : T, f x ∉ D → x ∈ f.smoothLocus)
    (n : ℕ) (m : Fin n → (S ⟶ T))
    (hm : ∀ i, m i ≫ f = 𝟙 S)
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (Set.range (m i)) (Set.range (m j))))
    (hmark : ∀ i, Set.range (m i) ⊆ (f.smoothLocus : Set T))
    (B : Closeds T) (hB : (B : Set T) = (⋃ i, Set.range (m i)) ∪ f ⁻¹' (D : Set S))
    (J : Type v) [Group J] [Finite J] (ρ : J →* (F ≃+* F))
    (aT : J →* Aut T) (aS : J →* Aut S)
    (heq : ∀ g, (aT g).hom ≫ f = f ≫ (aS g).hom)
    (hscalar : ∀ g, (aS g).hom ≫ s =
      s ≫ Spec.map (CommRingCat.ofHom (ρ g⁻¹).toRingHom))
    (hD : ∀ g, (aS g).hom '' (D : Set S) = D)
    (hM : ∀ g, (aT g).hom '' (⋃ i, Set.range (m i)) = ⋃ i, Set.range (m i))
    (hsplit : IsSplitMarkedNodalAction f aT aS n m)
    (S₀ : Scheme.{u}) [IsIntegral S₀] (t : S₀ ⟶ S)
    (ht : IsProjectiveBundle t) [Surjective t] [Smooth (t ≫ s)]
    (htbir : ∃ (U : S.Opens) (V : S₀.Opens) (e : V.toScheme ≅ U.toScheme),
      Dense (U : Set S) ∧ Dense (V : Set S₀) ∧ e.hom ≫ U.ι = V.ι ≫ t)
    (a₀ : J →* Aut S₀) (heqt : ∀ g, (a₀ g).hom ≫ t = t ≫ (aS g).hom)
    (hE : Scheme.IdealSheafData.IsSmoothStrictNormalCrossingsDivisor (t ≫ s)
      (((Scheme.IdealSheafData.vanishingIdeal D).comap t).radical)) :
    ∃ (T' : Scheme.{u}) (r : T' ⟶ pullback (C := Scheme.{u}) f t) (a' : J →* Aut T'),
      IsIntegral T' ∧ Smooth (r ≫ pullback.snd f t ≫ t ≫ s) ∧
      IsProjectiveBundle r ∧ Surjective r ∧
      (∃ (U : (pullback (C := Scheme.{u}) f t).Opens) (V : T'.Opens) (e : V.toScheme ≅ U.toScheme),
        Dense (U : Set (pullback (C := Scheme.{u}) f t)) ∧ Dense (V : Set T') ∧
          e.hom ≫ U.ι = V.ι ≫ r) ∧
      IsProjectiveBundle (r ≫ pullback.fst f t) ∧ Surjective (r ≫ pullback.fst f t) ∧
      (∃ (U : T.Opens) (V : T'.Opens) (e : V.toScheme ≅ U.toScheme),
        Dense (U : Set T) ∧ Dense (V : Set T') ∧
          e.hom ≫ U.ι = V.ι ≫ r ≫ pullback.fst f t) ∧
      (∀ g, (a' g).hom ≫ r ≫ pullback.fst f t = r ≫ pullback.fst f t ≫ (aT g).hom) ∧
      (∀ g, (a' g).hom ≫ r ≫ pullback.snd f t = r ≫ pullback.snd f t ≫ (a₀ g).hom) ∧
      (∀ U : (pullback (C := Scheme.{u}) f t).Opens,
        (U : Set (pullback (C := Scheme.{u}) f t)) = ((pullback.fst f t) ⁻¹' (B : Set T))ᶜ →
          IsIso (r ∣_ U)) ∧
      (∃ E' : T'.IdealSheafData,
        E' = ((Scheme.IdealSheafData.vanishingIdeal B).comap
          (r ≫ pullback.fst f t)).radical ∧
        E'.IsSmoothStrictNormalCrossingsDivisor (r ≫ pullback.snd f t ≫ t ≫ s) ∧
        ∃ (k : ℕ) (C : Fin k → T'.IdealSheafData),
          E' = (⨅ i, C i) ∧ (∀ i, IsIntegral (C i).subscheme) ∧
          (∀ i j, (C i).support ≤ (C j).support → i = j) ∧
          ∀ x : T', ∃ (U : T'.affineOpens) (hx : x ∈ U.1)
            (hR : IsNoetherianRing (T'.presheaf.stalk x))
            (params : List (T'.presheaf.stalk x)),
            @IsLocalRing.IsRegularSystemOfParameters (T'.presheaf.stalk x) _ _ hR params ∧
            ∃ ι : {i : Fin k // x ∈ (C i).support} → Fin params.length,
              Function.Injective ι ∧ ∀ i,
                ((C i.1).ideal U).map (T'.presheaf.germ U.1 x hx).hom =
                  Ideal.span {params.get (ι i)}) ∧
      IsRegularScheme T' ∧
      (IsHProjective (t ≫ s) → IsHProjective (r ≫ pullback.snd f t ≫ t ≫ s)) := by
  sorry

end AlgebraicGeometry
