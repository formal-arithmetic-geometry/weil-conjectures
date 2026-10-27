/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.Sober
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.AlgebraicGeometry.LocalFinitelyPresentedImmersionLocus
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.Span
import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.NagataQCOpenBasechangedAffineChartFP
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Representability of fixed generic-fibre free-rank loci

Source: Stacks Project, More on Flatness, Tag 05UC,
`lemma-free-at-generic-points-representable`, with `situation-free-at-generic-points`
and `equation-free-at-generic-points`
(blueprint: lem-sfb-smooth-generic-rank-locus-representability).

The subterminal functor is represented by its unique-factorization property on all
S-schemes. The freeness condition is on an open of the ambient base change, not merely
on its fibre. No separate definition of the already used generic-free predicate is needed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The fixed generic-fibre free-rank condition is represented by a locally closed
immersion of finite presentation. Geometric irreducibility includes nonempty fibres.
Unique factorization identifies each represented value with the specified singleton
or empty set, naturally under precomposition by morphisms of S-schemes.

Source: Stacks Project, More on Flatness, Tag 05UC
(blueprint: lem-sfb-smooth-generic-rank-locus-representability).

Proof:
1. We use the following geometry also after arbitrary base change and restriction to source and
base opens. Smoothness is preserved by these operations, and implies flatness and local finite
presentation. Smooth fibres are geometrically reduced; combined with the assumed geometric
irreducibility and nonemptiness this makes every fibre geometrically integral. Thus its generic
point has a field as its local ring within the fibre. Define
$p(s)=\dim_{\kappa(\xi_s)}(E_{\xi_s}\otimes\kappa(\xi_s))$. For $t\mapsto s$, the generic point of
$X_t$ maps to that of $X_s$: on affine fibre rings the field extension gives an injective map of
domains, and localization to their fraction fields still is injective. Tensoring a vector-space
basis with the resulting field extension shows $p(t)=p(s)$. Here all sheaf pullbacks have the
tensor description on affine opens. Consequently $H_r(T)$ implies $p(h(t))=r$ for every $t\in T$.
Pulling back a free neighbourhood preserves freeness and contains the new generic point, so $H_r$
is stable under arbitrary base change. Its predicate is Zariski local on $T$, directly from its
neighbourhood definition.
Uses: lem-pc-proper-base-change, lem-weil-pbc-smooth-restrict-open-subschemes, lem-pc-smooth-flat,
sbc-lem-smooth-geometrically-reduced, def-pc-geometrically-irreducible, lem-weil-pbc-module-
pullback-affine-sections.

2. Write $X=\operatorname{Spec}B$, $S=\operatorname{Spec}A$, and $M=\Gamma(X,E)$. The affine
finite-presentation criterion makes $M$ finitely presented, hence finitely generated. A finite
generating list of length $N$ gives $p(s)\leq N$ for all $s$. Fix $s$. Choose $p(s)$ elements of
$M$ whose images are a basis of $M\otimes_B\kappa(\xi_s)$, by selecting a basis from the images of
a generating list. Stalks are module localizations, and Nakayama over $B_{\xi_s}$ says these
elements generate $M_{\xi_s}$. The cokernel of their map $B^{\oplus p(s)}\to M$ is finitely
generated and vanishes on localization at $\xi_s$. Each of finitely many cokernel generators is
killed by an element outside $\xi_s$; their product $b\notin\xi_s$ kills the cokernel. We have a
surjection $\mathcal O_{D(b)}^{\oplus p(s)}\twoheadrightarrow E|_{D(b)}$. The image of $D(b)$ in
$S$ is open, since $g$ is flat and locally finitely presented. Choose an affine neighbourhood
$V_s$ of $s$ inside this image, and put $U_s=D(b)\times_S V_s$. Both $U_s,V_s$ are affine. Their
morphism is smooth, has nonempty geometrically integral fibres, and carries the displayed
generating surjection. For each $t\in V_s$, its fibre open $U_{s,t}$ is nonempty and has the same
generic point as $X_t$. This remains true after any base change. Therefore restricting to $U_s$
leaves every $H_r$ unchanged over $V_s$, and $p(t)\leq p(s)$ there.
Uses: lem-weil-pbc-quasi-coherent-finite-type-affine, lem-sbc-affine-module-germ-localization,
lem-weil-pbc-nakayama-local-generators, lem-weil-pbc-flat-lfp-open.

3. Consider any such chart $U\to V$ with a fixed surjection $u:\mathcal O_U^{\oplus
n}\twoheadrightarrow E|_U$. Its global-isomorphism predicate after base change equals $H_n$. Only
the forward implication needs work. Test on affine opens $T=\operatorname{Spec}R$ of an arbitrary
$V$-scheme. Write $U_T=\operatorname{Spec}C$ and $L=\Gamma(U_T,E_T)$. The affine flatness and
presentation criteria make $R\to C$ flat and finitely presented; its fibres are geometrically
integral and nonempty by step 1. The tensor pullback formula and preservation of finite module
presentation make $L$ finitely presented. Suppose $H_n(T)$ holds. For every prime $\mathfrak
p\subset R$, $\mathfrak q=\mathfrak p C$ is prime and contracts to $\mathfrak p$: $C/\mathfrak
pC=C\otimes_RR/\mathfrak p$ is flat over the domain $R/\mathfrak p$, hence torsion-free, so it
embeds into its localization $C\otimes_R\kappa(\mathfrak p)$, the fibre ring, which is a nonzero
domain; torsion-freeness of this nonzero module also makes $R/\mathfrak p\to C/\mathfrak pC$
injective. At $\mathfrak q$, $L_{\mathfrak q}$ is free of rank $n$ over $C_{\mathfrak q}$; it is
flat over $R_{\mathfrak p}$ by smooth flatness. The localized surjection is an isomorphism: in
chosen bases it is a surjective square matrix, whose right inverse makes its determinant a unit,
so its adjugate gives an inverse. In particular its residue-field map is an isomorphism. Apply
[lem-sfb-local-flat-generic-basis-universal-injectivity] at $\mathfrak p,\mathfrak q$. On some
$D(f)$ containing $\mathfrak p$ the specified $u$ is universally injective over $R_f$, hence
injective by taking the tensor test module $R_f$. It remains surjective, so is an isomorphism
there. These $D(f)$ cover $T$, proving $u_T$ is an isomorphism. Conversely an isomorphism $u_T$
trivializes $E_T$ everywhere on $U_T$ and immediately implies $H_n(T)$.
Uses: lem-weil-pbc-flat-morphism-affine-criterion, lem-weil-pbc-lfp-affine-opens-finite-
presentation, lem-pc-fp-module-base-change, lem-sfb-local-flat-generic-basis-universal-
injectivity.

4. For $n=p(s)$ apply [lem-sfb-flat-integral-free-surjection-iso-locus] to $U_s\to V_s$ and its
generating surjection. Flatness and finite presentation follow from smoothness and the affine
criteria used in step 3; the source is affine over the affine base and the target module is
finitely presented. This gives a closed immersion of finite presentation representing $H_{p(s)}$
over $V_s$, by step 3. For $q>p(s)$, $H_q$ over $V_s$ is the empty functor: a nonempty test scheme
satisfying it would have a point $t$ with $q=p(h(t))\leq p(s)$, a contradiction. On the empty test
scheme both predicates hold vacuously, as does factorization through the empty scheme.
Uses: lem-sfb-flat-integral-free-surjection-iso-locus.

5. We prove, simultaneously for all $r$, representability by a finitely presented locally closed
immersion over every quasi-compact open $B\subseteq S$, by induction on an upper bound $m$ for $p$
on $B$. Such a $B$ has a finite cover by principal affine opens of $S$, with affine intersections,
so is quasi-separated. The empty $B$ is immediate. For a nonempty $B$ take the actual maximum $m$;
it exists by the finite bound $N$ in step 2. At a point with $p(s)=m$, step 4 gives a closed
finitely presented representative of $H_m$ on a neighbourhood inside $B$. At a point with
$p(s)<m$, it gives the empty representative on a neighbourhood. Apply [lem-sc-local-finitely-
presented-immersion-locus] using the base-change stability and source-locality proved in step 1,
to glue these representatives to an immersion $Z_m\to B$ locally of finite presentation. All its
base restrictions just constructed are closed immersions. Closed immersion is local on the target,
so $Z_m\to B$ is closed. Its local defining ideals are of finite type by [lem-trf-closed-
immersion-finite-presentation-ideal]; these local finite-generation statements give a finite-type
ideal sheaf on $B$, and the same criterion shows $Z_m\to B$ is of finite presentation. Its
underlying set is exactly $\{s:p(s)=m\}$: the residue-field test at $s$ belongs to $H_{p(s)}$,
indeed on the affine integral fibre choose lifts of a basis over its fraction field. Their map
from a finite free module to the finitely presented fibre module is bijective at the zero prime.
By [lem-weil-pbc-finite-to-finitely-presented-map-iso-at-prime-spreads] it is bijective after
inverting a nonzero element, giving a free neighbourhood of the fibre generic point. It cannot
belong to another $H_r$, by step 1.
Uses: lem-sc-local-finitely-presented-immersion-locus, lem-weil-pbc-closed-finite-etale-zariski-
local, lem-trf-closed-immersion-finite-presentation-ideal, lem-weil-pbc-finite-to-finitely-
presented-map-iso-at-prime-spreads.

6. The open complement $B'=B\setminus |Z_m|$ is quasi-compact. Indeed take a finite affine cover
of $B$. On each member the ideal of $Z_m$ is quasi-coherent and of finite type by the ideal
criterion in step 5, so its sections there form a finitely generated ideal by [lem-weil-pbc-quasi-
coherent-finite-type-affine] (a), so its complement is a finite union of principal opens. Each
principal open is affine and quasi-compact, and a finite union of such spaces is quasi-compact.
Now $p\leq m-1$ on $B'$. If $m=0$, $B'$ is empty and all $H_r$ except $H_0$ are empty. Otherwise
apply the induction hypothesis to $B'$, a quasi-compact open of the original affine $S$. For
$r<m$, the predicate $H_r(T)$ for $T\to B$ forces the image of every point into $B'$, by step 1.
The open-factorization lemma then factors this map uniquely through $B'$. Conversely a test map
through $B'$ has exactly the same generic-freeness predicate there. Thus the representative
supplied by induction over $B'$ also represents $H_r$ over $B$. For $r>m$ the functor is empty,
and $r=m$ was settled in step 5.
Uses: lem-weil-pbc-quasi-coherent-finite-type-affine, lem-weil-pbc-spec-basic-opens-unit-ideal-
quasi-compact, lem-weil-pbc-morphism-factors-through-open-subscheme.

7. The inclusion $B'\hookrightarrow B$ in step 6 is finitely presented: apply [lem-nagata-qc-open-
basechanged-affine-chart-fp] with its base $S$ the original affine $S=\operatorname{Spec}A$, its
test scheme $T=B$, its affine chart $\operatorname{Spec}A\to S$ the identity, and its quasi-
compact open $W=B'\subseteq X_T=B$. The needed quasi-compactness and quasi-separatedness of $B$
were checked in step 5. Composition preserves finite presentation and immersions by [lem-weil-pbc-
proper-fp-permanence], clauses (d) and (e). Hence every representative inherited from $B'$ is a
finitely presented locally closed immersion into $B$. This completes the induction. Finally take
$B=S$, which is quasi-compact since affine, to obtain $S_r\to S$ for every $r\geq0$. All
comparisons were on arbitrary test schemes, using affine open covers only to test module
isomorphisms, so this represents $H_r$ on all $S$-schemes, including nonreduced and nonaffine
ones.
Uses: lem-nagata-qc-open-basechanged-affine-chart-fp, lem-weil-pbc-proper-fp-permanence, lem-weil-
pbc-spec-basic-opens-unit-ideal-quasi-compact. -/
theorem exists_smooth_generic_rank_locus
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (g : X ⟶ S) [Smooth g] [GeometricallyIrreducible g]
    (E : X.Modules) [E.IsQuasicoherent] [E.IsFinitePresentation] (r : ℕ) :
    ∃ (Sᵣ : Scheme.{u}) (i : Sᵣ ⟶ S),
      IsImmersion i ∧ LocallyOfFinitePresentation i ∧ QuasiCompact i ∧ QuasiSeparated i ∧
      ∀ (T : Scheme.{u}) (h : T ⟶ S),
        (∀ (t : T) (ξ : (pullback.snd g h).fiber t),
          IsGenericPoint ξ Set.univ →
            ∃ W : (Limits.pullback g h).Opens,
              (pullback.snd g h).fiberι t ξ ∈ W ∧
              Nonempty (((tensorPullback (pullback.fst g h)).obj E).over W ≅
                SheafOfModules.free (ULift.{u} (Fin r)))) ↔
        ∃! k : T ⟶ Sᵣ, k ≫ i = h := by
  sorry

end AlgebraicGeometry.Scheme.Modules
