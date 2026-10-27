/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
public import Sheaf.AlgebraicGeometry.SyntomicFixedDimensionOpen
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.JacobsonSpace
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Sheaf.TraceFormula.SyntomicLocusBaseChange
import Sheaf.TraceFormula.LciPointwiseCriterion
import Sheaf.AlgebraicGeometry.LCICohenMacaulayStalks
import WeilConjectures.AlgebraicGeometry.EquidimensionalFibreOpenPartition
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import WeilConjectures.AlgebraicGeometry.DimensionAtPointFieldExtension
import Sheaf.TraceFormula.RelativeDimensionBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.GeometricRegularitySmoothFieldCriterion
import Sheaf.RingTheory.SeparableClosedPointFormalPresentation
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import Sheaf.RingTheory.RegularQuotientCompletionKernelTest
import Sheaf.TraceFormula.CompletionLocalCompleteIntersection
import WeilConjectures.RingTheory.ClosedPointDimensionLocalRing
import WeilConjectures.RingTheory.CompletionDimensionEquality

/-! # The syntomic locus of a fixed relative dimension

Source: Stacks Project, morphisms.tex, Tags 02V3, 02NM, 02K1, 02NK and 01UF;
varieties.tex, Tag 0A21; more-algebra.tex, Tag 07NV; dpa.tex, Tags 09Q1 and 09Q6.
(blueprint: lem-sfb-syntomic-fixed-dimension-locus).

The candidate open is constructed as a supremum of source opens. The theorem asserts
that this union itself has the required properties, commutes with base change, and has
the stated geometric-fibre and completed-local-algebra descriptions.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The largest syntomic source open of relative dimension `d`, its arbitrary-base-change
compatibility, its geometric-fibre union description, smooth-neighbourhood inclusion,
and the closed-point criterion via the completed local algebra. The displayed ring
isomorphism respects the ground field through the original structure map and completion
map; no coefficient-field splitting is selected.

Source: Stacks Project, morphisms.tex, Tags 02V3, 02NM, 02K1, 02NK and 01UF;
varieties.tex, Tags 0A21 and 0C52; more-algebra.tex, Tag 07NV; dpa.tex, Tags 09Q1
and 09Q6; algebra.tex, Tag 00SG
(blueprint: lem-sfb-syntomic-fixed-dimension-locus).

Proof, following the node's steps:
1. We may restrict $g$ to a source open without losing flatness or local finite presentation: the
   local-ring maps are unchanged, and an affine presentation near a point can be restricted to a
   principal affine neighbourhood inside the open. Explicitly, replacing
   $B=A[z_1,\ldots,z_r]/(f_1,\ldots,f_s)$ by $B_b$ adds a variable $u$ and the single relation
   $ub-1$. A finite presentation is in particular a finite-type presentation, so $g$ is locally of
   finite type. For any base change $T'\to T$, [lem-weil-pbc-flat-morphism-base-change] and clause
   (3) of [lem-weil-pbc-qcqs-morphism-permanence] show that $g_{T'}$ is again flat and locally of
   finite presentation. These observations apply also to geometric fibres and all subsequent
   source opens.
2. Apply [lem-trf-syntomic-locus-base-change] to obtain the open $V\subseteq P$ of points $x$ for
   which the local ring of $P_{g(x)}$ at $x$ is a complete-intersection local ring over
   $\kappa(g(x))$. It satisfies $V(g_{T'})=p^{-1}V(g)$ for the projection $p:P\times_TT'\to P$. By
   [lem-trf-lci-pointwise-criterion], the ordinary fibres of $V$ have the affine lci covers stated
   here. For $t\in T$ and its chosen algebraic closure, $\bar
   t:\operatorname{Spec}\overline{\kappa(t)}\to T$, the same equality of loci says that every
   local ring of the geometric fibre $V_{\bar t}$ is a complete-intersection local ring over
   $\overline{\kappa(t)}$; the same criterion gives an affine lci cover of $V_{\bar t}$, and
   likewise of $O_{\bar t}$ for every open $O\subseteq V$, whose local rings are among these.
   Conversely, suppose an open $W$ has lci geometric fibres, and take $x\in W$ with $t=g(x)$. The
   ring $\kappa(x)\otimes_{\kappa(t)}\overline{\kappa(t)}$ is a tensor product of two nonzero
   vector spaces over a field, hence nonzero, so it has a prime ideal. By [lem-weil-pbc-fibre-
   product-points] there is a point $x_1$ of $P_{\bar
   t}=P\times_T\operatorname{Spec}\overline{\kappa(t)}$ with $p(x_1)=x$; it lies in the open
   $W_{\bar t}=p^{-1}(W)$. Its local ring there, which is its local ring on $P_{\bar t}$, is a
   complete intersection over $\overline{\kappa(t)}$ by the local-ring criterion, so $x_1\in
   V(g_{\bar t})=p^{-1}V(g)$ and hence $x\in V(g)$. Thus $g|_V$ and its restrictions to source
   opens are syntomic in precisely the geometric-fibre definition stated here, and every syntomic
   source open lies in $V$.
3. Every ordinary fibre of $V\to T$ has an affine lci cover by step 2. At each $x\in V$, its fibre
   is an open of $P_{g(x)}$ and has the same local ring at $x$. Thus [lem-sfb-lci-cohen-macaulay-
   stalks] gives depth equal to Krull dimension at every one of its points, including nonclosed
   points. Apply [lem-sbc-cohen-macaulay-equidimensional-fibre-pieces] with source $P$, base open
   $T$ and source open $W=V$. It gives pairwise disjoint opens $V_n$ covering $V$, such that every
   nonempty fibre of $V_n\to T$ is pure of dimension $n$. By [lem-sbc-equidimensional-open-local-
   dimension], for $x\in V_n$ the local topological dimension of the original fibre $P_{g(x)}$ at
   $x$ is $n$. Write this dimension as $\nu_g(x)$. As the $V_n$ cover $V$, each $V_n$ is exactly
   $\{x\in V:\nu_g(x)=n\}$. Define $L_d(g)=V_d$. In particular it is an open of $P$, and its
   ordinary nonempty fibres are pure of dimension $d$.
4. Let $T'\to T$ be arbitrary and let $x'\in P'=P\times_TT'$ map to $x\in P$, with base points
   $t'$ and $t$. The fibre through $x'$ is $P_t\times_{\kappa(t)}\kappa(t')$. On an affine
   neighbourhood $\operatorname{Spec}S$ of $x$ in $P_t$, the algebra $S$ is finite type over
   $\kappa(t)$ by [lem-weil-pbc-lft-affine-pairs]. The inverse-image chart is
   $\operatorname{Spec}(S\otimes_{\kappa(t)}\kappa(t'))$; the prime for $x'$ contracts to the
   prime for $x$ under $s\mapsto s\otimes1$. Applying [lem-weil-pbc-dimension-at-point-field-
   extension] to these primes gives $\nu_{g_{T'}}(x')=\nu_g(x)$; taking the affine neighbourhood
   does not change local topological dimension, since neighbourhoods contained in an open form a
   cofinal neighbourhood family. By step 2, $x'$ belongs to $V(g_{T'})$ exactly when $x\in V(g)$.
   Using the description of $V_d$ in step 3 on both schemes gives $x'\in L_d(g_{T'})$ exactly when
   $x\in L_d(g)$. The opens are therefore equal. Under the canonical fibre-product identification
   of inverse-image opens this is $L_d(g_{T'})=L_d(g)\times_TT'$.
5. The restriction to the open $L_d(g)\subseteq V$ is syntomic by step 2. Its ordinary fibres are
   pure of dimension $d$ by step 3, so [lem-trf-relative-dimension-base-change] shows that its
   geometric fibres are pure of dimension $d$ as well. For maximality, let $W\subseteq P$ be any
   open with the two required geometric-fibre properties. Step 2 gives $W\subseteq V$. For $x\in
   W$ with $t=g(x)$, [lem-weil-pbc-fibre-product-points] gives, as in step 2, a point $x_1$ of the
   geometric fibre $W_{\bar t}$ over the chosen $\overline{\kappa(t)}$ with $p(x_1)=x$. The open
   $W_{\bar t}$ of $P_{\bar t}$ is nonempty and pure of dimension $d$, so [lem-sbc-
   equidimensional-open-local-dimension] gives $\dim_{x_1}(P_{\bar t})=d$. Take an affine
   neighbourhood $\operatorname{Spec}S$ of $x$ in $P_t$, with $S$ finite type over $\kappa(t)$ by
   [lem-weil-pbc-lft-affine-pairs]. Then $x_1$ lies in the open
   $\operatorname{Spec}(S\otimes_{\kappa(t)}\overline{\kappa(t)})$ of $P_{\bar t}$, as a prime
   lying over the prime of $x$. The equality in [lem-weil-pbc-dimension-at-point-field-extension],
   with local dimension unchanged on passing to an open as in step 4, gives $\nu_g(x)=d$. Thus
   $x\in V_d$, proving $W\subseteq L_d(g)$.
6. For a geometric fibre $C=P\times_T\operatorname{Spec}\Omega$, step 4 identifies $L_d(g)_\Omega$
   with $L_d(C\to\operatorname{Spec}\Omega)$. The latter is itself an open lci scheme, pure of
   dimension $d$, by steps 2, 3 and 5. Conversely, if $O\subseteq C$ is any open lci scheme pure
   of dimension $d$, then $O\to\operatorname{Spec}\Omega$ is an open restriction of the geometric
   base change of the original flat, locally finitely presented $g$. Thus step 1 supplies both
   properties; flatness is inherited from $g$, without a new assumption on $O$. By [lem-trf-lci-
   pointwise-criterion] every local ring of $O$ is a complete intersection. Its locus in [lem-trf-
   syntomic-locus-base-change] is therefore all of $O$, and stays all of the source after any
   geometric base change; applying the local-ring criterion again makes those fibres lci. Its
   pure-dimensional ordinary fibre remains pure of dimension $d$ under every field extension by
   [lem-trf-relative-dimension-base-change]. Hence maximality from step 5 gives $O\subseteq
   L_d(C\to\operatorname{Spec}\Omega)$. Since this open is one of the $O$ under consideration, it
   is exactly their union.
7. Suppose $x$ has an open neighbourhood $H\subseteq P$ on which $g$ is smooth of relative
   dimension $d$. By [lem-sbc-smooth-relative-dimension-permanence], every geometric fibre of
   $H\to T$ is smooth of relative dimension $d$ over its algebraically closed base field, so is
   pure of dimension $d$ by [def-sbc-smooth-morphisms]. For such a smooth fibre, [lem-weil-pbc-
   geometric-regularity-smooth-field-criterion], taking the identity field extension, says every
   local ring is regular. By [lem-weil-pbc-lft-affine-pairs] and [lem-weil-pbc-affine-open-stalk-
   localization], it is also essentially of finite type over the field: it is a localization of a
   finite-type affine coordinate algebra. Such a regular local algebra is a complete-intersection
   local algebra by using its identity quotient and the empty regular sequence. The local-ring
   criterion [lem-trf-lci-pointwise-criterion] therefore gives an affine lci cover of that fibre.
   Step 1 supplies flatness and local finite presentation of $g|_H$, so $H$ has both properties in
   step 5 and $x\in H\subseteq L_d(g)$.
8. Fix a closed point $c$ of the geometric fibre $C$ and an affine neighbourhood
   $U=\operatorname{Spec}S\subseteq C$. By [lem-weil-pbc-lft-affine-pairs], $S$ is a finitely
   generated $\Omega$-algebra. Closedness of $c$ makes its prime $\mathfrak m$ maximal. By [lem-
   weil-pbc-affine-open-stalk-localization], $A=\mathcal O_{C,c}=S_{\mathfrak m}$. The residue-
   field result [lem-weil-pbc-closed-point-residue-field-base] identifies $S/\mathfrak m$ with
   $\Omega$ via its given structural map, not an unspecified field isomorphism. Apply [lem-trf-
   separable-closed-point-formal-presentation] to $k=F=\Omega$ (the identity extension is finite
   separable). It gives Noetherian local rings $A,\widehat A$ and a surjection of
   $\Omega$-algebras $\Phi:Q=\Omega[[t_1,\ldots,t_r]]\twoheadrightarrow\widehat A$, with kernel in
   $(t_1,\ldots,t_r)$. The $\Omega$-action is the original one: the $\Omega$-algebra section of
   the residue map is forced to be the structural map when $F=\Omega$.
9. If $c$ belongs to the syntomic open $V(C\to\operatorname{Spec}\Omega)$, then $A$ is a complete-
   intersection local $\Omega$-algebra. By [lem-trf-lci-pointwise-criterion], write $A\cong R/I$
   as a $\Omega$-algebra, where $R$ is regular local, essentially of finite type over $\Omega$,
   and $I$ is generated by a finite regular sequence. Since $A=S_{\mathfrak m}$ has residue field
   $\Omega$, it is nonzero. Hence $I$ is proper and lies in the unique maximal ideal of $R$, as
   required by the kernel test. The isomorphism $A\cong R/I$ identifies the unique maximal ideals,
   hence their powers and the quotients by those powers. Taking their inverse limits identifies
   $\widehat A$ with $\widehat{R/I}$ as $\Omega$-algebras. Via this identification, $\Phi$ is the
   surjection onto the completion of $R/I$ required below. By [lem-weil-pbc-power-series-field-
   cohen-regular-complete], the source $Q$ of $\Phi$ in step 8 is regular local. Apply [lem-trf-
   regular-quotient-completion-kernel-test] to $R,I,Q,\Phi$. It says that $\ker\Phi$ is generated
   by a finite $Q$-regular sequence $h_1,\ldots,h_s$ in the maximal ideal. Since $\Phi$ respects
   $\Omega$, its quotient isomorphism $Q/(h_1,\ldots,h_s)\cong\widehat A$ respects $\Omega$ as
   well. Conversely, an isomorphism of completed local $\Omega$-algebras to a finite-variable
   power series quotient by a regular sequence in its maximal ideal is in particular a ring
   isomorphism. By [lem-trf-completion-local-complete-intersection], applied to $S,\mathfrak m$,
   it gives a principal affine lci neighbourhood of $c$. The local-ring criterion then gives that
   $A$ is a complete-intersection local $\Omega$-algebra, so $c\in
   V(C\to\operatorname{Spec}\Omega)$. This proves the equivalence while retaining the coefficient-
   algebra structure in the forward direction.
10. At the closed point $c$, [lem-weil-pbc-closed-point-dimension-local-ring] applied on $U$ gives
   $\nu_{C\to\operatorname{Spec}\Omega}(c)=\dim A$: passing to the open $U$ does not change local
   dimension. Since $A$ is Noetherian local by step 8, [lem-weil-pbc-completion-dimension-eq]
   gives $\dim A=\dim\widehat A$. Together with the pointwise description $L_d=\{c\in
   V:\nu(c)=d\}$ in step 3 and the equivalence in step 9, this proves exactly that $c\in
   L_d(g)_\Omega$ if and only if $\widehat A$ is a complete-intersection completed local
   $\Omega$-algebra of Krull dimension $d$. All constructions and arguments include the empty
   source or an empty fibre: the partitions and loci there are empty, the empty scheme has pure
   dimension $d$ by [def-weil-pure-dimension], and the closed-point clauses have no instances.
   Empty regular sequences are allowed, so the regular and dimension-zero cases have not been
   excluded.
-/
theorem syntomic_fixed_dimension_locus {P T : Scheme.{u}} (g : P ⟶ T)
    [Flat g] [LocallyOfFinitePresentation g] (d : ℕ) :
    IsGreatest {U : P.Opens | (U.ι ≫ g).IsSyntomicOfRelativeDimension d}
      (g.syntomicFixedDimensionOpen d) ∧
    (∀ (T' : Scheme.{u}) (b : T' ⟶ T),
      (pullback.snd g b).syntomicFixedDimensionOpen d =
        (pullback.fst g b) ⁻¹ᵁ (g.syntomicFixedDimensionOpen d)) ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
      (pullback.fst g t) ⁻¹ᵁ (g.syntomicFixedDimensionOpen d) =
        sSup {O : (pullback g t).Opens |
          IsLocalCompleteIntersectionOver Ω O.toScheme (O.ι ≫ pullback.snd g t) ∧
            O.toScheme.IsPureDimension d}) ∧
    (∀ (x : P),
      (∃ H : P.Opens, x ∈ H ∧ SmoothOfRelativeDimension d (H.ι ≫ g)) →
        x ∈ g.syntomicFixedDimensionOpen d) ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
      (c : ↥(pullback (C := Scheme.{u}) g t)),
      c ∈ closedPoints ↥(pullback (C := Scheme.{u}) g t) →
      (c ∈ (pullback.fst g t) ⁻¹ᵁ (g.syntomicFixedDimensionOpen d) ↔
        (∃ (r s : ℕ) (h : Fin s → MvPowerSeries (Fin r) Ω),
          RingTheory.Sequence.IsRegular (MvPowerSeries (Fin r) Ω) (List.ofFn h) ∧
          (∀ i, h i ∈ Ideal.span (Set.range
            (fun j : Fin r ↦ (MvPowerSeries.X j : MvPowerSeries (Fin r) Ω)))) ∧
          ∃ e : (MvPowerSeries (Fin r) Ω ⧸ Ideal.span (Set.range h)) ≃+*
              AdicCompletion
                (IsLocalRing.maximalIdeal ((pullback g t).presheaf.stalk c))
                ((pullback g t).presheaf.stalk c),
            ∀ a : Ω,
              e (algebraMap Ω (MvPowerSeries (Fin r) Ω ⧸ Ideal.span (Set.range h)) a) =
                algebraMap ((pullback g t).presheaf.stalk c) _
                  (((pullback.snd g t).stalkMap c).hom
                    ((StructureSheaf.toStalk Ω ((pullback.snd g t) c)).hom a))) ∧
        ringKrullDim
          (AdicCompletion (IsLocalRing.maximalIdeal ((pullback g t).presheaf.stalk c))
            ((pullback g t).presheaf.stalk c)) = (d : WithBot ℕ∞))) := by
  sorry

end AlgebraicGeometry
