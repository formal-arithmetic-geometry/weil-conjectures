/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q81
-/
module

public import Sheaf.TraceFormula.ValuationHorizontalCurveModels
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.AlgebraicGeometry.NormalSectionsFiniteProduct
import WeilConjectures.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree
import Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal
import Sheaf.TraceFormula.SmoothGeometricallyNormal
import Sheaf.TraceFormula.ValuationCurveProjectivePreparation
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.MultipointedCurveModification

/-! # Factoring a semistable modification through the normal target

Source: Temkin, Stable modification of relative curves, Lemma 4.4.4, first sentence;
Lemma 4.4.1(i) and Remark 4.1
(blueprint: lem-trf-semistable-normal-target-factorization).

The normalization is Mathlib's relative integral-closure construction in the generic fibre.
The marking is specified by `FlatClosure`, including the equality with the kernel ideal of
its generic marking. Its presentation as an embedded scheme is existential, not chosen.
Both component comparisons use the original source, including after arbitrary geometric
base change. On an irreducible component the image is nonempty, so `Set.Subsingleton`
means precisely that the image consists of one point.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Temkin

/-- A semistable eta-modification factors through the finite relative normalization of its
original target, with its source curve and marking unchanged. The normal target carries
the schematic closure of the original generic marking. Contracted ordinary and geometric
fibre components are the same for the original map and its factor.
Source: Temkin, Lemma 4.4.4, first sentence (printed p. 31), Lemma 4.4.1(i) (p. 30),
and Remark 4.1 (pp. 24--25)
(blueprint: lem-trf-semistable-normal-target-factorization).

Proof plan (the eight steps of the DAG node):
1. The base $T$ is normal integral and affine, hence quasi-compact and quasi-separated. Indeed every
   localization $V_{\mathfrak p}$ is again a valuation domain: for an element of $K^\times$ one of
   it and its inverse already belongs to $V$. A valuation domain is integrally closed: if $z$ is
   integral but outside it, $z^{-1}$ is in its maximal ideal, and division of a monic equation by
   the highest power of $z$ puts $1$ in that maximal ideal. The generic point is a principal open.
   If $V=K$ take $a=1$; otherwise take $0\ne a$ in its least nonzero prime. Every nonzero prime
   contains $a$, so $D(a)=\eta$ and $V[1/a]=K$. For each flat $T$-scheme used below, [lem-sc-flat-
   invertible-sections-torsion-free] applied to its structure sheaf makes multiplication by $a$
   injective on every affine open. Thus localization into its generic fibre is injective, and that
   generic open is schematically dense. This applies to $X,D,Y,E$ and subsequently to $N,D_N$.
   Dependencies: lem-sc-flat-invertible-sections-torsion-free.

2. Apply the first assertion of [lem-trf-valuation-curve-projective-preparation] to the $T$-curve
   $X$: all valuation hypotheses agree, and $X_\eta$ is smooth. It gives a finite
   $\eta$-modification $X^\nu\to X$ with normal source, which is flat and finitely presented of pure
   relative dimension one. We identify this absolute normalization with the specified relative
   normalization $N$. On an affine open $\operatorname{Spec}A\subset X$, flatness gives
   $A\hookrightarrow A_K$ by Step 1. The reducedness and finite-component assertion of [lem-trf-
   valuation-horizontal-curve-models], together with the dense generic open from Step 1, shows that
   the irreducible components of $X$ and of $X_\eta$ have the same generic points. Its generic
   affine open is smooth over $K$, so its local rings are normal by [lem-trf-smooth-geometrically-
   normal], and it is Noetherian by [lem-weil-pbc-finite-type-over-noetherian]. By [lem-sbc-normal-
   sections-finite-product], $A_K$ is a finite product of integrally closed domains $C_i$. Thus the
   component function fields are $\operatorname{Frac}C_i$. An element of their product integral over
   $A$ is integral over $A_K$ as well; coordinatewise normality puts it in every $C_i$, hence in
   $A_K$. Conversely an element of $A_K$ integral over $A$ is integral in the product of these
   fraction fields. The two integral closures therefore coincide. Their affine normalization maps
   agree with the charts of [lem-weil-pbc-relative-normalization]; these canonical identifications
   glue over $X$. Hence $N=X^\nu$, proving all the asserted normality, finiteness, flatness, finite
   presentation, relative dimension and generic-fibre claims for $N$ and $\nu$. No integrality of
   $X$ is assumed. Dependencies: lem-trf-valuation-curve-projective-preparation, lem-trf-smooth-
   geometrically-normal, lem-weil-pbc-finite-type-over-noetherian, lem-sbc-normal-sections-finite-
   product, lem-weil-pbc-relative-normalization, lem-trf-valuation-horizontal-curve-models.

3. Apply [lem-trf-valuation-horizontal-curve-models] to $(X,D)$ and the reduced modification
   $\nu:N\to X$ of Step 2. Normality makes $N$ reduced, and $\nu$ is an $\eta$-modification. Its
   marking assertion says exactly that the schematic closure of $D_\eta$ in $N$ is a flat finitely
   presented marking of pure relative dimension zero, and that $(N,D_N)\to(X,D)$ is an
   $\eta$-modification of multipointed curves. It is the $D_N$ in the statement, since the cited
   closure is defined by the same restriction kernel. We shall also need $\nu_D:D_N\to D$ to be
   finite. The generic marking lies in $N\times_XD$, so every local equation defining that closed
   subscheme vanishes on $D_\eta$ and hence on its schematic closure $D_N$. Thus $D_N\hookrightarrow
   N\times_XD$ is a closed immersion. The projection $N\times_XD\to D$ is finite by [lem-weil-pbc-
   finite-morphism-permanence](a). Over an affine of $D$ it is a finite algebra, and its quotient
   defining $D_N$ is still generated by the images of the same finite module generators. Therefore
   $\nu_D$ is finite, and is proper and separated by [lem-weil-pbc-finite-proper]. Dependencies:
   lem-trf-valuation-horizontal-curve-models, lem-weil-pbc-finite-morphism-permanence, lem-weil-pbc-
   finite-proper.

4. The source $Y$ is normal. To prove this without assuming strict semistability, apply [lem-trf-
   geometrically-reduced-eta-normal] to the semistable multipointed curve $(Y,E)$ over the normal
   integral qcqs base $T$ from Step 1. Its statement explicitly includes this semistable instance
   and gives that $Y$ is $\eta$-normal. Since $f_\eta$ is an isomorphism, $Y_\eta\simeq X_\eta$ is
   smooth. Apply [lem-trf-valuation-curve-projective-preparation] to the $T$-curve $Y$. Its
   normalization $Y^\nu\to Y$ is a finite $\eta$-modification with normal source. By
   $\eta$-normality it is an isomorphism, so $Y$ itself is normal. Dependencies: lem-trf-
   geometrically-reduced-eta-normal, lem-trf-valuation-curve-projective-preparation.

5. The normal-source factorization assertion of [lem-trf-valuation-curve-projective-preparation] now
   applies to $f_Y:Y\to X$: it is an $\eta$-modification with normal source by Step 4. With the
   identification $N=X^\nu$ of Step 2 it gives a morphism $g_Y:Y\to N$ satisfying $\nu g_Y=f_Y$.
   This morphism is proper by [lem-weil-pbc-proper-to-separated], applied over $X$: $Y\to X$ is
   proper and $N\to X$ is separated since it is proper. Its generic fibre is
   $\nu_\eta^{-1}f_{Y,\eta}$, an isomorphism. The generic opens of $Y$ and $N$ are schematically
   dense by Step 1, so $g_Y$ is an $\eta$-modification of curves. Dependencies: lem-trf-valuation-
   curve-projective-preparation, lem-weil-pbc-proper-to-separated.

6. Let $h:E\hookrightarrow Y\xrightarrow{g_Y}N$. Its generic fibre is the prescribed inclusion of
   $D_\eta$ into $N_\eta$. Every section of the ideal of $D_N$ therefore pulls back to zero on the
   generic open of $E$. Since that open is schematically dense by Step 1, the pulled-back section is
   zero. The kernel-ideal factorization assertion [lem-weil-pbc-scheme-image-qc-kernel](2) gives a
   unique $g_D:E\to D_N$ with $h=i_Ng_D$. This use is legitimate on every affine open of $N$: the
   relevant ideal is contained in the kernel of the map to sections on its inverse image in $E$.
   Moreover $h$ is quasi-compact: $E$ is quasi-compact, and $N$ is quasi-separated, so [lem-weil-
   pbc-qcqs-morphism-permanence](1) applies. The equality $\nu_Dg_D=f_D$ follows by composing the
   marking square and cancelling the closed immersion $D\hookrightarrow X$. By [lem-weil-pbc-proper-
   to-separated] over $D$, $g_D$ is proper, since $f_D$ is proper and $\nu_D$ is separated by Step
   3. It is an isomorphism on the generic fibre. Its generic source and target are schematically
   dense by Step 1. Thus $g=(g_Y,g_D)$ is an $\eta$-modification of pairs, and both marking and
   curve equations give $f=\nu\circ g$. Dependencies: lem-weil-pbc-scheme-image-qc-kernel, lem-weil-
   pbc-qcqs-morphism-permanence, lem-weil-pbc-proper-to-separated.

7. Semistability is a condition on the source pair: the geometric curve fibres are nodal or smooth,
   and the marking is etale and lies in the smooth locus, as in [def-trf-multipointed-curve-
   modification]. The construction of $g$ has changed neither $Y$ nor $E$ nor its closed immersion
   into $Y$. Thus the same semistable source pair makes $g$ a semistable $\eta$-modification. This
   establishes the required factorization with the source and its marking unchanged. Dependencies:
   def-trf-multipointed-curve-modification.

8. Fix $t\in T$ and an irreducible component $C$ of $Y_t$. If $g_Y(C)$ is one point, then
   $f_Y(C)=\nu(g_Y(C))$ is one point. Conversely suppose $f_Y(C)=\{x\}$. The image $g_Y(C)$ is a
   nonempty irreducible subset of the topological fibre $\nu^{-1}(x)$. That fibre is finite
   discrete: over an affine neighbourhood of $x$, the finite map $\nu$ is given by a finite algebra
   $A\to B$, and the fibre algebra $B\otimes_A\kappa(x)$ is finite over the field $\kappa(x)$
   (tensor the finite set of module generators). Apply [lem-weil-pbc-finite-over-zero-dim-local-
   discrete-spectrum] with this field as the zero-dimensional local base. The fibre-prime
   correspondence of [lem-weil-pbc-fibre-ring-primes-bijection] identifies these points with the
   points of $N$ over $x$ and preserves specialization. Since all the fibre primes are maximal, no
   two distinct points of this finite subspace specialize to one another; it is therefore discrete.
   A nonempty irreducible subset of a finite discrete space has exactly one point. Hence $g_Y(C)$ is
   a singleton. For any algebraically closed $\Omega$ with $\operatorname{Spec}\Omega\to T$, [lem-
   weil-pbc-finite-morphism-permanence](a) makes $\nu_\Omega:N_\Omega\to X_\Omega$ finite. The same
   argument applies to every irreducible component of $Y_\Omega$ and the equation
   $f_\Omega=\nu_\Omega g_\Omega$. This proves the geometric-base-change assertion without assuming
   that an original component stays irreducible after extension. Dependencies: lem-weil-pbc-finite-
   over-zero-dim-local-discrete-spectrum, lem-weil-pbc-fibre-ring-primes-bijection, lem-weil-pbc-
   finite-morphism-permanence. -/
theorem semistable_normal_target_factorization
    (B : HorizontalValuationBase.{u}) (P Q : MultipointedCurve B.T) (f : Q.Hom P)
    (hSmooth : Smooth (pullback.snd P.x B.genericMap))
    (hEtale : Etale (pullback.snd P.d B.genericMap))
    (hf : f.IsEtaModification B.genericMap) (hQ : Q.IsSemistable) :
    ∃ (_ : QuasiCompact (pullback.fst P.x B.genericMap))
      (_ : QuasiSeparated (pullback.fst P.x B.genericMap)),
      (∀ z : (pullback.fst P.x B.genericMap).normalization,
        IsDomain ((pullback.fst P.x B.genericMap).normalization.presheaf.stalk z) ∧
        IsIntegrallyClosed ((pullback.fst P.x B.genericMap).normalization.presheaf.stalk z)) ∧
      IsFinite (pullback.fst P.x B.genericMap).fromNormalization ∧
      ∃ (hn : RelativeCurve ((pullback.fst P.x B.genericMap).fromNormalization ≫ P.x))
        (D : Scheme.{u}) (i : D ⟶ (pullback.fst P.x B.genericMap).normalization)
        (hD : FlatClosure ((pullback.fst P.x B.genericMap).fromNormalization ≫ P.x)
          B.genericMap
          (horizontalGenericMarkingι P B.genericMap
            (pullback.fst P.x B.genericMap).fromNormalization) i)
        (r : D ⟶ P.D)
        (hr : r ≫ P.d = i ≫ (pullback.fst P.x B.genericMap).fromNormalization ≫ P.x)
        (hi : r ≫ P.i = i ≫ (pullback.fst P.x B.genericMap).fromNormalization),
        (horizontalClosurePairMap P B.genericMap
          (pullback.fst P.x B.genericMap).fromNormalization i hn hD r hr hi).IsEtaModification
            B.genericMap ∧
        ∃ g : Q.Hom (horizontalClosurePair
            ((pullback.fst P.x B.genericMap).fromNormalization ≫ P.x) B.genericMap
            (horizontalGenericMarkingι P B.genericMap
              (pullback.fst P.x B.genericMap).fromNormalization) i hn hD),
          g.IsEtaModification B.genericMap ∧
          f.curve = g.curve ≫ (pullback.fst P.x B.genericMap).fromNormalization ∧
          f.marking = g.marking ≫ r ∧
          (∀ (t : B.T) (C : Set (Q.x.fiber t)), C ∈ irreducibleComponents (Q.x.fiber t) →
            (((Q.x.fiberι t ≫ f.curve) '' C).Subsingleton ↔
              ((Q.x.fiberι t ≫ g.curve) '' C).Subsingleton)) ∧
          (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B.T)
            (C : Set (pullback (C := Scheme) Q.x s)),
            C ∈ irreducibleComponents (pullback (C := Scheme) Q.x s) →
            (((f.curveBaseChange s) '' C).Subsingleton ↔
              ((g.curveBaseChange s) '' C).Subsingleton)) := by
  sorry

end AlgebraicGeometry.Temkin
