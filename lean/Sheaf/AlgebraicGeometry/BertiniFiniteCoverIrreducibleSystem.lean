/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import Sheaf.AlgebraicGeometry.IsRegularScheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Topology.Connected.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.AlgebraicGeometry.GeometricIrreducibilityFiniteSeparableTest
import Sheaf.AlgebraicGeometry.BertiniIrreducibleMember
import WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.AlgebraicGeometry.Properties
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Sheaf.AlgebraicGeometry.RationalUnramifiedCotangentCriterion
import Mathlib.Algebra.MvPolynomial.Basic
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionLocalRingLocalization
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Topology.Sets.Closeds
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre
import Sheaf.AlgebraicGeometry.ClosedPointField
import WeilConjectures.RingTheory.Etale.LocalDimension

/-! # Simultaneous irreducibility on a finite étale cover

Source: main-20261015 blueprint, proof of `lem-zl-bertini-finite-cover-curve`, paragraph 3;
Stacks Project, Tag 0G4F (blueprint: lem-zl-bertini-finite-cover-irreducible-system).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- General sections cut geometrically irreducible subschemes simultaneously on `X` and `T`.
A finite set of closed points represents the reduced finite set of rational points: over
an algebraically closed field, closed points of a finite-type scheme are exactly rational
points. `U₀` is its open complement. The basis supplies coordinates on `A(V)` and on `P(V)`;
no injectivity of `ψ` is assumed. An additive map with the displayed scalar identity is
precisely a `k`-linear map for the canonical action on global sections.

Source: main-20261015 blueprint, `lem-zl-bertini-finite-cover-curve.proof.md`, paragraph 3;
Stacks Project, Tag 0G4F (blueprint: lem-zl-bertini-finite-cover-irreducible-system).

Proof (the DAG's fifteen steps):
1. Write $X=\operatorname{Spec}A$. By [def-weil-finite-integral-morphism],
   $T=\operatorname{Spec}B$ with $B$ finite as an $A$-module. If $a_1,\ldots,a_m$ generate $A$
   over $k$ and $b_1,\ldots,b_n$ generate $B$ as an $A$-module, these elements together generate
   $B$ as a $k$-algebra: every element of $B$ is an $A$-linear combination of the $b_j$. Thus
   $T$ is affine of finite type over $k$. Form $L_T=\pi^*L$ and the linear map
   $\psi_T(v)=\pi^*\psi(v)$ using the tensor formula in [def-pc-module-pullback]. A local frame
   $e$ of $L$ pulls back to a frame $1\otimes e$ of $L_T$, so it is invertible. Etaleness
   includes flatness by [def-weil-etale-morphism]; hence [lem-pc-zero-scheme-properties]
   identifies $Z(\psi_T(v))$ with $T\times_X H_v=T_v$. Uses: def-weil-finite-integral-morphism,
   def-pc-module-pullback, def-weil-etale-morphism, lem-pc-zero-scheme-properties.
2. By [lem-weil-pbc-etale-smooth-zero-dimensional-fibres], $\pi$ is smooth. Its composition with
   the smooth map $X\to\operatorname{Spec}k$ is smooth by [lem-trf-smooth-composition], so both
   $X$ and $T$ are smooth over $k$. Apply [lem-weil-pbc-smooth-scheme-over-field-regular] to
   each, then [lem-sc-regular-connected-integral] using their assumed nonempty connectedness.
   Both schemes are integral; in particular $A$ and $B$ are domains by [def-pc-integral-scheme].
   Uses: lem-weil-pbc-etale-smooth-zero-dimensional-fibres, lem-trf-smooth-composition,
   lem-weil-pbc-smooth-scheme-over-field-regular, lem-sc-regular-connected-integral,
   def-pc-integral-scheme.
3. Every finite separable field extension $E/k$ is isomorphic to $k$ over $k$: the minimal
   polynomial of each element splits over the algebraically closed field $k$ and, being
   irreducible, is linear. Thus $\operatorname{Spec}(A\otimes_kE)$ and
   $\operatorname{Spec}(B\otimes_kE)$ are isomorphic to the integral, hence irreducible schemes
   $X$ and $T$. Apply [lem-zl-geometric-irreducibility-finite-separable-test] separately to $A$
   and $B$. It follows that $X$ and $T$ are geometrically irreducible over $k$. Uses:
   lem-zl-geometric-irreducibility-finite-separable-test, def-pc-integral-scheme.
4. Every closed point of either finite-type $k$-scheme has residue field finite over $k$ by
   [lem-kun-closed-point-field], hence equal to $k$. A $k$-rational point maps to a
   $k$-rational, therefore closed, point under $\pi$. Since $X$ is integral of pure dimension
   $d$, $\dim A=d$ by [lem-weil-pbc-spec-topological-krull-dimension-ring]. For every closed
   $x\in X$, [lem-weil-pbc-finite-type-domain-dimension-local-ring-localization] gives
   $\dim\mathcal O_{X,x}=d$. For every closed $t\in T$, with $x=\pi(t)$, the affine etale ring
   map $A\to B$ gives $\dim\mathcal O_{T,t}=\dim\mathcal O_{X,x}=d$ by
   [lem-sc-etale-local-dimension]. Finally [lem-sc-scheme-stalk-dimension-generalization-chains]
   identifies these dimensions with $\operatorname{codim}(\{x\},X)$ and
   $\operatorname{codim}(\{t\},T)$. Uses: lem-kun-closed-point-field,
   lem-weil-pbc-spec-topological-krull-dimension-ring,
   lem-weil-pbc-finite-type-domain-dimension-local-ring-localization,
   lem-sc-etale-local-dimension, lem-sc-scheme-stalk-dimension-generalization-chains.
5. The support of the common zero scheme on $X$ is exactly $S$: all sections vanish on $S$, and
   at every point outside $S$ some section is nonzero in the fibre by
   [lem-weil-pbc-invertible-generating-sections-fibre]. On $T$ the support is exactly
   $\pi^{-1}S$, since locally the pullback ideal is generated by the images of the same finitely
   many section coefficients. This asserts equality of supports, without asserting that the base
   schemes are reduced. Each fibre over $s\in S$ has dimension zero by
   [lem-weil-pbc-etale-smooth-zero-dimensional-fibres] and is affine of finite type over $k$
   (its ring is $B\otimes_A k$). By [lem-weil-pbc-finite-type-dim-zero-artinian] it has finitely
   many points. These points are $k$-rational and closed in $T$ by the preceding step. Thus both
   base supports are finite sets of closed points, and all their irreducible components have
   codimension $d\ge2$ by the preceding step. This verifies hypothesis (ii) of
   [lem-zl-bertini-irreducible-member] for both systems. Uses:
   lem-weil-pbc-invertible-generating-sections-fibre,
   lem-weil-pbc-etale-smooth-zero-dimensional-fibres,
   lem-weil-pbc-finite-type-dim-zero-artinian, lem-zl-bertini-irreducible-member.
6. The open $T\setminus\pi^{-1}S$ is nonempty. Otherwise the underlying space of the nonempty
   scheme $T$ would be a finite set of closed points, with no strict generalizations;
   [lem-sc-scheme-stalk-dimension-generalization-chains] would give dimension zero for all its
   local rings, contrary to dimension $d\ge2$ at closed points. By
   [lem-sc-lft-over-field-jacobson-space], closed points are dense in $T$, so choose a closed
   $t$ in this open and set $x=\pi(t)$. Both are $k$-rational and $x\notin S$. Uses:
   lem-sc-scheme-stalk-dimension-generalization-chains, lem-sc-lft-over-field-jacobson-space.
7. Choose $v_1\in V$ with $s_1=\psi(v_1)$ nonzero at $x$, using
   [lem-weil-pbc-invertible-generating-sections-fibre], and extend $v_1$ to a basis
   $v_1,e_2,\ldots,e_r$ of $V$. Near $x$, use $s_1$ as frame and put $a_i=\psi(e_i)/s_1$. By
   [def-weil-pbc-morphism-to-projective-space-by-sections] and
   [lem-weil-pbc-projective-space-standard-charts], these are the pullbacks of the polynomial
   coordinates $T_i/T_1$ on the corresponding affine chart. The assumed immersion gives a
   surjection from the local ring of projective space at the image of $x$ onto $\mathcal
   O_{X,x}$: factor it as an open immersion after a closed immersion and use
   [def-weil-closed-immersion]. It therefore gives a surjection on maximal ideals modulo their
   squares. The maximal ideal of the chart at this $k$-point is generated by $T_i/T_1-a_i(x)$
   (subtracting a polynomial's value expresses it in these generators). Consequently the classes
   of $a_i-a_i(x)$ span $\mathfrak m_x/\mathfrak m_x^2$. They are the local coefficients of
   $\psi(w_i)$, where $w_i=e_i-a_i(x)v_1$ vanishes at $x$. Uses:
   lem-weil-pbc-invertible-generating-sections-fibre,
   def-weil-pbc-morphism-to-projective-space-by-sections,
   lem-weil-pbc-projective-space-standard-charts, def-weil-closed-immersion.
8. For each of the two regular local rings $R=\mathcal O_{X,x}$ and $R=\mathcal O_{T,t}$, let
   $\mathfrak m$ be its maximal ideal and put $e=\dim_k\mathfrak m/\mathfrak m^2$. Regularity
   and $\dim R=d$ imply $e\le d$ by [def-weil-regular-scheme]. Lift a basis of this cotangent
   space to $e$ elements of $\mathfrak m$; they generate $\mathfrak m$ by
   [lem-weil-pbc-nakayama-local-generators], since $\mathfrak m$ is finite over the Noetherian
   ring $R$. Applying [lem-weil-pbc-noetherian-height-quotient-bound] with $J=\mathfrak
   P=\mathfrak m$ gives $d\le e$, since $R/\mathfrak m=k$ has height zero. Hence $e=d$ for both
   local rings. Uses: def-weil-regular-scheme, lem-weil-pbc-nakayama-local-generators,
   lem-weil-pbc-noetherian-height-quotient-bound.
9. Because $\pi$ is etale it is unramified by [def-weil-etale-morphism]. At the rational points
   $t,x$, [lem-sc-rational-unramified-cotangent-criterion] gives a surjection $\mathfrak
   m_x/\mathfrak m_x^2\to\mathfrak m_t/\mathfrak m_t^2$. Thus the pulled-back classes of
   $a_i-a_i(x)$ span the latter space, of dimension $d\ge2$. Choose two $k$-linear combinations
   of the $w_i$, denoted $v_2,v_3$, whose pulled-back coefficients have independent cotangent
   classes at $t$. Their coefficients at $x$ are also independent, since any relation at $x$
   would pull back to a relation at $t$. The sections $\psi(v_2),\psi(v_3)$ vanish at $x$, their
   pullbacks vanish at $t$, and $\psi(v_1)$ and its pullback are nonzero at these points. Uses:
   def-weil-etale-morphism, lem-sc-rational-unramified-cotangent-criterion.
10. In each local ring $R$ of step 8, let $f,g$ be the coefficients of these two sections in the
   frame $\psi(v_1)$ or its pullback. Their independent classes extend to a basis of $\mathfrak
   m/\mathfrak m^2$; lifting the rest and applying [lem-weil-pbc-nakayama-local-generators]
   extends $f,g$ to a minimal set of $d$ generators of $\mathfrak m$. By
   [lem-weil-pbc-regular-local-generators-regular-sequence], $R/(f)$ and $R/(f,g)$ are regular
   local rings of dimensions $d-1,d-2$. By [lem-sc-regular-local-domain], they and $R$ are
   domains. Thus $(0)\subsetneq(f)\subsetneq\mathfrak p=(f,g)$ is a strict chain of prime
   ideals: $f\ne0$ and $g\notin(f)$ follow from their independent cotangent classes. The height
   of $\mathfrak p$ is at least two. It is at most two by
   [lem-weil-pbc-noetherian-height-quotient-bound] with $J=\mathfrak P=\mathfrak p$ and two
   generators, because $\mathfrak P/J=0$ has height zero in the domain $R/\mathfrak p$. Hence
   $\operatorname{ht}_R(\mathfrak p)=2$. Uses: lem-weil-pbc-nakayama-local-generators,
   lem-weil-pbc-regular-local-generators-regular-sequence, lem-sc-regular-local-domain,
   lem-weil-pbc-noetherian-height-quotient-bound.
11. For each pair $(Y,y)=(X,x),(T,t)$ choose an affine neighbourhood $W=\operatorname{Spec}C$ on
   which the chosen frame is invertible; write the section coefficients as $f,g\in C$ and
   $R=C_{\mathfrak m_y}$. By [lem-weil-pbc-primes-of-localization], the prime $(f,g)R$ contracts
   to a prime $\mathfrak q\subseteq\mathfrak m_y$ of $C$. It is minimal over $(f,g)C$: a smaller
   prime containing this ideal would extend to a smaller prime containing the prime ideal
   $(f,g)R$, which is impossible. The same inclusion-preserving prime correspondence identifies
   all chains below $\mathfrak q$ with chains below $(f,g)R$, so $\operatorname{ht}_C\mathfrak
   q=2$. By [lem-pc-zero-scheme-properties] and
   [lem-weil-pbc-spec-irreducible-components-minimal-primes], $V(\mathfrak q)$ is an irreducible
   component of the intersection of the two zero schemes inside $W$. Uses:
   lem-weil-pbc-primes-of-localization, lem-pc-zero-scheme-properties,
   lem-weil-pbc-spec-irreducible-components-minimal-primes.
12. Take the closure $Z_Y$ of this component in the global intersection $Z(\psi_Y(v_2))\cap
   Z(\psi_Y(v_3))$. The open-subspace correspondence
   [lem-weil-pbc-open-subspace-irreducible-closed-correspondence] preserves strict inclusions
   and shows that this closure is an irreducible component of the global intersection. It
   contains $y$. At its generic point its codimension in $Y$ is two, by
   [lem-sc-scheme-stalk-dimension-generalization-chains] and the height calculation of step 11.
   Since $\psi_Y(v_1)$ is nonzero at $y$, this component is not contained in $Z(\psi_Y(v_1))$.
   Thus hypothesis (i) of [lem-zl-bertini-irreducible-member] holds on both $X$ and $T$, with
   the same $v_1,v_2,v_3$. Uses: lem-weil-pbc-open-subspace-irreducible-closed-correspondence,
   lem-sc-scheme-stalk-dimension-generalization-chains, lem-zl-bertini-irreducible-member.
13. Apply [lem-zl-bertini-irreducible-member] to $(X,L,V,\psi)$ and $(T,L_T,V,\psi_T)$. Finite
   type and geometric irreducibility were established in steps 1--3, condition (ii) in step 5,
   and condition (i) in step 12. The precise meaning of general in that lemma yields nonempty
   Zariski opens $U_X,U_T\subseteq\mathbf A(V)$ such that $H_v$ and $T_v$, respectively, are
   geometrically irreducible on these opens. Their parameter spaces are the same: the pullback
   system has domain $V$, even if a linear map of sections has a kernel. Uses:
   lem-zl-bertini-irreducible-member.
14. Set $U_{\rm irr}=U_X\cap U_T$. In any basis the coordinate ring of $\mathbf A(V)$ is a
   polynomial ring over $k$, a domain by [lem-weil-pbc-polynomial-ring-domain]. Its nilradical
   is the proper prime ideal $(0)$, so [lem-zl-spectrum-irreducible-nilradical-prime] makes its
   spectrum irreducible. Hence the two nonempty opens meet. For every $v\in U_{\rm irr}(k)$ both
   schemes are geometrically irreducible, as required. In particular they are nonempty and
   connected, by specializing geometric irreducibility to $k$ and using that two disjoint
   nonempty clopen pieces would contradict irreducibility. Uses:
   lem-weil-pbc-polynomial-ring-domain, lem-zl-spectrum-irreducible-nilradical-prime,
   def-pc-geometrically-irreducible, def-weil-connected-scheme.
15. The morphism $T_v\to H_v$ is the base change of the finite etale morphism $\pi$, hence is
   finite etale by the base-change functor of [def-weil-pbc-finite-etale-category]. If $H_v$ is
   smooth over $k$, then $T_v\to H_v$ is smooth by
   [lem-weil-pbc-etale-smooth-zero-dimensional-fibres], and $T_v\to\operatorname{Spec}k$ is
   smooth by [lem-trf-smooth-composition]. The connectedness of both schemes was proved in step
   14. This gives every clause of the final assertion. Uses: def-weil-pbc-finite-etale-category,
   lem-weil-pbc-etale-smooth-zero-dimensional-fibres, lem-trf-smooth-composition.
-/
theorem exists_open_geometricallyIrreducible_finiteCover_linearSystem
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsAffine X] [ConnectedSpace X]
    [Smooth (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (d : ℕ) (_hd : 2 ≤ d) (_hdim : X.IsPureDimension d)
    (T : Scheme.{u}) [ConnectedSpace T] (π : T ⟶ X) [IsFinite π] [Etale π]
    (S : Finset X) (_hS : S.Nonempty) (_hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (U₀ : X.Opens) (_hU₀ : (U₀ : Set X) = (S : Set X)ᶜ)
    (L : X.Modules) [L.IsInvertible]
    (V : Type v) [AddCommGroup V] [Module k V]
    (r : ℕ) (b : Module.Basis (Fin r) k V) (ψ : V →+ Γ(L, ⊤))
    (_hlinear : ∀ (c : k) (v : V),
      ψ (c • v) = (X ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c) • ψ v)
    (_hvan : ∀ (v : V) (x : X), x ∈ S →
      x ∈ (Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.support)
    (hgen : Epi (((Scheme.Modules.tensorPullback U₀.ι).obj L).freeHomEquiv.symm
      (fun i : ULift.{u} (Fin r) ↦ SheafOfModules.unitHomEquiv _
        (Scheme.Modules.homOfGlobalSection _
          (Scheme.Modules.tensorSectionsUnit U₀.ι L (ψ (b i.down)))))))
    [IsImmersion (@ProjectiveSpace.homOfGeneratingSections
      (ULift.{u} (Fin r)) inferInstance U₀.toScheme (Spec (.of k))
      (U₀.ι ≫ (X ↘ Spec (.of k))) ((Scheme.Modules.tensorPullback U₀.ι).obj L)
      (Scheme.Modules.IsInvertible.of_iso
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction U₀.ι)).leftAdjointUniq
          (Scheme.Modules.pullbackPushforwardAdjunction U₀.ι)).app L).symm)
      (fun i : ULift.{u} (Fin r) ↦ SheafOfModules.unitHomEquiv _
        (Scheme.Modules.homOfGlobalSection _
          (Scheme.Modules.tensorSectionsUnit U₀.ι L (ψ (b i.down))))) hgen)] :
    ∃ U : (Spec (.of (MvPolynomial (Fin r) k))).Opens,
      (U : Set (Spec (.of (MvPolynomial (Fin r) k)))).Nonempty ∧
      ∀ v : V,
        Set.range (Spec.map (CommRingCat.ofHom
          (MvPolynomial.eval₂Hom (RingHom.id k) (fun i ↦ b.repr v i)))) ⊆ (U : Set _) →
        GeometricallyIrreducible
          ((Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.subschemeι ≫
            (X ↘ Spec (.of k))) ∧
        GeometricallyIrreducible
          (pullback.snd π (Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.subschemeι ≫
            (Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.subschemeι ≫
              (X ↘ Spec (.of k))) ∧
        (Smooth ((Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.subschemeι ≫
            (X ↘ Spec (.of k))) →
          Smooth
            (pullback.snd π (Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.subschemeι ≫
              (Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.subschemeι ≫
                (X ↘ Spec (.of k))) ∧
          IsFinite (pullback.snd π
            (Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.subschemeι) ∧
          Etale (pullback.snd π
            (Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.subschemeι) ∧
          ConnectedSpace (Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.subscheme ∧
          ConnectedSpace
            (pullback π (Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.subschemeι :
              Scheme.{u})) := by
  sorry

end AlgebraicGeometry
