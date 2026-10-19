/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import WeilConjectures.RingTheory.CompletionMapForLocalHom
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Topology.JacobsonSpace

import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.MvPowerSeriesQuotientKernel
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import Mathlib.RingTheory.AdicCompletion.LocalRing
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.RingTheory.CompleteLocalQuotient
import WeilConjectures.RingTheory.FiniteAfterCompletion
import Mathlib.RingTheory.FiniteType
import WeilConjectures.RingTheory.FlatCompletion
import WeilConjectures.RingTheory.FlatModInjective
import WeilConjectures.RingTheory.LocalCompletionQuotient
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.LocalRing.Module
import WeilConjectures.RingTheory.PowerSeriesAdicEvaluation
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients
import WeilConjectures.RingTheory.PowerSeriesCompleteOverCompleteBase
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Formal local structure of a nodal family

Source: Stacks Project, Tag 0CBX, lemma-formal-local-structure-nodal-family
and Tag 0CBY, the completed-model formulation.
(blueprint: lem-trf-formal-local-structure-nodal-family).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry

/-- The maximal-ideal completion of a scheme stalk, as in Stacks Tags 0CBX and 0CBY.
(blueprint: lem-trf-formal-local-structure-nodal-family) -/
abbrev formalNodalCompletedStalk (X : Scheme.{u}) (x : X) :=
  AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)

/-- The coefficient map into a stalk of an affine-base scheme: constants followed by
 the stalk map. Source: Stacks Tag 0CBX, the fibre as a scheme over its residue field.
(blueprint: lem-trf-formal-local-structure-nodal-family) -/
noncomputable def formalNodalCoefficientMap (R : Type u) [CommRing R]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R)) (x : X) :
    R →+* X.presheaf.stalk x :=
  (g.stalkMap x).hom.comp (StructureSheaf.toStalk R (g x)).hom

/-- The canonical residue-field algebra structure on the completed fibre stalk.
Source: Stacks Tag 0CBX and Tag 0CBW, the split-node hypothesis.
(blueprint: lem-trf-formal-local-structure-nodal-family) -/
@[instance_reducible]
noncomputable def formalNodalFiberCompletionAlgebra {X Y : Scheme.{u}}
    (f : X ⟶ Y) (t : X) :
    Algebra (Y.residueField (f t))
      (formalNodalCompletedStalk (f.fiber (f t)) (f.asFiber t)) :=
  letI := (formalNodalCoefficientMap (Y.residueField (f t))
    (f.fiberToSpecResidueField (f t)) (f.asFiber t)).toAlgebra
  inferInstance

/-- The canonical completed stalk algebra structure. The chosen map is uniquely fixed by
all its finite quotient coordinates in `RingHom.exists_adicCompletion_map_of_local`;
thus this is the completed stalk map, with no arbitrary choice of scalar action.
Source: Stacks Tag 0CBX, the local map and its completion; Tag 07ED.
(blueprint: lem-trf-formal-local-structure-nodal-family) -/
@[instance_reducible]
noncomputable def formalNodalCompletedStalkAlgebra {X Y : Scheme.{u}}
    (f : X ⟶ Y) (t : X) :
    Algebra (formalNodalCompletedStalk Y (f t)) (formalNodalCompletedStalk X t) :=
  (Classical.choose (RingHom.exists_adicCompletion_map_of_local (f.stalkMap t).hom)).toAlgebra

/-- The two-variable completed hypersurface algebra of Stacks Tag 0CBX.
(blueprint: lem-trf-formal-local-structure-nodal-family) -/
abbrev formalNodalPowerSeriesQuotient (R : Type u) [CommRing R] (h : R) :=
  MvPowerSeries (Fin 2) R ⧸ Ideal.span
    ({MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) - MvPowerSeries.C h} :
      Set (MvPowerSeries (Fin 2) R))

/-- The coordinate algebra of the polynomial nodal model of Stacks Tag 0CBY.
(blueprint: lem-trf-formal-local-structure-nodal-family) -/
abbrev formalNodalModelRing (R : Type u) [CommRing R] (h : R) :=
  MvPolynomial (Fin 2) R ⧸ Ideal.span
    ({MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) - MvPolynomial.C h} :
      Set (MvPolynomial (Fin 2) R))

/-- The affine polynomial model `Spec(R[u,v]/(uv-h))` of Stacks Tag 0CBY.
(blueprint: lem-trf-formal-local-structure-nodal-family) -/
noncomputable abbrev formalNodalModel (R : Type u) [CommRing R] (h : R) : Scheme.{u} :=
  Spec (CommRingCat.of (formalNodalModelRing R h))

/-- The ideal `(m_A Â,u,v)` in the polynomial model's quotient coordinate ring.
Source: Stacks Tag 0CBY, first proof, third paragraph, the point `y_sigma`.
(blueprint: lem-trf-formal-local-structure-nodal-family) -/
noncomputable def formalNodalOriginIdeal (A : Type u) [CommRing A] [IsLocalRing A]
    (h : AdicCompletion (IsLocalRing.maximalIdeal A) A) :
    Ideal (formalNodalModelRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) h) :=
  Ideal.map (Ideal.Quotient.mk _) ((Ideal.map MvPolynomial.C
    (Ideal.map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))
      (IsLocalRing.maximalIdeal A))) ⊔
    Ideal.span ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} :
      Set (MvPolynomial (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A))))

/-- The canonical coefficient algebra structure on the completed stalk of the model.
Source: Stacks Tag 0CBY, first proof, third paragraph.
(blueprint: lem-trf-formal-local-structure-nodal-family) -/
@[instance_reducible]
noncomputable def formalNodalModelCompletionAlgebra (R : Type u) [CommRing R] (h : R)
    (o : formalNodalModel R h) :
    Algebra R (formalNodalCompletedStalk (formalNodalModel R h) o) :=
  letI : Algebra R ((formalNodalModel R h).presheaf.stalk o) :=
    ((StructureSheaf.toStalk (formalNodalModelRing R h) o).hom.comp
    (algebraMap R (formalNodalModelRing R h))).toAlgebra
  inferInstance

/-- A flat family with a split node has the standard completed local equation.
Source: Stacks Project, Tag 0CBX and Tag 0CBY, first proof, third paragraph.
(blueprint: lem-trf-formal-local-structure-nodal-family)

Proof (the fourteen DAG steps; `A₀` and `B₀` are the base and total-space local rings):

1. Put $A_0=\mathcal O_{S,s}$ and $B_0=\mathcal O_{T,t}$. The local map $A_0\to B_0$ is flat by
   the definition of flatness at $t$. To check Noetherianity of $B_0$ without assuming $S$ locally
   Noetherian, choose affine neighbourhoods $\operatorname{Spec}R_0$ of $s$ and
   $\operatorname{Spec}D$ of $t$ with $D$ finite type over $R_0$. The affine-stalk localization
   identifications give $A_0=(R_0)_{\mathfrak p}$ and $B_0=D_{\mathfrak q}$, with $\mathfrak q\cap
   R_0=\mathfrak p$. Inverting $R_0\setminus\mathfrak p$ first does not change $D_{\mathfrak q}$:
   each such denominator is already a unit there. Thus $B_0$ is a localization of the finite type
   $A_0$-algebra $D\otimes_{R_0}A_0$. This algebra, and then its localization $B_0$, are
   Noetherian by the two cited permanence statements.
   Uses:
   * `def-weil-flat-morphism`
   * `def-weil-finite-type-morphism`
   * `lem-weil-pbc-affine-open-stalk-localization`
   * `lem-weil-pbc-finite-type-algebra-noetherian`
   * `lem-weil-pbc-localization-noetherian`

2. Set $A=\widehat {A_0}$, $B=\widehat {B_0}$, $\mathfrak m=\mathfrak m_{A_0}A$, and $\mathfrak
   n=\mathfrak m_{B_0}B$. The completion-local-ring statement identifies these as the maximal
   ideals and identifies both residue fields with $k=\kappa(s)=\kappa(t)$. The
   completion-Noetherian statement makes $A,B$ Noetherian. Their maximal ideals are finitely
   generated, and the adic-completion-mod-ideal statement makes them complete for these maximal
   ideals. The flat-completion statement applies to the flat local map of Noetherian local rings
   $A_0\to B_0$, so $A\to B$ is flat.
   Uses:
   * `lem-weil-pbc-local-completion-local-ring`
   * `lem-weil-pbc-adic-completion-noetherian`
   * `lem-weil-pbc-adic-completion-mod-ideal`
   * `lem-weil-pbc-flat-completion`

3. The fibre-stalk quotient statement gives $B_0/\mathfrak m_{A_0}B_0\cong\mathcal O_{T_s,t}$.
   Apply the local-completion-quotient statement to this surjection, whose source $B_0$ is
   Noetherian local. Its completed kernel is $\mathfrak m_{A_0}B=\mathfrak mB$, and the quotient
   has the induced local maximal ideal. Hence the assumed split-fibre isomorphism supplies a
   $k$-algebra isomorphism $B/\mathfrak mB\cong k[[x,y]]/(xy)$. Denote by $\bar u,\bar v$ the
   classes of $x,y$ in $B/\mathfrak mB$.
   Uses:
   * `lem-sbc-scheme-fibre-stalk-quotient`
   * `lem-weil-pbc-local-completion-quotient`

4. Choose lifts $u_1,v_1\in B$ of $\bar u,\bar v$ and put $h_1=0$. They lie in $\mathfrak n$, and
   $u_1v_1-h_1\in\mathfrak mB$. More generally, every $b\in B$ can be written
   $b=a+u_1p+v_1q+\epsilon$ with $a\in A$, $p,q\in B$, $\epsilon\in\mathfrak mB$: reduce $b$ in
   $k[[x,y]]/(xy)$, subtract its constant coefficient (lifted from $k$ to $A$), and factor the
   remaining series into $x$ times a series plus $y$ times a series. Lift these two series classes
   to $B$. The same decomposition works with any $u,v$ lifting $\bar u,\bar v$.

5. For the induction step suppose $n\ge1$, $h\in\mathfrak m$, and $uv-h=\delta\in\mathfrak m^nB$,
   with $u,v$ lifting $\bar u,\bar v$. Write a finite sum $\delta=\sum_i f_ib_i$, $f_i\in\mathfrak
   m^n$, and use the preceding decomposition to write $b_i=a_i+up_i+vq_i+\epsilon_i$ with $a_i\in
   A$, $\epsilon_i\in\mathfrak mB$. Define $u'=u-\sum_i f_iq_i$, $v'=v-\sum_i f_ip_i$, and
   $h'=h+\sum_i f_ia_i$. Direct multiplication gives $$u'v'-h'=\sum_i f_i\epsilon_i+(\sum_i
   f_iq_i)(\sum_j f_jp_j)\in\mathfrak m^{n+1}B,$$ since $2n\ge n+1$. Also $u'-u,v'-v\in\mathfrak
   m^nB$, $h'-h\in\mathfrak m^n$, and $h'\in\mathfrak m$. This proves the inductive improvement
   and preserves the chosen reductions.

6. Starting from $(u_1,v_1,h_1)$, repeat the preceding improvement to obtain $u_n,v_n\in B$,
   $h_n\in\mathfrak m$ with consecutive differences in $\mathfrak m^nB,\mathfrak m^nB,\mathfrak
   m^n$ respectively and $u_nv_n-h_n\in\mathfrak m^nB$. Because $\mathfrak mB\subseteq\mathfrak
   n$, their reductions modulo any fixed power of $\mathfrak n$ (and of $\mathfrak m$ for $h_n$)
   eventually stabilize. Completeness, in the inverse-limit definition, supplies
   $u_\infty,v_\infty\in B$, $h\in A$ with those stabilized coordinates. The identities
   $u_nv_n-h_n\in\mathfrak n^n$ imply $u_\infty v_\infty=h$ by separatedness. The classes
   $u_\infty,v_\infty$ still lift $\bar u,\bar v$: the ideal $\mathfrak mB$ is closed for the
   $\mathfrak n$-adic topology, since $B/\mathfrak mB$ is a complete local quotient and hence
   separated for its induced maximal ideal. Likewise $\mathfrak m$ is closed in $A$, so
   $h\in\mathfrak m$. Only maximal-ideal completeness of $B$ is needed; no assertion of $\mathfrak
   mB$-adic completeness is made here.
   Uses:
   * `def-weil-pbc-adically-complete-ring`
   * `lem-weil-pbc-complete-local-quotient`

7. Let $R=A[[x,y]]$ and $\mathfrak a=\mathfrak mR+(x,y)$. The power-series Noetherian and
   local-ring statements show that $R$ is Noetherian local with maximal ideal $\mathfrak a$: a
   series with zero constant term is $xF+yG$, so the constant-term description of that maximal
   ideal is exactly this sum. The complete-over-complete-base statement makes $R$ $\mathfrak
   a$-adically complete. Put $C=R/(xy-h)$. Since $h\in\mathfrak m$, the equation belongs to
   $\mathfrak a$; the complete-local-quotient statement shows that $C$ is Noetherian local and
   complete, with maximal ideal the image $\mathfrak a_C$ of $\mathfrak a$.
   Uses:
   * `lem-weil-pbc-power-series-noetherian`
   * `lem-weil-pbc-power-series-local-ring`
   * `lem-weil-pbc-power-series-complete-over-complete-base`
   * `lem-weil-pbc-complete-local-quotient`

8. Apply the adic-evaluation statement with coefficient map $A\to B$, ideal $\mathfrak n$, and the
   elements $u_\infty,v_\infty\in\mathfrak n$. It supplies an $A$-algebra homomorphism $R\to B$
   sending $x,y$ to these elements. The identity $u_\infty v_\infty=h$ makes it factor through an
   $A$-algebra homomorphism $\phi:C\to B$. It is local: each generator of $\mathfrak a_C$, namely
   an element of $\mathfrak m$ or one of $x,y$, maps into $\mathfrak n$.
   Uses:
   * `lem-weil-pbc-power-series-adic-evaluation`

9. The coefficient-reduction kernel statement applies to the finitely generated ideal $\mathfrak
   m$ of $A$ and gives kernel $\mathfrak mR$ for $R\to k[[x,y]]$. This map is surjective: choose
   in $A$ a lift of each coefficient of a given series. Since $h\in\mathfrak m$, it identifies
   $C/\mathfrak mC$ with $k[[x,y]]/(xy)$. The reduction of $\phi$ sends $x,y$ to $\bar u,\bar v$
   and agrees with the chosen isomorphism of step 3. Indeed, modulo the $N$-th power of the
   maximal ideal of $B/\mathfrak mB$ both maps send a series to the image of its truncation below
   total degree $N$: for the reduction of $\phi$ by the explicit formula of the adic-evaluation
   statement, and for the chosen isomorphism because it is a $k$-algebra isomorphism of local
   rings, hence maps $(x,y)^N$ into the $N$-th power of the maximal ideal. Both send $x,y$ to
   $\bar u,\bar v$ and constants to constants, so the two maps agree at every finite truncation
   and then agree by separatedness of the complete local quotient $B/\mathfrak mB$. Thus
   $\bar\phi:C/\mathfrak mC\to B/\mathfrak mB$ is an isomorphism.
   Uses:
   * `lem-sbc-mv-power-series-quotient-kernel`
   * `lem-weil-pbc-complete-local-quotient`

10. Apply the flat-mod-injective statement with its $R=A$, $S=C$, $N=C$, $M=B$, and $u=\phi$. The
   map $A\to C$ is local, $C$ is Noetherian, $C$ is a finite module over itself, and $B$ is flat
   over $A$ by step 2. Step 9 supplies the required injectivity modulo $\mathfrak m$. The
   statement therefore implies that $\phi$ is injective. In particular this use needs no separate
   flatness assertion for the hypersurface $C$.
   Uses:
   * `lem-weil-pbc-flat-mod-injective`

11. In the closed fibre $B/\mathfrak mB\cong k[[x,y]]/(xy)$ the maximal ideal is $(\bar u,\bar
   v)$, by the local-ring and quotient-local-structure statements. Taking its inverse image in $B$
   gives $\mathfrak n=\mathfrak mB+(u_\infty,v_\infty)B=\mathfrak a_CB$. Consequently $B/\mathfrak
   a_CB=k$, a one-dimensional vector space over $C/\mathfrak a_C=k$. Apply the
   finite-after-completion statement to the local map $C\to B$. Both maximal ideals are finitely
   generated since these rings are Noetherian. Because both rings are already complete for their
   maximal ideals, its finite completed-module conclusion identifies $B$ as a finite $C$-module
   via $\phi$; the completed action agrees with $\phi$ on elements by its coordinatewise
   definition.
   Uses:
   * `lem-weil-pbc-power-series-local-ring`
   * `lem-weil-pbc-quotient-local-structure`
   * `lem-weil-pbc-finite-after-completion`

12. The element $1\in B$ generates $B/\mathfrak a_CB=k$. Nakayama's local-generators statement for
   the finite $C$-module $B$ now implies that $1$ generates $B$ over $C$. Thus $\phi$ is
   surjective. Together with step 10 this gives the required $A$-algebra isomorphism $B\cong
   A[[x,y]]/(xy-h)$. This implements the source's completeness/surjectivity argument through the
   existing finite-after-completion and Nakayama interfaces.
   Uses:
   * `lem-weil-pbc-nakayama-local-generators`

13. For the equivalent polynomial-model formulation put $P=A[x,y]$, $\mathfrak q=\mathfrak
   mP+(x,y)$ and $D=P_{\mathfrak q}$. Here $P/\mathfrak q=k$, so $\mathfrak q$ is maximal. The map
   $P\to R=A[[x,y]]$ identifies $P/\mathfrak q^r$ with $R/\mathfrak a^r$ for every $r\ge1$:
   truncate above total degree $r-1$, and use the combined-ideal coefficient criterion to check
   that the kernel on polynomials consists exactly of those whose coefficient of $x^iy^j$ lies in
   $\mathfrak m^{r-i-j}$ whenever $i+j<r$. Such polynomials belong to $\mathfrak q^r$ term by
   term. Every denominator outside $\mathfrak q$ is already a unit in this quotient: it has an
   invertible constant coefficient in $A$, and its remaining part is nilpotent modulo $\mathfrak
   q^r$, so a finite geometric sum gives its inverse. Therefore $D/(\mathfrak qD)^r\cong
   R/\mathfrak a^r$, compatibly with the transition maps, constants and variables. Taking
   compatible sequences and using the completeness of $R$ gives $\widehat D\cong R$ as
   $A$-algebras.
   Uses:
   * `lem-weil-pbc-power-series-combined-ideal-coefficients`
   * `lem-weil-pbc-power-series-complete-over-complete-base`
   * `def-weil-pbc-localization-at-prime`
   * `def-weil-pbc-adic-completion`

14. Let $M_h=\operatorname{Spec}(P/(xy-h))$ and let $o$ be its point with ideal $\mathfrak
   q/(xy-h)$. Its residue field is $k$ since evaluation $x=y=0$ gives $P/(xy-h,\mathfrak
   m,x,y)=k$. The affine-stalk localization statement identifies $\mathcal O_{M_h,o}$ with
   $(P/(xy-h))_{\mathfrak q/(xy-h)}$. The fraction map identifies this ring with $D/(xy-h)D$: the
   denominators on both sides are exactly the images of $P\setminus\mathfrak q$, and $a/s$ is in
   the kernel precisely when some denominator outside $\mathfrak q$ times $a$ belongs to $(xy-h)$.
   The ring $D$ is Noetherian by finite-type and localization permanence over the Noetherian ring
   $A$. Apply local-completion-quotient to $D\to D/(xy-h)D$, and use the constant-and-variable
   preserving identification of step 13. It gives $\widehat{\mathcal O}_{M_h,o}\cong\widehat
   D/(xy-h)\widehat D\cong A[[x,y]]/(xy-h)$. Composing with step 12 proves the equivalent
   formulation, with its specified residue field.
   Uses:
   * `lem-weil-pbc-affine-open-stalk-localization`
   * `lem-weil-pbc-finite-type-algebra-noetherian`
   * `lem-weil-pbc-localization-noetherian`
   * `lem-weil-pbc-local-completion-quotient`
-/
theorem formalLocalStructureNodalFamily (X Y : Scheme.{u}) (f : X ⟶ Y) (t : X)
    [IsNoetherianRing (Y.presheaf.stalk (f t))] [LocallyOfFiniteType f]
    (hflat : (f.stalkMap t).hom.Flat)
    (ht : f.asFiber t ∈ closedPoints (f.fiber (f t)))
    (hκ : Function.Bijective (f.residueFieldMap t).hom)
    (hspecial : Nonempty (@AlgEquiv (Y.residueField (f t))
      (formalNodalCompletedStalk (f.fiber (f t)) (f.asFiber t))
      (formalNodalPowerSeriesQuotient (Y.residueField (f t)) 0) _ _ _
      (formalNodalFiberCompletionAlgebra f t) inferInstance)) :
    ∃ h : formalNodalCompletedStalk Y (f t),
      h ∈ Ideal.map (algebraMap (Y.presheaf.stalk (f t))
        (formalNodalCompletedStalk Y (f t))) (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f t))) ∧
      Nonempty (@AlgEquiv (formalNodalCompletedStalk Y (f t))
        (formalNodalCompletedStalk X t)
        (formalNodalPowerSeriesQuotient (formalNodalCompletedStalk Y (f t)) h) _ _ _
        (formalNodalCompletedStalkAlgebra f t) inferInstance) ∧
      ∃ o : formalNodalModel (formalNodalCompletedStalk Y (f t)) h,
        o.asIdeal = formalNodalOriginIdeal (Y.presheaf.stalk (f t)) h ∧
        Nonempty (@AlgEquiv (formalNodalCompletedStalk Y (f t))
          (formalNodalCompletedStalk X t)
          (formalNodalCompletedStalk
            (formalNodalModel (formalNodalCompletedStalk Y (f t)) h) o) _ _ _
          (formalNodalCompletedStalkAlgebra f t)
          (formalNodalModelCompletionAlgebra (formalNodalCompletedStalk Y (f t)) h o)) ∧
        Nonempty ((formalNodalModel (formalNodalCompletedStalk Y (f t)) h).residueField o ≃+*
          (Y.presheaf.stalk (f t)) ⧸ IsLocalRing.maximalIdeal (Y.presheaf.stalk (f t))) := by
  sorry

end AlgebraicGeometry
