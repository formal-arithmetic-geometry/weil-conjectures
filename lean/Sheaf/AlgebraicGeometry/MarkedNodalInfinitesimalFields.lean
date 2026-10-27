/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.CurveVectorFieldsFixingPoints
public import Sheaf.AlgebraicGeometry.MarkedInfinitesimalAutomorphisms
public import Sheaf.AlgebraicGeometry.StablePointedCurve
public import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.DualNumber
import WeilConjectures.AlgebraicGeometry.Curve
import Sheaf.AlgebraicGeometry.RationalSectionDivisor
import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.Curve.UniformizerDifferentialBasis
import Sheaf.AlgebraicGeometry.ClosedPointField
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import Sheaf.AlgebraicGeometry.Curve.ProperProjective
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import Sheaf.TraceFormula.CurveNormalizationCompletion
import Sheaf.AlgebraicGeometry.NormalizationSingularSkyscraper
import Sheaf.AlgebraicGeometry.OrdinaryPointDeltaBranches
import Sheaf.TraceFormula.ReducedCurveNormalizationGenus
import WeilConjectures.RingTheory.CompletionDimension
import WeilConjectures.RingTheory.Derivation.CompletionAndLocalization
import WeilConjectures.RingTheory.PowerSeriesNormalDomain

import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Infinitesimal marked automorphisms and normalized vector fields

Source: Stacks Project, curves.tex, Tags 0E67 and 0E68, and more-morphisms.tex, Tag 02H5
(blueprint: lem-sfb-marked-nodal-infinitesimal-fields).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

namespace AlgebraicGeometry

/-- The branch and marking preimages on a canonical normalized component. A self-node
contributes its two distinct inverse images. Markings may be empty.
Source: Stacks Project, curves.tex, Tag 0E68 and section-vector-fields
(blueprint: lem-sfb-marked-nodal-infinitesimal-fields). -/
def markedNodalSpecialPoints {Ω : Type u} [Field Ω] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of Ω)) [LocallyOfFinitePresentation f] {n : ℕ}
    (p : Fin n → (Spec (.of Ω) ⟶ C)) (Z : irreducibleComponents C) :
    Set (C.reducedNormalizationComponent Z).normalization :=
  C.normalizedComponentMap Z ⁻¹'
    ({x | x ∉ f.smoothLocus} ∪ ⋃ i : Fin n, Set.range (p i))

/-- Characterization of the canonical identification: take the epsilon coefficient on `C`,
then extend the resulting derivation to each normalized component. The first equation is
written on every common subopen to avoid any choice of a proof that an identity-reducing
map acts identically on opens. The second equation says precisely that extension commutes
with the comorphism of normalization, and uniquely determines it in the rational functions.
Source: Stacks Project, more-morphisms.tex, Tag 02H5 and curves.tex, Tag 0E68
(blueprint: lem-sfb-marked-nodal-infinitesimal-fields). -/
def IsMarkedInfinitesimalNormalizationIdentification
    {Ω : Type u} [Field Ω] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of Ω)) [LocallyOfFinitePresentation f] {n : ℕ}
    (p : Fin n → (Spec (.of Ω) ⟶ C))
    (e : Additive (markedInfinitesimalAutomorphisms f p) ≃+
      ⨁ (Z : irreducibleComponents C),
        curveVectorFieldsFixingPoints (C.normalizedComponentMap Z ≫ f)
          (markedNodalSpecialPoints f p Z)) : Prop :=
  ∀ α : Additive (markedInfinitesimalAutomorphisms f p),
    ∃ D : f.relativeDifferentials ⟶ Scheme.Modules.unit C,
      (∀ (U V : C.Opens) (hVU : V ≤ U)
        (hVα : V ≤ (Additive.toMul α).val.hom.left ⁻¹ᵁ U) (a : Γ(C, U)),
        ((Additive.toMul α).val.hom.left.appLE U V hVα (TrivSqZeroExt.inl a)).snd =
          curveVectorFieldApply f D V (C.presheaf.map (homOfLE hVU).op a)) ∧
      ∀ (Z : irreducibleComponents C) (U : C.Opens) (a : Γ(C, U)),
        curveVectorFieldApply (C.normalizedComponentMap Z ≫ f) (e α Z).val
          (C.normalizedComponentMap Z ⁻¹ᵁ U) ((C.normalizedComponentMap Z).app U a) =
        (C.normalizedComponentMap Z).app U (curveVectorFieldApply f D U a)

/-- The canonical additive identification for a proper marked nodal curve.

Source: Stacks Project, curves.tex, Tags 0E67 and 0E68, and more-morphisms.tex, Tag 02H5
(blueprint: lem-sfb-marked-nodal-infinitesimal-fields).

Proof:
1. Put $k=\Omega$ and $R=k[\epsilon]/(\epsilon^2)$. On each open of $C$ its constant thickening
has ring $\mathcal O_C\oplus\epsilon\mathcal O_C$. Every $R$-algebra automorphism reducing to the
identity has the unique form $a+\epsilon b\mapsto a+\epsilon(b+D(a))$. Multiplicativity is
precisely $D(ab)=aD(b)+bD(a)$, and fixing $R$ says that $D$ is $k$-linear. Conversely this formula
for any sheaf derivation is multiplicative, compatible with restrictions, and has inverse given by
$-D$. It gives local ring maps since reduction is the identity and nilpotents do not change the
underlying space. Composing the formulas adds $D$'s. At a marked point $p$, evaluation of this
formula along the constant section is unchanged exactly when $D(a)(p)=0$ for every local function
$a$. Since $D$ kills $k$, this is equivalent to $D(\mathcal I_p)\subseteq\mathcal I_p$. Thus the
group in the statement is additively the space of derivations on $C$ preserving the marked ideals.
Uses: def-sc-dual-numbers.
2. If $C$ is empty, both sides are trivial; assume $C$ nonempty. The scheme $C$ is Noetherian by
[lem-weil-pbc-finite-type-over-noetherian]: proper implies finite type and a field is Noetherian;
so its local rings are Noetherian. The normalization is finite with finitely many smooth proper
connected components by [lem-trf-reduced-curve-normalization-genus]; those components are
projective by [lem-sc-proper-dim-one-projective]. By [lem-trf-normalization-singular-skyscraper],
the set $S$ of non-smooth points of $C$ is a finite set of closed points, which by the hypothesis
is the set of nodes, and there is an exact sequence $0\to\mathcal O_C\to\nu_*\mathcal
O_{\widetilde C}\to Q\to0$ with $Q$ supported on $S$. So $\mathcal O_U\cong(\nu_*\mathcal
O_{\widetilde C})|_U$ on $U=C\setminus S$. Since $\nu$ is finite, hence affine
[def-weil-finite-integral-morphism], for every affine open $V\subseteq U$ the inverse image
$\nu^{-1}(V)$ is the spectrum of $(\nu_*\mathcal O_{\widetilde C})(V)=\mathcal O_C(V)$; thus
$\nu^{-1}(U)\to U$ is an isomorphism. At a node $x$, put $A=\mathcal O_{C,x}$ and let $B$ be its
integral closure in $Q(A)$, the localization at the non-zero-divisors; by the same node
[lem-trf-normalization-singular-skyscraper], $B$ is the stalk $(\nu_*\mathcal O_{\widetilde
C})_x$, a semilocal ring, not a product of the uncompleted branch stalks. By
[lem-trf-curve-normalization-completion], $B$ is finite over $A$ and $B\otimes_A\widehat A$ is the
normalization of $\widehat A$. The hypothesis applies: $A$ is reduced and essentially of finite
type over $k$; also $\dim A=\dim\widehat A=1$ by [lem-weil-pbc-completion-dimension]. Indeed every
prime of $k[[u,v]]/(uv)$ contains $u$ or $v$, and a one-variable power-series ring has only the
primes $(0),(t)$ since each nonzero series is $t^n$ times a unit. The node has exactly two
normalization points by [lem-trf-ordinary-point-delta-branches], which also gives normalization
defect one. As $S$ is finite and $\nu$ has finite fibres over it, each $E_a$ is finite. Uses:
lem-trf-reduced-curve-normalization-genus, lem-trf-normalization-singular-skyscraper,
lem-trf-curve-normalization-completion, lem-trf-ordinary-point-delta-branches,
lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-completion-dimension,
lem-sc-proper-dim-one-projective, def-weil-finite-integral-morphism.
3. Write $\widehat A=k[[u,v]]/(uv)$. The map $h\mapsto(h(u,0),h(0,v))$ identifies this ring with
the pairs in $P=k[[u]]\times k[[v]]$ having equal constant terms: every such pair is uniquely
$c+uf(u)+vg(v)$. Its total fraction ring is $k((u))\times k((v))$: inverting the non-zero-divisor
$u+v$ produces the idempotents $(1,0)=u/(u+v)$ and $(0,1)$ and then the two Laurent-series fields.
Moreover $P=\widehat A[(1,0)]$, an integral extension since the adjoined element is idempotent.
Both factors of $P$ are integrally closed by [lem-weil-pbc-power-series-normal-domain] applied to
the field $k$; integral closure in the product of fraction fields is checked coordinatewise. Thus
$P$ is the normalization of $\widehat A$, so step 2 identifies $B\otimes_A\widehat A=P$. By
[lem-weil-pbc-completion-finite-module-tensor], this is also the $\mathfrak m_AB$-adic completion
of $B$. Uses: lem-weil-pbc-power-series-normal-domain,
lem-weil-pbc-completion-finite-module-tensor.
4. Here is the membership test used below. The map $A\to\widehat A$ is faithfully flat by
[lem-weil-pbc-local-completion-faithfully-flat]. By
[lem-weil-pbc-faithfully-flat-universally-injective], the map $N\to N\otimes_A\widehat A$ is
injective for every $A$-module $N$. Taking $N=Q(A)/B$ shows that an element of $Q(A)$ whose image
belongs to $B\otimes_A\widehat A=P$ already belongs to $B$. Taking $N=B/A$ shows that an element
of $B$ whose image in $P$ belongs to $\widehat A$ already belongs to $A$. These assertions follow
by taking the class modulo the indicated submodule and using injectivity; tensoring the quotient
gives the corresponding quotient of the tensor product. Flatness ensures that the inclusions into
$Q(A)\otimes_A\widehat A$ remain inclusions. Uses: lem-weil-pbc-local-completion-faithfully-flat,
lem-weil-pbc-faithfully-flat-universally-injective.
5. For a derivation $D:A\to A$, [lem-weil-pbc-derivation-extends] gives its continuous extension
$\widehat D$ to $\widehat A$ and its unique extension to $Q(A)$, with $D(a/s)=D(a)/s-aD(s)/s^2$.
In the completed node, $0=\widehat D(uv)=v\widehat D(u)+u\widehat D(v)$. Writing the two branch
coordinates shows $\widehat D(u)\in(u)$ and $\widehat D(v)\in(v)$: the $v$-coordinate of the first
and the $u$-coordinate of the second must vanish, including their constant terms. Consequently
$\widehat D(u)=uf(u)$ and $\widehat D(v)=vg(v)$. Its extension to $P$ is the pair of continuous
derivations $uf(u)\partial_u$ and $vg(v)\partial_v$. The formulas agree with $\widehat D$ first on
polynomials and then on power series by continuity. Both derivations preserve the respective
maximal ideals. Localizing these formulas agrees with the extension of $D$ on $Q(A)$ by the
displayed quotient rule. For $b\in B\subset Q(A)$, its derivative therefore has image in $P$. Step
4 implies $D(b)\in B$. Thus $D$ extends uniquely to $B$, and the residue at either branch of every
$D(b)$ is zero, so the extended derivation fixes both branch points. Uses:
lem-weil-pbc-derivation-extends.
6. Conversely let $D'$ be a derivation on the normalization fixing the two branch points above
$x$. It induces a derivation of $B$. Extend it to the $\mathfrak m_AB$-adic completion $P$ by
[lem-weil-pbc-derivation-extends]. The two residue evaluations are continuous (their kernels
contain $\mathfrak m_AB$), so their composites with the extended derivation are zero, as they
already are on the dense subring $B$: for $b\in B$, subtract its residue in $k$ and use ideal
preservation and $k$-linearity. A derivation kills an idempotent $e$, since $D'(e)=2eD'(e)$
implies, after multiplying by $e$ and subtracting, $eD'(e)=0$ and then $D'(e)=0$, in every
characteristic. Hence the derivation on $P$ acts separately on the two factors and has zero
residue in each. It therefore takes every equal-constant pair to a pair with both constants zero,
and preserves $\widehat A$. For $a\in A$, $D'(a)\in B$ has image in $\widehat A$, so step 4 gives
$D'(a)\in A$. This descends $D'$ to a derivation of $A$. The two procedures are inverse by
uniqueness of extension to fractions. Uses: lem-weil-pbc-derivation-extends.
7. These constructions glue to sheaf derivations. Indeed the extension on every localization is
uniquely given by the quotient rule of [lem-weil-pbc-derivation-extends]; thus local constructions
restrict to the same maps in the rational-function rings. Regularity was proved at nodes in steps
5--6, and elsewhere normalization is an isomorphism by step 2. This also proves uniqueness and
additivity. At every smooth marked point that isomorphism identifies its ideal with the ideal of
its unique preimage, so the fixed-marked-ideal conditions of step 1 become precisely the remaining
conditions in $E_a$. A sheaf map on a disjoint union is a tuple of sheaf maps on its
open-and-closed components; there are finitely many components by step 2, so their product of
additive groups is their direct sum. We obtain the stated canonical additive identification. Uses:
lem-weil-pbc-derivation-extends.
-/
theorem marked_nodal_infinitesimal_fields
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of Ω)) [IsProper f] [ConnectedSpace C] [IsReduced C]
    (hpure : C.IsPureDimension 1)
    (hnodal : ∀ x : C, x ∉ f.smoothLocus →
      Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
        (C.presheaf.stalk x) ≃+*
        (MvPowerSeries (Fin 2) Ω ⧸
          Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
            (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Ω)})))
    {n : ℕ} (p : Fin n → (Spec (.of Ω) ⟶ C))
    (hp : ∀ i : Fin n, p i ≫ f = 𝟙 (Spec (.of Ω)))
    (hdistinct : Pairwise (fun i j : Fin n ↦ Disjoint (Set.range (p i)) (Set.range (p j))))
    (hsmooth : ∀ i : Fin n, Set.range (p i) ⊆ (f.smoothLocus : Set C)) :
    ∃! e : Additive (markedInfinitesimalAutomorphisms f p) ≃+
      ⨁ (Z : irreducibleComponents C),
        curveVectorFieldsFixingPoints (C.normalizedComponentMap Z ≫ f)
          (markedNodalSpecialPoints f p Z),
      IsMarkedInfinitesimalNormalizationIdentification f p e := by
  sorry

/-- The three genus bounds on fixed closed points of a nonzero smooth-curve derivation.

Source: Stacks Project, curves.tex, Tags 0E67 and 0E68, and more-morphisms.tex, Tag 02H5
(blueprint: lem-sfb-marked-nodal-infinitesimal-fields).

Proof:
8. Let $X$ now be any smooth proper connected curve over $k$. It is integral by
[lem-sc-smooth-connected-curve-local-rings]. Every closed point has residue field $k$: by
[lem-kun-closed-point-field] it is finite over $k$, and an algebraically closed field has no
proper finite field extension. By the universal property of [def-sc-relative-differential-sheaf],
its derivations are the maps $\theta:\Omega^1_{X/k}\to\mathcal O_X$. By [lem-sc-canonical-sheaf]
and [lem-pc-tensor-dual-invertible], these maps are global sections of the invertible sheaf
$T=(\Omega^1_{X/k})^\vee$. At any closed point $q$, [lem-a1-uniformizer-differential-basis]
applies, since $\kappa(q)=k$ is separable over $k$, and gives a basis $dt$ for a uniformizer $t$.
The ideal of $q$ is locally $(t)$, so the Leibniz formula $D(th)=tD(h)+hD(t)$ says
$D((t))\subseteq(t)$ exactly when $D(t)\in(t)$. But $D(t)=\theta(dt)$, so this condition is
exactly vanishing of the corresponding section of $T$ at $q$. The assertion for the ideal sheaf
follows stalkwise, since the ideal is the unit ideal away from $q$. Uses:
def-sc-relative-differential-sheaf, lem-sc-canonical-sheaf, lem-pc-tensor-dual-invertible,
lem-a1-uniformizer-differential-basis, lem-sc-smooth-connected-curve-local-rings,
lem-kun-closed-point-field.
9. Let $g$ be the genus. The degree homomorphism [def-sc-pic0] and [lem-sc-canonical-degree] give
$\deg T=-(2g-2)=2-2g$. For completeness, the usual bound on zeros follows directly from the
existing divisor statements. The curve is integral by [lem-sc-smooth-connected-curve-local-rings].
A nonzero global section $s$ of $T$ is a nonzero rational section: locally it is a function times
a basis, and the local-to-generic maps are injective. By [def-sc-rational-section-divisor],
$Z=\operatorname{div}(s)$ has at $q$ the valuation of that local coefficient. These integers are
nonnegative because the coefficients are regular, and are positive exactly where $s$ vanishes. By
[lem-sc-line-bundle-rational-section], $T\cong\mathcal O_X(Z)$, whence [def-sc-pic0] gives $\deg
Z=\deg T=2-2g$. By step 8 all closed points have residue field $k$, so each distinct zero
contributes at least one to this sum. If $g\ge2$ its right side is negative, impossible for a
nonzero section. If $g=1$ it is zero, so there is no fixed point. If $g=0$ it is two, so there are
at most two fixed points. Step 8 translates all three conclusions to derivations. Uses:
def-sc-pic0, lem-sc-canonical-degree, lem-sc-smooth-connected-curve-local-rings,
def-sc-rational-section-divisor, lem-sc-line-bundle-rational-section.
-/
theorem smooth_proper_curve_vector_field_bounds
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of Ω)) [IsProper f] [Smooth f] [ConnectedSpace C]
    (hpure : C.IsPureDimension 1) :
    (2 ≤ @Scheme.arithmeticGenus Ω _ C ⟨f⟩ →
      Subsingleton (f.relativeDifferentials ⟶ Scheme.Modules.unit C)) ∧
    (@Scheme.arithmeticGenus Ω _ C ⟨f⟩ = 1 →
      ∀ D : f.relativeDifferentials ⟶ Scheme.Modules.unit C, D ≠ 0 →
        ∀ x : C, IsClosed ({x} : Set C) → D ∉ curveVectorFieldsFixingPoints f {x}) ∧
    (@Scheme.arithmeticGenus Ω _ C ⟨f⟩ = 0 →
      ∀ D : f.relativeDifferentials ⟶ Scheme.Modules.unit C, D ≠ 0 →
        ({x : C | IsClosed ({x} : Set C) ∧
          D ∈ curveVectorFieldsFixingPoints f {x}} : Set C).encard ≤ 2) := by
  sorry

/-- Stability of every normalized component kills the infinitesimal marked automorphisms.

Source: Stacks Project, curves.tex, Tags 0E67 and 0E68, and more-morphisms.tex, Tag 02H5
(blueprint: lem-sfb-marked-nodal-infinitesimal-fields).

Proof:
10. Finally $2g(C_a)-2+\#E_a>0$ forces $\#E_a\ge3$ for $g(C_a)=0$ and $\#E_a\ge1$ for $g(C_a)=1$.
In those cases step 9 excludes any nonzero derivation fixing $E_a$; for $g(C_a)\ge2$ it excludes
all nonzero derivations already. Every summand in step 7 is therefore zero, so its additive
identification makes the infinitesimal marked automorphism group trivial. No markings are required
in the construction: when $n=0$, $E_a$ consists only of node preimages, and when there are no
nodes the normalization identification is the identity.
-/
theorem marked_nodal_infinitesimal_automorphisms_subsingleton
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of Ω)) [IsProper f] [ConnectedSpace C] [IsReduced C]
    (hpure : C.IsPureDimension 1)
    (hnodal : ∀ x : C, x ∉ f.smoothLocus →
      Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
        (C.presheaf.stalk x) ≃+*
        (MvPowerSeries (Fin 2) Ω ⧸
          Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
            (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Ω)})))
    {n : ℕ} (p : Fin n → (Spec (.of Ω) ⟶ C))
    (hp : ∀ i : Fin n, p i ≫ f = 𝟙 (Spec (.of Ω)))
    (hdistinct : Pairwise (fun i j : Fin n ↦ Disjoint (Set.range (p i)) (Set.range (p j))))
    (hsmooth : ∀ i : Fin n, Set.range (p i) ⊆ (f.smoothLocus : Set C))
    (hstable : ∀ Z : irreducibleComponents C,
      0 < (2 * C.normalizedComponentGenus f Z : ℤ) - 2 +
        ((markedNodalSpecialPoints f p Z).ncard : ℤ)) :
    Subsingleton (markedInfinitesimalAutomorphisms f p) := by
  sorry

end AlgebraicGeometry
