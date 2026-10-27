/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleDifferentialPullbackPresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Sheaf.AlgebraicGeometry.ChartLogSmoothDeformationCalculus
public import Sheaf.AlgebraicGeometry.LogIdealChartPresentation
public import Sheaf.AlgebraicGeometry.LogInfinitesimalLifting
import WeilConjectures.AlgebraicGeometry.FlatUnramifiedFormallyEtale
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.AssociatedLogUniversalStalks
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.EtaleQuasiCoherentDescent
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde

/-!
# Finite chart models of logarithmic differentials

Source: Kato, Logarithmic structures of Fontaine--Illusie, §§1.7, 2.1, 2.9;
ILO, Exposé XVI Proposition 3.6.3, printed p.252
(blueprint: lem-sfb-log-differential-finite-chart-model).

The sheaf and both symbols are the published generators-and-relations construction.
The affine model uses its sections on the terminal étale object as the module W.
The pullback is specified by its tensor universal property and normalized on both symbols.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Scalar extension with its actual algebra structure supplied by the ring map.
Source: Kato §1.7, the affine tensor formula
(blueprint: lem-sfb-log-differential-finite-chart-model). -/
noncomputable def logDifferentialScalarExtension (A B : CommRingCat.{u})
    (ρ : A ⟶ B) (W : ModuleCat.{u} A) : ModuleCat.{u} B :=
  letI := ρ.hom.toAlgebra
  ModuleCat.of B (TensorProduct A B W)

/-- Pure tensors in the scalar-extension module, with the same structural ring map.
Source: Kato §1.7
(blueprint: lem-sfb-log-differential-finite-chart-model). -/
noncomputable def logDifferentialPureTensor (A B : CommRingCat.{u})
    (ρ : A ⟶ B) (W : ModuleCat.{u} A) (b : B) (w : W) :
    logDifferentialScalarExtension A B ρ W :=
  letI := ρ.hom.toAlgebra
  TensorProduct.tmul A b w

/-- The finite affine tensor model, normalized by restriction of every global section.
In particular the same equation applies to da and dlog m. Linearity gives scalar
compatibility; the pure-tensor equation and presheaf functoriality give compatibility
with every restriction between affine étale objects. The chosen W is the actual module
of sections on the affine source, equivalent to any W in the tensor presentation by
its value at the terminal object. Finite presentation includes the zero module.
Source: Kato §§1.7, 2.1, 2.9; ILO XVI 3.6.3
(blueprint: lem-sfb-log-differential-finite-chart-model). -/
def EtaleLogMap.HasFiniteAffineDifferentialModel {X Y : Scheme.{u}}
    {M : EtaleLogStructure X} {N : EtaleLogStructure Y} (f : EtaleLogMap M N) : Prop :=
  Module.FinitePresentation Γ(X, ⊤)
      (f.differentialSheaf.val.obj (op (Scheme.Etale.mk (𝟙 X)))) ∧
    ∃ e : ∀ (T : X.Etale) (_hT : IsAffine T.left),
        logDifferentialScalarExtension Γ(X, ⊤) Γ(T.left, ⊤) T.hom.appTop
            (f.differentialSheaf.val.obj (op (Scheme.Etale.mk (𝟙 X)))) ≃ₗ[Γ(T.left, ⊤)]
          f.differentialSheaf.val.obj (op T),
      ∀ (T : X.Etale) (hT : IsAffine T.left) (b : Γ(T.left, ⊤))
        (w : f.differentialSheaf.val.obj (op (Scheme.Etale.mk (𝟙 X)))),
        e T hT (logDifferentialPureTensor Γ(X, ⊤) Γ(T.left, ⊤) T.hom.appTop
          (f.differentialSheaf.val.obj (op (Scheme.Etale.mk (𝟙 X)))) b w) =
          b • f.differentialSheaf.val.map
            (MorphismProperty.Over.homMk T.hom (Category.comp_id T.hom)).op w

/-- The canonical comparison isomorphism, fixed on the tensor unit for every relative
étale diagram and on both sorts of generators. The representing pullback is precisely
O_X' tensor over g-inverse O_X with g-inverse omega, by its full tensor-Hom property.
Source: Kato §1.7 and ordinary formally étale differential comparison
(blueprint: lem-sfb-log-differential-finite-chart-model). -/
def EtaleLogMap.HasEtaleDifferentialComparison
    {X Y X' Y' : Scheme.{u}} {M : EtaleLogStructure X} {N : EtaleLogStructure Y}
    {M' : EtaleLogStructure X'} {N' : EtaleLogStructure Y'}
    (f : EtaleLogMap M N) (g : EtaleLogMap M' M) (f' : EtaleLogMap M' N') : Prop :=
  ∃ (P : EtaleDifferentialPullbackPresentation g.base f.differentialSheaf)
    (e : P.module ≅ f'.differentialSheaf),
    (∀ (U : X.Etale) (V : X'.Etale) (k : V.left ⟶ U.left)
      (hk : k ≫ U.hom = V.hom ≫ g.base) (a : Γ(U.left, ⊤)),
      e.hom.val.app (op V) (P.unit.app U V k hk (f.sheafD U a)) =
        f'.sheafD V (k.appTop a)) ∧
    ∀ (U : X.Etale) (V : X'.Etale) (k : V.left ⟶ U.left)
      (hk : k ≫ U.hom = V.hom ≫ g.base) (m : M.monoidSheaf.obj.obj (op U)),
      e.hom.val.app (op V) (P.unit.app U V k hk (f.sheafDLog U m)) =
        f'.sheafDLog V (g.sectionMap U V k hk m)

/-- Finite affine chart models at every geometric point, and compatibility with every
commutative strict étale localization square, including noncartesian squares.
No logarithmic smoothness or lifting hypothesis is used.
Source: Kato §§1.7, 2.1, 2.9; ILO XVI Proposition 3.6.3, p.252
(blueprint: lem-sfb-log-differential-finite-chart-model).

Proof (following the fifteen steps of the DAG node):

1. First record an ordinary etale calculation that will be used below. If $R\to A\to B$ are ring
   maps with $A\to B$ etale, and $H$ is any $B$-module, restriction gives a bijection
   $\operatorname{Der}_R(B,H)\to\operatorname{Der}_R(A,H)$. Indeed form the ring $B\oplus H$
   with $(b,h)(b',h')=(bb',bh'+b'h)$, square-zero ideal $0\oplus H$, and $A$-structure
   $a\mapsto(\bar a,D(a))$. The unique infinitesimal lifting property of the etale map gives a
   unique $A$-map $B\to B\oplus H$ lifting $\mathrm{id}_B$. It has the form
   $b\mapsto(b,\widetilde D(b))$, and the ring-map equations say exactly that $\widetilde D$ is
   an $R$-derivation extending $D$. The cited lifting theorem applies because etale implies flat
   and unramified; it requires no Noetherian condition on the test ring. In particular
   derivations over an etale base vanish. If also $R\to R'$ is etale and $R'\to B$ is
   compatible, every extended $R$-derivation of $B$ kills $R'$: its restriction to $R'$ and zero
   are the two lifts of the zero derivation on $R$, hence agree.
   Uses: def-weil-etale-morphism, lem-weil-pbc-flat-unramified-formally-etale.

2. Fix a geometric point $\bar x$ of $X$. By the definition of an fs log scheme choose an affine
   pointed etale chart neighbourhood $V\to Y$ of $f(\bar x)$ with chart $Q$, and a pointed etale
   chart neighbourhood of $\bar x$ over $X\times_Y V$ with chart $P$. The fibre-product point is
   the pair of the chosen lifts. Etale base change and composition ensure that the latter
   neighbourhood is etale over $X$. These charts may be refined by affine opens. Both $P$ and
   $Q$ are finitely generated integral monoids. All log structures in these choices are the
   pulled-back ones. Every map here is a scheme morphism, hence representable by algebraic
   spaces over $Y$; thus the current representability hypothesis of the cited calculus holds.
   Uses: def-trf-fs-log-blowup, lem-sfb-stack-chartwise-smooth-etale-calculus, lemma-weil-pbc-
   affine-neighbourhood-cofinal, lem-weil-pbc-etale-cover-geometric-point-lift.

3. Choose monoid generators $q_1,\ldots,q_s$ of $Q$ and write $m_i=f^\flat(q_i)$ on the source
   chart neighbourhood. The associated-log description says that the germ of each $m_i$ has the
   form $[v_i,u_i]$ with $v_i\in P$ and $u_i$ an invertible function germ. The stalk colimit and
   cofilteredness let us lift these finitely many units and equalities simultaneously to one
   pointed etale refinement. Equivalently the local-section description of sheafification gives
   representatives $m_i=[v_i,u_i]$ there. Shrink further so all $u_i$ remain units. We do not
   assert a homomorphism $Q\to P$ or select compatible lifts of the relations of $Q$; only the
   finitely many displayed log sections are used.
   Uses: lem-trf-associated-log-universal-stalks, def-weil-pbc-geometric-stalks, lem-weil-pbc-
   pointed-etale-neighbourhoods-cofiltered, lem-weil-pbc-site-sheafification-sections-local.

4. After these refinements the underlying map to $V$ is locally of finite presentation, by the
   base-change and composition calculus and the fact that etale morphisms are locally of finite
   presentation. Its definition allows us to replace the two neighbourhoods by affine opens
   $U=\operatorname{Spec}A$ and $V=\operatorname{Spec}R$ with
   $A=R[x_1,\ldots,x_n]/(F_1,\ldots,F_l)$. All previously chosen charts and identities restrict
   to these opens. The source $U$ is locally Noetherian: $U\to X$ is etale, hence locally of
   finite type, and $X$ is locally Noetherian. Therefore $A$ is Noetherian by the affine-open
   theorem, applied to the whole of $U$. This is the only use of Noetherianity below.
   Uses: lem-sfb-stack-chartwise-smooth-etale-calculus, def-sbc-locally-finite-presentation,
   def-weil-etale-morphism, pqf-lem-locnoeth-lft, pqf-lem-affine-open-locnoeth.

5. Let $\beta:P\to A$ be the source chart, and let $[p]\in P^{\rm gp}$ denote the class of $p$.
   Form $$E=\Omega_{A/R}\oplus(A\otimes_{\mathbf Z}P^{\rm gp}).$$ Write
   $\lambda_p=(0,1\otimes[p])$. Define $W$ as the quotient of $E$ by the $A$-submodule generated
   by $$(d\beta(p),0)-\beta(p)\lambda_p\quad(p\in P),\qquad
   (u_i^{-1}du_i,0)+\lambda_{v_i}\quad(1\le i\le s).$$ We use the same notation for the images
   of $da$ and $\lambda_p$ in $W$. Thus the construction imposes the source structural relations
   and kills the chosen generators of the base log structure. It does not use a lifting or
   smoothness hypothesis.
   Uses: def-weil-pbc-kahler-differentials, def-trf-fs-log-blowup.

6. The Leibniz and additivity relations show that $\Omega_{A/R}$ is generated by
   $dx_1,\ldots,dx_n$: differentiate a polynomial expression for any $a\in A$, with $dr=0$ for
   $r\in R$. If $p_1,\ldots,p_t$ generate $P$, then their classes generate $P^{\rm gp}$ as an
   abelian group, so the $\lambda_{p_j}$ generate $A\otimes_{\mathbf Z}P^{\rm gp}$. Consequently
   $W$ is generated by the images of these $n+t$ elements. The cited Noetherian finite-module
   theorem now gives a finite presentation $A^u\to A^v\to W\to0$. There is no need to claim that
   the displayed possibly infinite set of structural relations itself is finite, nor to assume
   $P^{\rm gp}$ is torsion-free.
   Uses: def-weil-pbc-kahler-differentials, def-trf-fs-log-blowup, lem-sc-noetherian-finite-
   module-finite-presentation.

7. Let $\mathcal H=(\widetilde W)_{\rm et}$. The affine associated-module theorem supplies the
   quasi-coherent sheaf $\widetilde W$ with $\Gamma(U,\widetilde W)=W$ (take the principal open
   $D(1)$). Quasi-coherent etale descent makes $T\mapsto\Gamma(T,t^*\widetilde W)$ a sheaf on
   $U_{\rm et}$. For every affine etale $t:T=\operatorname{Spec}B\to U$, affine pullback
   sections give $$\mathcal H(T)=B\otimes_AW,$$ with the map on a pure tensor equal to
   multiplication by $b$ of the pulled-back section $w$. These identifications are natural in
   $W$. Restrictions between affine objects are $b\otimes w\mapsto\rho(b)\otimes w$: the
   pullback of a section pulled back from $U$ is its pullback along the composite, and the
   scalar action restricts by $\rho$.
   Uses: lem-weil-pbc-spec-module-tilde-sections, lem-sc-etale-qcoherent-descent, lem-weil-pbc-
   module-pullback-affine-sections.

8. For an affine etale $T=\operatorname{Spec}B\to U$, extend the derivation $A\to B\otimes_AW$,
   $a\mapsto1\otimes da$, uniquely to an $R$-derivation $D_B:B\to B\otimes_AW$ using step 1. For
   a map of affine etale $U$-objects with ring map $B\to C$, the two derivations from $B$ to
   $C\otimes_AW$ obtained by restricting $D_C$ or extending scalars in $D_B$ agree on $A$, hence
   agree by step 1. Thus these are a derivation of sheaves $D:\mathcal O_U\to\mathcal H$, with
   the analogous formula on nonaffine objects obtained by gluing on affine opens.
   Uses: def-weil-pbc-kahler-differentials, lem-weil-pbc-etale-composition-cancellation, lem-
   weil-pbc-affine-etale-essentially-small-cover.

9. On a local representative $[p,u]$ of the source associated log structure define
   $$\delta([p,u])=1\otimes\lambda_p+u^{-1}D(u).$$ This is well defined on its pushout: for $e$
   with $\beta(e)$ a unit, the relation in $W$ gives
   $1\otimes\lambda_e=\beta(e)^{-1}D(\beta(e))$, so the representatives $[pe,u]$ and
   $[p,\beta(e)u]$ have the same value. The Leibniz rule gives
   $(uv)^{-1}D(uv)=u^{-1}D(u)+v^{-1}D(v)$, hence additivity under monoid multiplication. Also
   $$D(\beta(p)u)=\beta(p)u\bigl(1\otimes\lambda_p+u^{-1}D(u)\bigr).$$ The associated-log node
   identifies $M|_U$ with the sheafification of these pushouts. The displayed maps respect
   restrictions, so sheafification extends them uniquely to $\delta:M|_U\to\mathcal H$
   satisfying $D\alpha(m)=\alpha(m)\delta(m)$. In particular the calculation proves the
   extension across logification rather than invoking an unnamed log-differential comparison
   theorem.
   Uses: lem-trf-associated-log-universal-stalks, def-weil-pbc-sheafification.

10. The pair $(D,\delta)$ kills the base ring and base log sections, including those defined
   only etale locally on $V$. Indeed any such function is locally on an affine etale
   $\operatorname{Spec}R'\to V$; its pullback has derivative zero by the last assertion of step
   1. Any base log section is etale locally $[q,c]$ in the associated-log chart $Q$, with $c$ a
   unit of such an $R'$. Since $q$ is a product of the $q_i$, its image has $\delta$ equal to
   the sum of the $\delta(m_i)$, each zero by the second family of relations defining $W$. The
   unit contributes $c^{-1}D(c)=0$. Local representatives suffice because the target $\mathcal
   H$ is a sheaf. This checks all base relations, not just the global functions in $R$ or the
   selected $q_i$.
   Uses: lem-trf-associated-log-universal-stalks, lem-weil-pbc-site-sheafification-sections-
   local.

11. Send each differential symbol $db$ to $D(b)$ and each log symbol $d\log m$ to $\delta(m)$.
   Steps 8--10 verify additivity, Leibniz, monoid additivity, the structural relation and all
   base relations. The maps commute with restrictions, so the universal property of
   sheafification gives a map $\Phi:\omega_{U/V}\to\mathcal H$. Conversely send $da\in W$ to the
   differential of $a$ in $\omega_{U/V}(U)$ and $\lambda_p$ to $d\log p$. The universal property
   of $\Omega_{A/R}$ supplies the first summand's map. The defining relations of $W$ hold in
   $\omega_{U/V}$; for the second family use $d\log m_i=0$ and $d\log u_i=u_i^{-1}du_i$. This
   gives $W\to\omega_{U/V}(U)$. On affine etale $T$ extend it by $b\otimes w\mapsto b\,w|_T$.
   The tensor restriction formula in step 7 makes these maps compatible; affine cover density
   and the sheaf gluing axiom extend them uniquely to $\Psi:\mathcal H\to\omega_{U/V}$.
   Uses: def-weil-pbc-sheafification, def-weil-pbc-kahler-differentials, lem-weil-pbc-affine-
   etale-essentially-small-cover.

12. The composite $\Phi\Psi$ fixes $1\otimes da$ and $1\otimes\lambda_p$, hence every $b\otimes
   w$. For $\Psi\Phi$, the induced derivation on an affine etale $B$ with values in
   $\omega_{U/V}(\operatorname{Spec}B)$ agrees with $b\mapsto db$ on $A$; uniqueness in step 1
   makes it agree on every $b\in B$. On a log representative $[p,u]$ it gives $d\log
   p+u^{-1}du=d\log[p,u]$, since $du=u\,d\log u$ for a unit. Local representatives and sheaf
   gluing give equality on every log symbol. The composites are therefore identities. Hence
   $\omega_{U/V}\simeq\mathcal H$ on the entire small etale site, with affine sections
   $B\otimes_AW$ and the required scalar, restriction and symbol formulas.
   Uses: lem-trf-associated-log-universal-stalks, lem-weil-pbc-affine-etale-essentially-small-
   cover.

13. We also check that the chart computation calculates the restriction of the original
   $\omega_f$. For the etale map $j:U\to X$, the inverse-image restriction theorem identifies
   $j^{-1}\omega_f$ with $\omega_f|_U$. The same restriction identifies $j^{-1}\mathcal O_X$
   with $\mathcal O_U$, since on $T\to U$ both assign $\Gamma(T,\mathcal O_T)$; hence the tensor
   formula gives $j^*\omega_f=\omega_f|_U$. The etale slice equivalence identifies the local
   source symbols with those on $U_{\rm et}$. Restriction of their sheafification has the same
   local generators and relations: sections of a sheafification are locally represented, and
   equality of two representatives is local, by the cited local-section theorem. The maps and
   inverse check of steps 8--12 thus work for $\omega_f|_U$ as well. Here $R$ and the $q_i$
   already define base symbols through the etale object $V\to Y$. For any other base symbol on
   an etale $Z\to Y$, pull back along $Z\times_YV\to V$ and refine by affine opens; this is
   etale over $V$, so step 10 kills that symbol too. Therefore the canonical identifications are
   $j^*\omega_f\simeq\omega_{U/V}\simeq\mathcal H$.
   Uses: lem-weil-pbc-etale-inverse-image-restriction, lem-weil-pbc-etale-site-localization-
   open, lem-weil-pbc-site-sheafification-sections-local, lem-weil-pbc-etale-base-change-finite-
   limits.

14. Now take the general square in the statement. Etale locally on $X'$ and $Y'$ refine the
   above chart neighbourhoods to affine compatible neighbourhoods $U'=\operatorname{Spec}B$ and
   $V'=\operatorname{Spec}R'$ mapping to $U$ and $V$, with $A\to B$ and $R\to R'$ etale.
   Explicitly choose an affine pointed refinement $V'$ of $Y'\times_YV$, then an affine pointed
   refinement $U'$ of $X'\times_{Y'}V'\times_{X\times_YV}U$. The map to $U$ is etale: before the
   open refinements it is a composite of base changes of $g$ and $V'\to V$. Thus both ring maps
   are etale. Because the log structures are pulled back, $P$ and $Q$ remain charts and the base
   log generators are still $[v_i,u_i|_{U'}]$. Step 1 gives a bijection between $R'$-derivations
   of $B$ and $R$-derivations of $A$ with values in any $B$-module: extension along $A\to B$ is
   unique, and it kills $R'$ by etaleness of $R\to R'$. For the log part the formula in step 9
   adjoins precisely the new units, with their forced values $u^{-1}D(u)$. If $\beta(p)$ becomes
   a unit only in $B$, the scalar-extended structural relation forces
   $\lambda_p=\beta(p)^{-1}D(\beta(p))$, so logification still respects that relation. For any
   $B$-module $H$, a map $B\otimes_AW\to H$ is exactly an $R$-derivation of $A$ and an additive
   map $P^{\rm gp}\to H$ satisfying the two relation families of step 5. Extend the derivation
   uniquely to $B$ and extend the log map by the unit formula of step 9; these satisfy all $R'$
   and base-log relations by step 10. Conversely restriction recovers the two maps and their
   relations. The extensions are unique and inverse to restriction. Thus the same quotient
   relations as in step 5, extended to $B$, give the symbol sheaf for $U'/V'$; the explicit
   inverse-map verification in steps 8--12 applies unchanged and identifies it with
   $(\widetilde{B\otimes_AW})_{\rm et}$. This argument does not assume that the square is
   cartesian.
   Uses: lem-sfb-stack-chartwise-smooth-etale-calculus, lem-trf-associated-log-universal-stalks,
   def-weil-pbc-kahler-differentials.

15. The quasi-coherent change-of-topology comparison identifies the ringed-etale tensor pullback
   of $(\widetilde W)_{\rm et}$ with the etale sheaf associated to the ordinary module pullback
   of $\widetilde W$. Affine tilde pullback identifies the latter with
   $(\widetilde{B\otimes_AW})_{\rm et}$. Combined with steps 13--14 this makes the canonical map
   $g^*\omega_f\to\omega_{f'}$ an isomorphism on the chosen neighbourhoods. It is the canonical
   map because its effect is $1\otimes da\mapsto d(g^\sharp a)$ and $1\otimes d\log m\mapsto
   d\log(g^\flat m)$. The same formulas hold on overlaps and determine the maps on local symbol
   generators, so the local inverses agree on overlaps and glue uniquely to a global inverse.
   This also shows that every identification respects scalar multiplication and restriction, and
   completes both assertions.
   Uses: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence, lem-weil-pbc-tilde-pullback-
   base-change, def-weil-pbc-sheafification.
-/
theorem EtaleLogHom.logDifferential_finite_chart_model
    {X Y : FineSaturatedLogScheme.{u}} (f : EtaleLogHom X Y)
    [LocallyOfFinitePresentation f.base] :
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme),
      ∃ (U V : FineSaturatedLogScheme.{u}) (g : EtaleLogHom U X)
        (h : EtaleLogHom V Y) (f₀ : EtaleLogHom U V),
        g.toLogMap.IsStrictEtale ∧ h.toLogMap.IsStrictEtale ∧
        g.toLogMap.CompositesEq f.toLogMap f₀.toLogMap h.toLogMap ∧
        IsAffine U.scheme ∧ IsAffine V.scheme ∧
        ∃ (t₀ : Spec (.of Ω) ⟶ U.scheme), t₀ ≫ g.base = t ∧
          ∃ (P : Type u) (_ : CommMonoid P)
            (β : P →* U.logStructure.monoidSheaf.obj.obj
              (op (Scheme.Etale.mk (𝟙 U.scheme)))),
            (∃ S : Finset P, Submonoid.closure (S : Set P) = ⊤) ∧
            Function.Injective (Algebra.GrothendieckGroup.of (M := P)) ∧
            U.logStructure.IsChart (Scheme.Etale.mk (𝟙 U.scheme)) β ∧
            f₀.toLogMap.HasFiniteAffineDifferentialModel) ∧
    ∀ (X' Y' : FineSaturatedLogScheme.{u}) (g : EtaleLogHom X' X)
      (h : EtaleLogHom Y' Y) (f' : EtaleLogHom X' Y'),
      g.toLogMap.IsStrictEtale → h.toLogMap.IsStrictEtale →
      g.toLogMap.CompositesEq f.toLogMap f'.toLogMap h.toLogMap →
        f.toLogMap.HasEtaleDifferentialComparison g.toLogMap f'.toLogMap := by
  sorry

end AlgebraicGeometry
