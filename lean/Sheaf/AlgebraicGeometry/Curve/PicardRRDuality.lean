/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.ResidueTrace
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
public import Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Sheaf.AlgebraicGeometry.Curve.PicardDuality
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.ProperBasic
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.AlgebraicGeometry.GlobalSectionsGeomConnected
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import Sheaf.AlgebraicGeometry.RegularCurveDivisorCalculus
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
import Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.CurveBaseChangeRelativeDimensionOne
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologySeparated
import Mathlib.RingTheory.Kaehler.Basic
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.AlgebraicGeometry.ScalarCupPullbackNaturality
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations

/-! # Curve duality, canonical degree, high-degree vanishing and field extension

Source: blueprint main-20261015, sec-picard-framework/sk-thm-picard-rr/
sk-thm-picard-rr-duality.md, clauses (1)–(4) (blueprint: det-picard-rr-duality).

All cohomology carriers below are the recorded right-derived module cohomology.
The abelian-cohomology API is used only through its resolution-normalized comparison
for the residue trace and the canonical flat base-change map. The field-extension
pairing equation uses Hom(L, omega), canonically H0(L-dual tensor omega), so that
pulling back a morphism specifies the dual/evaluation comparison without an arbitrary map.
-/

@[expose] public section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

open Modules

/-- The residue trace transported to actual module cohomology by the common-resolution
comparison. The function-field scalar structure is the one induced by the structure map.
Source: blueprint sk-thm-picard-rr-duality.md, clause (1), and Tate, sections 3–4
(blueprint: det-picard-rr-duality). -/
noncomputable def picardRRModuleTrace (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (.of k))] [IsSmoothProjectiveCurve (C ↘ Spec (.of k))]
    (z : scalarCohomology (C ↘ Spec (.of k)) (C ↘ Spec (.of k)).relativeDifferentials 1) :
    k :=
  letI := functionFieldAlgebra k C
  letI := isFunctionFieldAlgebra_functionFieldAlgebra k C
  residueTrace k C
    (moduleCohomologyExtResolutionEquiv C (C ↘ Spec (.of k)).relativeDifferentials 1 z)

/-- The value of canonical scalar extension on a pure tensor c tensor x. The comparison
is transported through the common-resolution equivalences and the uniquely normalized
adjunction comparison between the two existing pullbacks. No isomorphism is chosen here.
Source: blueprint sk-thm-picard-rr-duality.md, clause (4); Stacks Tag 02KH
(blueprint: det-picard-rr-duality). -/
noncomputable def picardRRModuleBaseChangeValue (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (.of k))] (K : Type u) [Field K] [Algebra k K]
    (M : C.Modules) (q : ℕ) (c : K) (x : scalarCohomology (C ↘ Spec (.of k)) M q) :
    scalarCohomology (C.baseChangeField k K ↘ Spec (.of K))
      ((tensorPullback (baseChangeFst (S := K) (C ↘ Spec (.of k)))).obj M) q :=
  letI : (baseChangedScheme (S := K) (C ↘ Spec (.of k))).Over (Spec (.of K)) :=
    ⟨baseChangeSnd (S := K) (C ↘ Spec (.of k))⟩
  (moduleCohomologyExtResolutionEquiv (C.baseChangeField k K) _ q).symm
    (H.map (((tensorPullbackSectionAdjunction
        (baseChangeFst (S := K) (C ↘ Spec (.of k)))).leftAdjointUniq
          (pullbackPushforwardAdjunction
            (baseChangeFst (S := K) (C ↘ Spec (.of k))))).inv.app M) q
      (H.baseChange (S := K) (C ↘ Spec (.of k)) M q
        (c ⊗ₜ[k] moduleCohomologyExtResolutionEquiv C M q x)))

/-- The full field-extension assertion, with the differential comparison normalized on da
and cohomology comparison normalized on pure tensors. The final equation is scalar
extension of the trace pairing, expressed on Hom(L, omega) = H0(L-dual tensor omega).
Its two scalars give exactly the formula <a tensor c, b tensor d> = cd <a,b>.
The let-instance merely makes the proved base-changed curve structure available inside
this predicate; it adds no hypothesis to the theorem using it.
Source: blueprint sk-thm-picard-rr-duality.md, clause (4)
(blueprint: det-picard-rr-duality). -/
def PicardRRDualityFieldExtension (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (.of k))] [IsSmoothProjectiveCurve (C ↘ Spec (.of k))]
    (L : C.Modules) (K : Type u) [Field K] [Algebra k K] : Prop :=
  ∃ hC : IsSmoothProjectiveCurve (C.baseChangeField k K ↘ Spec (.of K)),
    letI := hC
    letI : (baseChangedScheme (S := K) (C ↘ Spec (.of k))).Over (Spec (.of K)) :=
      ⟨baseChangeSnd (S := K) (C ↘ Spec (.of k))⟩
    GeometricallyConnected (C.baseChangeField k K ↘ Spec (.of K)) ∧
    arithmeticGenus K (C.baseChangeField k K) = arithmeticGenus k C ∧
    ((tensorPullback (baseChangeFst (S := K) (C ↘ Spec (.of k)))).obj L).degree K =
      L.degree k ∧
    ∃ e : (tensorPullback (baseChangeFst (S := K) (C ↘ Spec (.of k)))).obj
          (C ↘ Spec (.of k)).relativeDifferentials ≅
            (C.baseChangeField k K ↘ Spec (.of K)).relativeDifferentials,
      (∀ (W : C.Opens) (a : Γ(C, W)),
        e.hom.val.app (op (baseChangeFst (S := K) (C ↘ Spec (.of k)) ⁻¹ᵁ W))
          (Hom.relativeDifferentialsPullbackGenerator (C ↘ Spec (.of k))
            (baseChangeFst (S := K) (C ↘ Spec (.of k))) W a) =
        (C.baseChangeField k K ↘ Spec (.of K)).relativeDifferentialsDerivation.d
          (X := op (baseChangeFst (S := K) (C ↘ Spec (.of k)) ⁻¹ᵁ W))
          ((baseChangeFst (S := K) (C ↘ Spec (.of k))).app W a)) ∧
      (∀ (M : C.Modules) [M.IsInvertible] (q : ℕ),
        ∃ β : TensorProduct k K (scalarCohomology (C ↘ Spec (.of k)) M q) ≃ₗ[K]
            scalarCohomology (C.baseChangeField k K ↘ Spec (.of K))
              ((tensorPullback (baseChangeFst (S := K) (C ↘ Spec (.of k)))).obj M) q,
          ∀ c x, β (c ⊗ₜ[k] x) = picardRRModuleBaseChangeValue k C K M q c x) ∧
      ∀ (φ : L ⟶ (C ↘ Spec (.of k)).relativeDifferentials)
        (a : scalarCohomology (C ↘ Spec (.of k)) L 1) (c d : K),
        picardRRModuleTrace K (C.baseChangeField k K)
          (d • scalarCohomologyMap (C.baseChangeField k K ↘ Spec (.of K))
            ((tensorPullback (baseChangeFst (S := K) (C ↘ Spec (.of k)))).map φ ≫ e.hom) 1
            (picardRRModuleBaseChangeValue k C K L 1 c a)) =
          c * d * algebraMap k K
            (picardRRModuleTrace k C (scalarCohomologyMap (C ↘ Spec (.of k)) φ 1 a))

/-- Duality through the normalized residue trace, the three canonical invariants,
vanishing and Riemann–Roch above 2g-2, and compatibility with every field extension.
Tensor factors in the dual bundle are reversed by the canonical symmetry.
Source: blueprint sk-thm-picard-rr-duality.md, clauses (1)–(4)
(blueprint: det-picard-rr-duality).

Proof (the nine steps of the node):
1. The projective curve $C$ is proper, hence quasi-compact and separated. It is Noetherian,
being of finite type over the Noetherian scheme $\operatorname{Spec}k$ (the only ideals of $k$
are $0$ and $k$). Smoothness makes it geometrically reduced, so geometric connectedness gives
$H^0(C,\mathcal O_C)=k$. Its local rings are regular, and $C$ is integral and one-dimensional by
the curve hypothesis. Coherent cohomology is finite-dimensional and vanishes above degree one.
Consequently $\chi(\mathcal O_C)=1-g$ and $\chi(\mathcal N)=h^0(\mathcal N)-h^1(\mathcal N)$ for
every line bundle $\mathcal N$. The curve base-change lemma, applied with
$T=\operatorname{Spec}k$, shows that $C\to\operatorname{Spec}k$ is smooth of relative dimension
one. Hence $\omega=\Omega^1_{C/k}$ is locally free of rank one.

2. Here is the line-bundle Riemann–Roch calculation needed below, independently of the parent
sketch theorem. Write $\mathcal N\simeq\mathcal O_C(D)$ using the regular-curve divisor
calculus, with $D=\sum_x n_x[x]$. For a closed point $x$, that calculus gives $0\to\mathcal
O_C(D-[x])\to\mathcal O_C(D)\to i_{x,*}V\to0$, with $\dim_{\kappa(x)}V=1$. As specified in
clause (3), the action on $V$ factors through $\mathcal O_{C,x}\to\kappa(x)$, and the skyscraper
is the pushforward along the closed immersion $i_x:\operatorname{Spec}\kappa(x)\to C$. Closed-
immersion cohomology and the zero-dimensional support formula give $\chi(i_{x,*}V)=\dim_k
V=[\kappa(x):k]$. Additivity therefore gives $\chi(\mathcal O_C(D))-\chi(\mathcal
O_C(D-[x]))=[\kappa(x):k]$. Induct on $\sum_x|n_x|$: remove $[x]$ if $n_x>0$; if $n_x<0$, apply
the same equality to $D+[x]$ and solve for $\chi(\mathcal O_C(D))$. The base $D=0$ was computed
in step 1. Thus $\chi(\mathcal N)=\sum_x n_x[\kappa(x):k]+1-g$. In particular the divisor degree
agrees with $\chi(\mathcal N)-\chi(\mathcal O_C)$, the degree used by the base-change node.
Multiplication $\mathcal O(D)\otimes\mathcal O(E)\simeq\mathcal O(D+E)$ now gives additivity of
degree, and $\deg\mathcal N^{-1}=-\deg\mathcal N$.

3. The curve $C$ is integral of pure dimension one by step 1. Apply coherent Serre duality in
its integral case, with $n=1\in\{0,1\}$, $q=1$, and the finite locally free sheaf $\mathcal
F=\mathcal L$. Its stated perfect trace pairing identifies $H^1(C,\mathcal L)^\vee$ with
$H^0(C,\mathcal L^\vee\otimes\omega)$. For a line bundle the evaluation pairing identifies its
dual with its inverse (in a local frame $e$, the dual frame sends $e$ to $1$). Interchanging
tensor factors gives precisely (1).

4. Keeping $n=1$, apply the same duality to $\mathcal F=\mathcal O_C$ first with $q=1$ and then
with $q=0$. It gives $h^0(\omega)=h^1(\mathcal O_C)=g$ and $h^1(\omega)=h^0(\mathcal O_C)=1$;
the dual of a finite-dimensional space has the same dimension, as seen in a basis and its dual
basis. Hence $\chi(\omega)=g-1$. The line-bundle formula of step 2 gives
$\deg\omega=(g-1)-(1-g)=2g-2$, proving (2).

5. Suppose $\deg\mathcal L>2g-2$ and put $\mathcal M=\omega\otimes\mathcal L^{-1}$. Step 2 gives
$\deg\mathcal M=2g-2-\deg\mathcal L<0$. A nonzero global section $s$ is nonzero at the generic
point: in a local trivialization its coefficient is a regular function in a domain, which
injects into the function field. The regular-curve divisor calculus therefore identifies
$\mathcal M$ with $\mathcal O_C(\operatorname{div}_{\mathcal M}(s))$ with effective divisor. Its
degree is a sum of nonnegative integers $v_x(s)[\kappa(x):k]$, contradicting the strict negative
degree. Thus $H^0(C,\mathcal M)=0$. By (1), $H^1(C,\mathcal L)^\vee=0$, so $H^1(C,\mathcal L)=0$
(a nonzero vector in a finite-dimensional space admits a nonzero coordinate functional). The
formula in step 2 then gives $h^0(\mathcal L)=\deg\mathcal L+1-g$. This proves (3).

6. Fix any extension $K/k$. Projectivity and smoothness persist under base change; the curve
base-change lemma gives relative dimension one. Geometric connectedness persists directly from
its definition: for every extension $E/K$, $(C_K)_E\simeq C_E$, which is connected. Since
$C_K\to\operatorname{Spec}K$ is smooth, $C_K$ is regular by the smooth-over-a-field regularity
lemma (which needs no integrality), and $C_K$ is nonempty and connected; the regular-connected-
integral lemma makes $C_K$ integral, so it is a smooth projective geometrically connected curve.
The field-extension-flat node gives flatness of $\operatorname{Spec}K\to\operatorname{Spec}k$.
Flat coherent base change gives the cohomology isomorphisms, and the separated flat-cohomology
theorem says specifically that the comparison $\beta$ is bijective, since step 1 established
quasi-compactness and separatedness. Thus we have the canonical comparisons $H^i(C_K,\mathcal
N_K)\simeq H^i(C,\mathcal N)\otimes_kK$ for the line bundles at issue. Repeating this regularity
and connectedness argument for $C_E$ over every extension $E/k$ shows that $C$ is geometrically
integral. The genus base-change lemma therefore applies, using also $H^0=k$ from step 1; it
gives genus $g$. The degree base-change lemma applies to the cohomological degree, identified
with divisor degree in step 2, and gives $\deg\mathcal L_K=\deg\mathcal L$.

7. The canonical differential comparison is $\omega_K\simeq\Omega^1_{C_K/K}$. On an affine chart
$\operatorname{Spec}A$, its map sends $(da)\otimes c$ to $c\,d(a\otimes1)$. Its inverse is
induced by the $K$-derivation $a\otimes c\mapsto da\otimes c$: the Leibniz relations show this
is a derivation, and the two composites are the identity on the differential generators. These
maps respect localization, so glue. Pullback also identifies $(\mathcal L^\vee)_K$ with
$(\mathcal L_K)^\vee$: in a local frame both evaluations send $e\otimes e^\vee$ to $1$. The
tensor comparison consequently identifies $(\omega\otimes\mathcal L^{-1})_K$ with
$\omega_{C_K/K}\otimes\mathcal L_K^{-1}$.

8. Both $C$ and $C_K$ are integral of pure dimension one by steps 1 and 6, so the integral
residue-trace clause applies to each. Use the principal-parts cokernel description of
$H^1(C,\omega)$ in coherent Serre duality. A representative is a finite tuple $(\eta_x)_x$ of
rational differentials modulo regular differentials at $x$. Its pullback has, for each $x$,
component $\eta_{x,K}$ at each closed point $y$ above $x$, modulo regular differentials there,
and zero elsewhere. This is the cohomology pullback: restrict the maps of sheaves to each stalk
in the residue exact sequence and then pass to its cokernel; the coefficient maps take regular
differential germs to regular germs. More explicitly, the connecting class is the extension
obtained by pulling the residue sequence back along the tuple section of the quotient sheaf. The
connecting-map statement for sheaf Ext identifies this with composition by the extension class.
Inverse image followed by coefficient pushout takes that extension to the extension of the
pulled tuple, so it is precisely the cohomology map defined by the canonical comparison. The
local residue field-extension lemma gives
$$t_{C_K}(p^*[(\eta_x)_x])=\sum_x\sum_{y\mid x}\operatorname{res}_y(\eta_{x,K})=\iota\left(\sum_
x\operatorname{res}_x(\eta_x)\right)=\iota(t_C([(\eta_x)_x])).$$
Every original class has such a representative. The flat base-change comparison sends $a\otimes
c$ to $c\,p^*a$, so $K$-linearity yields $t_{C_K}(a\otimes c)=c\,\iota(t_C(a))$ for all pure
tensors, and hence all classes. No separability of closed residue fields is used.

9. Finally use naturality of scalar cup product under pullback, viewing $C_K\to C$ as a map of
$k$-schemes and then retaining its $K$-module structure. The definition of scalar cohomology is
restriction of the scalars of module cohomology, so these are the underlying $k$-linear maps of
the comparisons in step 6. The evaluation maps agree by the local-frame calculation in step 7.
Combining cup naturality with step 8 gives, for $a\in H^1(C,\mathcal L)$, $b\in
H^0(C,\omega\otimes\mathcal L^{-1})$ and $c,d\in K$,
$$\langle a\otimes c,b\otimes d\rangle_{C_K}=cd\,\iota(\langle a,b\rangle_C).$$
Pure tensors span, so this determines the full pairing. A finite basis $v_i$ and its dual
identify $H^1(C,\mathcal L)^\vee\otimes_kK$ with $(H^1(C,\mathcal L)\otimes_kK)^\vee$ by
$(f\otimes c)(v\otimes d)=cd\,\iota(f(v))$. Under this identification the displayed equality
says that the map to the dual induced by the perfect pairing is its scalar extension. The
inverses of these isomorphisms therefore also agree, which proves the final assertion of (4).
-/
theorem picard_rr_duality (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (.of k))] [IsSmoothProjectiveCurve (C ↘ Spec (.of k))]
    [GeometricallyConnected (C ↘ Spec (.of k))] (L : C.Modules) [L.IsInvertible] :
    (∃ e : scalarCohomology (C ↘ Spec (.of k))
          (MonoidalCategoryStruct.tensorObj (C := C.Modules)
            (dual L) (C ↘ Spec (.of k)).relativeDifferentials) 0 ≃ₗ[k]
            Module.Dual k (scalarCohomology (C ↘ Spec (.of k)) L 1),
      ∀ b a, e b a = picardRRModuleTrace k C
        (scalarCohomologyMap (C ↘ Spec (.of k))
          (evalTensor L (C ↘ Spec (.of k)).relativeDifferentials) 1
          (scalarCohomologyCup (C ↘ Spec (.of k)) L
            (MonoidalCategoryStruct.tensorObj (C := C.Modules)
            (dual L) (C ↘ Spec (.of k)).relativeDifferentials) 1 0 a b))) ∧
    Module.finrank k (scalarCohomology (C ↘ Spec (.of k))
      (C ↘ Spec (.of k)).relativeDifferentials 0) = arithmeticGenus k C ∧
    Module.finrank k (scalarCohomology (C ↘ Spec (.of k))
      (C ↘ Spec (.of k)).relativeDifferentials 1) = 1 ∧
    (C ↘ Spec (.of k)).relativeDifferentials.degree k =
      2 * (arithmeticGenus k C : ℤ) - 2 ∧
    (2 * (arithmeticGenus k C : ℤ) - 2 < L.degree k →
      Subsingleton (scalarCohomology (C ↘ Spec (.of k)) L 1) ∧
      (Module.finrank k (scalarCohomology (C ↘ Spec (.of k)) L 0) : ℤ) =
        L.degree k + 1 - (arithmeticGenus k C : ℤ)) ∧
    ∀ (K : Type u) [Field K] [Algebra k K], PicardRRDualityFieldExtension k C L K := by
  sorry

end AlgebraicGeometry.Scheme
