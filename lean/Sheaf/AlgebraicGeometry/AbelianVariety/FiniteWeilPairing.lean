module

public import Sheaf.AlgebraicGeometry.AbelianVariety.PolarizationCalculus
public import Sheaf.AlgebraicGeometry.AbelianVariety.RationalDualityData
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Algebra.Group.Hom.Instances

import WeilConjectures.AlgebraicGeometry.EtaleFieldGsets
import WeilConjectures.AlgebraicGeometry.Descent
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Rigidity
import Sheaf.AlgebraicGeometry.AbelianSpacePoincareCalculus
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor

/-! # Finite Poincare Weil pairings

Source: Milne, Abelian Varieties, I §§8–9 and §13, pp.57–58,
Lemma 13.1 and Proposition 13.2(a),(d).
(blueprint: lem-sfb-finite-torsion-weil-pairing)

The descent character fixes the pairing, including its sign: a trivialization of
`[m]⁎ P(-,y)` divided by its translate by `x` is the pairing value. This is Milne's
`g / (g ∘ t_x)` convention. All pullback comparisons are the canonical ones.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- The kernel of the power map on rational points, with its inherited group law.
Multiplicative notation for the source group means that `x ^ m = 1` is `m x = 0`.
Source: Milne AV I §13, p.57 (blueprint: lem-sfb-finite-torsion-weil-pairing). -/
abbrev abelianFiniteTorsionPoints {k : Type u} [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A] (m : ℕ) :=
  (powMonoidHom m : (𝟙_ (Over (Spec (.of k))) ⟶ A) →*
    (𝟙_ (Over (Spec (.of k))) ⟶ A)).ker

/-- The line bundle classified by the specified dual point, pulled from the specified
Poincare module. Source: Milne AV I §§9, 13, pp.41, 57
(blueprint: lem-sfb-finite-torsion-weil-pairing). -/
def abelianPoincarePointModule {k : Type u} [Field k]
    (A : AbelianVarietyWithDual k) (y : 𝟙_ (Over (Spec (.of k))) ⟶ A.datum.dual) :
    A.variety.left.Modules :=
  (Scheme.Modules.pullback
    (lift (𝟙 A.variety) (toUnit A.variety ≫ y)).left).obj A.datum.poincare

/-- The descent-character characterization of the finite Poincare Weil value.
The multiplication pullback is trivial and, for every trivialization, its ratio to
the translated trivialization is `c`. The equality of base maps is explicitly supplied;
`pullbackComp` and `pullbackCongr` then give the canonical deck identification.
No arbitrary comparison between line bundles is used.
Source: Milne AV I §9, pp.41–42, and §13, p.57, `g / (g ∘ t_x)`
(blueprint: lem-sfb-finite-torsion-weil-pairing). -/
def IsPoincareFiniteWeilValue {k : Type u} [Field k]
    (A : AbelianVarietyWithDual k) (m : ℕ)
    (x : abelianFiniteTorsionPoints A.variety m)
    (y : abelianFiniteTorsionPoints A.datum.dual m) (c : kˣ) : Prop :=
  ∃ h : (lift (𝟙 A.variety) (toUnit A.variety ≫ x.val) ≫ μ[A.variety]) ≫
      (𝟙 A.variety ^ m) = (𝟙 A.variety ^ m),
    Nonempty ((Scheme.Modules.pullback (𝟙 A.variety ^ m).left).obj
      (abelianPoincarePointModule A y.val) ≅ 𝟙_ A.variety.left.Modules) ∧
    ∀ σ : (Scheme.Modules.pullback (𝟙 A.variety ^ m).left).obj
        (abelianPoincarePointModule A y.val) ≅ 𝟙_ A.variety.left.Modules,
      ((Scheme.Modules.pullbackComp
        (lift (𝟙 A.variety) (toUnit A.variety ≫ x.val) ≫ μ[A.variety]).left
        (𝟙 A.variety ^ m).left).app (abelianPoincarePointModule A y.val)).hom ≫
        ((Scheme.Modules.pullbackCongr (congrArg Over.Hom.left h)).app
          (abelianPoincarePointModule A y.val)).hom ≫ σ.hom =
      (Scheme.Modules.pullback
        (lift (𝟙 A.variety) (toUnit A.variety ≫ x.val) ≫ μ[A.variety]).left).map σ.hom ≫
        (Scheme.Modules.pullbackObjUnitIso
          (lift (𝟙 A.variety) (toUnit A.variety ≫ x.val) ≫ μ[A.variety]).left).hom ≫
        Scheme.Modules.smulHom (𝟙_ A.variety.left.Modules)
          (((Scheme.ΓSpecIso (.of k)).inv ≫ A.variety.hom.appTop).hom (c : k))

/-- The finite Weil pairings of the normalized Poincare modules, with both perfectness
maps, transition, dual adjunction and skew symmetry for every invertible sheaf.
Source: Milne AV I §13, pp.57–58, Lemma 13.1, Proposition 13.2(a),(d), and I §9, p.41
(blueprint: lem-sfb-finite-torsion-weil-pairing).

Proof plan:
1. First identify the two duals used below, without assuming their group laws agree. For each
abelian variety $C$, [lem-sfb-abelian-polarization-calculus] and
[lem-sfb-abelian-space-poincare-calculus] represent the same functor of rigidified algebraically
trivial families over $\operatorname{Spec}k$. The hypotheses of the latter hold: commutativity is
[lem-sc-av-commutative], and the other properties are in the definition of an abelian variety.
Yoneda gives an isomorphism $\psi:C^\vee\simeq D$ preserving $0$ and the universal rigidified
sheaf, where $D$ is the space dual. It is a group isomorphism: apply [lem-sc-rigidity] to
$$h(s,t)=\psi^{-1}(\psi(s+t)-\psi(s)-\psi(t)):C^\vee\times C^\vee\to C^\vee.$$ The first factor is
proper geometrically connected and geometrically reduced by
[lem-sc-abelian-variety-characterization]; the second is connected and the target separated of
finite type. Since $h(s,0)=0$, rigidity makes $h$ independent of $s$, and $h(0,t)=0$ makes it
zero. Thus the biadditivity and dual-pullback isomorphisms in the space node hold for exactly the
dual and Poincare sheaf in this item. Uniqueness of representation identifies its $\phi_L$ and
$a^\vee$ with those of the item as well. Uses: lem-sfb-abelian-polarization-calculus,
lem-sfb-abelian-space-poincare-calculus, lem-sc-av-commutative, lem-sc-rigidity,
lem-sc-abelian-variety-characterization.

2. Write $P(z,b)$ for the fibre of the normalized Poincare sheaf. Use the two axis-preserving
tensor laws of [lem-sfb-abelian-space-poincare-calculus]. They are associative, symmetric within
either addition law, and satisfy interchange between the laws. Indeed, each of the two composites
in any such diagram is an isomorphism between the same line modules, and preserves the
rigidification at the first identity. Their quotient is a rigidification-preserving automorphism
on $C\times T$, with the other coordinates included in $T$, hence is the identity by the
automorphism clause of that node. This also proves compatibility with an axis-preserving pullback
comparison. Iterating the laws therefore gives unambiguous maps $$P(z,b)^{\otimes m}\simeq
P(mz,b),\qquad P(z,b)^{\otimes m}\simeq P(z,mb).$$ Tensor pullback and its action on pure tensors
are [lem-weil-pbc-module-pullback-tensor]. All later comparisons use these normalized maps, not
arbitrary trivializations of point fibres. Uses: lem-sfb-abelian-space-poincare-calculus,
lem-weil-pbc-module-pullback-tensor.

3. For $m=\ell^n$, $x\in A[m](k)$ and $b\in A^\vee[m](k)$, the two maps of step 2, followed by the
identity-axis trivializations, give $$t^1_m(x,b),t^2_m(x,b):P(x,b)^{\otimes m}\longrightarrow k.$$
Define $r_m(x,b)\in k^\times$ by $t^1_m=r_m t^2_m$. This is independent of any choice of a basis
in $P(x,b)$. To check additivity in $x$, use $P(x+x',b)\simeq P(x,b)\otimes P(x',b)$. Interchange
identifies each $t^i_m(x+x',b)$ with $t^i_m(x,b)\otimes t^i_m(x',b)$, so taking ratios gives
$r_m(x+x',b)=r_m(x,b)r_m(x',b)$. The second tensor law gives the same equality in $b$. The axis
maps give $r_m(0,b)=r_m(x,0)=1$, hence $r_m(x,b)^m=r_m(mx,b)=1$. Thus $r_m$ has values in
$\mu_m(k)$. This two-trivialization construction is the finite Poincare Weil pairing, with the
ratio convention $t^1/t^2$; set $w_{A,n}=r_{\ell^n}$. Uses:
lem-sfb-abelian-space-poincare-calculus.

4. For nondegeneracy, fix $b\in A^\vee[m](k)$ and let $M=P(-,b)$. For arbitrary $z\in A$, the
first tensor law identifies $[m]^*M$ at $z$ with $P(z,b)^{\otimes m}$; the second law and $mb=0$
give a trivialization $\sigma:[m]^*M\simeq\mathcal O_A$. The map $q=[m]:A\to A$ is finite flat and
surjective by [lem-sc-mult-n-finite-flat] and [lem-sc-mult-n-isogeny], hence is an fpqc covering.
Its kernel $H=A[m]$ is finite etale by [lem-sc-ntorsion-etale]. Over the algebraically closed
field $k$, [lem-exc-etale-field-gsets] identifies $H$ with the constant scheme on $H(k)$ (the
absolute Galois group is trivial). The group-law formulas give the isomorphism $$A\times H\simeq
A\times_{q,A,q}A,\quad (z,x)\mapsto(z,z+x),$$ whose inverse subtracts the first coordinate from
the second. Consequently a trivialization of $q^*M$ is a morphism of descent data precisely when
it is invariant under these translations, for every $x\in H(k)$. Uses:
lem-sfb-abelian-space-poincare-calculus, lem-sc-mult-n-finite-flat, lem-sc-mult-n-isogeny,
lem-sc-ntorsion-etale, lem-exc-etale-field-gsets.

5. Under the first-addition identification $P(z+x,b)\simeq P(z,b)\otimes P(x,b)$, the second-law
trivialization $\sigma$ gains the factor $t^2_m(x,b)$. The canonical deck identification of $q^*M$
gains $t^1_m(x,b)$ instead: its base points agree since $m(z+x)=mz$. Their quotient is
$t^2_m/t^1_m=r_m(x,b)^{-1}$. Interchange in [lem-sfb-abelian-space-poincare-calculus] justifies
these identifications on the whole overlap, not just its individual fibres. If $r_m(x,b)=1$ for
all $x$, $\sigma$ is therefore a compatible trivialization of the canonical descent datum. Apply
the compatible-trivialization clause of [lem-pc-fpqc-descent], with the fpqc singleton $q$ of step
4, to conclude $M\simeq\mathcal O_A$. Rescale this isomorphism by its nonzero value at $0$ so that
it respects the rigidification. The representing property in
[lem-sfb-abelian-polarization-calculus] then implies $b=0$. This proves injectivity of
$A^\vee[m](k)\to\operatorname{Hom}(A[m](k),\mu_m(k))$. Uses:
lem-sfb-abelian-space-poincare-calculus, lem-pc-fpqc-descent,
lem-sfb-abelian-polarization-calculus.

6. Put $g=\dim A=\dim A^\vee$, the equality being part of [lem-sfb-abelian-polarization-calculus].
By [lem-sc-ntorsion-etale], both torsion groups are isomorphic to $(\mathbf Z/m\mathbf Z)^{2g}$.
By [lem-sc-primitive-root], $\mu_m(k)$ is cyclic of order $m$. Every character of $(\mathbf
Z/m\mathbf Z)^{2g}$ is uniquely determined by the $2g$ arbitrary images of its coordinate
generators. Thus its character group has $m^{2g}$ elements. The injection of step 5 is
consequently a bijection. These characters separate points: for a nonzero coordinate $c\bmod m$,
the character sending its generator to a primitive $m$-th root $\zeta$ takes the value
$\zeta^c\ne1$. Surjectivity from step 5 therefore implies injectivity of the other evaluation map.
Its source and target again have $m^{2g}$ elements, so it too is bijective. This proves both
asserted perfectness clauses, including $g=0$. Uses: lem-sfb-abelian-polarization-calculus,
lem-sc-ntorsion-etale, lem-sc-primitive-root.

7. Let $M=mr$, $u\in A[M](k)$ and $v\in A^\vee[M](k)$. The two tensor laws identify
$P(ru,rv)^{\otimes m}$ with $P(u,v)^{\otimes mr^2}$. Expand $t^1_m(ru,rv)$ by first adding $r$
copies of $u$, then $m$ copies, and expand the second variable into $r$ copies of $v$.
Associativity and interchange from step 2 identify the result with $(t^1_M(u,v))^{\otimes r}$.
Expanding in the opposite order gives $t^2_m(ru,rv)=(t^2_M(u,v))^{\otimes r}$ under the same
identification. Taking ratios yields $r_m(ru,rv)=r_M(u,v)^r$. With $m=\ell^n$ and $r=\ell$, this
is precisely $w_{A,n}(\ell u,\ell v)=w_{A,n+1}(u,v)^\ell$. In particular the exponent is $\ell$,
despite multiplication by $\ell$ in both input coordinates. Uses:
lem-sfb-abelian-space-poincare-calculus.

8. For $a:A\to B$, use the axis-preserving comparison $(a\times1)^*P_B\simeq(1\times a^\vee)^*P_A$
of [lem-sfb-abelian-space-poincare-calculus], identified in step 1 with the dual pullback fixed in
the statement. It identifies $P_B(ax,y)$ with $P_A(x,a^\vee y)$. Here $a$ is a homomorphism by
hypothesis, and $a^\vee$ is one as well: pulling back the trivial rigidified family gives
$a^\vee(0)=0$, so the morphism $h(s,t)=a^\vee(s+t)-a^\vee(s)-a^\vee(t):B^\vee\times B^\vee\to
A^\vee$ satisfies $h(s,0)=0$ and $h(0,t)=0$, and [lem-sc-rigidity] applies exactly as in step 1
(the first factor is proper, geometrically connected and geometrically reduced by
[lem-sc-abelian-variety-characterization]), giving $h=0$. Because $a$ and $a^\vee$ are group
homomorphisms, it carries the first $m$-fold addition map to the first and the second to the
second; these are the normalized comparisons whose uniqueness was checked in step 2. It also
carries each axis trivialization to the corresponding one. Therefore it identifies $t^1_m$ on the
two fibres and separately identifies $t^2_m$. Their ratios give $r_{B,m}(ax,y)=r_{A,m}(x,a^\vee
y)$, the claimed finite adjunction identity. Uses: lem-sfb-abelian-space-poincare-calculus,
lem-sc-rigidity, lem-sc-abelian-variety-characterization.

9. For an arbitrary invertible $L$, pull the Poincare sheaf back by $1\times\phi_L$. By
[lem-sfb-abelian-space-poincare-calculus] and step 1 this is $$N_L=m_A^*L\otimes
p_1^*L^{-1}\otimes p_2^*L^{-1}\otimes q^*0^*L.$$ Commutativity of $A$ [lem-sc-av-commutative]
makes this normalized family symmetric under swapping $x,y$: the $m_A^*L$ and constant factors are
unchanged, and the other two factors are interchanged by the ordinary tensor symmetry. This
isomorphism preserves both axis trivializations. Consequently it swaps the first and second
tensor-addition laws: each resulting comparison preserves the first identity rigidification, so
uniqueness in [lem-sfb-abelian-space-poincare-calculus] makes the two composites equal. On
$m$-torsion fibres it thus carries $t^1_m(x,\phi_Ly)$ to $t^2_m(y,\phi_Lx)$ and $t^2_m(x,\phi_Ly)$
to $t^1_m(y,\phi_Lx)$. Taking ratios proves $$r_m(x,\phi_Ly)=r_m(y,\phi_Lx)^{-1}.$$ This argument
uses the normalized difference family for every invertible $L$, without an isogeny or ampleness
hypothesis. It proves skew symmetry also for $\ell=2$, without dividing by $2$. Uses:
lem-sfb-abelian-space-poincare-calculus, lem-sc-av-commutative.
-/
theorem IsAbelianVariety.exists_finite_weilPairing
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ≠ ringChar k) :
    ∃ w : ∀ (A : AbelianVarietyWithDual k) (n : ℕ),
        abelianFiniteTorsionPoints A.variety (ℓ ^ (n + 1)) →*
          abelianFiniteTorsionPoints A.datum.dual (ℓ ^ (n + 1)) →*
            rootsOfUnity (ℓ ^ (n + 1)) k,
      (∀ (A : AbelianVarietyWithDual k) (n : ℕ)
        (x : abelianFiniteTorsionPoints A.variety (ℓ ^ (n + 1)))
        (y : abelianFiniteTorsionPoints A.datum.dual (ℓ ^ (n + 1))),
        IsPoincareFiniteWeilValue A (ℓ ^ (n + 1)) x y (w A n x y).val) ∧
      (∀ (A : AbelianVarietyWithDual k) (n : ℕ),
        Finite (abelianFiniteTorsionPoints A.variety (ℓ ^ (n + 1))) ∧
        Finite (abelianFiniteTorsionPoints A.datum.dual (ℓ ^ (n + 1))) ∧
        Function.Bijective (w A n) ∧ Function.Bijective (w A n).flip) ∧
      (∀ (A : AbelianVarietyWithDual k) (n : ℕ)
        (x : abelianFiniteTorsionPoints A.variety (ℓ ^ (n + 2)))
        (y : abelianFiniteTorsionPoints A.datum.dual (ℓ ^ (n + 2)))
        (x' : abelianFiniteTorsionPoints A.variety (ℓ ^ (n + 1)))
        (y' : abelianFiniteTorsionPoints A.datum.dual (ℓ ^ (n + 1))),
        x'.val = x.val ^ ℓ → y'.val = y.val ^ ℓ →
          (w A (n + 1) x y).val ^ ℓ = (w A n x' y').val) ∧
      (∀ (A B : AbelianVarietyWithDual k) (a : A.variety ⟶ B.variety),
        IsMonHom a → ∀ aDual : B.datum.dual ⟶ A.datum.dual,
        Nonempty
          ((Scheme.Modules.pullback (a ▷ B.datum.dual).left).obj B.datum.poincare ≅
            (Scheme.Modules.pullback (A.variety ◁ aDual).left).obj A.datum.poincare) →
        ∀ (n : ℕ)
          (x : abelianFiniteTorsionPoints A.variety (ℓ ^ (n + 1)))
          (y : abelianFiniteTorsionPoints B.datum.dual (ℓ ^ (n + 1)))
          (ax : abelianFiniteTorsionPoints B.variety (ℓ ^ (n + 1)))
          (ay : abelianFiniteTorsionPoints A.datum.dual (ℓ ^ (n + 1))),
          ax.val = x.val ≫ a → ay.val = y.val ≫ aDual →
            w B n ax y = w A n x ay) ∧
      (∀ (A : AbelianVarietyWithDual k) (L : A.variety.left.Modules),
        L.IsInvertible → ∀ φ : A.variety ⟶ A.datum.dual,
        ClassifiesAbelianDifference A.datum L φ → ∀ (n : ℕ)
          (x y : abelianFiniteTorsionPoints A.variety (ℓ ^ (n + 1)))
          (φx φy : abelianFiniteTorsionPoints A.datum.dual (ℓ ^ (n + 1))),
          φx.val = x.val ≫ φ → φy.val = y.val ≫ φ →
            w A n x φy = (w A n y φx)⁻¹) := by
  sorry

end AlgebraicGeometry
