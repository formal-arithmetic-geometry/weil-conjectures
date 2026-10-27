module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
import WeilConjectures.RingTheory.IntegralClosureFiniteNormalProduct
import WeilConjectures.AlgebraicGeometry.NormalSectionsFiniteProduct
import WeilConjectures.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres
import Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal
import Sheaf.TraceFormula.GeometricallyReducedFibresLimitDescent
import Sheaf.TraceFormula.ValuationReducedFibreNormalization
import Sheaf.RingTheory.ColimitCategoryFpAlgebras
import WeilConjectures.RingTheory.FiniteMapColimitDescent
import WeilConjectures.RingTheory.ColimitFlatRingMap
import WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Localization.Integral
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.FiniteType

/-!
# Raynaud normalization over an absolute Dedekind integral closure

Source: Anantharaman, Appendix II, Theorem 1, printed p.73.
(blueprint: lem-sfb-absolute-dedekind-normalization-reduced-fibres)

Tensor factors are written with the scalar algebra on the left. Thus the generic
algebra is `Ω ⊗[K] (K ⊗[R] A)`, canonically the node's `(A ⊗[R] K) ⊗[K] Ω`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v w x y z

open scoped TensorProduct

namespace AbsoluteDedekindNormalization

variable (R : Type u) (K : Type v) (Ω : Type w) (A : Type x)
    [CommRing R] [Field K] [Field Ω] [CommRing A]
    [Algebra R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω] [Algebra R A]

/-- The canonical generic algebra, with scalar factors on the left.
Source: Anantharaman, Appendix II, Theorem 1, p.73.
(blueprint: lem-sfb-absolute-dedekind-normalization-reduced-fibres) -/
abbrev Generic := Ω ⊗[K] (K ⊗[R] A)

/-- The canonical map from the absolute integral base change to the generic algebra.
It sends `b ⊗ a` to `b ⊗ (1 ⊗ a)`.
Source: Anantharaman, Appendix II, Theorem 1, p.73.
(blueprint: lem-sfb-absolute-dedekind-normalization-reduced-fibres) -/
def baseMap : (integralClosure R Ω) ⊗[R] A →ₐ[integralClosure R Ω] Generic R K Ω A :=
  Algebra.TensorProduct.lift
    (Algebra.ofId (integralClosure R Ω) (Generic R K Ω A))
    (((Algebra.TensorProduct.includeRight :
      K ⊗[R] A →ₐ[K] Generic R K Ω A).restrictScalars R).comp
        Algebra.TensorProduct.includeRight)
    (fun _ _ ↦ Commute.all _ _)

/-- The ambient algebra structure is induced by the specified canonical map.
Source: Anantharaman, Appendix II, Theorem 1, p.73.
(blueprint: lem-sfb-absolute-dedekind-normalization-reduced-fibres) -/
instance ambientAlgebra : Algebra ((integralClosure R Ω) ⊗[R] A) (Generic R K Ω A) :=
  (baseMap R K Ω A).toRingHom.toAlgebra

/-- Compatibility of the canonical ambient algebra with the absolute integral base.
Source: Anantharaman, Appendix II, Theorem 1, p.73.
(blueprint: lem-sfb-absolute-dedekind-normalization-reduced-fibres) -/
instance ambientTower :
    IsScalarTower (integralClosure R Ω) ((integralClosure R Ω) ⊗[R] A) (Generic R K Ω A) :=
  IsScalarTower.of_algHom (baseMap R K Ω A)

/-- The prescribed relative integral closure, as a subalgebra of the generic algebra.
Source: Anantharaman, Appendix II, Theorem 1, p.73.
(blueprint: lem-sfb-absolute-dedekind-normalization-reduced-fibres) -/
abbrev closure := integralClosure ((integralClosure R Ω) ⊗[R] A) (Generic R K Ω A)

/-- The canonical generic-fibre map of the prescribed integral closure.
It sends `c ⊗ ω` to `ω * c` inside the generic algebra.
Source: Anantharaman, Appendix II, Theorem 1, p.73.
(blueprint: lem-sfb-absolute-dedekind-normalization-reduced-fibres) -/
def genericMap : (closure R K Ω A) ⊗[integralClosure R Ω] Ω →ₐ[integralClosure R Ω]
    Generic R K Ω A :=
  Algebra.TensorProduct.lift
    ((closure R K Ω A).val.restrictScalars (integralClosure R Ω))
    (IsScalarTower.toAlgHom (integralClosure R Ω) Ω (Generic R K Ω A))
    (fun _ _ ↦ Commute.all _ _)

end AbsoluteDedekindNormalization

open AbsoluteDedekindNormalization

/-- Raynaud normalization after passing to the absolute integral closure of a Dedekind domain.
Source: Anantharaman, Appendix II, Theorem 1, printed p.73.
(blueprint: lem-sfb-absolute-dedekind-normalization-reduced-fibres)

Proof plan (the node's steps):

1. By [lem-weil-pbc-integral-closure-algebraic-extension-normal], $B$ is a normal domain with
fraction field $\Omega$. Flatness of $A$ tensors the injection $B\hookrightarrow\Omega$ over $R$
to an injection $A_B\hookrightarrow A\otimes_R\Omega=D$. Tensor associativity identifies these
maps and identifies $(A_B)\otimes_B\Omega$ with $D$. Base-changing a finite polynomial
presentation of $A$ gives one of $A_B$ over $B$. Flatness also base-changes directly: for an
injection of $B$-modules, tensoring with $A_B$ is the same as tensoring the underlying $R$-modules
with $A$. Thus $A_B$ is flat finitely presented over $B$.

2. For each finite intermediate field $F/K$ in $\Omega$, let $R_F$ be the integral closure of $R$
in $F$. Every element of $B$ belongs to such a field by
[lem-weil-pbc-algebraic-generators-finite-extension]; its monic equation is unchanged there. Hence
$B=\bigcup_FR_F$. By [lem-sc-integral-closure-dedekind-surjective-fibres], each $R_F$ is a
Dedekind domain. Fix a prime $\mathfrak p$ of $B$, and put $\mathfrak p_F=\mathfrak p\cap R_F$.
Inside $\Omega$ we have $B_{\mathfrak p}=\bigcup_F(R_F)_{\mathfrak p_F}$: each fraction has its
numerator and denominator in a common finite field. Every ring in this union is a field if
$\mathfrak p_F=0$, and otherwise a DVR by [lem-sc-dedekind-localization-dvr], thus a valuation
ring by [def-sc-discrete-valuation-ring]. For $0\ne x\in\Omega$, choose $F$ containing $x$; either
$x$ or $x^{-1}$ is in $(R_F)_{\mathfrak p_F}$. This proves that $V=B_{\mathfrak p}$ is a valuation
ring with fraction field $\Omega$.

3. The hypothesis makes $D$ normal and makes $D\otimes_\Omega L$ normal for every field extension
$L/\Omega$. A nilpotent in any of these rings is zero: its germ in each prime localization is zero
because that localization is a domain; if the element were nonzero its annihilator would be a
proper ideal, contained in a maximal ideal where the germ is nonzero. Thus $D$ is geometrically
reduced. By [lem-weil-pbc-integral-closure-commutes-localization], $C\otimes_B V$ is precisely the
integral closure of $A_B\otimes_B V$ in $D$. Apply [lem-trf-valuation-reduced-fibre-normalization]
over $V$ with fraction field $\Omega$, which is algebraically and hence separably closed. Its
input algebra is flat finitely presented by the same tensor argument as Step 1. It gives
$C_{\mathfrak p}$ finite over $(A_B)_{\mathfrak p}$, flat finitely presented over $V$, with
generic fibre $D$ and reduced fibres over all algebraically closed fields. Here subscripts
$\mathfrak p$ mean localization in the base $B$.

4. Keep $\mathfrak p$ fixed. The small nonempty system $B_f$, indexed by $f\in B\setminus\mathfrak
p$ and enlargement of the finite set of inverted elements, has colimit $V$: fractions and their
equalities give its universal property. Products combine finitely many denominators. Apply
[lem-kun-fp-algebra-descent] to $C_{\mathfrak p}$ to obtain a finitely presented $B_f$-algebra $H$
with $H\otimes_{B_f}V\cong C_{\mathfrak p}$. The algebra $(A_B)_f$ is finitely presented by Step
1. By [lem-weil-pbc-colimit-category-fp-algebras], after enlarging the denominators the map
$(A_B)_{\mathfrak p}\to C_{\mathfrak p}$ descends to $(A_B)_f\to H$, with exactly that base
change. Every later occurrence of $H$ means this fixed model after base change.

5. Enlarge $f\notin\mathfrak p$ so $(A_B)_f\to H$ is finite by
[lem-weil-pbc-colimit-finite-ring-map]: $H$ is finite type over $B_f$, hence over $(A_B)_f$, and
its limit map is finite by Step 3. Enlarge again so $H$ is flat over $B_f$ by
[lem-weil-pbc-colimit-flat-ring-map], whose finite-presentation hypothesis is the chosen
presentation of $H$. The inverse system $\operatorname{Spec}B_g$ has limit $\operatorname{Spec}V$
by [lem-weil-pbc-limit-affine-transition]. It consists of affine qcqs schemes with affine
transitions. The affine map $\operatorname{Spec}H\to\operatorname{Spec}B_f$ is of finite
presentation, by its finite algebra presentation and the affine comparisons
[lem-trf-affine-geometric-fibre-reduced-comparison]. Its limit has reduced geometric fibres by
Step 3. Thus [lem-trf-geometrically-reduced-fibres-limit-descent] allows a further enlargement
making every geometric fibre reduced. Finiteness persists by tensoring a finite spanning list, and
flatness and finite presentation persist by the injection and presentation arguments of Step 1.

6. The chosen comparison $H\otimes_{B_f}V\cong C_{\mathfrak p}$ gives, after tensoring with
$\Omega$, a canonical identification $H\otimes_{B_f}\Omega\cong D$ under $(A_B)_f$. Flatness of
$H$ over the domain $B_f$ makes $H\to H\otimes_{B_f}\Omega$ injective, by tensoring
$B_f\hookrightarrow\Omega$. Hence view $H$ as a subring of $D$ containing $(A_B)_f$. Its
finiteness over $(A_B)_f$ makes every element integral by
[lem-weil-pbc-finite-algebra-is-integral], and localization of integral closure
[lem-weil-pbc-integral-closure-commutes-localization] therefore gives $H\subseteq C_f$. The
normality of $B$ in Step 1 implies that $\operatorname{Spec}B_f$ is normal: its local rings are
the corresponding local rings of $B$. This base is integral and affine qcqs. Step 5 and
[lem-weil-pbc-flat-ring-map-iff-flat-affine] verify every hypothesis of
[lem-trf-geometrically-reduced-eta-normal] for $\operatorname{Spec}H\to\operatorname{Spec}B_f$.

7. For $c\in C_f$, the equality $H\otimes_{B_f}\Omega=D$ writes $c=h/s$ with $h\in H$ and $0\ne
s\in B_f$. The element $c$ satisfies a monic equation over $(A_B)_f\subseteq H$, so $H[c]$ is
finite over $H$: powers below the monic degree span. The map
$\operatorname{Spec}H[c]\to\operatorname{Spec}H$ is finite [def-weil-finite-integral-morphism],
hence proper by [lem-weil-pbc-finite-proper]. It is an isomorphism on the generic fibre and on the
open $D(s)$ since $c=h/s$. On both schemes that open is schematically dense: multiplication by $s$
is injective on the rings and all their localizations, as they are subrings of the
$\Omega$-algebra $D$ and $s$ is a unit there. This is a finite $\eta$-modification. The conclusion
of [lem-trf-geometrically-reduced-eta-normal], whose hypotheses were verified in Step 6, makes it
an isomorphism. Therefore $c\in H$. This proves $C_f=H$ on an actual principal neighbourhood of
$\mathfrak p$, not merely after localization at $\mathfrak p$.

8. As $\mathfrak p$ varies, Steps 4–7 give principal opens $D(f)$ covering $\operatorname{Spec}B$,
on which $C_f$ is finite over $(A_B)_f$, flat finitely presented over $B_f$. A finite subcover
exists since an affine spectrum is quasi-compact, as recorded in
[lem-trf-affine-geometric-fibre-reduced-comparison]; equivalently these finitely many $f$ generate
the unit ideal. The corresponding opens in $\operatorname{Spec}A_B$ form an fpqc covering, by
[def-weil-pbc-fpqc-covering] and localization flatness [lem-weil-pbc-localization-flat]. Thus
[lem-weil-pbc-fpqc-descend-finite] makes $C$ finite over $A_B$. The flat-localization criterion
[lem-sc-affine-standard-cover-flat-localization-span] makes $C$ flat over $B$. For finite
presentation, [lem-sfb-separated-lfp-target-open-locality] applied over the opens $D(f)$ makes
$\operatorname{Spec}C\to\operatorname{Spec}B$ locally of finite presentation. Finally
[lem-weil-pbc-lfp-affine-opens-finite-presentation] gives the required finite polynomial
presentation of the global $B$-algebra $C$.

9. To verify normality of the prescribed ring $C$, apply [lem-wf-affine-noetherian-components] to
the finite-type $\Omega$-algebra $D$. Hence $\operatorname{Spec}D$ is locally Noetherian; it is
normal by hypothesis. The section-ring theorem [lem-sbc-normal-sections-finite-product] applied to
the whole affine open writes $D$ as a finite product of integrally closed domains. Now
[lem-sbc-integral-closure-finite-normal-product], with $A=A_B$ and ambient ring $D$, says
precisely that each prime localization of its integral closure $C$ is an integrally closed domain.
Thus $C$ is normal; the empty product covers $D=0$.

10. Since $A_B\subseteq C\subseteq D$ and $D=(B\setminus\{0\})^{-1}A_B$, localization gives
$D\subseteq C\otimes_B\Omega\subseteq D$. The second inclusion is injective because $C$ is a
subring of $D$: a fraction mapping to zero has zero numerator. Thus the specified canonical map
$C\otimes_B\Omega\to D$ is an isomorphism. By Steps 5–8 every geometric fibre of
$\operatorname{Spec}C\to\operatorname{Spec}B$ is reduced, since it lies over a principal
neighbourhood where $C_f=H$. For any $B\to E$, put $\mathfrak p=\ker(B\to E)$; the induced
embedding $\kappa(\mathfrak p)\hookrightarrow E$ identifies $C\otimes_BE'$ with
$(C\otimes_B\kappa(\mathfrak p))\otimes_{\kappa(\mathfrak p)}E'$ for every extension $E'/E$. By
[lem-trf-affine-geometric-fibre-reduced-comparison], the residue-field algebra is geometrically
reduced, so this ring is reduced. All arguments allow zero algebras and empty fibres; none assumes
$B$ Noetherian or $B/R$ finite.
-/
theorem absolute_dedekind_normalization_reduced_fibres
    (R : Type u) (K : Type v) (Ω : Type w) (A : Type x)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [Algebra R Ω] [IsScalarTower R K Ω]
    [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A] [Module.Flat R A]
    (hdim : ringKrullDim R = 1)
    (hgeom : ∀ (E : Type (max u v w x y)) [Field E] [Algebra K E]
      (p : Ideal (E ⊗[K] (K ⊗[R] A))) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    Function.Injective (baseMap R K Ω A) ∧
    Module.Finite ((integralClosure R Ω) ⊗[R] A) (closure R K Ω A) ∧
    Module.Flat (integralClosure R Ω) (closure R K Ω A) ∧
    Algebra.FinitePresentation (integralClosure R Ω) (closure R K Ω A) ∧
    (∀ (p : Ideal (closure R K Ω A)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ∧
    Function.Bijective (genericMap R K Ω A) ∧
    (∀ (E : Type (max u v w x y)) [Field E] [Algebra (integralClosure R Ω) E]
      (E' : Type (max u v w x y z)) [Field E'] [Algebra E E']
      [Algebra (integralClosure R Ω) E'] [IsScalarTower (integralClosure R Ω) E E'],
      IsReduced ((closure R K Ω A) ⊗[integralClosure R Ω] E')) := by
  sorry
