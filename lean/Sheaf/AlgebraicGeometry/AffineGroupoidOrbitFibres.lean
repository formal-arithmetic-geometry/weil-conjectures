/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Logic.Relation
public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Mathlib.AlgebraicGeometry.Scheme
import Sheaf.AlgebraicGeometry.Morphisms.FiniteAffineTensorBaseChange
import Sheaf.AlgebraicGeometry.FiniteLocallyFreeNormCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.LinearAlgebra.Determinant
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Sheaf.AlgebraicGeometry.AffineGroupoidIntegralInvariants
import Sheaf.AlgebraicGeometry.AffineGroupoidInvariantNorm

/-!
# Orbit fibres of the affine invariant spectrum

Source: Stacks Project, Groupoids, Tag 03BL, `groupoids-lemma-points`
(blueprint: lem-a1-affine-groupoid-orbit-fibres).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The spectrum of the equalizer of the source and target coordinate maps is
surjected onto by the object scheme. Its ordinary fibres are single-arrow orbits,
and its fibres on algebraically closed field points are generated equivalence classes.
Source: Stacks Project, Groupoids, Tag 03BL
(blueprint: lem-a1-affine-groupoid-orbit-fibres).

Proof plan:
1. Apply [lem-a1-affine-groupoid-integral-invariants] with the given groupoid: $C\hookrightarrow
A$ is integral. It is injective because $C$ is the displayed subring of $A$. Lying over [lem-
weil-pbc-integral-injective-lying-over] therefore gives a prime of $A$ over every prime of $C$,
proving surjectivity of $|U|\to|M|$. This includes $A=0$, when both spectra are empty.
Uses: lem-a1-affine-groupoid-integral-invariants, lem-weil-pbc-integral-injective-lying-over.
2. Fix an algebraically closed field $k$ and a map $c:C\to k$. Put $\mathfrak p=\ker c$. Lying
over supplies $\mathfrak q\subset A$ over $\mathfrak p$. The map $c$ extends to
$\kappa(\mathfrak p)\to k$ by sending a fraction to the quotient of its images. By
[lem-a1-integral-residue-extension-algebraic], $\kappa(\mathfrak q)/\kappa(\mathfrak p)$ is
algebraic. Apply [lem-weil-pbc-algebraic-extension-embeds-algebraically-closed] to extend that
embedding to $\kappa(\mathfrak q)\to k$. Composing $A\to\kappa(\mathfrak q)\to k$ lifts $c$. The
affine spectrum correspondence identifies this with a $k$-point of $U$ over the prescribed
$k$-point of $M$.
Uses: lem-a1-affine-groupoid-integral-invariants, lem-weil-pbc-integral-injective-lying-over,
lem-a1-integral-residue-extension-algebraic, lem-weil-pbc-algebraic-extension-embeds-
algebraically-closed, def-weil-affine-spectrum.
3. To compare two lifts $a_0,a_1:A\to k$ of $c$, form $A'=A\otimes_C k$, $B'=B\otimes_C k$ and
$\sigma',\tau':A'\to B'$. The affine tensor-product base-change formula [lem-sbc-finite-affine-
tensor-base-change], with one summand, identifies these with the schemes obtained by base change
from $M$ to $\operatorname{Spec}k$. The structure maps are over $M$: the two maps from $R$ agree
on $C$; also $s\circ e=t\circ e=1$, inversion interchanges $s,t$, and composition preserves the
common $M$-image. Thus their base changes satisfy the same groupoid identities. The maps $a_j$
extend to $k$-algebra maps $\alpha_j:A'\to k$, $\alpha_j(a\otimes\lambda)=a_j(a)\lambda$.
Finite, flat, and locally finite presentation are separately preserved by arbitrary base change
by the three cited permanence statements, so $s',t'$ satisfy exactly the finite locally free
definition. On each local free norm chart, tensoring a basis gives a basis over the new ring.
This also gives the chartwise multiplication matrices used below.
Uses: lem-sbc-finite-affine-tensor-base-change, lem-pd-finite-locally-free-norm-charts, def-
weil-finite-integral-morphism, def-pc-fibre-product, def-weil-module-base-change, lem-weil-pbc-
finite-morphism-permanence, lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-qcqs-morphism-
permanence, def-pc-finite-locally-free.
4. Use the norm sections of [lem-pd-finite-locally-free-norm-charts]. Their compatibility with
scalar extension is a direct determinant calculation: on a free chart the matrix of
multiplication by $b\otimes1$ is obtained by applying the scalar ring map to every entry of the
matrix for $b$. The permutation-sum formula for the determinant [def-weil-endomorphism-
determinant] therefore gives $N(b)\otimes1=N(b\otimes1)$. The same calculation holds after any
substitution in a polynomial ring. It holds globally since the pulled-back free charts cover and
the norm sections restrict to these determinants. No freeness on the whole affine scheme or
constant rank is needed.
Uses: lem-pd-finite-locally-free-norm-charts, def-weil-endomorphism-determinant, def-weil-
module-base-change.
5. For any $f\in A'$ write $f=\sum_{j=1}^m a_j'\otimes\lambda_j$ and put $F=\sum_j a_j'T_j\in
A[T_1,\ldots,T_m]$. Extend the original groupoid by adjoining these same polynomial variables to
both rings. This is its product with affine $m$-space over $\operatorname{Spec}\mathbf Z$, hence
still a groupoid with finite locally free source and target (finite, flat and locally finite
presentation are preserved separately as in step 3). Apply [lem-a1-affine-groupoid-invariant-
norm] to obtain $G=N_{\sigma[T]}(\tau[T](F))\in C[T_1,\ldots,T_m]$: polynomial source and target
images agree exactly when their coefficients agree. Substitute $a\mapsto a\otimes1$ and
$T_j\mapsto1\otimes\lambda_j$. By step 4 the resulting element is $g=N_{\sigma'}(\tau'(f))\in
A'$. Since every coefficient of $G$ belongs to $C$, this substitution sends $G$ to the scalar
$c[T](G)(\lambda_1,\ldots,\lambda_m)\in k\subset A'$. Consequently $\alpha_0(g)=\alpha_1(g)$.
This proves the needed scalar equality for these particular norms directly, without assuming
invariants commute with nonflat scalar extension.
Uses: lem-a1-affine-groupoid-invariant-norm, lem-pd-finite-locally-free-norm-charts, def-weil-
endomorphism-determinant, def-weil-module-base-change, lem-weil-pbc-finite-morphism-permanence,
lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-qcqs-morphism-permanence.
6. Let $D_1=B'\otimes_{A',\alpha_1}k$, using $\sigma'$ for the $A'$-algebra structure. The
affine tensor formula identifies $\operatorname{Spec}D_1$ with the source fibre of $s'$ over
$\alpha_1$. It is finite-dimensional over $k$ by tensoring finite module generators of $B'$;
hence its structure morphism is finite and it has finitely many points by [lem-weil-pbc-finite-
closed-map-finite-fibres]. Finite implies integral by [pqf-lem-finite-integral-lft], and every
prime over the maximal ideal $(0)$ of $k$ is maximal by [lem-weil-pbc-integral-prime-over-
maximal-maximal]. Also $D_1$ is finitely generated as a $k$-algebra (a finite module generating
set already generates it as an algebra), so [lem-weil-pbc-closed-point-residue-field-base] gives
residue field $k$ at each of these closed points. Thus the points correspond to a finite list of
all $k$-algebra maps $\beta_i:B'\to k$ with $\beta_i\sigma'=\alpha_1$. This list is nonempty
because it contains the identity arrow at $\alpha_1$.
Uses: lem-sbc-finite-affine-tensor-base-change, def-weil-finite-integral-morphism, lem-weil-pbc-
finite-closed-map-finite-fibres, pqf-lem-finite-integral-lft, lem-weil-pbc-integral-prime-over-
maximal-maximal, lem-weil-pbc-closed-point-residue-field-base.
7. Suppose no arrow has source $\alpha_1$ and target $\alpha_0$. For the finite list in step 6
put $\alpha_i'=\beta_i\tau'$, $\mathfrak m_i=\ker\alpha_i'$ and $\mathfrak m_0=\ker\alpha_0$.
These kernels are maximal because all the maps are $k$-algebra maps to $k$, hence surjective.
The kernels are unequal: two such maps with the same kernel identify the quotient with $k$
identically on its subfield $k$, so are equal, contrary to the assumption. Distinct maximal
ideals do not contain each other, so $\mathfrak m_0\not\subset\mathfrak m_i$ for each $i$. Prime
avoidance [lem-weil-pbc-prime-avoidance] therefore supplies $f\in\mathfrak m_0$ outside all
$\mathfrak m_i$. Equivalently, $\alpha_0(f)=0$ whereas $\alpha_i'(f)\ne0$ for every $i$.
Uses: lem-weil-pbc-prime-avoidance.
8. Apply the local norm prime criterion [lem-pd-finite-free-norm-prime-criterion] to $\tau'(f)$.
More explicitly, choose a free affine norm chart around the point $\ker\alpha_1$; restriction
does not change its source fibre, so all primes over this point are the points listed in step 6.
At each of them the value of $\tau'(f)$ is $\beta_i\tau'(f)=\alpha_i'(f)\ne0$. The criterion and
the chart description of the norm imply $\alpha_1(g)\ne0$ for $g=N_{\sigma'}(\tau'(f))$. Around
$\ker\alpha_0$ use another free norm chart. The identity arrow at $\alpha_0$ is a prime in its
source fibre and evaluates $\tau'(f)$ to $\alpha_0(f)=0$. The same criterion gives
$\alpha_0(g)=0$. This contradicts the scalar equality in step 5. Thus an arrow with source
$\alpha_1$ and target $\alpha_0$ exists.
Uses: lem-pd-finite-free-norm-prime-criterion, lem-pd-finite-locally-free-norm-charts.
9. A $k$-arrow in the scalar-extended groupoid gives an original $k$-arrow by precomposing $B\to
B'$. Conversely an original $k$-arrow $\gamma:B\to k$ whose endpoints restrict to $c$ extends by
$b\otimes\lambda\mapsto\gamma(b)\lambda$, so step 8 gives an arrow relating any two original
lifts. An arrow always preserves the restrictions to $C$ since $\sigma|_C=\tau|_C$. Identity,
inverse and composition in $R(k)\rightrightarrows U(k)$ make the relation of being joined by one
arrow reflexive, symmetric and transitive. Therefore it equals the equivalence relation
generated by $s,t$, and steps 2 and 8 prove exactly the surjectivity and fibre assertion on
$k$-points.
Uses: def-weil-affine-spectrum, def-weil-module-base-change.
10. Finally let $u_0,u_1\in|U|$ have the same image $m\in|M|$. By integrality and
[lem-a1-integral-residue-extension-algebraic], both $\kappa(u_j)/\kappa(m)$ are algebraic.
Choose an algebraic closure $k$ of $\kappa(m)$ [def-weil-algebraic-closure]. By [lem-weil-pbc-
algebraic-extension-embeds-algebraically-closed] embed both residue fields into this same $k$,
extending its fixed inclusion of $\kappa(m)$. The composites $A\to\kappa(u_j)\to k$ have
underlying points $u_j$ and the same restriction $C\to\kappa(m)\to k$. By step 9 they are joined
by a $k$-arrow. Its underlying point in $R$ has the two required endpoints; invert the arrow if
necessary to match the order $s(r)=u_0$, $t(r)=u_1$. Conversely, an underlying point $r\in|R|$
has equal $M$-images under $s,t$, since the two ring maps $C\to B$ are equal. Together with step
1 this proves the entire assertion on ordinary points.
Uses: lem-a1-affine-groupoid-integral-invariants, lem-a1-integral-residue-extension-algebraic,
def-weil-algebraic-closure, lem-weil-pbc-algebraic-extension-embeds-algebraically-closed, def-
weil-affine-spectrum.
-/
theorem affineGroupoid_orbit_fibres
    {A B : CommRingCat.{u}} (s t : Spec B ⟶ Spec A)
    (e : Spec A ⟶ Spec B) (i : Spec B ⟶ Spec B) (c : pullback s t ⟶ Spec B)
    (hgroupoid : IsGroupoidScheme s t e i c)
    [s.IsFiniteLocallyFree] [t.IsFiniteLocallyFree] :
    Function.Surjective
      (PrimeSpectrum.comap ((Spec.homEquiv s).hom.eqLocus (Spec.homEquiv t).hom).subtype) ∧
    (∀ u₀ u₁ : Spec A,
      PrimeSpectrum.comap ((Spec.homEquiv s).hom.eqLocus (Spec.homEquiv t).hom).subtype u₀ =
        PrimeSpectrum.comap ((Spec.homEquiv s).hom.eqLocus (Spec.homEquiv t).hom).subtype u₁ ↔
      ∃ r : Spec B, s r = u₀ ∧ t r = u₁) ∧
    ∀ (k : Type (max u v)) [Field k] [IsAlgClosed k],
      Function.Surjective (fun a : A →+* k ↦
        a.comp ((Spec.homEquiv s).hom.eqLocus (Spec.homEquiv t).hom).subtype) ∧
      ∀ a₀ a₁ : A →+* k,
        a₀.comp ((Spec.homEquiv s).hom.eqLocus (Spec.homEquiv t).hom).subtype =
          a₁.comp ((Spec.homEquiv s).hom.eqLocus (Spec.homEquiv t).hom).subtype ↔
        Relation.EqvGen (fun x y : A →+* k ↦
          ∃ r : B →+* k, r.comp (Spec.homEquiv s).hom = x ∧
            r.comp (Spec.homEquiv t).hom = y) a₀ a₁ := by
  sorry

end AlgebraicGeometry
