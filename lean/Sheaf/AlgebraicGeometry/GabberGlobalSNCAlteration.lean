module

public import Mathlib.Topology.Irreducible

public import Mathlib.Algebra.Algebra.Defs

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

public import Sheaf.AlgebraicGeometry.IsRegularScheme

public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsDivisor
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.QuasiProjective
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Sober
public import Mathlib.LinearAlgebra.Dimension.Finrank
import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.RelativeProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import Mathlib.AlgebraicGeometry.PullbackCarrier

import Mathlib.GroupTheory.Sylow

/-!
# Gabber's global prime-to-ell alteration with relative SNC boundary

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose X, Theorem 2.1,
printed pp. 148--149, and its proof in X 2.3, pp. 150--152; VIII 4.2.2(i)
(blueprint: lem-sfb-gabber-global-snc-alteration).
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- Gabber's projective prime-to-ell alteration of a separated finite-type pair over a field.
The field extension is `i`; generic residue degrees use the canonical residue-field map of `a`.
The ideal `D` is exactly the radical of the inverse-image ideal of the given closed subset.
The relative SNC predicate supplies the finite distinct integral components, their smoothness,
and smooth intersections of the expected codimension. The stalk equation is a product of
distinct parameters, so its individual prime factors give the equations of the components
through the point. The empty sublist is the unit ideal off the boundary.

Source: ILO, Expose X, Theorem 2.1 and the preceding definition of an ell-prime alteration,
pp. 148--149; relative SNC explained immediately after the theorem; VIII 4.2.2(i).
(blueprint: lem-sfb-gabber-global-snc-alteration)

Proof:
1. If $X=\varnothing$, then $Z=\varnothing$. Take $k'=k$, $P=\varnothing$ and the identity of the
empty scheme. Its field degree is $1$, and every boundary, generic-point and intersection
condition is vacuous. Hence assume $X$ nonempty.

2. Apply proper-pair radicial preparation to $(X,Z)$. It gives the dense open $X\subseteq\overline
X$, the closed extension $C$ of $Z$, a common finite radicial extension $e/k$, and
$r:B\to\overline X$. In particular $B$ is proper, normal and geometrically reduced over $e$, with
finitely many disjoint integral components, and $C_B=r^{-1}C$ is the support of an effective
Cartier divisor. At every generic point the residue extension for $r$ is finite purely
inseparable. Its degree and $[e:k]$ are powers of the characteristic, or $1$ in characteristic
zero, so they are prime to $\ell$. Every component of $\overline X$ meets $X$, since $X$ is dense.
Uses: lem-sfb-proper-pair-radicial-preparation.

3. Apply the equivariant smooth Galois-model node to $(B,C_B)$ over $e$. Obtain the finite
extension $K/e$, finite group $G$, smooth projective $K$-scheme $Y$ and invariant projective
surjection $h:Y\to B$. The reduced divisor $D=(h^{-1}C_B)_{\rm red}$ is relative strict normal
crossings over $K$. The fixed field $K^G/e$ is radicial and the full scheme quotient $Y/G\to B$ is
a finite universal homeomorphism over a dense open meeting each component. These two full-quotient
properties, not just a generically finite cover, are the hypotheses needed for the subsequent
Sylow argument. The model is chosen simultaneously for all components of $B$, so there is only one
field $K$ and one group $G$. Uses: lem-sfb-equivariant-smooth-galois-model.

4. Choose an $\ell$-Sylow subgroup $L\leq G$ by the Sylow prime-index node. Apply the semilinear
Sylow good-components node to $h$. Set $F=K^L$ and write $Q^\circ\subseteq Y/L$ for the selected
open and closed union. It gives $[F:e]$ prime to $\ell$, a finite separable extension $K/F$, a
projective surjection $d:Q^\circ\to B$, and finite prime-to-$\ell$ residue extensions at every
generic point of $Q^\circ$. Use exactly these selected components: a total prime-to-$\ell$ degree
does not assert that every component has prime-to-$\ell$ degree. Let $Y^\circ$ be their
open-and-closed inverse image. The $L$-quotient is $q:Y^\circ\to Q^\circ$; the restriction
$D^\circ=D\cap Y^\circ$ is an invariant relative strict normal crossings divisor over $K$, since
the same components and their intersections restrict to this union of connected components. Uses:
lem-weil-pbc-sylow-subgroup-prime-index, lem-sfb-semilinear-sylow-good-components.

5. The group $L$ has $\ell$-power order, hence its order is invertible in $F$ because
$\ell\ne\operatorname{char}(k)$. The hypotheses of the tame semilinear SNC-quotient resolution
node now hold for $(Y^\circ,D^\circ,K/F,L)$. Apply it to obtain $v:R\to Q^\circ$, with $R$ smooth
projective over $F$ and $v$ projective surjective, an isomorphism on a dense open meeting every
component, and inducing equality of the generic residue fields. It also gives a reduced relative
strict normal crossings divisor $E$ with support $v^{-1}q(|D^\circ|)$, together with the local
regular-parameter and regular-scheme boundary assertions. Because $h$ factors as $d q$ on
$Y^\circ$ and $q$ is surjective, $q(|D^\circ|)=d^{-1}(C_B)$: a point of $Q^\circ$ lies over $C_B$
exactly when every point above it in $Y^\circ$ lies in $h^{-1}C_B$. Thus $|E|=(r d v)^{-1}(C)$.
Uses: lem-sfb-tame-snc-quotient-resolution.

6. Set $c=r d v:R\to\overline X$; it is surjective by composing the three surjections. Each
generic point of $R$ maps to a generic point of $\overline X$. For the corresponding tower of
residue fields, $v$ has degree $1$, $d$ has degree prime to $\ell$, and $r$ has purely inseparable
degree prime to $\ell$. The degree of the composite is their product (multiply field bases), hence
prime to $\ell$. Likewise $F/k$ has degree $[F:e][e:k]$ prime to $\ell$. This checks every generic
point, including all components retained by the Sylow step. Projectivity of $c$ is obtained
through its graph, without composing projective-bundle maps over the non-projective bases $B$ and
$\overline X$. The finite morphism $\operatorname{Spec}F\to\operatorname{Spec}k$ is projective in
the projective-bundle sense by the finite-morphism node; $\operatorname{Spec}k$ is affine, so
$\mathcal O$ is ample (take the section $1$), and the projective-bundle-to-H-projective node makes
it H-projective. $R$ is H-projective over $F$ by Step 5, so the H-projective composition node
gives a closed immersion $\iota:R\hookrightarrow\mathbf P^M_k$ over $k$. Since $\overline X$ is
proper, hence separated, over $k$, the graph $(\mathrm{id},c):R\to R\times_k\overline X$ is the
base change of the closed diagonal of $\overline X$ along $c\times\mathrm{id}$, so it is a closed
immersion; $\iota\times\mathrm{id}:R\times_k\overline X\to\mathbf P^M_k\times_k\overline X$ is a
closed immersion by base change, and $\mathbf P^M_k\times_k\overline X=\mathbf P^M_{\overline X}$
by associativity of the fibre product $\overline X\times_{\mathbf Z}\mathbf P^M_{\mathbf Z}$. The
composite closed immersion $R\hookrightarrow\mathbf P^M_{\overline X}$ lies over $c$, so $c$ is
H-projective. Uses: lem-trf-finite-projective-bundle, def-weil-pbc-ample-invertible-module,
lem-trf-projective-bundle-to-h-projective, lem-trf-h-projective-composition,
def-weil-proper-morphism, lem-weil-pbc-closed-immersion-base-change,
def-nagata-projective-space-base-change, def-kun-projective.

7. Take $k'=F$ and $P=c^{-1}(X)=R\times_{\overline X}X$, with $a:P\to X$. Base change of the
closed immersion $R\hookrightarrow\mathbf P^M_{\overline X}$ of Step 6 along the open immersion
$X\subseteq\overline X$ gives a closed immersion $P\hookrightarrow\mathbf P^M_{\overline
X}\times_{\overline X}X=\mathbf P^M_X$ over $X$, so $a$ is H-projective. By the projective-space
definition, $\mathbf P^M_X$ is the same scheme over $X$ as the relative projective space
$\operatorname{Proj}_X\operatorname{Sym}(\mathcal O_X^{\oplus(M+1)})$, the projective bundle of
the finite-type quasi-coherent module $\mathcal O_X^{\oplus(M+1)}$; hence $a$ is projective in the
projective-bundle sense. Surjective base change makes $a$ surjective, and H-projective morphisms
are proper. Every generic point of $R$ belongs to $P$, since its image is generic in $\overline X$
and hence lies in the dense open $X$; the generic residue extensions for $a$ are therefore exactly
those checked in Step 6. Uses: lem-weil-pbc-closed-immersion-base-change,
def-nagata-projective-space-base-change, def-nagata-relative-projective-space,
def-trf-projective-bundle-morphism, lem-weil-pbc-surjective-base-change,
lem-kun-projective-implies-proper.

8. The open subscheme $P\subseteq R$ is smooth over $F$: locally on $R$, choose a constant
relative dimension $n$ for its smooth structure morphism, as in the smooth-morphism definition.
The open inclusion is etale by etale composition/cancellation clause (1), hence smooth of relative
dimension $0$; relative-dimension composition makes its composite smooth of relative dimension
$n$. The same argument applies to each open intersection of components of $E$. Their codimensions
persist because the local rings of an open subscheme agree with the original local rings. If
$R\hookrightarrow\mathbf P^n_F$ is its projective embedding, $P$ is closed in the complement of
the closed subset $R\setminus P$ of that projective space, hence locally closed in $\mathbf
P^n_F$. This proves quasi-projectivity. Finally $C\cap X=Z$ gives $|E|\cap P=a^{-1}Z$. Restrict
the finitely many integral components of $E$ to $P$ and omit empty ones; each remaining one is
still integral because a nonempty open of an integral scheme is integral. Their local parameter
equations and local rings are unchanged. Thus they give the claimed reduced divisor, all the
relative smooth-intersection and codimension assertions, and the regular-scheme strict normal
crossings boundary. Empty intersections and the empty boundary obey the same conventions. Uses:
def-sbc-smooth-morphisms, lem-weil-pbc-etale-composition-cancellation,
lem-sbc-smooth-relative-dimension-permanence, def-trf-strict-normal-crossings-boundary.
-/
theorem exists_gabber_global_snc_alteration
    (k : Type u) [Field k] (ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hchar : ℓ ≠ ringChar k)
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Z : Set X) (hZ : IsClosed Z) (hZnd : interior Z = ∅) :
    ∃ (K : Type u) (_ : Field K) (i : k →+* K),
      i.Finite ∧ Nat.Coprime (@Module.finrank k K _ _ i.toAlgebra.toModule) ℓ ∧
      ∃ (P : Scheme.{u}) (p : P ⟶ Spec (.of K)) (a : P ⟶ X),
        Smooth p ∧ IsQuasiProjective p ∧ IsProper a ∧ IsProjectiveBundle a ∧ Surjective a ∧
        a ≫ f = p ≫ Spec.map (CommRingCat.ofHom i) ∧
        (∀ (C : Set P), C ∈ irreducibleComponents P →
          ∀ η : P, IsGenericPoint η C →
            (∃ B ∈ irreducibleComponents X, IsGenericPoint (a η) B) ∧
            (a.residueFieldMap η).hom.Finite ∧
            Nat.Coprime
              (@Module.finrank (X.residueField (a η)) (P.residueField η) _ _
                (a.residueFieldMap η).hom.toAlgebra.toModule) ℓ) ∧
        ∃ D : P.IdealSheafData,
          D = ((Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩).comap a).radical ∧
          D.IsStrictNormalCrossingsDivisor p ∧ IsStrictNormalCrossingsBoundary D ∧
          IsRegularScheme P ∧
          ∀ x : P, ∃ (U : P.affineOpens) (hx : x ∈ U.1)
            (hR : IsNoetherianRing (P.presheaf.stalk x)) (t s : List (P.presheaf.stalk x)),
            @IsLocalRing.IsRegularSystemOfParameters (P.presheaf.stalk x) _ _ hR t ∧
            s.Sublist t ∧ s.Nodup ∧
            (D.ideal U).map (P.presheaf.germ U.1 x hx).hom = Ideal.span {s.prod} := by
  sorry

end AlgebraicGeometry
