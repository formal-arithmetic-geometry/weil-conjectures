/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.InversePartialMapRestrictions
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Sheaf.TraceFormula.ReducedSchemeImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.RationalMapExtensionValuationPoint
import Sheaf.AlgebraicGeometry.NormalModificationCodimensionOne
import Sheaf.AlgebraicGeometry.SchemeProductDimension
import Sheaf.AlgebraicGeometry.LfpSmoothFlatBaseChange
import WeilConjectures.AlgebraicGeometry.Dimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.FiniteTypeDimensionFormula
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # A birational model with an invariant boundary divisor

Source: Milne, A Proof of the Barsotti-Chevalley Theorem (2013), Lemma 4.4
and proof of Proposition 4.1, pp. 8–9; Algebraic Groups (2017), Proposition 8.25.
(blueprint: lem-sfb-rational-boundary-divisor-model).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory TopologicalSpace

namespace AlgebraicGeometry

/-- A normal proper model with an integral invariant boundary divisor.

The maximal representative is encoded by `a.domain = a.toRationalMap.domain`.
The map `v` identifies `G × Y` inside this representative. The domain of `t` is
exactly the inverse image of `a.domain` on `G × D`. Its two projection equations
express `(g,x) ↦ (g⁻¹,a(g,x))` and the factorization through the closed subscheme D.
The self-isomorphism of W records both birationality and the involution identity.

Source: Milne (2013), Lemma 4.4 and Proposition 4.1 proof, pp. 8–9
(blueprint: lem-sfb-rational-boundary-divisor-model).

Proof plan, with the dependencies of the DAG:
1. Put $n=\dim X_0$. We will use the following dimension calculation on integral finite-type
$k$-schemes $Q$. Every nonempty open has dimension $\dim Q$ by
[lem-sc-integral-locally-algebraic-opens-dimension]; hence $\dim_qQ=\dim Q$ by
[def-kun-topological-dimension-at-point]. For an integral closed subset $C$ with generic point
$c$, [lem-kun-dimension-formula] and [lem-sc-closed-irreducible-dimension-trdeg] give
$\dim\mathcal O_{Q,c}=\dim Q-\dim C$. In particular a prime divisor has dimension $\dim Q-1$.
All schemes of finite type over $k$ are Noetherian by
[lem-weil-pbc-finite-type-over-noetherian]. The interpretation of codimension as this local-ring
dimension is [lem-sc-scheme-stalk-dimension-generalization-chains].
2. The dimension convention in [lem-sfb-scheme-product-dimension] agrees with topological
dimension by [lem-pc-scheme-dimension-local-rings]. For any normal integral $k$-variety $Q$,
[lem-sfb-algclosed-integral-product] makes $G\times_kQ$ integral. Its projection to $Q$ is
smooth: $Q\to\operatorname{Spec}k$ is flat by [lem-pc-flat-field], so
[lem-sfb-scheme-lfp-smooth-flat-base-change] applies to the smooth, locally finitely presented
structure map of $G$. Thus [lem-sfb-smooth-normal-ascent] makes the product normal. At each
codimension-one point its local ring is a DVR by [lem-sc-normal-dim1-dvr], hence a valuation
ring by [def-sc-discrete-valuation-ring]. For a proper target,
[lem-sfb-rational-map-extension-valuation-point] therefore puts every such point in the maximal
rational-map domain. Apply this to $Q=X_0$ and $\alpha_0$. Choose a reduced boundary component
$E_1$. Step 1 and [lem-sfb-scheme-product-dimension] show that $G\times_kE_1$ has codimension
one in $G\times_kX_0$. Consequently $T=\operatorname{Dom}(\alpha_0)\cap(G\times_kE_1)$ is a
nonempty dense open of this integral divisor, and a prime divisor in the normal integral source
$V=\operatorname{Dom}(\alpha_0)$.
3. The map $\alpha_0:V\to X_0$ is dominant since its restriction to $G\times_kY$ is the action
and contains $Y$ in its image. Its defined boundary points map into $E_0$: if $g\cdot z\in Y(k)$
for $z\notin Y(k)$, then $g^{-1}\cdot(g\cdot z)$ is defined in $Y$, while
[lem-sfb-rational-action-domain-laws] makes it equal to $z$, a contradiction. Closed points are
dense and $k$-rational by [lem-sc-lft-over-field-jacobson-space] and
[lem-weil-pbc-closed-point-residue-field-base], so the inverse image of the closed set $E_0$
contains all of $T$. Apply [lem-sfb-prime-divisor-image-extraction] to $(V,X_0,\alpha_0,T,E_0)$.
Obtain $b:X\to X_0$, an isomorphism over $Y$, normal integral proper $X$, and the integral
divisor $D\subset b^{-1}(E_0)$ of dimension $n-1$ which is the closure of the lifted image of
$T$. Since $b$ is an isomorphism over the nonempty open $Y$,
[lem-sc-integral-locally-algebraic-opens-dimension] gives $\dim X=\dim Y=\dim X_0=n$ already at
this stage.
4. Let $E_1^{\prime}$ be the strict transform of $E_1$ in $X$, namely the reduced closure of its
inverse image on an isomorphism open of $b$ containing its generic point. Such an open exists by
[lem-sfb-normal-modification-codimension-one], since the generic local ring of $E_1$ in normal
$X_0$ is a DVR by [lem-sc-normal-dim1-dvr]. The isomorphism on these dense opens identifies
$G\times E_1^{\prime}$ birationally with $G\times E_1$. Let $\alpha:G\times X\dashrightarrow X$
extend the action on $Y$, as in [lem-sfb-rational-action-domain-laws]. Its rational identity
$\alpha=b^{-1}\alpha_0(1\times b)$ follows by checking on $G\times Y$. Thus on a dense open
$R\subset G\times E_1^{\prime}$ its restriction is a dominant morphism $r:R\to D$, by the
image-closure assertion of the extraction lemma. The open
$U_D=\operatorname{Dom}(\alpha)\cap(G\times D)$ is dense in integral $G\times D$: step 2 applies
to normal $X$, since $D$ has codimension one by step 1.
5. The rational map $\lambda:G\times G\times E_1^{\prime}\dashrightarrow G\times D$,
$(g,h,z)\mapsto(g,r(h,z))$, is dominant. Indeed $r$ has scheme-theoretic image $D$ by
[lem-trf-reduced-scheme-image], and its base change along the flat projection $G\times D\to D$
has the same property by [lemma-nagata-dense-flat-pullback]; flatness follows from the smooth
projection of step 2 and [lem-pc-smooth-flat]. On a dense open of the triple product, both
$g\cdot(h\cdot z)$ and $(gh)\cdot z$ are defined: use dominance of $\lambda$ for the first and
the automorphism $(g,h,z)\mapsto(g,gh,z)$ for the second. The domain laws give $g\cdot(h\cdot
z)=(gh)\cdot z\in D$ on its $k$-points. These are dense by the two closed-point lemmas. Since
the image of this dense open under $\lambda$ is dense in $G\times D$, the closed inverse image
of $D$ under $\alpha|_{U_D}$ is all of $U_D$. The source is reduced by
[lem-sfb-algclosed-integral-product], so
[lem-weil-pbc-reduced-source-factors-through-closed-subscheme] gives the required
scheme-theoretic factorization through $D$.
6. Now $\tau(g,x)=(g^{-1},g\cdot x)$ is a rational self-map of integral $G\times D$. It is
dominant, a point not supplied by its formula alone: on the dense triple-product open of step 5,
$\tau\lambda(g,h,z)=(g^{-1},r(gh,z))$. The latter is dominant, since it is $\lambda$ precomposed
with the automorphism $(g,h,z)\mapsto(g^{-1},gh,z)$, whose inverse is
$(a,b,z)\mapsto(a^{-1},ab,z)$. Thus $\tau$ is dominant. Its square is defined on a dense open.
At its $k$-points, the composition and unit identities of [lem-sfb-rational-action-domain-laws]
give $g^{-1}\cdot(g\cdot x)=e\cdot x=x$. The closed points are dense and $k$-rational by
[lem-sc-lft-over-field-jacobson-space] and [lem-weil-pbc-closed-point-residue-field-base]. Apply
[lem-sfb-relative-separated-dominant-ext] to their disjoint union mapping densely into the
reduced open source; this makes $\tau^2=1$ an equality of rational maps. The two coordinates
agree, since inversion squared is the identity on $G$.
7. Apply [lem-sbc-inverse-partial-map-restrictions] to $\tau$ and itself. It gives an
isomorphism $f:A\to B$ on dense opens with $A\subset U_D$ and $f$ the restriction of $\tau$; its
statement does not require $B\subset U_D$. Set $B_0=B\cap U_D$ and $A_0=f^{-1}(B_0)$. These are
dense nonempty opens and $f:A_0\to B_0$ is an isomorphism. Its inverse agrees with $\tau|_{B_0}$
on a dense open, because $\tau^2=1$ as a rational map. By
[lem-sfb-relative-separated-dominant-ext] the agreement holds everywhere on reduced $B_0$. Now
set $W=A_0\cap B_0\subset U_D$. For $x\in W$, its image under $\tau$ lies in $B_0$ using $x\in
A_0$, and in $A_0$ using $x\in B_0$ and the inverse description. Thus $\tau:W\to W$ is an
isomorphism with square the identity. The open $W$ is nonempty by irreducibility of $G\times D$.
Finally $b$ identifies nonempty opens of integral $X,X_0$, so
[lem-sc-integral-locally-algebraic-opens-dimension] gives $\dim X=\dim X_0=n$.
-/
theorem exists_rational_boundary_divisor_model
    (k : Type u) [Field k] [IsAlgClosed k]
    (G X₀ Y : Over (Spec (.of k))) [GrpObj G] [ModObj G Y]
    [IsIntegral G.left] [Smooth G.hom] [IsSeparated G.hom]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [IsIntegral X₀.left] [IsProper X₀.hom]
    (hX₀ : ∀ x : X₀.left, IsIntegrallyClosed (X₀.left.presheaf.stalk x))
    [Smooth Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (j : Y ⟶ X₀) [IsOpenImmersion j.left] (hj : DenseRange j.left)
    (hE : (Set.range j.left)ᶜ.Nonempty)
    (hcodim : ∀ C ∈ irreducibleComponents (↥((Set.range j.left)ᶜ)),
      ∀ η : X₀.left, IsGenericPoint η (Subtype.val '' C) →
        ringKrullDim (X₀.left.presheaf.stalk η) = 1) :
    ∃ (X : Over (Spec (.of k))) (b : X ⟶ X₀) (jX : Y ⟶ X),
      IsIntegral X.left ∧ IsProper X.hom ∧
      (∀ x : X.left, IsIntegrallyClosed (X.left.presheaf.stalk x)) ∧
      IsProper b.left ∧ IsOpenImmersion jX.left ∧ DenseRange jX.left ∧
      IsPullback jX.left (𝟙 Y.left) b.left j.left ∧
      topologicalKrullDim X.left = topologicalKrullDim X₀.left ∧
      ∃ (D : Over (Spec (.of k))) (d : D ⟶ X),
        IsIntegral D.left ∧ IsClosedImmersion d.left ∧
        Set.range d.left ⊆ (Set.range jX.left)ᶜ ∧
        topologicalKrullDim D.left + 1 = topologicalKrullDim X₀.left ∧
        ∃ (a : (G ⊗ X).left.PartialMap X.left)
          (v : (G ⊗ Y).left ⟶ a.domain.toScheme),
          a.domain = a.toRationalMap.domain ∧
          a.hom ≫ X.hom = a.domain.ι ≫ (G ⊗ X).hom ∧
          v ≫ a.domain.ι = (G ◁ jX).left ∧
          v ≫ a.hom = (ModObj.smul (M := G) (X := Y) ≫ jX).left ∧
          ∃ (t : (G ⊗ D).left.PartialMap (G ⊗ D).left)
            (m : t.domain.toScheme ⟶ a.domain.toScheme),
            t.domain = (G ◁ d).left ⁻¹ᵁ a.domain ∧
            m ≫ a.domain.ι = t.domain.ι ≫ (G ◁ d).left ∧
            t.hom ≫ (snd G D).left ≫ d.left = m ≫ a.hom ∧
            t.hom ≫ (fst G D).left =
              t.domain.ι ≫ (fst G D).left ≫ (GrpObj.inv (X := G)).left ∧
            ∃ (W : (G ⊗ D).left.Opens) (hW : W ≤ t.domain)
              (f : W.toScheme ≅ W.toScheme),
              (W : Set (G ⊗ D).left).Nonempty ∧
              f.hom ≫ W.ι = (G ⊗ D).left.homOfLE hW ≫ t.hom ∧
              f.hom ≫ f.hom = 𝟙 W.toScheme := by
  sorry

end AlgebraicGeometry
