/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.StalkAut
public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.FiniteOverProjective
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.RingTheory.PolynomialDistinctLinearCRT
import WeilConjectures.AlgebraicGeometry.Morphisms.FlatFibreEtaleNeighbourhoods
import WeilConjectures.AlgebraicGeometry.GenericFibreIsoSpreadBaseOpen
import WeilConjectures.FieldTheory.FiniteGaloisReceivingSeparableExtensions
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension
import WeilConjectures.AlgebraicGeometry.SpreadFiniteSeparableExtension
import Sheaf.AlgebraicGeometry.FinitePresentationOfFiniteLocallyNoetherian

import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Flat.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.FieldTheory.SeparableDegree

/-! # Equivariant finite covers splitting prescribed residue schemes

Source: de Jong, Families of curves and alterations (1997), Lemma 5.6, p. 614,
and Situation 5.3, p. 613. Finite etale schemes are split by splitting their
finite separable residue algebras; normalize the resulting cover.
(blueprint: lem-sfb-equivariant-finite-residue-domination).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- A finite equivariant generically etale cover splits each prescribed finite etale
residue scheme at every point above its specified base point. The actions may have
kernels. The generic-stalk map fixes the inclusion of function fields, and the
splitting isomorphism commutes with the projection to the new residue spectrum.

Source: de Jong (1997), Lemma 5.6 and Situation 5.3, pp. 613--614.
(blueprint: lem-sfb-equivariant-finite-residue-domination).

Proof:

1. If the point list is empty, take $W=S$, $J=H$, $\rho=\mathrm{id}$ and $a=\mathrm{id}$; all
assertions follow directly, including $N=1$ and $k(W)^N=k(S)$. Hence assume the list is nonempty.
Put $K=k(S)$ and $F_i=\kappa(s_i)$. A field is Noetherian, since its only ideals are zero and the
whole field. Finite type over $k$ therefore makes $S$ Noetherian. If $s_i$ corresponds to
$\mathfrak p_i$ on an affine chart $\operatorname{Spec}A_i$, then $R_i=\mathcal
O_{S,s_i}=(A_i)_{\mathfrak p_i}$ is a Noetherian local domain with fraction field $K$ and residue
field $F_i$.
Uses: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-localization-noetherian, def-sc-
function-field.

2. Since $E_i\to\operatorname{Spec}F_i$ is finite it is affine, say $E_i=\operatorname{Spec}D_i$.
The etale field-algebra decomposition writes $D_i=\prod_j F_{ij}$ with each $F_{ij}/F_i$ finite
separable. Choose a finite Galois extension $L_i/F_i$ receiving all these fields. Choose a
primitive element $\alpha_i$ of $L_i/F_i$, with monic separable minimal polynomial $q_i$. If $E_i$
is empty, the product is empty and we can choose $L_i=F_i$, $\alpha_i=0$, $q_i=T$. The minimal-
polynomial quotient identifies $F_i[T]/(q_i)$ with $L_i$.
Uses: def-weil-finite-integral-morphism, lem-weil-pbc-etale-algebra-over-field-product, lem-weil-
pbc-finite-galois-receiving-separable-extensions, lem-weil-pbc-finite-separable-extension-
primitive-element, lem-weil-pbc-minimal-polynomial-quotient-field-iso.

3. Lift the finitely many nonleading coefficients of $q_i$ through the surjection $R_i\to F_i$,
keeping leading coefficient $1$, to obtain $f_i\in R_i[T]$. Set $C_i=R_i[T]/(f_i)$ and
$u_i:\operatorname{Spec}C_i\to\operatorname{Spec}R_i$. The monic quotient theorem gives a finite
free $R_i$-basis $1,T,\ldots,T^{d_i-1}$, where $d_i=\deg q_i\ge1$, and identifies its closed fibre
with $\operatorname{Spec}L_i$. Finite free modules are flat, and the affine flatness criterion
makes $u_i$ flat. It is finite and, since $R_i$ is Noetherian, finitely presented. Its closed
fibre is etale, because $L_i/F_i$ is finite separable.
Uses: lem-weil-pbc-monic-quotient-free, lem-sc-affine-standard-cover-finite-free-local-fp-flat,
lem-weil-pbc-flat-ring-map-iff-flat-affine, pqf-lem-finite-fp-locnoeth, lem-weil-pbc-finite-
separable-extension-etale.

4. Apply the flat, locally finitely presented fibre criterion at the closed point of
$\operatorname{Spec}R_i$. Every point of the closed fibre has an open neighbourhood on which $u_i$
is etale. Let $V_i$ be the union of these neighbourhoods and $Z_i=\operatorname{Spec}C_i\setminus
V_i$. The finite-map closedness theorem makes $u_i(Z_i)$ closed. It misses the closed point of the
local spectrum, and hence is empty: every nonempty closed subset $V(I)$ of a local spectrum
contains its maximal ideal. Thus $Z_i=\varnothing$, and etaleness local on the source shows that
$u_i$ is etale everywhere. Base change to $K$ and the etale field-algebra decomposition now give
$K[T]/(f_i)=C_i\otimes_{R_i}K\cong\prod_j K_{ij}$, with $K_{ij}/K$ finite separable. The product
is nonempty, since its $K$-dimension is $d_i\ge1$.
Uses: lem-sbc-flat-fibre-etale-neighbourhoods, lem-weil-pbc-finite-closed-map-finite-fibres, lem-
weil-pbc-etale-local-on-source, lem-weil-pbc-etale-ring-base-change, lem-weil-pbc-etale-algebra-
over-field-product.

5. Write $A_h=(h^{-1})^*$ for the induced left field action of $H$ on $K$, let $H_0$ be its image
in $\operatorname{Aut}(K)$ and put $F=K^{H_0}$. Apply the finite faithful field-action theorem to
$H_0$, giving $K/F$ finite Galois. Each $K_{ij}/F$ is finite separable: separability follows by
the tower theorem, and products of finite spanning sets span the composite tower. Apply the
finite-Galois-receiving theorem over $F$ to the finite family consisting of $K$ and all $K_{ij}$.
Obtain a finite Galois field $M/F$ and identify $K$ with its chosen embedded copy; view each
$K_{ij}$ as a $K$-subfield using its compatible embedding from the theorem applied to their
$F$-extensions, after the adjustment in the next step.
Uses: lem-wf-finite-field-action-fixed-degree, lem-zl-separable-permanence, lem-weil-pbc-finite-
galois-receiving-separable-extensions.

6. The embeddings into $M$ obtained in Step 5 initially need only be $F$-linear. For each $K_{ij}$
its restriction on $K$ is an $F$-embedding whose image is $K$: $K/F$ is normal, so every conjugate
of an element of $K$ is still in $K$, and injectivity plus finite dimension makes the restricted
map onto $K$. Lift the inverse of this restriction to an $F$-automorphism of $M$ by normal-
intermediate-isomorphism lifting, and compose. This gives the promised $K$-embedding
$K_{ij}\hookrightarrow M$. The extension $M/K$ is normal by normality over an intermediate field,
finite because an $F$-spanning set also spans over $K$, and separable because every minimal
polynomial over $K$ divides the separable minimal polynomial over $F$.
Uses: lem-sfb-normal-intermediate-isomorphism-lifts, lem-weil-pbc-normal-extension-normal-over-
intermediate.

7. Every $f_i$ splits in $M[T]$. Indeed, let $g\in K[T]$ be a monic irreducible factor of $f_i$.
The quotient field $K[T]/(g)$ is a field quotient of $K[T]/(f_i)=\prod_jK_{ij}$. A map from a
finite product to a field sends exactly one coordinate idempotent to $1$ and all others to $0$, so
this quotient is isomorphic to some $K_{ij}$. Its class of $T$ is consequently a root of $g$ in
$M$. Normality of $M/K$ says precisely that the minimal polynomial $g$ of this root splits in $M$.
Factoring $f_i$ into irreducibles over the field $K$ then shows that
$f_i=\prod_{\nu=1}^{d_i}(T-\beta_{i\nu})$ for elements $\beta_{i\nu}\in M$.
Uses: lem-weil-pbc-normal-extension-normal-over-intermediate.

8. Define $J=\{(h,\sigma)\in H\times\operatorname{Aut}_F(M):\sigma|_K=A_h\}$ with componentwise
multiplication, and $\rho(h,\sigma)=h$. The restriction condition is closed under multiplication
and inverse. The finite Galois fixed-field theorem makes $\operatorname{Aut}_F(M)$ finite, so $J$
is finite. For each $h$, normal-intermediate-isomorphism lifting extends $A_h:K\to K$ to an
$F$-automorphism of $M$, proving that $\rho$ is onto. Its kernel is exactly
$\{(1,\sigma):\sigma\in\operatorname{Aut}_K(M)\}$. Since $M/K$ is finite Galois, the same fixed-
field theorem gives $M^{\ker\rho}=K$. Keeping pairs retains the original, possibly nonfaithful,
group $H$.
Uses: lem-weil-pbc-finite-galois-fixed-field, lem-sfb-normal-intermediate-isomorphism-lifts.

9. Let $a:W\to S$ be the normalization of $S$ in $M$. Apply normalization in a finite extension of
a residue field to the generic point of $S$. It gives that $W$ is normal integral and has function
field $M$. Since $S$ is integral of finite type over the field $k$ and $M/K$ is finite, finiteness
of normalization makes $a$ finite. On every nonempty affine chart $\operatorname{Spec}A\subset S$,
write its inverse image as $\operatorname{Spec}B$, where $B$ is the integral closure of $A$ in
$M$. Localizing at $A\setminus\{0\}$ gives the integral closure of $K$ in the algebraic extension
$M$, which is $M$ itself; thus $W_K=\operatorname{Spec}M$.
Uses: def-fin-normalization-extension, lem-weil-pbc-normalization-in-residue-field-extension, lem-
fin-normalization-extension-finite.

10. The finite-over-projective theorem applies to $W\to S\to\operatorname{Spec}k$: the base
$\operatorname{Spec}k$ is affine Noetherian. Hence $W$ is projective in the required global
closed-embedding convention. Projective implies proper, and proper includes finite type, so $W$ is
finite type over $k$. The finite-map closedness theorem says that $a(W)$ is closed in $S$; it
contains the generic point by Step 9 and therefore is all of integral $S$. Thus $a$ is surjective.
Uses: lem-fin-finite-over-projective, lem-kun-projective-implies-proper, def-weil-proper-morphism,
lem-weil-pbc-finite-closed-map-finite-fibres.

11. For $j=(h,\sigma)\in J$ the generic geometric action is $\operatorname{Spec}(\sigma^{-1})$,
covering the given geometric action of $h$ on $S$. It extends to $W$ on the integral-closure
charts of Step 9. An isomorphism of base charts together with $\sigma^{-1}$ carries integral
elements to integral elements, since it sends a monic equation to a monic equation. Applying the
inverse shows that it is an isomorphism of their integral closures. These maps commute with
localization and hence glue. Their composites are the prescribed composites on the subrings of
$M$, proving the group law. This produces a $J$-action and $a\circ j=\rho(j)\circ a$. Its scalar
action on $k$ is exactly the original action through $\rho$. The generic field action has image
$\operatorname{Aut}_K(M)$ on $N$, so Step 8 proves $k(W)^N=k(S)$.
Uses: def-fin-normalization-extension.

12. To verify generically etale in the scheme-theoretic sense, choose a nonempty affine
$U=\operatorname{Spec}A\subset S$. The finite separable extension $M/K$ spreads to a finite etale
domain algebra $A'$ over $A[c^{-1}]$ for some nonzero $c\in A$, with fraction field $M$. The
affine schemes $W\times_SU_c$ and $\operatorname{Spec}A'$ have the same generic fibre
$\operatorname{Spec}M$. Both are finitely presented over $U_c$: the former by finite-over-locally-
Noetherian finite presentation, the latter by etaleness and finiteness (or that same finite-
presentation theorem). Generic-fibre isomorphism spreading therefore supplies an isomorphism over
a smaller nonempty open $V\subset U_c$. The restriction of $a$ over $V$ is etale, since its
isomorphic model is etale and etaleness is preserved by base change. Integral $S$ makes $V$ dense.
Thus $a$ is etale over a dense open of $S$.
Uses: lem-weil-pbc-spread-finite-separable-extension, pqf-lem-finite-fp-locnoeth, lem-sbc-generic-
fibre-iso-spread-base-open, lem-weil-pbc-etale-scheme-base-change.

13. Fix $i$ and any $w\in W$ above $s_i$. The integral closure of $R_i=\mathcal O_{S,s_i}$ in $M$
is obtained by localizing the integral-closure chart $B$ at $A\setminus\mathfrak p_i$, by the
localization clause of normalization. Every $\beta_{i\nu}$ of Step 7 belongs to this ring, because
it satisfies the monic equation $f_i(\beta_{i\nu})=0$. Map this ring to $\mathcal O_{W,w}$ and
then to $\kappa(w)$. The factorization in Step 7 reduces to
$q_i(T)=\prod_{\nu=1}^{d_i}(T-\overline\beta_{i\nu})$ in $\kappa(w)[T]$. In particular $q_i$ has a
root in $\kappa(w)$. Evaluation at it and $F_i[T]/(q_i)\cong L_i$ yield an $F_i$-embedding
$L_i\hookrightarrow\kappa(w)$: the unital map from the field $L_i$ is injective. This argument
uses no selection of a distinguished $w$ and proves the assertion for every point above $s_i$.
Uses: def-fin-normalization-extension, def-weil-residue-field, lem-weil-pbc-minimal-polynomial-
quotient-field-iso.

14. For each component field $F_{ij}$ of $D_i$, choose a primitive element with monic separable
minimal polynomial $p_{ij}$ over $F_i$. Its chosen embedding into the normal extension $L_i/F_i$
makes $p_{ij}$ split there; normality here applies directly to the minimal polynomial of that
embedded element. Under the embedding of Step 13 it also splits in $\kappa(w)$. Its roots are
distinct: the Bezout identity between $p_{ij}$ and $p_{ij}'$ remains an identity after coefficient
extension, and rules out a repeated root. The minimal-polynomial quotient and evaluation Chinese
remainder isomorphism give $F_{ij}\otimes_{F_i}\kappa(w)\cong\kappa(w)[T]/(p_{ij})\cong\prod_{\deg
p_{ij}}\kappa(w)$. The first isomorphism sends $\theta\otimes1$ to the class of $T$ and $1\otimes
t$ to $t$; its inverse sends $T$ to $\theta\otimes1$ and scalars to $1\otimes t$. The sole
relation $p_{ij}(\theta)=0$ makes both maps well-defined, and they are inverse on their algebra
generators. Tensoring the finite product $D_i=\prod_jF_{ij}$ distributes over it (send
$(x_j)\otimes t$ to $(x_j\otimes t)$, with inverse the sum of the coordinate inclusions). Taking
spectra gives the required finite disjoint union of rational points. The empty product gives the
empty scheme. Together with Steps 8--12 this proves every clause.
Uses: lem-weil-pbc-finite-separable-extension-primitive-element, lem-weil-pbc-minimal-polynomial-
quotient-field-iso, lem-pc-polynomial-quotient-distinct-linear-crt.
-/
theorem exists_equivariant_finite_residue_domination
    (k : Type u) [Field k] (S : Scheme.{u})
    (pS : S ⟶ Spec (.of k)) [IsIntegral S] [IsHProjective pS]
    [LocallyOfFiniteType pS] [QuasiCompact pS]
    (hnormal : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (H : Type v) [Group H] [Finite H]
    (σk : H →* (k ≃+* k)) (σS : H →* Aut S)
    (hsemilinear : ∀ h : H, (σS h).hom ≫ pS =
      pS ≫ Spec.map (CommRingCat.ofHom (σk h⁻¹).toRingHom))
    (r : ℕ) (s : Fin r → S) (E : Fin r → Scheme.{u})
    (e : ∀ i : Fin r, E i ⟶ Spec (S.residueField (s i)))
    [hefinite : ∀ i : Fin r, IsFinite (e i)] [heetale : ∀ i : Fin r, Etale (e i)] :
    ∃ (J : Type (max u v)) (_ : Group J) (_ : Finite J) (ρ : J →* H),
      Function.Surjective ρ ∧
      ∃ (W : Scheme.{u}) (_ : IsIntegral W) (pW : W ⟶ Spec (.of k))
        (σW : J →* Aut W) (a : W ⟶ S),
        IsHProjective pW ∧ LocallyOfFiniteType pW ∧ QuasiCompact pW ∧
        (∀ w : W, IsDomain (W.presheaf.stalk w) ∧
          IsIntegrallyClosed (W.presheaf.stalk w)) ∧
        a ≫ pS = pW ∧ IsFinite a ∧ Surjective a ∧
        (∃ U : S.Opens, Dense (U : Set S) ∧ Etale (a ∣_ U)) ∧
        (∀ j : J, (σW j).hom ≫ pW =
          pW ≫ Spec.map (CommRingCat.ofHom (σk (ρ j⁻¹)).toRingHom)) ∧
        (∀ j : J, (σW j).hom ≫ a = a ≫ (σS (ρ j)).hom) ∧
        (∃ ha : a (genericPoint W) = genericPoint S,
          ∀ z : W.functionField,
            (∃ b : S.functionField,
              (S.presheaf.stalkSpecializes (specializes_of_eq ha) ≫
                a.stalkMap (genericPoint W)).hom b = z) ↔
              ∀ j : ρ.ker, (Scheme.functionFieldAut (σW j.val)).hom z = z) ∧
        (∀ (i : Fin r) (w : W) (hw : a w = s i),
          ∃ (n : ℕ)
            (ι : pullback (e i)
              (Spec.map (eqToHom (congrArg S.residueField hw.symm) ≫ a.residueFieldMap w)) ≅
              ∐ (fun _ : Fin n ↦ Spec (W.residueField w))),
            ι.hom ≫ Sigma.desc (fun _ : Fin n ↦ 𝟙 (Spec (W.residueField w))) =
              pullback.snd (e i)
                (Spec.map (eqToHom (congrArg S.residueField hw.symm) ≫
                  a.residueFieldMap w))) := by
  sorry

end AlgebraicGeometry
