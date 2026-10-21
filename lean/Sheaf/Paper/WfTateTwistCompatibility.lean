/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.WfTateTwist
public import Sheaf.Paper.PurIntegralTwistLineInverseImage
public import Mathlib.AlgebraicGeometry.Sites.Proetale
import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.Paper.WeilTensorWeil
import Sheaf.Algebra.Homology.SignedLineDerivedBaseChange
import Sheaf.Paper.InvertibleTensorScalarExtension
import Sheaf.Paper.CompletedLineTensorCoherence
import Sheaf.CategoryTheory.SemilinearScalarLocalization
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.PbcAutomorphismTransport
import Sheaf.Paper.PbcScalarExtension

/-! # Compatibility of Tate twists with finite scalar extension

Source: main-20261015, sec-algebraic-groups-lie-algebras/sk-p-cyclotomic,
Compatibility of the Tate twists (blueprint: lem-wf-tate-twist-compatibility).

The strict root arrow is `WfTateTwist.rationalLineMap D c X₀ E 1`. Its definition
uses the root-limit map below, extends integral coefficients and rationalizes.
The comparison asserted here is in the category of strict Weil pairs; its
naturality therefore includes the Frobenius commuting square on every component.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Functorial root pullback gives the strict Tate arrow, and every integer Tate
functor commutes with finite scalar extension as a functor on strict Weil pairs.
The first conjunct verifies the root-limit map defining the strict arrow against
all finite root projections; the coefficient and degree-zero rational transports
are the ones fixed in def-wf-tate-twist, not arbitrary line isomorphisms.
Source: main-20261015, lem-wf-tate-twist-compatibility
(blueprint: lem-wf-tate-twist-compatibility).

Proof:
1. Use the finite-field datum, $X_0$, $X$, the automorphism $\Phi_X$, and the raw rational
   coefficient categories of [def-wf-weil-category]. Put $R_E=\widehat{\mathcal O}_{E,X}$ and
   $L_E=\mathbf Z_\ell(1)_X\otimes_{(\mathbf Z_\ell)_X}(\mathcal O_E)_X$. By [lem-pur-twist-
   sheaf-locally-free], $L_E$ is a locally free rank-one $R_E$-module with its stated finite
   reductions. Let $L_E^{[m]}$ denote its signed tensor powers: unit for $m=0$, left-associated
   tensor powers for $m>0$, sheaf dual of the positive power for $m<0$. Locally these are all
   $R_E$. The characterization [lem-weil-pbc-integral-stratified-perfect-characterization]
   applies: $X$ is noetherian and finite-dimensional, being of finite type over $k$, and $\ell$
   is invertible. Thus each signed line is an object of the PBC integral category, using the
   single stratum $X$ and perfect model $\mathcal O_E[0]$. Tensoring any stratified perfect
   model for $K$ with such a line leaves that model unchanged on a refining cover, so it
   preserves this category. The same characterization identifies this category with the
   completed integral category in [def-coefficient-twists-detailed] over this $X$. Consequently
   its signed-line rationalizations are the $E(m)$ of [def-wf-tate-twist]; tensor with a line
   needs no additional completion, since the resulting object is already complete. This
   identifies the conventions here without replacing the rational category by discrete
   $E$-module sheaves.

2. Apply clauses 1--3 of [lem-pur-integral-twist-line-inverse-image] with $h=\Phi_X$ and $H=E$.
   They give the coefficient isomorphism $\alpha_{\Phi,E}:\Phi_X^{-1}R_E\cong R_E$, the root-
   limit isomorphism $\tau:\Phi_X^{-1}\mathbf Z_\ell(1)\cong\mathbf Z_\ell(1)$, and the
   semilinear isomorphism $\rho_E:\Phi_X^{-1}L_E\cong L_E$. Its $r$th root projection is the
   pulled-back root projection followed by the canonical roots-of-unity map; in particular the
   maps commute with $u\mapsto u^\ell$. Here $\Phi_X$ is a scheme automorphism, so [lem-weil-
   proetale-isomorphism-inverse-image] ensures that its inverse image really preserves the
   inverse limit. With the coefficient map $\alpha_{\Phi,E}$, $\rho_E$ is a linear isomorphism
   $P_E L_E\to L_E$. The transport $P_E$ is precisely the integral transport underlying the
   rationalized $\Phi_X^*$ of [def-wf-weil-category]. Rationalizing gives
   $\tau_{E,1}:\Phi_X^*E(1)\xrightarrow{\sim}E(1)$, the claimed strict Weil datum. No claim that
   inverse image along an arbitrary morphism preserves arbitrary limits is used.

3. For $m=0$ use the coefficient-unit comparison. For $m>0$ tensor the datum of step 2 in the
   left-associated order fixed by [def-wf-tate-twist], inserting the tensor-pullback comparison.
   For $m<0$ apply internal Hom to the positive power and the unit. The statements [lem-wf-
   tensor-weil] and [lem-wf-internal-hom-weil] give these Weil objects and their maps: the
   latter specifies $H(\varphi_K^{-1},\varphi_L)\alpha_{K,L}$, with the first argument
   contravariant. On integral lines apply [lem-pur-signed-line-derived-base-change] to the
   ringed-site equivalence $\Phi_X$ with coefficient isomorphism $\alpha_{\Phi,E}$ and line
   isomorphism $\rho_E$. The sites use the fixed small-site universe, the equivalence preserves
   finite limits and coverings, and step 1 gives locally free lines. Rebracket its right-
   associated powers to the left-associated powers here using canonical tensor associators: on a
   local line basis both identify the same ordered tensor of $m$ generators, and their dual maps
   identify its dual generator. A change of basis multiplies both positive generators by $u^m$
   and both dual generators by $u^{-m}$, so these identifications agree on overlaps and commute
   with transport. The negative datum is characterized by preservation of evaluation,
   equivalently $\mathcal Hom(\rho_{E,m}^{-1},\alpha_{\Phi,E})$ after the internal-Hom
   comparison. Thus these are precisely the signed Weil maps of [def-wf-tate-twist]. Only the
   asserted bifunctors and conjugation are used; no triangulation of fixed pairs is required.

4. Fix finite intermediate fields $E\subset F$. There is a canonical map
   $b_{FE}:L_E\otimes_{R_E}R_F\to L_F$ induced by $t\otimes a\mapsto t\otimes a$ on the
   coefficient inclusions. To check it is an isomorphism, use the compatible-root cover in [lem-
   pur-twist-sheaf-locally-free]. On that cover $\mathbf Z_\ell(1)$ has basis $e$ over
   $\widehat{\mathbf Z}_\ell$, and the same node identifies $R_H=\widehat{\mathbf
   Z}_\ell\otimes_{(\mathbf Z_\ell)_X}(\mathcal O_H)_X$ for $H=E,F$. Hence $b_{FE}$ is the
   multiplication isomorphism $R_E\otimes_{R_E}R_F\to R_F$ in these coordinates. Its inverse is
   $s\mapsto1\otimes s$. These formulas are unchanged by replacing $e$ by $ue$ for a unit $u$,
   so give the canonical isomorphism globally. For $E\subset F\subset H$ the two composite maps
   agree, since both send $(e\otimes a)\otimes b\otimes c$ to $e\otimes abc$; for repeated
   fields this is the unitor.

5. By [lem-sp-invertible-tensor-scalar-extension], $b_{FE}$ extends to canonical isomorphisms
   $b_{FE,m}:L_E^{[m]}\otimes_{R_E}R_F\cong L_F^{[m]}$ for every integer $m$, compatible with
   units, powers, duals and successive extensions. The integral functor underlying the
   transition $T_{F/E}$ of [def-wf-weil-category] is the ordinary derived change of rings
   $B_{FE}K=K\otimes^L_{R_E}R_F$ of [prop-weil-pbc-scalar-extension] (its $C_{F/E}$), restricted
   to constructible objects and rationalized, with $T_{E/E}=\mathrm{id}$ literally. Apply [lem-
   pur-completed-line-tensor-coherence] to a field chain with these $R_E,L_E,b_{FE}$; its
   hypotheses are exactly the line, unit and composition checks in steps 1 and 4. It gives
   natural isomorphisms $\bar\beta_{FE,m,K}:B_{FE}(K\otimes^L_{R_E}L_E^{[m]})\cong
   B_{FE}K\otimes^L_{R_F}L_F^{[m]}$, on a flat-term K-flat representative $(x\otimes l)\otimes
   s\mapsto(x\otimes s)\otimes b_{FE,m}(l\otimes1)$. This $\bar\beta$, for the functor $B_{FE}$
   actually used by the Weil transition, is the comparison of this proof; its conjugate $\beta$
   by the maps $\chi$ of that node is the same comparison for the quotient-tower extension
   $C_{FE}$ and is not needed. The same node states that each $T_{i,m}$ preserves derived
   completeness, so for complete $K$ the completion maps of the completed tensor of [def-wf-
   tensor-product] are isomorphisms $K\otimes^L L^{[m]}\cong K\mathbin{\widehat\otimes}^L
   L^{[m]}$; by step 1 these rationalize to $K(m)$, and both sides of $\bar\beta$ lie in the
   constructible categories. For $E=F$, $\bar\beta_{EE,m}$ followed by the multiplication
   isomorphisms $K\otimes_{R_E}R_E\cong K$ is the identity on pure tensors, matching
   $T_{E/E}=\mathrm{id}$.

6. The integral functors $B_{FE}T_{E,m}$ and $T_{F,m}B_{FE}$ are additive and semilinear over
   $\mathcal O_E\subset\mathcal O_F$. By [lem-pur-semilinear-scalar-localization], the integral
   comparisons $\bar\beta$ of step 5, composed with the completion isomorphisms there, give
   natural isomorphisms $\beta_{FE,m,K}:T_{F/E}(K(m))\xrightarrow{\sim}(T_{F/E}K)(m)$ in the raw
   rational categories. Its inverted-element condition holds: the image of $\varpi_E\ne0$ is
   invertible in $F=\mathcal O_F[1/\varpi_F]$. On a localized arrow $f/\varpi_E^r$ the extension
   is $T(f)/\varpi_E^r$, so the integral naturality equation, multiplied by this same
   denominator on both sides, is precisely rational naturality. The finite-extension and
   pullback comparisons here are those of [def-wf-weil-category]; its transition on Weil pairs
   is $(K,\varphi_K)\mapsto(TK,T(\varphi_K)\circ c_K)$, where $c:P_FT\cong TP_E$. It remains to
   check that $\beta$ commutes with these data; an underlying natural isomorphism alone would
   not finish the claim.

7. Clause 4 of [lem-pur-integral-twist-line-inverse-image] gives
   $\rho_F\Phi_X^{-1}(j_{EF})=j_{EF}\rho_E$ as well as the corresponding coefficient-ring
   equation. Balancing this equality with $R_F$ says exactly that $b_{FE,1}$ intertwines the
   degree-one Frobenius data with the scalar/pullback comparison. The signed-line naturality
   clause of [lem-pur-signed-line-derived-base-change] extends this square to $b_{FE,m}$ for
   every integer $m$. For negative $m$ it follows by the evaluation equation in that statement:
   compose either proposed square with evaluation and the already equal positive-power square;
   both become the coefficient-unit square, and the perfect evaluation of a line determines its
   dual map uniquely. Thus there is no use of scalar extension commuting with an arbitrary
   internal Hom.

8. The ordinary binary tensor comparison of [lem-weil-pbc-ringed-topoi-derived-tensor-pullback],
   for the identity geometric morphism and coefficient map $R_E\to R_F$, followed by $1\otimes
   b_{FE,m}$, is the $\bar\beta$ of step 5. Its compatibility with the transport comparison of
   [def-wf-automorphism-completed-transport] can be checked on flat-term K-flat representatives:
   both routes send $(x\otimes l)\otimes s$ to $(\Phi x\otimes\Phi s)\otimes\rho_{F,m}(\Phi
   b_{FE,m}(l\otimes1))$, with the equality supplied by step 7. These are equal maps of total
   tensor complexes, since all factors other than $x$ are in degree zero. The twist uses the
   completed tensor of [def-wf-tensor-product], whose completion maps are isomorphisms here
   (step 5). Its transport comparison $\mu$ is built by applying the inverse-image equivalence
   componentwise to the product and mapping-fiber terms of the Koszul completion model.
   Transport is an exact equivalence preserving products [lem-weil-proetale-isomorphism-inverse-
   image], and its coefficient map fixes $\varpi$; so it carries each tower projection, each
   transition and $1-t$ to the same maps, and carries the completion map, with zero shifted-
   product component, to the completion map. The just-checked ordinary square consequently
   commutes also after composing with the completion isomorphisms on both sides. This checks the
   comparison for the actual completed twist rather than inferring it from equality of all
   derived reductions.

9. Finally tensor the equal square of step 8 with the datum $\varphi_K$ of a Weil object.
   Bifunctor naturality and the definition of the tensor datum give
   $\beta_K\circ\varphi_{T(K(m))}=\varphi_{(TK)(m)}\circ P_F(\beta_K)$. After rationalization
   this remains an equality by [lem-pur-semilinear-scalar-localization]. By the morphism
   definition in [def-wf-weil-category], $\beta_K$ is therefore an isomorphism of strict Weil
   pairs, natural in $K$. The unit, positive-power and negative-evaluation normalizations of
   steps 3 and 5 identify these with the twists of [def-wf-tate-twist]. This proves that
   $(-)(m)$ commutes with finite scalar extension for all $m$, including $0$ and negative
   integers, together with the roots-of-unity arrow of step 2.
-/
theorem wf_tate_twist_compatibility
    (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (IsIso (FrobeniusCoefficientTwists.rootLineMap c.l (D.geometricFrobenius X₀).hom) ∧
      IsPurRootLimitComparison (D.geometricFrobenius X₀).hom c.l
        (FrobeniusCoefficientTwists.rootLineMap c.l (D.geometricFrobenius X₀).hom)) ∧
    ∀ (m : ℤ) (E F : Padic.FiniteCoefficientFields c.l c.Qbar) (h : E ≤ F),
      Nonempty (WfTateTwist.functor D c X₀ E m ⋙ weilScalarExtension D c X₀ h ≅
        weilScalarExtension D c X₀ h ⋙ WfTateTwist.functor D c X₀ F m) := by
  sorry

end WeilConjectures
