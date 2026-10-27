/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.StalkAut
public import Sheaf.FieldTheory.FieldTower
public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Sheaf.AlgebraicGeometry.FiniteOverProjective
import Sheaf.FieldTheory.AlgebraicSeparableSmooth
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.DimZeroFiniteOverField
import WeilConjectures.AlgebraicGeometry.GlobalSectionsProper
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import Sheaf.AlgebraicGeometry.ProperGeometricallyReducedGlobalSectionsSeparable
import Sheaf.AlgebraicGeometry.NormalSteinConstantField
import Sheaf.AlgebraicGeometry.NormalTopologicallyNoetherianComponents
import Sheaf.AlgebraicGeometry.NormalizationInseparableBaseChange
import Sheaf.AlgebraicGeometry.NormalizationGeonormalInsep
import Sheaf.AlgebraicGeometry.NormalizationProjectiveComponents
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Etale.Field
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Equivariant regularization of the constants of a normal alteration

Source: de Jong, Families of curves and alterations (1997), Lemma 5.5 and its proof,
printed p. 614; Stacks Project, Tags 0BXT and 03H0
(blueprint: lem-sfb-normal-alteration-constant-regularization).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- Equivariant constant-field regularization, allowing nonfaithful semilinear actions.
Source: de Jong, Lemma 5.5 and proof, p. 614; Stacks Tags 0BXT and 03H0
(blueprint: lem-sfb-normal-alteration-constant-regularization).

The field inclusions are the generic-stalk maps. The equation for the e-algebra structure
identifies its spectrum map with the structure map at the generic point. Scalar towers
specify the composite inclusions, and the range equality identifies precisely the constants
algebraic over k. Normality is stated on local rings. The zero-dimensional conclusion uses
the actual structure map, so its resulting isomorphism with Spec e is equivariant.

Proof (the node's sixteen steps):
1. Apply [lem-weil-pbc-normalization-geonormal-insep] to $S$. It gives a finite purely inseparable
   extension $l_0/k$ such that the normalization $N_0$ of $S_{l_0}$ is geometrically normal over
   $l_0$. Take a perfect purely inseparable overfield $P/k$ from [lem-weil-pbc-perfect-purely-
   inseparable-overfield]. Embed $l_0$ in $P$: in characteristic $p$, an element $a$ with
   $a^{p^n}=c\in k$ maps to the unique $p^n$-th root of $c$ in $P$. Uniqueness makes this
   independent of $n$ and compatible with field operations. In characteristic zero all these
   extensions equal $k$.
   Uses: lem-weil-pbc-normalization-geonormal-insep, lem-weil-pbc-perfect-purely-inseparable-
   overfield.
2. Each automorphism $h$ of $k$ extends uniquely to $P$ by $h(a)^{p^n}=h(a^{p^n})$; root
   uniqueness verifies preservation of sums, products and the composition law. Thus $H$, and hence
   $J$ through $\rho$, acts on $P$. Choose finitely many field generators $a_1,\ldots,a_r$ of
   $l_0/k$ and let $l$ be generated over $k$ by $j(a_i)$ for every $j\in J$ and every $i$. It is
   $J$-stable. Each of these finitely many elements has a $p$-power in $k$, so adjoining them
   successively gives a finite purely inseparable extension $l/k$ containing $l_0$. The same power
   condition proves that $l/l_0$ is finite purely inseparable. Also $A$ fixes $l$ pointwise: it
   fixes $k$, and all the relevant roots are unique. In characteristic zero take $l=k$.
   Uses: def-weil-pbc-finite-purely-inseparable-extension.
3. Let $B$ be the componentwise normalization of $S_l$. The reduction of $S_l$ is integral by
   [lem-trf-normalization-inseparable-base-change]; that lemma identifies $B$ with
   $N_0\times_{l_0}l$ and makes it geometrically normal over $l$. In particular $B$ is nonempty,
   normal and integral. The embedding of $S$ base-changes to one of $S_l$ by [lem-pc-projective-
   base-change]; its quasi-compactness follows from finite type, as required by [def-pc-
   projective-morphism]. Apply [lem-weil-pbc-normalization-projective-components] to $S_l$: there
   is just one normalized component, $n:B\to S_l$ is finite and surjective, and $B$ is projective
   and proper over $l$. Properness includes finite type.
   Uses: lem-trf-normalization-inseparable-base-change, lem-pc-projective-base-change, lem-weil-
   pbc-normalization-projective-components, def-pc-projective-morphism.
4. Write $\pi:S_l\to S$ for the projection and $q=\pi\circ n$. In characteristic zero $l=k$, so
   $B$ is the normalization of $S$, and normality of $S$ with [lem-sc-normalization-over-normal-
   locus] for $U=S$ makes $q$ an isomorphism. In characteristic $p$ choose $N$ with
   $\lambda^{p^N}\in k$ for all $\lambda\in l$; this holds for the finitely many generators of the
   finite purely inseparable $l/k$ [def-weil-pbc-finite-purely-inseparable-extension], hence for
   all of $l$ since Frobenius is additive. Let $\operatorname{Spec}C\subseteq S$ be a nonempty
   affine open, $R=(C\otimes_kl)_{\mathrm{red}}$, a domain by step 3, and
   $q^{-1}(\operatorname{Spec}C)=\operatorname{Spec}D$, where $D$ is the integral closure of $R$
   in $\operatorname{Frac}R$ by [def-sc-normalization]. Since $S$ is normal, $C$ is an integrally
   closed domain [def-weil-pbc-normal-ring]; $C\to D$ is injective because $C\to C\otimes_kl$ is.
   For $a=\sum c_i\otimes\lambda_i$ one has $a^{p^N}=\sum c_i^{p^N}\lambda_i^{p^N}\in C$. Hence
   every $d=x/y\in D$ has $d^{p^N}=x^{p^N}/y^{p^N}\in K=\operatorname{Frac}C$, and the $p^N$-th
   power of a monic equation of $d$ over $R$ is a monic equation of $d^{p^N}$ over $C$; so
   $d^{p^N}\in C$. Thus a prime $Q$ of $D$ equals $\{d:d^{p^N}\in Q\cap C\}$, and for every prime
   $P$ of $C$ the set $\{d:d^{p^N}\in P\}$ is a prime of $D$ (additivity of Frobenius) meeting $C$
   in $P$. Residue fields of $D$ have $p^N$-th powers in those of $C$. Every point of $S$ lies in
   such a chart, so $q$ is surjective [def-weil-surjective-morphism], injective, with purely
   inseparable residue field extensions: by [def-weil-radicial-morphism] it is radicial,
   equivalently universally injective.
   Uses: lem-sc-normalization-over-normal-locus, def-weil-pbc-finite-purely-inseparable-extension,
   def-sc-normalization, def-weil-pbc-normal-ring, def-weil-surjective-morphism, def-weil-
   radicial-morphism.
5. The finite field map $k\to l$ gives a finite spectrum map by [lem-weil-pbc-spec-finite-ring-
   map-finite]. Its base change $\pi$ is finite by [lem-weil-pbc-finite-morphism-permanence](a),
   and [lem-weil-pbc-finite-composition] makes $q$ finite. Step 4 gives every element of
   $F=k(B)=\operatorname{Frac}D$ a $p^N$-th power in $K=k(S)$, and $F=K$ in characteristic zero;
   so $F/K$ is purely inseparable [def-weil-pbc-finite-purely-inseparable-extension]. To verify
   finiteness, choose a nonempty affine $\operatorname{Spec}C\subseteq S$; its inverse image is
   $\operatorname{Spec}D$, with $D$ a finite $C$-module. Both rings are domains, and $C\to D$ is
   injective by dominance. Now [lem-trf-finite-domain-fraction-degree] and [lem-sc-integral-
   function-field-affine-fraction] give $[F:K]<\infty$.
   Uses: lem-weil-pbc-spec-finite-ring-map-finite, lem-weil-pbc-finite-morphism-permanence, lem-
   weil-pbc-finite-composition, lem-trf-finite-domain-fraction-degree, lem-sc-integral-function-
   field-affine-fraction, def-weil-pbc-finite-purely-inseparable-extension.
6. The compatible actions on $S$ and $l$ give a $J$-action on $S_l$, hence on its canonical
   reduction $T=(S_l)_{\mathrm{red}}$. Lift it to $B$ using [def-sc-normalization]. An
   automorphism takes an affine domain $C$ of $T$ isomorphically onto the corresponding affine
   domain, sends a fraction $u/v$ to $j(u)/j(v)$, and takes monic equations to monic equations. It
   therefore takes the integral closure onto the integral closure, with inverse given by $j^{-1}$.
   These maps glue in the sheaf of integral closures. Their formulas on fractions give the group
   law, so $n$, $\pi$ and $q$ are $J$-equivariant. The induced action on $F$ restricts to the
   original actions on $K$ and $l$. No faithfulness is required.
   Uses: def-sc-normalization.
7. The finite-type hypothesis makes $S$ quasi-compact, so its given projective embedding satisfies
   [def-pc-projective-morphism]. Apply [lem-fin-finite-over-projective] over the affine Noetherian
   base $\operatorname{Spec}k$ to $S\to\operatorname{Spec}k$ and the finite $q:B\to S$. This
   supplies a closed immersion $B\hookrightarrow\mathbf P^N_k$. Thus $B$ is projective over $k$
   and proper by [lem-kun-projective-implies-proper]. It remains normal integral as established in
   step 3.
   Uses: def-pc-projective-morphism, lem-fin-finite-over-projective, lem-kun-projective-implies-
   proper.
8. Apply [lem-sfb-normal-stein-constant-field] to $B\to\operatorname{Spec}k$, which is proper
   dominant with normal integral finite-type source. Its canonical factorization is
   $B\to\operatorname{Spec}e\to\operatorname{Spec}k$, where $e=\Gamma(B,\mathcal O_B)$. Inside
   $F$, this is exactly the field of elements algebraic over $k$. In particular $e/k$ is finite,
   $e$ is algebraically closed in $F$, and $B\to\operatorname{Spec}e$ is proper with geometrically
   connected fibres. The $l$-structure embeds $l$ into these global sections. Also $e/l$ is
   finite: a finite $k$-spanning family of $e$ spans it over the intermediate field $l$.
   Uses: lem-sfb-normal-stein-constant-field.
9. The action on $B$ acts on $e=\Gamma(B,\mathcal O_B)$ by $j(a)=(j^{-1})^*a$, the left-action
   convention. This is the restriction of the action on the generic stalk $F$ of [def-sc-function-
   field], because germ maps commute with pullback. Its stability follows also from step 8:
   applying $j$ to a monic polynomial over $k$ gives another monic polynomial over $k$. Naturality
   of evaluation of global sections makes $B\to\operatorname{Spec}e$ equivariant. Thus the field
   action extends the given action on $k$ and gives the required compatible, possibly semilinear
   $J$-action on the $e$-scheme $B$.
   Uses: def-sc-function-field.
10. The finite $e/k$ gives a finite $\operatorname{Spec}e\to\operatorname{Spec}k$ by [lem-weil-
   pbc-spec-finite-ring-map-finite], hence a separated map by [lem-weil-pbc-finite-closed-map-
   finite-fibres]; the projective $Y\to\operatorname{Spec}k$ is proper, hence separated, by [lem-
   kun-projective-implies-proper]. Let $g:T\to\operatorname{Spec}k$ be either of these maps and
   $f:B\to T$ the map $B\to\operatorname{Spec}e$ or $bq$; in both cases $g\circ f$ is the
   structure map of $B$. Let $i:B\hookrightarrow\mathbf P^N_k$ be the embedding of step 7. By
   [lem-weil-pbc-fibre-product-change-of-base-closed-immersion], applied to $f$, $\mathrm{id}_T$
   and the separated $g$, the map $B\times_TT\to B\times_kT$ is a closed immersion; by [def-pc-
   fibre-product] it is the graph $(\mathrm{id}_B,f):B\to B\times_kT$. The map
   $i\times\mathrm{id}_T:B\times_kT\to\mathbf P^N_k\times_kT$ is the base change of $i$ along the
   first projection, hence a closed immersion by [lem-weil-pbc-closed-immersion-base-change]. By
   [lem-weil-pbc-closed-immersion-comp] their composite $(i,f)$ is a closed immersion, and [lemma-
   nagata-projective-space-base-change-pullback] identifies its target with $\mathbf P^N_T$ over
   $T$, so that its projection to $T$ is $f$. Thus $B\hookrightarrow\mathbf P^N_e$ over $e$, and
   $bq$ is H-projective, in the convention of [def-kun-projective]. Finite type over $e$ is also
   explicit: on a finite affine cover of $B$, the same finite algebra generators over $k$ generate
   over $e$, whose global sections restrict to each chart.
   Uses: lem-weil-pbc-spec-finite-ring-map-finite, lem-weil-pbc-finite-closed-map-finite-fibres,
   lem-kun-projective-implies-proper, lem-weil-pbc-fibre-product-change-of-base-closed-immersion,
   def-pc-fibre-product, lem-weil-pbc-closed-immersion-base-change, lem-weil-pbc-closed-immersion-
   comp, lemma-nagata-projective-space-base-change-pullback, def-kun-projective.
11. The proper $l$-scheme $B$ is geometrically normal by step 3, hence geometrically reduced:
   every local ring after any field extension is a domain, so is reduced, by [def-weil-pbc-normal-
   ring]. Its global-sections algebra is the field $e$. Therefore [lem-pc-proper-geometrically-
   reduced-global-sections-separable] applies and gives separability of $e/l$. Together with step
   8 this makes $e/l$ finite separable algebraic.
   Uses: lem-pc-proper-geometrically-reduced-global-sections-separable, def-weil-pbc-normal-ring.
12. Fix any field extension $E/e$. Finite separable field extensions are etale by [lem-kun-
   algebraic-separable-smooth]. By [lem-weil-pbc-etale-base-change-finite-limits](1),
   $\operatorname{Spec}(e\otimes_lE)\to\operatorname{Spec}E$ is etale. By [lem-weil-pbc-etale-
   algebra-over-field-product], $e\otimes_lE$ is a finite product of finite separable field
   extensions of $E$. The map $\mu:e\otimes_lE\to E$, $a\otimes t\mapsto at$, selects one factor:
   coordinate idempotents map to $0$ or $1$ and sum to $1$. That factor injects into $E$ and maps
   onto it, since the map is an $E$-algebra map. Thus $\operatorname{Spec}\mu$ includes an open-
   and-closed component. Its pullback along $B\times_lE\to\operatorname{Spec}(e\otimes_lE)$
   identifies $B\times_eE$ with an open-and-closed subscheme of $B\times_lE$.
   Uses: lem-kun-algebraic-separable-smooth, lem-weil-pbc-etale-base-change-finite-limits, lem-
   weil-pbc-etale-algebra-over-field-product.
13. Geometric normality over $l$ makes $B\times_lE$ normal. The open subscheme $B_E=B\times_eE$
   from step 12 has the same local rings there, so is normal too. It is Noetherian: step 10 gives
   finite type over $e$, [lem-sfb-finite-type-composition-base-change](2) gives finite type of
   $B_E/E$, and [lem-weil-pbc-finite-type-over-noetherian] applies over the Noetherian field $E$.
   The Stein factorization in step 8 gives nonemptiness and connectedness of $B_E$. By [lem-trf-
   normal-topologically-noetherian-components] its normal integral components are pairwise
   disjoint open-and-closed subschemes. Connectedness forces just one, so $B_E$ is integral. Since
   $E/e$ was arbitrary, this proves geometric integrality over $e$ as defined in [def-pc-
   geometrically-irreducible].
   Uses: lem-sfb-finite-type-composition-base-change, lem-weil-pbc-finite-type-over-noetherian,
   lem-trf-normal-topologically-noetherian-components, def-pc-geometrically-irreducible.
14. Apply [lem-sfb-normal-stein-constant-field] to $Y\to\operatorname{Spec}k$ as well: normality,
   integrality and finite type are hypotheses, and its projectivity implies properness by [lem-
   kun-projective-implies-proper]. The resulting Stein field is the algebraic closure of $k$ in
   $k(Y)$. Geometric integrality of $Y/k$ and [lem-pc-h0-proper-variety](2) give
   $\Gamma(Y,\mathcal O_Y)=k$. Thus the Stein field is $k$: every element of $k(Y)$ algebraic over
   $k$ belongs to $k$.
   Uses: lem-sfb-normal-stein-constant-field, lem-pc-h0-proper-variety, lem-kun-projective-
   implies-proper.
15. In characteristic $p>0$, take $x\in F^A$. Pure inseparability of $F/K$ gives $x^{p^n}\in K$
   for some $n$. It is $A$-fixed, hence in $K^A$. The assumed pure inseparability of $K^A/k(Y)$
   gives $x^{p^{n+m}}\in k(Y)$ for some $m$. Thus $F^A/k(Y)$ is purely inseparable. For $c\in e^A$
   the same calculation gives $c^{p^r}\in k(Y)$; it is algebraic over $k$ since $e/k$ is finite,
   so step 14 puts it in $k$. Hence $e^A/k$ is purely inseparable. These are extensions of the
   indicated base fields because $A=\ker\rho$ fixes $k$ and $k(Y)$. In characteristic zero $F=K$
   and $K^A=k(Y)$; then $e^A\subseteq k(Y)$ is algebraic over $k$, so step 14 gives $e^A=k$. This
   verifies [def-weil-pbc-finite-purely-inseparable-extension] in both characteristics.
   Uses: def-weil-pbc-finite-purely-inseparable-extension.
16. Suppose $\dim Y=0$. By [lem-pc-algebraic-dim-zero-affine-finite], $Y$ is affine finite over
   $k$, and [lem-pc-h0-proper-variety](2) identifies its coordinate ring with $k$. Thus
   $Y=\operatorname{Spec}k$. An alteration is finite over a dense open of its target; the only
   dense open here is the whole target, so $b:S\to\operatorname{Spec}k$ is finite. By [lem-weil-
   pbc-finite-composition], $B$ is finite over $k$. Its source is affine by [lem-weil-pbc-finite-
   morphism-permanence](b), giving $B=\operatorname{Spec}\Gamma(B,\mathcal
   O_B)=\operatorname{Spec}e$. This canonical isomorphism over $e$ is equivariant by naturality of
   global sections.
   Uses: lem-pc-algebraic-dim-zero-affine-finite, lem-pc-h0-proper-variety, lem-weil-pbc-finite-
   composition, lem-weil-pbc-finite-morphism-permanence.
-/
theorem exists_normal_alteration_constant_regularization
    (k : Type u) [Field k] (Y S : Scheme.{u})
    (pY : Y ⟶ Spec (.of k)) (pS : S ⟶ Spec (.of k))
    [IsIntegral Y] [IsIntegral S] [IsHProjective pY] [IsHProjective pS]
    [GeometricallyIntegral pY]
    (hYnormal : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
      IsIntegrallyClosed (Y.presheaf.stalk y))
    (hSnormal : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (b : S ⟶ Y) [IsProper b] [Surjective b] (hb : b ≫ pY = pS)
    (hbfinite : ∃ U : Y.Opens, Dense (U : Set Y) ∧ IsFinite (b ∣_ U))
    (H : Type v) [Group H] [Finite H] (J : Type w) [Group J] [Finite J]
    (ρ : J →* H) (hρ : Function.Surjective ρ)
    (σk : H →* (k ≃+* k)) (σY : H →* Aut Y) (σS : J →* Aut S)
    (hY : ∀ h : H, (σY h).hom ≫ pY =
      pY ≫ Spec.map (CommRingCat.ofHom (σk h⁻¹).toRingHom))
    (hS : ∀ j : J, (σS j).hom ≫ pS =
      pS ≫ Spec.map (CommRingCat.ofHom (σk (ρ j⁻¹)).toRingHom))
    (heq : ∀ j : J, (σS j).hom ≫ b = b ≫ (σY (ρ j)).hom)
    (hgeneric : b (genericPoint S) = genericPoint Y)
    [Algebra Y.functionField S.functionField]
    (hfield : algebraMap Y.functionField S.functionField =
      (Y.presheaf.stalkSpecializes (specializes_of_eq hgeneric) ≫
        b.stalkMap (genericPoint S)).hom)
    (hinsep : ∃ K : IntermediateField Y.functionField S.functionField,
      (∀ z : S.functionField, z ∈ K ↔
        ∀ a : ρ.ker, (Scheme.functionFieldAut (σS a.val)).hom z = z) ∧
      IsPurelyInseparable Y.functionField K) :
    ∃ (e : Type u) (_ : Field e) (_ : Algebra k e), Module.Finite k e ∧
      ∃ γ : J →* (e ≃+* e),
        (∀ (j : J) (a : k), γ j (algebraMap k e a) = algebraMap k e (σk (ρ j) a)) ∧
        (∃ K : IntermediateField k e,
          (∀ z : e, z ∈ K ↔ ∀ a : ρ.ker, γ a.val z = z) ∧
          IsPurelyInseparable k K) ∧
        ∃ (B : Scheme.{u}) (_ : IsIntegral B) (pB : B ⟶ Spec (.of e))
          (q : B ⟶ S) (τ : J →* Aut B),
          IsHProjective pB ∧ GeometricallyIntegral pB ∧
          (∀ x : B, IsDomain (B.presheaf.stalk x) ∧
            IsIntegrallyClosed (B.presheaf.stalk x)) ∧
          q ≫ pS = pB ≫ Spec.map (CommRingCat.ofHom (algebraMap k e)) ∧
          IsFinite q ∧ Surjective q ∧ UniversallyInjective q ∧
          (∀ j : J, (τ j).hom ≫ pB =
            pB ≫ Spec.map (CommRingCat.ofHom (γ j⁻¹).toRingHom)) ∧
          (∀ j : J, (τ j).hom ≫ q = q ≫ (σS j).hom) ∧
          IsHProjective (q ≫ b) ∧
          (∃ (hq : q (genericPoint B) = genericPoint S)
              (_ : Algebra S.functionField B.functionField)
              (_ : Algebra Y.functionField B.functionField)
              (_ : IsScalarTower Y.functionField S.functionField B.functionField),
            algebraMap S.functionField B.functionField =
              (S.presheaf.stalkSpecializes (specializes_of_eq hq) ≫
                q.stalkMap (genericPoint B)).hom ∧
            Module.Finite S.functionField B.functionField ∧
            IsPurelyInseparable S.functionField B.functionField ∧
            ∃ K : IntermediateField Y.functionField B.functionField,
              (∀ z : B.functionField, z ∈ K ↔
                ∀ a : ρ.ker, (Scheme.functionFieldAut (τ a.val)).hom z = z) ∧
              IsPurelyInseparable Y.functionField K) ∧
          (∃ (_ : Algebra e B.functionField) (_ : Algebra k B.functionField)
              (_ : IsScalarTower k e B.functionField),
            Spec.map (CommRingCat.ofHom (algebraMap e B.functionField)) =
              B.fromSpecFunctionField ≫ pB ∧
            Set.range (algebraMap e B.functionField) =
              {z : B.functionField | IsAlgebraic k z}) ∧
          (topologicalKrullDim Y = 0 → IsIso pB) := by
  sorry

end AlgebraicGeometry
