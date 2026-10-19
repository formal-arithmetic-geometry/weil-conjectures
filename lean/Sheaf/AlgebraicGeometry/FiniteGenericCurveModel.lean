/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.Curve.GenericModel
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# A generic curve model with finite comparison boundary

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-fin-generic-curve-model.md`,
statement and Proof paragraphs 1–7 (blueprint: lem-fin-generic-curve-model).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- After shrinking an integral finite-type base and taking a finite surjective integral cover,
a projective family of geometric dimension at most one has a finite surjective comparison
from a finite coproduct of smooth projective relative curves and finite étale families.
The comparison is an isomorphism away from a closed subscheme finite over the new base.

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-fin-generic-curve-model.md`,
statement and Proof paragraphs 1–7 (blueprint: lem-fin-generic-curve-model).

The factors are `Y i`, with structure maps `g i`; their coproduct is `∐ Y`. The equality
makes the comparison a morphism over `S'`. The closed immersion `d` represents `D` and `V`
is its open complement. Thus the final pullback projection is the restriction of `ν`.

Proof steps:
1. First replace $S$ by a nonempty affine open $\operatorname{Spec}A$; its generic point remains
in this open, and $A$ is a domain. Schemes of finite type over the given field are Noetherian by
[lem-weil-pbc-finite-type-over-noetherian]. Thus all schemes of finite type used below are
Noetherian. On their affine charts finite type implies finite presentation by
[lem-weil-pbc-finite-type-noetherian-finite-presentation]; separatedness gives
quasi-separatedness, so the projective schemes and their finite covers are of finite presentation
over their respective ground fields (the original field, $K$, or $\bar K$). A field is Noetherian
because its only ideals are zero and the whole field. Put $K=\operatorname{Frac}A$ and choose an
algebraic closure $\bar K$. Projectivity survives both the generic-fibre and field base changes by
[lem-pc-projective-base-change]. Put $\bar T=(X_{\bar K})_{\mathrm{red}}$; its closed immersion
into $X_{\bar K}$ followed by the fixed projective embedding is still a closed immersion
(affine-locally it is the composite of surjective quotient maps), so $\bar T$ is projective.
Reduction has the same underlying space, hence $\dim\bar T\leq1$.
Uses: lem-weil-pbc-finite-type-over-noetherian,
lem-weil-pbc-finite-type-noetherian-finite-presentation, lem-pc-projective-base-change,
def-pc-projective-morphism, def-weil-pbc-scheme-reduction.
2. By [lem-sc-component-intersections-finite], $\bar T$ has finitely many irreducible components.
Give each component its reduced closed structure. Normalize each one-dimensional component $C_a$
in its own function field. The identity extension of that field is finite, so
[lem-fin-normalization-extension-finite] gives a finite normalization;
[lem-sc-normalization-exists] gives surjectivity, birationality and preservation of dimension.
Since $\bar K$ is perfect, [lem-sc-normalized-curve-smooth] makes the normalized curves smooth.
Each zero-dimensional component is $\operatorname{Spec}\bar K$ by
[lem-weil-pbc-zero-dim-integral-point], and is retained unchanged. Take their finite coproduct
using [lem-weil-pbc-scheme-coproduct-family]. The resulting $\bar\nu:\bar Y\to\bar T$ is finite:
on an affine chart it corresponds to a finite product of finite modules, with the component
inclusions given by quotient maps. It is surjective because the components cover $\bar T$ and each
normalization is surjective. Each factor is projective over the affine Noetherian base
$\operatorname{Spec}\bar K$ by [lem-fin-finite-over-projective], applied to its finite map to
$\bar T$. A smooth integral curve has pure dimension one: the fibre-dimension function is locally
constant by [sbc-lem-smooth-relative-dimension-locally-constant], hence constant on the
irreducible normalization, and its value is one since its dimension is one. The point factors have
relative dimension zero.
Uses: lem-sc-component-intersections-finite, lem-fin-normalization-extension-finite,
lem-sc-normalization-exists, lem-sc-normalized-curve-smooth, lem-weil-pbc-zero-dim-integral-point,
lem-weil-pbc-scheme-coproduct-family, lem-fin-finite-over-projective,
sbc-lem-smooth-relative-dimension-locally-constant.
3. The map $\mathcal O_{\bar T}\to\bar\nu_*\mathcal O_{\bar Y}$ is injective. Indeed on an affine
chart a section in its kernel vanishes in the function field of every component meeting the chart,
by the inclusions into the normalization algebras. It therefore belongs to every minimal prime,
hence to every prime, and is nilpotent by [lem-weil-pbc-zero-locus-eq-iff-radical-eq]; reducedness
makes it zero. The pushforward is coherent by [lem-pc-f3-finite-pushforward-finite-type] and
[pqf-lem-coherent-ft-locnoeth], and its cokernel is coherent by
[lem-weil-pbc-coherent-kernel-cokernel-locnoeth]. Its support $\bar E$ is closed by
[lem-weil-pbc-finite-type-module-support-closed]. At each generic point only its own component
remains (the other finitely many closed components can be excluded); the normalization induces the
same function field by birationality, so the cokernel stalk is zero there. The complement of $\bar
E$ is dense. The projective $\bar T$ is separated, of finite type over $\bar K$, and of dimension
at most one, hence is a curve in [def-sc-curves], including when it is empty or has isolated point
components; [lem-sc-dense-open-finite-complement] makes $\bar E$ a finite set of closed points.
Off $\bar E$ the algebra map is an isomorphism and hence $\bar\nu$ is an isomorphism. Thus the
generic comparison boundary has dimension at most zero.
Uses: lem-weil-pbc-zero-locus-eq-iff-radical-eq, lem-sc-normalization-exists,
lem-pc-f3-finite-pushforward-finite-type, pqf-lem-coherent-ft-locnoeth,
lem-weil-pbc-coherent-kernel-cokernel-locnoeth, lem-weil-pbc-finite-type-module-support-closed,
lem-sc-dense-open-finite-complement, def-sc-curves.
4. The finite intermediate extensions $L/K$ in $\bar K$ form a small directed set, with union
$\bar K$; their spectra have affine transition maps and are Noetherian and quasi-separated. This
is an actual limit diagram: on coordinate rings its colimit is the union $\bar K$. Apply all three
clauses of [thm-pd-spreading-out] to $\bar T$, the finitely many factors of $\bar Y$, their maps
to $\bar T$, and $\bar T\to X_{\bar K}$, with the existing $X_K$ as the fixed model. Choosing a
common finite stage descends the objects, arrows and their commuting relations to a finite
extension $K'/K$. The descended $T'\to X_{K'}$ is a closed immersion by
[lem-pc-fpqc-descend-closed-immersion], since its pullback to $\bar K$ is one; the covering is
fpqc because a field extension is faithfully flat and its spectrum map is affine. Form $Y'$ as the
coproduct of the descended factors. Its map $Y'\to T'$ is finite by
[lem-sbc-finite-morphism-fpqc-descent], applied to $T'_{\bar K}\to T'$. All these source and
target schemes are of finite presentation, as required for the limit theorem.
Uses: thm-pd-spreading-out, lem-pc-fpqc-descend-closed-immersion,
lem-weil-pbc-scheme-coproduct-family, lem-sbc-finite-morphism-fpqc-descent.
5. Identify the descended closed subscheme with the reduction, rather than assuming reduction
commutes with field extension. On a chart $\operatorname{Spec}B\subset X_{K'}$, let $I\subset B$
define $T'$. Its extended ideal in $B\otimes_{K'}\bar K$ is the nilradical. Every $b\in I$
therefore has $(b\otimes1)^N=0$ for some $N$, and injectivity of $B\to B\otimes_{K'}\bar K$
implies $b^N=0$. Conversely $B/I$ injects into $(B/I)\otimes_{K'}\bar K$, which is reduced, so
$B/I$ is reduced. These two observations give $I=\sqrt{0}$, and glue to
$T'=(X_{K'})_{\mathrm{red}}$. Tensor injectivity here is elementary linear algebra: extend a
nonzero vector to a field-vector-space basis. No assertion about transcendental extensions is
needed. In particular the erroneous exponent $\max N_j$ in the imported proof is not used; if
generators satisfy $b_j^{N_j}=0$, a valid exponent for their ideal is $1+\sum_j(N_j-1)$.
Uses: def-weil-pbc-scheme-reduction.
6. Apply [lem-sbc-affine-limit-smooth-stage] to the total descended $Y'$ over the directed system
of finite intermediate fields extending $K'$: its pullback to $\bar K$ is smooth. This gives a
further finite field stage at which $Y'$ is smooth; replace $K'$ by that stage and all objects by
their pullbacks. Each open-and-closed factor is smooth as well. The preceding reduction argument
still applies after this replacement. For each factor its dimension at every point equals that at
a point above it over $\bar K$, by [lem-weil-pbc-dimension-at-point-field-extension], applied on
finite-type affine charts. Points above exist because a field extension is faithfully flat (for a
prime, the residue-field tensor product is nonzero and has a prime). Thus its relative dimension
over $K'$ is exactly the one or zero of its geometric model. Also the map $\mathcal
O_{T'}\to\nu'_*\mathcal O_{Y'}$ is injective and its cokernel has dimension-zero support: on
affine charts tensoring with $\bar K$ is exact, so the kernel tensors to zero, and
[lem-weil-pbc-support-pullback-finite-type] identifies the cokernel's pulled-back support with
$\bar E$. The dimensions of its affine support charts are unchanged by
[lem-weil-pbc-dimension-preserved-field-extension].
Uses: lem-sbc-affine-limit-smooth-stage, lem-weil-pbc-dimension-at-point-field-extension,
lem-weil-pbc-support-pullback-finite-type, lem-weil-pbc-dimension-preserved-field-extension.
7. Choose finitely many generators $\alpha_i$ of the finite extension $K'/K$. Each satisfies a
monic polynomial with coefficients in $K$. Invert the product $a\ne0$ of the denominators of all
those coefficients in $A$, so the same polynomials show the $\alpha_i$ integral over $A_a$. Then
$A'=A_a[\alpha_1,\ldots,\alpha_r]\subset K'$ is a domain, finite over $A_a$: monomials whose
individual exponents are less than the respective monic degrees span it. Its fraction field is
$K'$. The injective integral inclusion $A_a\hookrightarrow A'$ gives a surjective spectrum map by
[pqf-lem-lying-over]. Therefore $p:S'=\operatorname{Spec}A'\to\operatorname{Spec}A_a$ is finite
and surjective. Put $T=(X_{S'})_{\mathrm{red}}$. By [lem-pc-projective-base-change] and the
reduction closed immersion, $T$ is projective. Its generic fibre is $T'$: localization commutes
with reduction, since if $b/s$ is nilpotent, some nonzero localization denominator $t$ has
$tb^n=0$, whence $(tb)^n=0$, so $b/s$ is the localization of a nilpotent element. Conversely
localizing a nilpotent stays nilpotent.
Uses: pqf-lem-lying-over, lem-pc-projective-base-change, def-weil-pbc-scheme-reduction,
def-pc-projective-morphism.
8. Use [lem-fin-spread-finite-algebra] over the Noetherian domain $A'$ on the finite coherent
$\mathcal O_{T'}$-algebra of $Y'\to T'$, including its finite product decomposition. After
inverting one nonzero element of $A'$, it gives a finite $\nu:Y\to T$ and a finite decomposition
$Y=\coprod_aY_a$ whose generic factors are the prescribed ones. Each $Y_a\to T$ is finite, because
a product factor is a finite quotient of the finite algebra. By [lem-fin-finite-over-projective],
all $Y_a$ are projective over this affine open of $S'$. Their finite-type morphisms are of finite
presentation by the Noetherian affine-ring criterion
[lem-weil-pbc-finite-type-noetherian-finite-presentation].
Uses: lem-fin-spread-finite-algebra, lem-fin-finite-over-projective,
lem-weil-pbc-finite-type-noetherian-finite-presentation.
9. For the total projective $Y$ over the current affine domain base, apply
[lem-sbc-affine-limit-smooth-stage] to the system of principal nonempty base opens
$\operatorname{Spec}A'_h$ ($h\ne0$), whose limit is $\operatorname{Spec}K'$. Their transitions are
affine, their stages are Noetherian and quasi-separated, and $Y$ is of finite presentation. Its
generic fibre is smooth by Step 6, so after one further localization $Y$ and all its factors are
smooth. On a factor $Y_a$ of generic relative dimension $n_a\in\{0,1\}$,
[sbc-lem-smooth-relative-dimension-locally-constant] says the locus where the fibre dimension is
not $n_a$ is closed (indeed open and closed). It has empty generic fibre. Projectivity implies
properness by [lem-pc-projective-proper], so its image is closed by
[lem-weil-pbc-proper-closed-image]; remove these finitely many images. Now every factor is smooth
of pure relative dimension $n_a$. For each $n_a=0$ factor apply
[lem-fin-projective-generically-finite] to make its structural map finite by a further nonempty
base restriction. Smooth relative dimension zero means etale by [def-sbc-smooth-morphisms], so
these are finite etale families. The $n_a=1$ factors are the required smooth projective families.
Uses: lem-sbc-affine-limit-smooth-stage, sbc-lem-smooth-relative-dimension-locally-constant,
lem-pc-projective-proper, lem-weil-pbc-proper-closed-image, lem-fin-projective-generically-finite,
def-sbc-smooth-morphisms.
10. Let $I=\ker(\mathcal O_T\to\nu_*\mathcal O_Y)$ and $Q=\operatorname{coker}(\mathcal
O_T\to\nu_*\mathcal O_Y)$. Finiteness gives a quasi-coherent finite-type pushforward by
[lem-pc-f3-finite-pushforward-finite-type]; on the Noetherian $T$ it is coherent by
[pqf-lem-coherent-ft-locnoeth]. Hence $I,Q$ are coherent by
[lem-weil-pbc-coherent-kernel-cokernel-locnoeth], with closed supports by
[lem-weil-pbc-finite-type-module-support-closed]. Generic localization is exact, so $I$ restricts
to zero on $T'$ by Step 6. The support comparison [lem-weil-pbc-support-pullback-finite-type]
shows its support misses the generic fibre. This support is a closed subscheme of the projective
$T$, therefore projective and proper; [lem-pc-projective-proper] and
[lem-weil-pbc-proper-closed-image] allow removal of its closed image from $S'$. Then $I=0$, and
[pqf-lem-lying-over], applied on every affine chart to the injective finite algebra map, makes
$\nu$ surjective. Let $D\subset T$ be the reduced closed subscheme on $\operatorname{Supp}Q$. It
is projective and its generic fibre has dimension at most zero by Step 6 and support pullback.
Apply [lem-fin-projective-generically-finite] to make $D\to S'$ finite. On $T\setminus D$ the
kernel and cokernel vanish, so the finite algebra map is bijective. Taking affine spectra gives
that $\nu$ is an isomorphism there.
Uses: lem-pc-f3-finite-pushforward-finite-type, pqf-lem-coherent-ft-locnoeth,
lem-weil-pbc-coherent-kernel-cokernel-locnoeth, lem-weil-pbc-finite-type-module-support-closed,
lem-weil-pbc-support-pullback-finite-type, lem-pc-projective-proper,
lem-weil-pbc-proper-closed-image, pqf-lem-lying-over, lem-fin-projective-generically-finite.
11. Keep the original finite map $p:S'\to\operatorname{Spec}A_a$ before the subsequent
restrictions, and let $V\subset S'$ be the intersection of all the finitely many nonempty opens
used in Steps 8-10. Every one contains the unique generic point of the integral $S'$. Its
complement $Z=S'\setminus V$ has a reduced closed subscheme structure; its map to $S'$ is finite
(quotient algebras are cyclic modules), so $Z\to\operatorname{Spec}A_a$ is finite by
[lem-weil-pbc-finite-composition]. It is proper by [lem-weil-pbc-finite-proper] and has closed
image by [lem-weil-pbc-proper-closed-image]. That image misses the generic point of
$\operatorname{Spec}A_a$, because the generic fibre of $p$ is the one-point
$\operatorname{Spec}K'$ and its point is in $V$. Remove the image and choose a nonempty principal
affine open $U$ inside the remaining open. Its full inverse image $p^{-1}(U)$ lies in $V$ and is
affine and integral. The restricted $p$ is finite by [lem-weil-pbc-finite-morphism-permanence] and
surjective (each fibre is the same fibre as for the original surjection). The finite comparison
and finite boundary remain finite by the same base-change lemma; projectivity remains by
[lem-pc-projective-base-change], and smoothness with its specified relative dimension remains by
[lem-sbc-smooth-relative-dimension-permanence]. Reduction commutes with this open restriction by
the localization argument in Step 7. Renaming $U$ and $p^{-1}(U)$ as $S$ and $S'$ gives every
clause of the original statement. Empty generic fibre is included: the coproduct may be empty, and
Step 10 removes the entire vertical target by the kernel-support argument.
Uses: lem-weil-pbc-finite-composition, lem-weil-pbc-finite-proper,
lem-weil-pbc-proper-closed-image, lem-weil-pbc-finite-morphism-permanence,
lem-pc-projective-base-change, lem-sbc-smooth-relative-dimension-permanence.
-/
theorem exists_finite_generic_curve_model
    (k : Type u) [Field k] (X S : Scheme.{u}) [S.Over (Spec (.of k))]
    [IsIntegral S] [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))] (f : X ⟶ S) [IsProjective f]
    (h_dim : ∀ s : S,
      topologicalKrullDim (pullback f
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s) : Scheme.{u}) ≤ 1) :
    ∃ U : S.Opens, Nonempty U ∧
      ∃ (S' : Scheme.{u}) (p : S' ⟶ U.toScheme),
        IsIntegral S' ∧ IsFinite p ∧ Surjective p ∧
        ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (g : ∀ i : Fin n, Y i ⟶ S')
          (ν : (∐ Y) ⟶ (pullback f (p ≫ U.ι)).nilradical.subscheme),
          IsFinite ν ∧ Surjective ν ∧
          (∀ i : Fin n, (SmoothOfRelativeDimension 1 (g i) ∧ IsProjective (g i)) ∨
            (IsFinite (g i) ∧ Etale (g i))) ∧
          Sigma.desc g = ν ≫ (pullback f (p ≫ U.ι)).nilradical.subschemeι ≫
            pullback.snd f (p ≫ U.ι) ∧
          ∃ (D : Scheme.{u}) (d : D ⟶ (pullback f (p ≫ U.ι)).nilradical.subscheme),
            IsClosedImmersion d ∧
            IsFinite (d ≫ (pullback f (p ≫ U.ι)).nilradical.subschemeι ≫
              pullback.snd f (p ≫ U.ι)) ∧
            ∃ V : (pullback f (p ≫ U.ι)).nilradical.subscheme.Opens,
              (∀ x, x ∈ V ↔ x ∉ Set.range d) ∧ IsIso (pullback.snd ν V.ι) := by
  classical
  have hf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ 1 := by
    intro Ω _ _ s
    obtain ⟨⟨y, t⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω S).symm.surjective s
    change topologicalKrullDim (pullback f (Spec.map t ≫ S.fromSpecResidueField y) : Scheme) ≤ 1
    have hfield (K : Type u) [Field K] (q : Spec (.of K) ⟶ Spec (.of (S.residueField y))) :
        topologicalKrullDim (pullback f (q ≫ S.fromSpecResidueField y) : Scheme.{u}) =
          topologicalKrullDim (pullback f (S.fromSpecResidueField y) : Scheme.{u}) := by
      calc
        _ = topologicalKrullDim (pullback (pullback.snd f (S.fromSpecResidueField y)) q :
          Scheme.{u}) := by
            let e := pullbackLeftPullbackSndIso f (S.fromSpecResidueField y) q
            exact (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).symm
        _ = _ := topologicalKrullDim_pullback_eq_of_field
          (pullback.snd f (S.fromSpecResidueField y)) q
    rw [hfield]
    simpa only [hfield] using h_dim y
  obtain ⟨m, _, i, _, hi⟩ := IsHProjective.exists_isClosedImmersion (f := f)
  obtain ⟨U, hU, S', hS', p, hp, hps, T, t, ht, hts, hT, ι, hι, Y, ν, hν, hνs,
    D, d, hd, hD, hV, hY⟩ :=
    exists_isFinite_sigmaDesc_genericCurveModel (S ↘ Spec (.of k)) f i hi hf
  let := hS'
  let := hp
  let := hps
  let := ht
  let := hts
  let := hT
  let := hι
  let := hν
  let := hνs
  let := hd
  let h := (IsPullback.of_hasPullback (f ∣_ U) p).flip.paste_vert
    (isPullback_morphismRestrict f U)
  let e₀ := h.flip.isoPullback
  let a := t ≫ e₀.hom
  let b := a.liftNilradical
  have hb : b ≫ (pullback f (p ≫ U.ι)).nilradical.subschemeι = a := by
    exact Scheme.Hom.liftNilradical_subschemeι a
  have : IsClosedImmersion a := by dsimp [a]; infer_instance
  have : Surjective a := by dsimp [a]; infer_instance
  have : IsClosedImmersion b := by
    have : IsClosedImmersion (b ≫ (pullback f (p ≫ U.ι)).nilradical.subschemeι) :=
      hb.symm ▸ inferInstance
    exact IsClosedImmersion.of_comp_isClosedImmersion b
      (pullback f (p ≫ U.ι)).nilradical.subschemeι
  have : Surjective b := by
    constructor
    intro y
    obtain ⟨x, hx⟩ := a.surjective ((pullback f (p ≫ U.ι)).nilradical.subschemeι y)
    refine ⟨x, ?_⟩
    apply (pullback f (p ≫ U.ι)).nilradical.subschemeι.isClosedEmbedding.injective
    change (b ≫ (pullback f (p ≫ U.ι)).nilradical.subschemeι) x = _
    simpa only [hb] using hx
  have : IsIso b := isIso_of_isClosedImmersion_of_surjective b
  let e := asIso b
  have he : e.hom ≫ (pullback f (p ≫ U.ι)).nilradical.subschemeι ≫
      pullback.snd f (p ≫ U.ι) = t ≫ pullback.snd (f ∣_ U) p := by
    change b ≫ _ ≫ _ = _
    rw [← Category.assoc, hb]
    dsimp [a, e₀, h]
    simp
  let := Fintype.ofFinite ι
  let j := (Fintype.equivFin ι).symm
  let Y' := Y ∘ j
  let c := Sigma.reindex j Y
  let ν' := c.hom ≫ ν ≫ e.hom
  let d' := d ≫ e.hom
  let g (i : Fin (Fintype.card ι)) := Sigma.ι Y (j i) ≫ ν ≫ t ≫
    pullback.snd (f ∣_ U) p
  refine ⟨U, ?_, S', p, hS', hp, hps, Fintype.card ι, Y', g, ν',
    inferInstance, inferInstance, ?_, ?_, D, d', inferInstance, ?_, ?_⟩
  · by_contra hne
    apply hU
    apply SetLike.coe_injective
    exact Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦ hne ⟨⟨x, hx⟩⟩
  · intro i
    rcases hY (j i) with ⟨⟨m, hm, z, hz, hzg⟩, hs⟩ | hfin
    · left
      refine ⟨hs, ?_⟩
      let := hm
      let := hz
      have : IsHProjective (g i) := ⟨⟨m, hm, z, hz, hzg⟩⟩
      exact IsHProjective.isProjective (g i)
    · exact Or.inr hfin
  · apply Sigma.hom_ext
    intro i
    dsimp [g, ν', Y', c]
    simp only [Sigma.ι_desc]
    rw [Category.assoc, Category.assoc, he]
    simp only [Sigma.ι_reindex_hom_assoc]
  · dsimp [d']
    simpa only [Category.assoc, he] using hD
  · let W : T.Opens := ⟨(Set.range d)ᶜ, d.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    let V := e.inv ⁻¹ᵁ W
    have hpre : e.hom ⁻¹ᵁ V = W := by
      simp [V, ← Scheme.Hom.comp_preimage]
    refine ⟨V, ?_, ?_⟩
    · intro x
      change e.inv x ∉ Set.range d ↔ x ∉ Set.range d'
      rw [Set.mem_range, Set.mem_range]
      constructor
      · rintro h ⟨y, hy⟩
        apply h
        refine ⟨y, ?_⟩
        rw [← hy]
        change d y = (d ≫ e.hom ≫ e.inv) y
        simp
      · rintro h ⟨y, hy⟩
        apply h
        refine ⟨y, ?_⟩
        change (d ≫ e.hom) y = x
        rw [Scheme.Hom.comp_apply, hy]
        change (e.inv ≫ e.hom) x = x
        simp
    · have : IsIso (ν ∣_ W) := hV
      have : IsIso (ν ∣_ (e.hom ⁻¹ᵁ V)) := hpre.symm ▸ inferInstance
      have : IsIso (ν' ∣_ V) := by
        dsimp [ν']
        rw [morphismRestrict_comp, morphismRestrict_comp]
        infer_instance
      rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict ν' V]
      infer_instance

end AlgebraicGeometry
