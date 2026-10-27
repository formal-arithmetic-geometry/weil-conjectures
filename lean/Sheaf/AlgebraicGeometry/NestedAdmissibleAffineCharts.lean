/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Nested admissible affine charts for a smooth pair

Source: the current Weil conjectures blueprint, `sec-smooth-purity`,
`sk-prop-sp-composition/sk-prop-sp-composition-factors.proof.md`, proof (1), first sentence;
Stacks Project, Tags 054L and 01M0 (blueprint: lem-sp-nested-affine-charts).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

private noncomputable def orderedAffineIso (S : Scheme.{u}) (d e : ℕ) :
    AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin e)) S) ≅
      AffineSpace (ULift.{u} (Fin (d + e))) S where
  hom := AffineSpace.homOfVector
    ((AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin e)) S) ↘
      AffineSpace (ULift.{u} (Fin e)) S) ≫ (AffineSpace (ULift.{u} (Fin e)) S ↘ S))
    (fun i ↦ Fin.addCases
      (fun j ↦ AffineSpace.coord (AffineSpace (ULift.{u} (Fin e)) S) (ULift.up j))
      (fun j ↦ (AffineSpace (ULift.{u} (Fin d))
        (AffineSpace (ULift.{u} (Fin e)) S) ↘
          AffineSpace (ULift.{u} (Fin e)) S).appTop (AffineSpace.coord S (ULift.up j)))
      i.down)
  inv := AffineSpace.homOfVector
    (AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin (d + e))) S ↘ S)
      (fun j ↦ AffineSpace.coord S (ULift.up (j.down.natAdd d))))
    (fun i ↦ AffineSpace.coord S (ULift.up (i.down.castAdd e)))
  hom_inv_id := by
    apply AffineSpace.hom_ext
    · apply AffineSpace.hom_ext
      · simp
      · intro j
        simp
    · intro i
      simp
  inv_hom_id := by
    apply AffineSpace.hom_ext
    · simp only [Category.assoc, AffineSpace.homOfVector_over]
      rw [AffineSpace.homOfVector_over_assoc, AffineSpace.homOfVector_over,
        Category.id_comp]
    · rintro ⟨i⟩
      refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
      · simp
      · simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          AffineSpace.homOfVector_appTop_coord, Fin.addCases_right]
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
          AffineSpace.homOfVector_over, AffineSpace.homOfVector_appTop_coord]
        simp

private theorem nestedLocalCharts {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g] (x : X) :
    ∃ (S : Z.Opens) (V : Y.Opens) (U : X.Opens)
      (hVS : V ≤ g ⁻¹ᵁ S) (hUV : U ≤ f ⁻¹ᵁ V)
      (v : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin e)) S.toScheme)
      (u : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) V.toScheme),
      x ∈ U ∧ f x ∈ V ∧ g (f x) ∈ S ∧
      IsAffineOpen S ∧ IsAffineOpen V ∧ IsAffineOpen U ∧ Etale v ∧ Etale u ∧
      v ≫ (AffineSpace (ULift.{u} (Fin e)) S.toScheme ↘ S.toScheme) =
        g.resLE S V hVS ∧
      u ≫ (AffineSpace (ULift.{u} (Fin d)) V.toScheme ↘ V.toScheme) =
        f.resLE V U hUV := by
  obtain ⟨S, V, hS, hV, hxS, hxV, hVS, v, hv, hvg⟩ :=
    Smooth.exists_etale_to_affineSpace g e (f x)
  have : SmoothOfRelativeDimension d (f ∣_ V) :=
    IsZariskiLocalAtTarget.restrict (P := @SmoothOfRelativeDimension d) inferInstance V
  obtain ⟨W, U₀, _, hU₀, _, hxU₀, hU₀W, u₀, hu₀, hu₀f⟩ :=
    Smooth.exists_etale_to_affineSpace (f ∣_ V) d ⟨x, hxV⟩
  let U := (f ⁻¹ᵁ V).ι ''ᵁ U₀
  have hUV : U ≤ f ⁻¹ᵁ V := (f ⁻¹ᵁ V).ι_image_le U₀
  let u := ((f ⁻¹ᵁ V).ι.isoImage U₀).inv ≫ u₀ ≫
    AffineSpace.map (ULift.{u} (Fin d)) W.ι
  have : Etale u₀ := hu₀
  have : IsOpenImmersion (AffineSpace.map (ULift.{u} (Fin d)) W.ι) :=
    MorphismProperty.of_isPullback
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin d)) W.ι).flip inferInstance
  refine ⟨S, V, U, hVS, hUV, v, u, ⟨⟨x, hxV⟩, hxU₀, rfl⟩,
    hxV, hxS, hS, hV, hU₀.image_of_isOpenImmersion _, hv, inferInstance, hvg, ?_⟩
  apply (cancel_mono V.ι).1
  simp only [u, Category.assoc, AffineSpace.map_over_assoc]
  rw [← Category.assoc u₀, hu₀f, Scheme.Hom.resLE_comp_ι_assoc,
    morphismRestrict_ι, Scheme.Hom.isoImage_inv_ι_assoc, Scheme.Hom.resLE_comp_ι]

private theorem affineFiniteTypeProperties {k : Type u} [Field k]
    {T : Scheme.{u}} [IsAffine T] (a : T ⟶ Spec (.of k)) [LocallyOfFiniteType a] :
    IsNoetherian T ∧ IsSeparated a ∧ LocallyOfFiniteType a ∧ QuasiCompact a := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian a
  exact ⟨⟨⟩, inferInstance, inferInstance, inferInstance⟩

private theorem affineArrowProperties {A B : Scheme.{u}} [IsAffine A]
    [QuasiSeparatedSpace B] (a : A ⟶ B) [LocallyOfFinitePresentation a] :
    IsSeparated a ∧ LocallyOfFinitePresentation a ∧ QuasiCompact a ∧ QuasiSeparated a := by
  have : IsSeparated a := inferInstance
  have : QuasiCompact a := quasiCompact_of_compactSpace a
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- Nested affine etale charts for a pair of smooth separated morphisms.
The coordinate equations characterize the ordered identification uniquely: the outer
(`f`) coordinates occupy the first `d` positions and the base (`g`) coordinates the last `e`.
`Over.mk` records each space with its specified structure map to the field spectrum;
`Arrow.mk` lists exactly the indicated chart arrows for their admissibility assertions.
Source: blueprint `det-sp-composition-factors`, proof (1), first sentence;
Stacks Project, Tags 054L, 02NK, 02GO, 02GN and 01M0
(blueprint: lem-sp-nested-affine-charts).

Proof plan:
1. Fix $x\in X$. Apply [lem-sp-smooth-admissible-coordinate-cover] to $g:Y\to Z$ with relative
   dimension $e$, and select a source chart containing $f(x)$. Write its source as $V$, its
   affine base as $S$, and its affine-base etale map as $v:V\to\mathbf A^e_S$. Its statement
   supplies $gf(x)\in S$, $V\subset g^{-1}S$, $g|_V=p_{e,S}v$, and the separated finite-type
   Noetherian properties of $S,V,\mathbf A^e_S$. The field hypothesis holds because $k$ has
   characteristic $p>0$; the relative dimension is the specified $e$, not an unspecified
   dimension from the variable-dimension normal form. Dependencies: lem-sp-smooth-admissible-
   coordinate-cover.
2. Put $X_V=f^{-1}V$ with its open subscheme structure and let $f_V:X_V\to V$ be the
   restriction. A field is Noetherian since its only ideals are zero and the unit ideal. Thus
   [lem-weil-pbc-finite-type-over-noetherian] makes $X$ Noetherian, and [lem-weil-pbc-
   noetherian-open-subscheme-noetherian] makes $X_V$ Noetherian and hence quasi-compact. The
   target $X$ is quasi-separated by [lem-weil-pbc-qcqs-over-affine], applied to its separated
   finite-type structure morphism over the affine field spectrum. Consequently [lem-weil-pbc-
   qcqs-morphism-permanence](1) makes $X_V\hookrightarrow X$ quasi-compact. It is an open
   immersion, so [lem-weil-pbc-qc-open-immersion-finite-type] makes it finite type, and [lem-
   weil-pbc-separated-cancellation](a) makes it separated. Composition with
   $X\to\operatorname{Spec}k$ gives separated finite type over $k$, using [lem-sfb-finite-type-
   composition-base-change](1) and [lem-weil-pbc-proper-fp-permanence](e). Thus $X_V$ and $V$
   satisfy the scheme hypotheses of the coordinate-cover theorem. Dependencies: lem-weil-pbc-
   finite-type-over-noetherian, lem-weil-pbc-noetherian-open-subscheme-noetherian, lem-weil-pbc-
   proper-fp-permanence, lem-weil-pbc-qcqs-morphism-permanence, lem-weil-pbc-qc-open-immersion-
   finite-type, lem-weil-pbc-separated-cancellation, lem-sfb-finite-type-composition-base-
   change, def-weil-open-immersion, lem-weil-pbc-qcqs-over-affine.
3. The restriction $f_V$ is the base change of $f$ by $V\hookrightarrow Y$, so [lem-sbc-smooth-
   relative-dimension-permanence](1) makes it smooth of relative dimension $d$. Apply [lem-sp-
   smooth-admissible-coordinate-cover] to $f_V$ and select a source chart $U$ containing $x$.
   Use the theorem's composite map $u:U\to\mathbf A^d_V$ over its ORIGINAL base $V$, not merely
   its affine-base map to $\mathbf A^d_W$ for a smaller $W\subset V$. Its statement says exactly
   that $u$ is separated etale of finite presentation, $f_V|_U=p_{d,V}u$, and $U,\mathbf A^d_V$
   are separated finite-type Noetherian $k$-schemes. An affine open of the open subscheme $X_V$
   is an affine open of $X$: the inclusion identifies it with an open subset with the same
   restricted structure sheaf [def-weil-open-immersion]. Hence $x\in U\subset f^{-1}V$ with the
   required interpretation in $X$. Dependencies: lem-sbc-smooth-relative-dimension-permanence,
   lem-sp-smooth-admissible-coordinate-cover, def-weil-open-immersion.
4. Set $T=\mathbf A^d_{\mathbf A^e_S}$ and $b=\mathbf A^d(v):\mathbf A^d_V\to T$. By [def-sbc-
   affine-space], $\mathbf A^d_B=B\times_{\operatorname{Spec}\mathbf Z}\mathbf A^d_{\mathbf Z}$.
   Applying the universal property in [def-pc-fibre-product], a map to either $\mathbf A^d_V$ or
   $V\times_{\mathbf A^e_S}T$ is the same pair of maps to $V$ and $\mathbf A^d_{\mathbf Z}$
   agreeing over $\operatorname{Spec}\mathbf Z$; the resulting maps are inverse because their
   two projections agree. Thus the square with horizontal maps $b,v$ and vertical affine-space
   projections is cartesian. It follows from [lem-weil-pbc-etale-scheme-base-change] that $b$ is
   etale. Since $u$ is etale, [lem-weil-pbc-etale-composition-cancellation](2) makes $bu$ etale.
   Dependencies: def-sbc-affine-space, def-pc-fibre-product, lem-weil-pbc-etale-scheme-base-
   change, lem-weil-pbc-etale-composition-cancellation.
5. Write $S=\operatorname{Spec}R$. The affine descriptions in [def-sbc-affine-space] identify
   $T$ with $\operatorname{Spec}(R[t_1,\ldots,t_e][s_1,\ldots,s_d])$. The polynomial algebra
   maps to and from $R[z_1,\ldots,z_{d+e}]$ sending $s_i\leftrightarrow z_i$ and
   $t_j\leftrightarrow z_{d+j}$ and fixing $R$ are inverse: their composites fix every
   coefficient and every generator. Functoriality of [def-weil-affine-spectrum] gives the
   ordered isomorphism $c:T\simeq\mathbf A^{d+e}_S$. Under $c$, $p_{d+e,S}$ is the composite of
   the two projections, since both ring maps are the inclusion of $R$. The cartesian square in
   Step 4 says $p_{d,\mathbf A^e_S}b=vp_{d,V}$. Consequently $$p_{d+e,S}cbu=p_{e,S}p_{d,\mathbf
   A^e_S}bu=p_{e,S}vp_{d,V}u=(g|_V)(f|_U)=h|_U.$$ The first $d$ coordinates are exactly those of
   $f$. Dependencies: def-sbc-affine-space, def-weil-affine-spectrum.
6. The only chart spaces not already covered by Steps 1 and 3 are $T$ and $\mathbf A^{d+e}_S$.
   For each affine open $W\subseteq S$, [def-sbc-affine-space] identifies the inverse image
   under $\mathbf A^{d+e}_S\to S$ with $\operatorname{Spec}(\mathcal
   O_S(W)[z_1,\ldots,z_{d+e}])$. This single affine chart has an algebra generated by the finite
   list of displayed variables, so [def-weil-finite-type-morphism] says the projection is finite
   type. Its source is affine, so [lem-weil-pbc-affine-source-morphism-separated] makes the
   projection separated. Compose with the separated finite-type structure map of $S$ using [lem-
   weil-pbc-proper-fp-permanence](e) and [lem-sfb-finite-type-composition-base-change](1). Thus
   $\mathbf A^{d+e}_S$ is separated finite type over $k$; [lem-weil-pbc-finite-type-over-
   noetherian] over $S$ makes it Noetherian. The isomorphism $c$ gives all the same properties
   for $T$. In particular every indicated affine space, as well as $U,V,S$, is affine.
   Dependencies: def-sbc-affine-space, def-weil-finite-type-morphism, lem-weil-pbc-proper-fp-
   permanence, lem-sfb-finite-type-composition-base-change, lem-weil-pbc-finite-type-over-
   noetherian, lem-weil-pbc-affine-source-morphism-separated.
7. Every displayed chart arrow is a $k$-morphism between the separated finite-type spaces just
   obtained (this also includes the projections, the restricted structural maps, and the
   coordinate isomorphism). For each such arrow $a:A\to B$, the composite with
   $B\to\operatorname{Spec}k$ is the separated finite-type structural map of $A$. Thus [lem-
   weil-pbc-separated-cancellation](b) makes $a$ separated and [lem-weil-pbc-proper-fp-
   permanence](f) makes it locally of finite type. Its target is Noetherian, so [pqf-lem-lft-fp-
   locnoeth] makes it locally of finite presentation. The separated finite-type structure
   morphisms to the affine field spectrum make both $A$ and $B$ quasi-compact and quasi-
   separated by [lem-weil-pbc-qcqs-over-affine]; [lem-weil-pbc-qcqs-morphism-permanence](1) now
   makes $a$ of finite presentation. This proves the remaining admissibility assertions,
   including those for $v,b,bu$; $u$ was already supplied with them. If chart inclusions into
   the original schemes are included, the same argument applies since $X,Y,Z$ are separated
   finite-type Noetherian and hence quasi-separated. Dependencies: lem-weil-pbc-separated-
   cancellation, lem-weil-pbc-proper-fp-permanence, pqf-lem-lft-fp-locnoeth, lem-weil-pbc-qcqs-
   morphism-permanence, lem-weil-pbc-qcqs-over-affine.
8. The construction was made for an arbitrary $x$, with $x\in U$, so the resulting opens cover
   $X$. For $X=\varnothing$ take the empty family; no chart at a nonexistent point is requested.
   If $d=0$ or $e=0$, the corresponding lists of polynomial variables in Step 5 are empty, and
   [def-sbc-affine-space] identifies zero-dimensional affine space with its base. Every map,
   generator calculation, and projection identity above remains valid. No surjectivity of $f$ or
   $g$, nonempty fibre, or positive relative dimension was used. Dependencies: def-sbc-affine-
   space.
-/
theorem SmoothOfRelativeDimension.exists_nested_admissible_affine_charts
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ)
    (_hell : ell.Prime) (_hne : ell ≠ D.p)
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
    [IsSeparated f] [IsSeparated g]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g] :
    ∀ x : X, ∃ (S : Z.Opens) (V : Y.Opens) (U : X.Opens)
      (hVS : V ≤ g ⁻¹ᵁ S) (hUV : U ≤ f ⁻¹ᵁ V)
      (v : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin e)) S.toScheme)
      (u : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) V.toScheme)
      (c : AffineSpace (ULift.{u} (Fin d))
          (AffineSpace (ULift.{u} (Fin e)) S.toScheme) ≅
        AffineSpace (ULift.{u} (Fin (d + e))) S.toScheme),
      x ∈ U ∧ f x ∈ V ∧ g (f x) ∈ S ∧
      IsAffineOpen S ∧ IsAffineOpen V ∧ IsAffineOpen U ∧
      Etale v ∧ Etale u ∧
      v ≫ (AffineSpace (ULift.{u} (Fin e)) S.toScheme ↘ S.toScheme) =
        g.resLE S V hVS ∧
      u ≫ (AffineSpace (ULift.{u} (Fin d)) V.toScheme ↘ V.toScheme) =
        f.resLE V U hUV ∧
      Etale (AffineSpace.map (ULift.{u} (Fin d)) v) ∧
      Etale (u ≫ AffineSpace.map (ULift.{u} (Fin d)) v) ∧
      (∀ i : Fin d,
        c.hom.appTop (AffineSpace.coord S.toScheme (ULift.up (i.castAdd e))) =
          AffineSpace.coord (AffineSpace (ULift.{u} (Fin e)) S.toScheme) (ULift.up i)) ∧
      (∀ j : Fin e,
        c.hom.appTop (AffineSpace.coord S.toScheme (ULift.up (j.natAdd d))) =
          (AffineSpace (ULift.{u} (Fin d))
            (AffineSpace (ULift.{u} (Fin e)) S.toScheme) ↘
              AffineSpace (ULift.{u} (Fin e)) S.toScheme).appTop
                (AffineSpace.coord S.toScheme (ULift.up j))) ∧
      c.hom ≫ (AffineSpace (ULift.{u} (Fin (d + e))) S.toScheme ↘ S.toScheme) =
        (AffineSpace (ULift.{u} (Fin d))
          (AffineSpace (ULift.{u} (Fin e)) S.toScheme) ↘
            AffineSpace (ULift.{u} (Fin e)) S.toScheme) ≫
          (AffineSpace (ULift.{u} (Fin e)) S.toScheme ↘ S.toScheme) ∧
      U.ι ≫ f ≫ g =
        u ≫ AffineSpace.map (ULift.{u} (Fin d)) v ≫ c.hom ≫
          (AffineSpace (ULift.{u} (Fin (d + e))) S.toScheme ↘ S.toScheme) ≫ S.ι ∧
      (∀ W : Over (Spec (.of D.k)),
        W ∈ [
          Over.mk (S.ι ≫ (Z ↘ Spec (.of D.k))),
          Over.mk (V.ι ≫ (Y ↘ Spec (.of D.k))),
          Over.mk (U.ι ≫ (X ↘ Spec (.of D.k))),
          Over.mk ((AffineSpace (ULift.{u} (Fin e)) S.toScheme ↘ S.toScheme) ≫ S.ι ≫ (Z ↘ Spec
            (.of D.k))),
          Over.mk ((AffineSpace (ULift.{u} (Fin d)) V.toScheme ↘ V.toScheme) ≫ V.ι ≫ (Y ↘ Spec
            (.of D.k))),
          Over.mk ((AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin e)) S.toScheme)
            ↘ AffineSpace (ULift.{u} (Fin e)) S.toScheme) ≫ (AffineSpace (ULift.{u} (Fin e))
            S.toScheme ↘ S.toScheme) ≫ S.ι ≫ (Z ↘ Spec (.of D.k))),
          Over.mk ((AffineSpace (ULift.{u} (Fin (d + e))) S.toScheme ↘ S.toScheme) ≫ S.ι ≫ (Z ↘
            Spec (.of D.k)))]
        → IsNoetherian W.left ∧ IsSeparated W.hom ∧
          LocallyOfFiniteType W.hom ∧ QuasiCompact W.hom) ∧
      (∀ a : Arrow Scheme.{u},
        a ∈ [
          Arrow.mk (v),
          Arrow.mk (u),
          Arrow.mk (AffineSpace.map (ULift.{u} (Fin d)) v),
          Arrow.mk (u ≫ AffineSpace.map (ULift.{u} (Fin d)) v),
          Arrow.mk (u ≫ AffineSpace.map (ULift.{u} (Fin d)) v ≫ c.hom),
          Arrow.mk (c.hom),
          Arrow.mk (c.inv),
          Arrow.mk (AffineSpace (ULift.{u} (Fin e)) S.toScheme ↘ S.toScheme),
          Arrow.mk (AffineSpace (ULift.{u} (Fin d)) V.toScheme ↘ V.toScheme),
          Arrow.mk (AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin e)) S.toScheme)
            ↘ AffineSpace (ULift.{u} (Fin e)) S.toScheme),
          Arrow.mk (AffineSpace (ULift.{u} (Fin (d + e))) S.toScheme ↘ S.toScheme),
          Arrow.mk (g.resLE S V hVS),
          Arrow.mk (f.resLE V U hUV),
          Arrow.mk (u ≫ AffineSpace.map (ULift.{u} (Fin d)) v ≫ c.hom ≫ (AffineSpace (ULift.{u}
            (Fin (d + e))) S.toScheme ↘ S.toScheme)),
          Arrow.mk (U.ι),
          Arrow.mk (V.ι),
          Arrow.mk (S.ι)]
        → IsSeparated a.hom ∧ LocallyOfFinitePresentation a.hom ∧
          QuasiCompact a.hom ∧ QuasiSeparated a.hom) := by
  classical
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D.k))
  have : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of D.k))
  have : QuasiSeparatedSpace Z :=
    quasiSeparatedSpace_of_quasiSeparated (Z ↘ Spec (.of D.k))
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  have : Smooth g := SmoothOfRelativeDimension.smooth e g
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of D.k))
  have : IsLocallyNoetherian Z :=
    LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of D.k))
  intro x
  obtain ⟨S, V, U, hVS, hUV, v, u, hxU, hxV, hxS, hS, hV, hU, hv, hu, hvg, huf⟩ :=
    nestedLocalCharts f g d e x
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : IsAffine S.toScheme := hS
  have : Etale u := hu
  have : Etale v := hv
  have : Etale (AffineSpace.map (ULift.{u} (Fin d)) v) :=
    MorphismProperty.of_isPullback
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin d)) v).flip hv
  have : LocallyOfFinitePresentation (f.resLE V U hUV) := by
    rw [← huf]
    infer_instance
  have : LocallyOfFinitePresentation (g.resLE S V hVS) := by
    rw [← hvg]
    infer_instance
  let c := orderedAffineIso S.toScheme d e
  refine ⟨S, V, U, hVS, hUV, v, u, c, hxU, hxV, hxS, hS, hV, hU, hv, hu,
    hvg, huf, inferInstance, inferInstance, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp [c, orderedAffineIso]
  · intro j
    simp [c, orderedAffineIso]
  · simp [c, orderedAffineIso]
  · have hc : c.hom ≫ (AffineSpace (ULift.{u} (Fin (d + e))) S.toScheme ↘
          S.toScheme) =
        (AffineSpace (ULift.{u} (Fin d))
          (AffineSpace (ULift.{u} (Fin e)) S.toScheme) ↘
            AffineSpace (ULift.{u} (Fin e)) S.toScheme) ≫
          (AffineSpace (ULift.{u} (Fin e)) S.toScheme ↘ S.toScheme) := by
      simp [c, orderedAffineIso]
    rw [reassoc_of% hc, AffineSpace.map_over_assoc, reassoc_of% hvg,
      Scheme.Hom.resLE_comp_ι, reassoc_of% huf, Scheme.Hom.resLE_comp_ι_assoc]
  · intro W hW
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hW
    rcases hW with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [Over.mk_left, Over.mk_hom]
      exact affineFiniteTypeProperties _
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom]
      exact affineArrowProperties _

end AlgebraicGeometry
