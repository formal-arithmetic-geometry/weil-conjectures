/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # The Cartesian diagonal neighbourhood of an étale coordinate chart

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-orientation/sk-prop-sp-orientation-charts.proof.md, Step 1.
(blueprint: lem-pur-chart-cartesian-domain).

All products and restricted schemes below are Mathlib's scheme pullbacks. In particular
`pullback p V.ι` is the canonical base-change presentation of affine space over V.
The open neighbourhood is specified by its exact carrier, and the two inverse-image
assertions are Cartesian squares of schemes, retaining their scheme structures.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The complete geometric conclusion for the chart. The local names only abbreviate
canonical pullbacks, projections and maps between pullbacks. `z` is the closed map
U_V ×_{A_V} U_V → U_V ×_V U_V; `r` changes the second coordinate and `s` changes
the first. The existential diagonal into O is uniquely specified by its composite
with the open inclusion. No choice of a neighbourhood is left: its carrier is the
complement of the image of the off-diagonal component of Z.
Source: blueprint chart proof Step 1 and its separated finite-type domain checks.
(blueprint: lem-pur-chart-cartesian-domain). -/
def ChartCartesianDomainConclusion (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    (aY : Y ⟶ Spec (.of P.field.k)) (U : X.Opens)
    (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) Y)
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = U.ι ≫ f) : Prop :=
  let A := AffineSpace (ULift.{u} (Fin d)) Y
  let p : A ⟶ Y := A ↘ Y
  let h := U.ι ≫ f
  (∀ T ∈ [Y, X, U.toScheme, A], IsNoetherian T) ∧
  IsSeparated h ∧ LocallyOfFiniteType h ∧ QuasiCompact h ∧
  IsSeparated e ∧ LocallyOfFiniteType e ∧ QuasiCompact e ∧
  QuasiCompact U.ι ∧ LocallyOfFiniteType U.ι ∧
  ∀ (V : Y.Opens), IsAffineOpen V →
    let XV := pullback f V.ι
    let UV := pullback h V.ι
    let AV := pullback p V.ι
    let fV : XV ⟶ V.toScheme := pullback.snd f V.ι
    let hV := pullback.snd h V.ι
    let pV := pullback.snd p V.ι
    let jV : UV ⟶ XV := pullback.map h V.ι f V.ι U.ι (𝟙 _) (𝟙 _)
      (Category.comp_id h)
      ((Category.comp_id V.ι).trans (Category.id_comp V.ι).symm)
    let eV : UV ⟶ AV := pullback.map h V.ι p V.ι e (𝟙 _) (𝟙 _)
      ((Category.comp_id h).trans w.symm)
      ((Category.comp_id V.ι).trans (Category.id_comp V.ι).symm)
    let b := eV ≫ pV
    let W := pullback b b
    let WA := pullback pV pV
    let Z := pullback eV eV
    let M := pullback b pV
    let z : Z ⟶ W := pullback.mapDesc eV eV pV
    let ee : W ⟶ WA := pullback.map b b pV pV eV eV (𝟙 _)
      (Category.comp_id b) (Category.comp_id b)
    let r : W ⟶ M := pullback.map b b b pV (𝟙 _) eV (𝟙 _)
      ((Category.comp_id b).trans (Category.id_comp b).symm) (Category.comp_id b)
    let s : M ⟶ WA := pullback.map b pV pV pV eV (𝟙 _) (𝟙 _)
      (Category.comp_id b)
      ((Category.comp_id pV).trans (Category.id_comp pV).symm)
    let graph : UV ⟶ M := pullback.lift (𝟙 UV) eV (Category.id_comp b)
    (∀ T ∈ [Over.mk (V.ι ≫ aY),
        Over.mk (pullback.fst f V.ι ≫ f ≫ aY),
        Over.mk (pullback.fst h V.ι ≫ h ≫ aY),
        Over.mk (pullback.fst p V.ι ≫ p ≫ aY),
        Over.mk (pullback.fst b b ≫ b ≫ V.ι ≫ aY),
        Over.mk (pullback.fst pV pV ≫ pV ≫ V.ι ≫ aY),
        Over.mk (pullback.fst eV eV ≫ b ≫ V.ι ≫ aY),
        Over.mk (pullback.fst b pV ≫ b ≫ V.ι ≫ aY)],
      IsSeparated T.hom ∧ LocallyOfFiniteType T.hom ∧ QuasiCompact T.hom) ∧
    SmoothOfRelativeDimension d fV ∧ SmoothOfRelativeDimension d hV ∧
    SmoothOfRelativeDimension d pV ∧
    SmoothOfRelativeDimension d (pullback.fst b b) ∧
    SmoothOfRelativeDimension d (pullback.snd b b) ∧
    SmoothOfRelativeDimension d (pullback.fst pV pV) ∧
    SmoothOfRelativeDimension d (pullback.snd pV pV) ∧
    QuasiCompact V.ι ∧ LocallyOfFiniteType V.ι ∧
    QuasiCompact jV ∧ LocallyOfFiniteType jV ∧
    QuasiCompact (pullback.fst f V.ι) ∧ LocallyOfFiniteType (pullback.fst f V.ι) ∧
    QuasiCompact (pullback.fst h V.ι) ∧ LocallyOfFiniteType (pullback.fst h V.ι) ∧
    QuasiCompact (pullback.fst p V.ι) ∧ LocallyOfFiniteType (pullback.fst p V.ι) ∧
    IsSeparated hV ∧ LocallyOfFiniteType hV ∧ QuasiCompact hV ∧
    IsSeparated eV ∧ LocallyOfFiniteType eV ∧ QuasiCompact eV ∧
    IsOpenImmersion (pullback.diagonal eV) ∧
    IsClosedImmersion (pullback.diagonal eV) ∧
    QuasiCompact (pullback.diagonal eV) ∧ LocallyOfFiniteType (pullback.diagonal eV) ∧
    IsClosedImmersion z ∧
    IsClosed (z '' (Set.range (pullback.diagonal eV))ᶜ) ∧
    ∃ O : W.Opens,
      (O : Set W) = (z '' (Set.range (pullback.diagonal eV))ᶜ)ᶜ ∧
      QuasiCompact O.ι ∧ LocallyOfFiniteType O.ι ∧
      ∃ δ : UV ⟶ O.toScheme,
        δ ≫ O.ι = pullback.diagonal b ∧
        IsPullback δ eV (O.ι ≫ ee) (pullback.diagonal pV) ∧
        Etale (O.ι ≫ ee) ∧ IsClosedImmersion δ ∧
        SmoothOfRelativeDimension d (O.ι ≫ pullback.fst b b) ∧
        IsSeparated (O.ι ≫ pullback.fst b b) ∧
        LocallyOfFiniteType (O.ι ≫ pullback.fst b b) ∧
        QuasiCompact (O.ι ≫ pullback.fst b b) ∧
        δ ≫ (O.ι ≫ pullback.fst b b) = 𝟙 UV ∧
        O.ι ≫ ee = (O.ι ≫ r) ≫ s ∧ Etale (O.ι ≫ r) ∧
        (O.ι ≫ r) ≫ pullback.fst b pV = O.ι ≫ pullback.fst b b ∧
        IsPullback (pullback.fst b pV) s eV (pullback.fst pV pV) ∧
        IsPullback δ (𝟙 UV) (O.ι ≫ r) graph ∧
        IsSeparated (O.ι ≫ pullback.fst b b ≫ b ≫ V.ι ≫ aY) ∧
        LocallyOfFiniteType (O.ι ≫ pullback.fst b b ≫ b ≫ V.ι ≫ aY) ∧
        QuasiCompact (O.ι ≫ pullback.fst b b ≫ b ≫ V.ι ≫ aY)

/-- Cutting out the closed complement of an open component gives its Cartesian square. -/
private theorem cartesianOpenCut {D Z W : Scheme.{u}}
    (i : D ⟶ Z) (z : Z ⟶ W) [IsOpenImmersion i] [IsClosedImmersion z]
    (O : W.Opens) (hO : (O : Set W) = (z '' (Set.range i)ᶜ)ᶜ) :
    ∃ δ : D ⟶ O.toScheme, δ ≫ O.ι = i ≫ z ∧ IsPullback δ i O.ι z := by
  classical
  have hr : Set.range (i ≫ z) ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι, hO]
    rintro _ ⟨x, rfl⟩ ⟨y, hy, heq⟩
    exact hy ⟨x, z.isClosedEmbedding.injective heq.symm⟩
  let δ := IsOpenImmersion.lift O.ι (i ≫ z) hr
  have hδ : δ ≫ O.ι = i ≫ z := IsOpenImmersion.lift_fac _ _ _
  refine ⟨δ, hδ, IsOpenImmersion.isPullback δ i O.ι z hδ.symm ?_⟩
  apply TopologicalSpace.Opens.ext
  change z ⁻¹' (Set.range O.ι) = Set.range i
  rw [Scheme.Opens.range_ι, hO]
  ext x
  constructor
  · intro hx
    by_contra hn
    exact hx ⟨x, hn, rfl⟩
  · rintro hx ⟨y, hy, heq⟩
    exact hy (z.isClosedEmbedding.injective heq ▸ hx)

/-- The inverse image of the graph imposes exactly equality of the two e-composites. -/
private theorem mapGraphPullback {D A S : Scheme.{u}} (e : D ⟶ A) (p : A ⟶ S) :
    IsPullback (pullback.mapDesc e e p) (pullback.fst e e)
      (pullback.map (e ≫ p) (e ≫ p) (e ≫ p) p (𝟙 D) e (𝟙 S)
        (by simp) (by simp))
      (pullback.lift (𝟙 D) e (Category.id_comp (e ≫ p))) := by
  let b := e ≫ p
  let r := pullback.map b b b p (𝟙 D) e (𝟙 S) (by simp) (by simp [b])
  let graph := pullback.lift (𝟙 D) e (Category.id_comp b)
  have key (c : PullbackCone r graph) :
      c.fst ≫ pullback.fst b b = c.snd ∧
      c.fst ≫ pullback.snd b b ≫ e = c.snd ≫ e := by
    constructor
    · simpa [r, graph] using c.condition =≫ pullback.fst b p
    · simpa [r, graph] using c.condition =≫ pullback.snd b p
  change IsPullback (pullback.mapDesc e e p) (pullback.fst e e) r graph
  have comm : pullback.mapDesc e e p ≫ r = pullback.fst e e ≫ graph := by
    apply pullback.hom_ext <;> simp [b, r, graph, pullback.mapDesc, pullback.map,
      pullback.condition]
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ comm) ?_
  refine PullbackCone.IsLimit.mk _
    (fun c ↦ pullback.lift (c.fst ≫ pullback.fst b b)
      (c.fst ≫ pullback.snd b b) ?_) ?_ ?_ ?_
  · simp only [Category.assoc]
    rw [(key c).2, ← Category.assoc, (key c).1]
  · intro c
    apply pullback.hom_ext <;> simp [b, pullback.mapDesc, pullback.map]
  · intro c
    simpa using (key c).1
  · intro c m hm _
    apply pullback.hom_ext
    · simpa [b, pullback.mapDesc, pullback.map] using hm =≫ pullback.fst b b
    · simpa [b, pullback.mapDesc, pullback.map] using hm =≫ pullback.snd b b

/-- A coordinate chart has the prescribed Cartesian diagonal neighbourhood after
restriction to each affine open of Y. The setting contains k = algebraic closure
of F_q, a prime ell distinct from its characteristic, and n ≥ 1; the bottom
coefficient extension is exactly E = Q_ell. Y need not be separated over k.
Source: blueprint chart proof Step 1, with the node's expanded domain checks.
(blueprint: lem-pur-chart-cartesian-domain).

Proof:
1. Apply lem-weil-pbc-finite-type-over-noetherian to X and Y over Spec k.
   Open subschemes remain Noetherian by lem-weil-pbc-noetherian-open-subscheme-noetherian;
   lem-weil-pbc-locally-noetherian-quasi-separated, lem-weil-pbc-qcqs-morphism-permanence
   and lem-weil-pbc-qc-open-immersion-finite-type give finite-type open inclusions.
2. Affine space is affine and finite type over Y (def-sbc-affine-space).
   lem-weil-pbc-affine-morphism-permanence gives separatedness. Compose with aY
   using lem-sfb-finite-type-composition-base-change. Separated cancellation
   (lem-weil-pbc-separated-cancellation) gives separatedness of h and e, and
   lemma-nagata-finite-type-to-separated-target gives finite type of e.
3. Apply lem-pod-separated-finite-type-base-change to all restrictions and product
   projections. V is separated over k by lem-weil-pbc-affine-source-morphism-separated.
   Compose using lem-weil-pbc-proper-fp-permanence and finite-type composition.
4. Open immersions are étale (lem-weil-pbc-open-immersion-etale), hence smooth of
   dimension zero (lem-weil-pbc-etale-smooth-zero-dimensional-fibres). Apply
   sbc-lem-affine-space-smooth and lem-sbc-smooth-relative-dimension-permanence
   under base change and composition to obtain all the dimension assertions.
5. The universal property def-pc-fibre-product identifies Z with the inverse
   image of the diagonal of AV. Since pV is separated, z is closed by
   lem-weil-pbc-proper-fp-permanence. The diagonal of the separated étale eV
   is clopen (def-weil-etale-morphism and def-weil-unramified-morphism).
   Thus its complement in Z has closed image C in W. Take O = W minus C.
6. Each factor r and s is a base change of eV, so is étale by
   lem-weil-pbc-etale-scheme-base-change. Restrict and compose using
   lem-weil-pbc-etale-composition-cancellation. The inverse image of the
   diagonal in O is the diagonal component of Z as schemes, giving IsPullback.
7. The diagonal is a closed section because hV is separated. The open inclusion
   into the Noetherian W is finite type, giving all properties of O and p_U.
   The inverse image of the graph under r is Z by the same universal property;
   restricting to O makes it exactly the diagonal, as a Cartesian square.
   The intermediate product is separated finite type by base change and composition.
   These arguments include empty opens and relative dimension zero. -/
theorem chartCartesianDomain (P : PurityFiniteSetting.{u}) (_hE : P.extension = ⊥)
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (U : X.Opens) (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = U.ι ≫ f) :
    P.ChartCartesianDomainConclusion d f aY U e w := by
  let A := AffineSpace (ULift.{u} (Fin d)) Y
  let p : A ⟶ Y := A ↘ Y
  let h := U.ι ≫ f
  have hY : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  have hYc : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := ⟨⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  have : CompactSpace U := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact (U : Set X))
  have : IsNoetherian U.toScheme := ⟨⟩
  have hp : SmoothOfRelativeDimension d p := by
    simpa [p, A] using AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin d)) Y
  have : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian A := ⟨⟩
  have he : IsSeparated e := by
    have : IsSeparated (e ≫ p) := by
      change IsSeparated (e ≫ (A ↘ Y))
      rw [w]
      infer_instance
    exact IsSeparated.of_comp e p
  dsimp only [ChartCartesianDomainConclusion]
  refine ⟨?_, inferInstance, inferInstance, inferInstance, he, inferInstance,
    inferInstance, inferInstance, inferInstance, ?_⟩
  · intro T hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl | rfl | rfl <;> infer_instance
  · intro V hVaff
    have : IsAffine V.toScheme := hVaff
    let XV := pullback f V.ι
    let UV := pullback h V.ι
    let AV := pullback p V.ι
    let fV : XV ⟶ V.toScheme := pullback.snd f V.ι
    let hV := pullback.snd h V.ι
    let pV := pullback.snd p V.ι
    let jV : UV ⟶ XV := pullback.map h V.ι f V.ι U.ι (𝟙 _) (𝟙 _)
      (Category.comp_id h)
      ((Category.comp_id V.ι).trans (Category.id_comp V.ι).symm)
    let eV : UV ⟶ AV := pullback.map h V.ι p V.ι e (𝟙 _) (𝟙 _)
      ((Category.comp_id h).trans w.symm)
      ((Category.comp_id V.ι).trans (Category.id_comp V.ι).symm)
    let b := eV ≫ pV
    let W := pullback b b
    let WA := pullback pV pV
    let Z := pullback eV eV
    let M := pullback b pV
    let z : Z ⟶ W := pullback.mapDesc eV eV pV
    let ee : W ⟶ WA := pullback.map b b pV pV eV eV (𝟙 _)
      (Category.comp_id b) (Category.comp_id b)
    let r : W ⟶ M := pullback.map b b b pV (𝟙 _) eV (𝟙 _)
      ((Category.comp_id b).trans (Category.id_comp b).symm) (Category.comp_id b)
    let s : M ⟶ WA := pullback.map b pV pV pV eV (𝟙 _) (𝟙 _)
      (Category.comp_id b)
      ((Category.comp_id pV).trans (Category.id_comp pV).symm)
    let graph : UV ⟶ M := pullback.lift (𝟙 UV) eV (Category.id_comp b)
    have hb : b = hV := by
      dsimp [b, eV, pV, hV]
      simp
    have hs : SmoothOfRelativeDimension d h := by
      simpa using (smoothOfRelativeDimension_comp (f := U.ι) (n := 0) (m := d) f)
    have : SmoothOfRelativeDimension d b := by rw [hb]; infer_instance
    have : IsSeparated b := by rw [hb]; infer_instance
    have : LocallyOfFiniteType b := by rw [hb]; infer_instance
    have : QuasiCompact b := by rw [hb]; infer_instance
    have hev : IsPullback (pullback.fst h V.ι) eV e (pullback.fst p V.ι) := by
      apply IsPullback.of_bot ?_ (by simp [eV]) (IsPullback.of_hasPullback p V.ι)
      simpa only [show e ≫ p = h from w, eV, pullback.lift_snd, Category.comp_id] using
        IsPullback.of_hasPullback h V.ι
    have : IsOpenImmersion jV := MorphismProperty.of_isPullback
      (isPullback_pullback_map_left U.ι f V.ι) inferInstance
    have : Etale eV := MorphismProperty.of_isPullback hev inferInstance
    have : IsSeparated eV := MorphismProperty.of_isPullback hev he
    have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst b b ≫ pullback.fst h V.ι)
    have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace
      (pullback.fst b b ≫ pullback.fst h V.ι)
    have : IsNoetherian W := ⟨⟩
    have hr : IsPullback r (pullback.snd b b) (pullback.snd b pV) eV :=
      isPullback_pullback_map b b pV eV rfl
    have hsp : IsPullback (pullback.fst b pV) s eV (pullback.fst pV pV) :=
      isPullback_pullback_map_left eV pV pV
    have : Etale r := MorphismProperty.of_isPullback hr.flip inferInstance
    have : Etale s := MorphismProperty.of_isPullback hsp inferInstance
    have hee : ee = r ≫ s := by
      apply pullback.hom_ext <;> simp [ee, r, s]
    have : Etale ee := by rw [hee]; infer_instance
    have hz : IsClosed (z '' (Set.range (pullback.diagonal eV))ᶜ) :=
      z.isClosedEmbedding.isClosedMap _
        (IsOpenImmersion.isOpen_range (pullback.diagonal eV)).isClosed_compl
    let O : W.Opens := ⟨_, hz.isOpen_compl⟩
    have hO : (O : Set W) = (z '' (Set.range (pullback.diagonal eV))ᶜ)ᶜ := rfl
    obtain ⟨δ, hδ, hcut⟩ := cartesianOpenCut (pullback.diagonal eV) z O hO
    have hdiag : pullback.diagonal eV ≫ z = pullback.diagonal b := by
      apply pullback.hom_ext <;> simp [b, z, pullback.mapDesc, pullback.map]
    have hδ' : δ ≫ O.ι = pullback.diagonal b := hδ.trans hdiag
    have hbig : IsPullback z (pullback.fst eV eV ≫ eV) ee
        (pullback.diagonal pV) :=
      (pullback_map_diagonal_isPullback eV eV pV).flip
    have hcart : IsPullback δ eV (O.ι ≫ ee) (pullback.diagonal pV) := by
      simpa only [Category.assoc, pullback.diagonal_fst_assoc, Category.id_comp]
        using hcut.paste_vert hbig
    have hgraph : IsPullback δ (𝟙 UV) (O.ι ≫ r) graph := by
      simpa only [pullback.diagonal_fst] using
        hcut.paste_vert (mapGraphPullback eV pV)
    have : IsClosedImmersion δ := by
      have : IsClosedImmersion (δ ≫ O.ι) := by rw [hδ']; infer_instance
      exact IsClosedImmersion.of_comp δ O.ι
    have : SmoothOfRelativeDimension d (O.ι ≫ pullback.fst b b) := by
      simpa using (smoothOfRelativeDimension_comp
        (f := O.ι) (n := 0) (m := d) (pullback.fst b b))
    have : IsSeparated (V.ι ≫ aY) := inferInstance
    have : IsSeparated (b ≫ V.ι ≫ aY) := inferInstance
    have : LocallyOfFiniteType (b ≫ V.ι ≫ aY) := inferInstance
    have : QuasiCompact (b ≫ V.ι ≫ aY) := inferInstance
    have : IsSeparated (pV ≫ V.ι ≫ aY) := inferInstance
    have : LocallyOfFiniteType (pV ≫ V.ι ≫ aY) := inferInstance
    have : QuasiCompact (pV ≫ V.ι ≫ aY) := inferInstance
    have hspaces : ∀ T ∈ [Over.mk (V.ι ≫ aY),
        Over.mk (pullback.fst f V.ι ≫ f ≫ aY),
        Over.mk (pullback.fst h V.ι ≫ h ≫ aY),
        Over.mk (pullback.fst p V.ι ≫ p ≫ aY),
        Over.mk (pullback.fst b b ≫ b ≫ V.ι ≫ aY),
        Over.mk (pullback.fst pV pV ≫ pV ≫ V.ι ≫ aY),
        Over.mk (pullback.fst eV eV ≫ b ≫ V.ι ≫ aY),
        Over.mk (pullback.fst b pV ≫ b ≫ V.ι ≫ aY)],
        IsSeparated T.hom ∧ LocallyOfFiniteType T.hom ∧ QuasiCompact T.hom := by
      intro T hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
      rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals dsimp only [Over.mk, Over.hom, CostructuredArrow.mk]
      all_goals first
        | exact ⟨inferInstance, inferInstance, inferInstance⟩
        | (rw [pullback.condition_assoc]
           exact ⟨inferInstance, inferInstance, inferInstance⟩)
    refine ⟨hspaces, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, ?_⟩
    refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, hz, O, hO,
      inferInstance, inferInstance, δ, hδ', hcart, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      ?_, ?_, inferInstance, ?_, hsp, hgraph, ?_, ?_, ?_⟩
    · rw [← Category.assoc, hδ', pullback.diagonal_fst]
    · change O.ι ≫ ee = (O.ι ≫ r) ≫ s
      rw [hee, Category.assoc]
    · change (O.ι ≫ r) ≫ pullback.fst b pV = O.ι ≫ pullback.fst b b
      simp [r]
    · infer_instance
    · infer_instance
    · infer_instance

end WeilConjectures.PurityFiniteSetting
