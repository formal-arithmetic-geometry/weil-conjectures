/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Connected.Clopen

import WeilConjectures.Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.DescendQCOpenFGSubalgebra
import Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Geometric components after a finite constant extension

Source: Stacks Project, varieties.tex, Tags 038E and 0387; morphisms.tex, Tags 01VB and 02NK
(blueprint: lem-zl-affine-geometric-components-finite-extension).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-- The data expressing a finite-field decomposition into affine open-and-closed geometric
components.  The maps `baseComponent` are characterized by their two pullback projections, so
that they are the canonical base changes of the inclusions `inclusion`.
Source: Stacks Project, varieties.tex, Tags 038E and 0387
(blueprint: lem-zl-affine-geometric-components-finite-extension). -/
structure AffineGeometricComponentDecomposition
    (D : WeilConjectures.FiniteFieldDatum.{u}) {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (CommRingCat.of D.k₀)) (e : ℕ) (he : 1 ≤ e) where
  I : Type u
  finite_I : Finite I
  component : I → Scheme.{u}
  componentMap : ∀ i, component i ⟶
    Spec (CommRingCat.of (D.extensionSubfield e he))
  inclusion : ∀ i, component i ⟶
    pullback f₀ (Spec.map (CommRingCat.ofHom (D.extensionEmbedding e he)))
  inclusion_over : ∀ i, inclusion i ≫
      pullback.snd f₀ (Spec.map (CommRingCat.ofHom (D.extensionEmbedding e he))) = componentMap i
  affine : ∀ i, IsAffine (component i)
  nonempty : ∀ i, Nonempty (component i).carrier
  open_closed : ∀ i, IsOpenImmersion (inclusion i) ∧ IsClosedImmersion (inclusion i)
  cover : Set.univ = ⋃ i, Set.range (inclusion i).base
  pairwise_disjoint : ∀ ⦃i j⦄, i ≠ j →
    Disjoint (Set.range (inclusion i).base) (Set.range (inclusion j).base)
  geometrically_connected : ∀ i, GeometricallyConnected (componentMap i)
  baseComponent : ∀ i,
    pullback (componentMap i)
      (Spec.map (CommRingCat.ofHom ((D.extensionSubfield e he).subtype))) ⟶
      pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  baseComponent_fst : ∀ i, baseComponent i ≫
      pullback.fst f₀ (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
    pullback.fst (componentMap i)
      (Spec.map (CommRingCat.ofHom ((D.extensionSubfield e he).subtype))) ≫
      inclusion i ≫ pullback.fst f₀
        (Spec.map (CommRingCat.ofHom (D.extensionEmbedding e he)))
  baseComponent_snd : ∀ i, baseComponent i ≫
      pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
    pullback.snd (componentMap i)
      (Spec.map (CommRingCat.ofHom ((D.extensionSubfield e he).subtype)))
  componentPoint : ∀ i,
    (pullback (componentMap i)
      (Spec.map (CommRingCat.ofHom ((D.extensionSubfield e he).subtype)))).carrier
  component_range : ∀ i, Set.range (baseComponent i).base =
    connectedComponent ((baseComponent i).base (componentPoint i))
  components_bijective : Function.Bijective (fun i ↦
    ConnectedComponents.mk ((baseComponent i).base (componentPoint i)))

private noncomputable def constantChange
    {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (φ : A →ₐ[k] B) :
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap k B))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
  baseChangeMap f (Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun h ↦ Spec.map (CommRingCat.ofHom h)) φ.comp_algebraMap) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k B))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))))

private theorem constantChange_comp
    {k A B C : Type u} [Field k] [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (φ : A →ₐ[k] B) (ψ : B →ₐ[k] C) :
    constantChange f ψ ≫ constantChange f φ = constantChange f (ψ.comp φ) := by
  unfold constantChange
  rw [← baseChangeMap_comp]
  congr 1
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

private theorem compact_open_descends_field
    {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (V : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).Opens)
    (hV : IsCompact V.1) :
    ∃ L : IntermediateField k Ω, Module.Finite k L ∧
      ∃ W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))).Opens,
        V = constantChange f L.val ⁻¹ᵁ W := by
  obtain ⟨A, hA, W, -, p, hp, hpre⟩ := descend_qc_open_fg_subalgebra k X f Ω V hV
  have hfin : Module.Finite k A := by
    obtain ⟨s, hs⟩ := hA
    have hf := Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet
      (fun x _ ↦ (Algebra.IsAlgebraic.isAlgebraic (R := k) x).isIntegral)
    rw [hs] at hf
    exact hf
  let L := A.toIntermediateField' (by
    let := fieldOfFiniteDimensional k A
    exact Field.toIsField A)
  exact ⟨L, hfin, W, by rw [hpre, hp]; rfl⟩

private theorem finite_opens_descend_field
    {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {I : Type u} [Finite I]
    (V : I → (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).Opens)
    (hV : ∀ i, IsCompact (V i).1) :
    ∃ L : IntermediateField k Ω, Module.Finite k L ∧
      ∃ W : I → (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))).Opens,
        ∀ i, V i = constantChange f L.val ⁻¹ᵁ W i := by
  classical
  choose K hK W hW using fun i ↦ compact_open_descends_field f (V i) (hV i)
  let (i : I) : Module.Finite k (K i) := hK i
  let L : IntermediateField k Ω := ⨆ i, K i
  let t (i : I) := IntermediateField.inclusion (le_iSup K i : K i ≤ L)
  refine ⟨L, inferInstance, fun i ↦ constantChange f (t i) ⁻¹ᵁ W i, ?_⟩
  intro i
  rw [← Scheme.Hom.comp_preimage, constantChange_comp]
  exact hW i

private theorem finite_opens_descend_extension
    (D : WeilConjectures.FiniteFieldDatum.{u}) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of D.k₀)) {I : Type u} [Finite I]
    (V : I → (pullback f (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).Opens)
    (hV : ∀ i, IsCompact (V i).1) :
    ∃ (e : ℕ) (he : 1 ≤ e),
      ∃ p : pullback f (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ⟶
        pullback f (Spec.map (CommRingCat.ofHom (D.extensionEmbedding e he))),
      (IsPullback p (pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
        (pullback.snd f (Spec.map (CommRingCat.ofHom (D.extensionEmbedding e he))))
        (Spec.map (CommRingCat.ofHom (D.extensionSubfield e he).subtype)) ∧
        p ≫ pullback.fst f
          (Spec.map (CommRingCat.ofHom (D.extensionEmbedding e he))) =
          pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) ∧
      ∃ W : I → (pullback f
          (Spec.map (CommRingCat.ofHom (D.extensionEmbedding e he)))).Opens,
        ∀ i, V i = p ⁻¹ᵁ W i := by
  classical
  obtain ⟨L, hL, W, hW⟩ := finite_opens_descend_field f V hV
  let := hL
  let e := Module.finrank D.k₀ L
  have he : 1 ≤ e := Module.finrank_pos
  let E := D.extensionSubfield e he
  have hspec := (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime
    D.exponent_pos D.cardinality_eq D.k₀ D.card_base D.k e he).choose_spec
  have hcard : Nat.card L = D.q ^ e := by
    rw [Module.natCard_eq_pow_finrank (K := D.k₀), D.card_base]
  have hEq : L.toSubfield = E := hspec.2.2.1 L.toSubfield hcard
  have hemb : E.subtype.comp (D.extensionEmbedding e he) = algebraMap D.k₀ D.k :=
    hspec.2.2.2.2.2.2.choose_spec
  let : Algebra D.k₀ E := (D.extensionEmbedding e he).toAlgebra
  let φ : L →ₐ[D.k₀] E :=
    { toRingHom := (RingEquiv.subfieldCongr hEq).toRingHom
      commutes' := by
        intro x
        apply Subtype.ext
        exact (congrArg (fun h : D.k₀ →+* D.k ↦ h x) hemb).symm }
  let ψ : E →ₐ[D.k₀] D.k :=
    { toRingHom := E.subtype
      commutes' := fun x ↦ congrArg (fun h : D.k₀ →+* D.k ↦ h x) hemb }
  refine ⟨e, he, constantChange f ψ, ?_,
    fun i ↦ constantChange f φ ⁻¹ᵁ W i, ?_⟩
  · exact ⟨isPullback_baseChangeMap f _, baseChangeMap_fst f _⟩
  · intro i
    rw [← Scheme.Hom.comp_preimage, constantChange_comp]
    exact hW i

private theorem exists_affine_geometric_component_decomposition
    (D : WeilConjectures.FiniteFieldDatum.{u}) {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (CommRingCat.of D.k₀)) [IsAffine X₀]
    [LocallyOfFiniteType f₀] [QuasiCompact f₀] :
    ∃ (e : ℕ) (he : 1 ≤ e), Nonempty (AffineGeometricComponentDecomposition D f₀ e he) := by
  classical
  let X := pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  have : IsLocallyNoetherian X := inferInstance
  have : IsNoetherian X := ⟨⟩
  let I := ConnectedComponents X
  choose r hr using (ConnectedComponents.surjective_coe : ∀ i : I, ∃ x : X,
    ConnectedComponents.mk x = i)
  let V (i : I) : X.Opens :=
    ⟨ConnectedComponents.mk ⁻¹' {i},
      (isOpen_discrete {i}).preimage ConnectedComponents.continuous_coe⟩
  have hVr (i : I) : (V i : Set X) = connectedComponent (r i) := by
    change ConnectedComponents.mk ⁻¹' {i} = _
    simpa only [hr i] using (connectedComponents_preimage_singleton (x := r i))
  obtain ⟨e, he, p, ⟨hp, hpfst⟩, W, hW⟩ := finite_opens_descend_extension D f₀ V
    (fun i ↦ TopologicalSpace.NoetherianSpace.isCompact _)
  let Y := pullback f₀ (Spec.map (CommRingCat.ofHom (D.extensionEmbedding e he)))
  let g := pullback.snd f₀ (Spec.map (CommRingCat.ofHom (D.extensionEmbedding e he)))
  let b := Spec.map (CommRingCat.ofHom (D.extensionSubfield e he).subtype)
  have : Surjective b := inferInstance
  have : Surjective p := MorphismProperty.of_isPullback hp.flip inferInstance
  have hmem (i : I) (x : X) : p x ∈ W i ↔ ConnectedComponents.mk x = i := by
    change x ∈ p ⁻¹ᵁ W i ↔ _
    rw [← hW i]
    rfl
  have hcover : (⋃ i, (W i : Set Y)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨x, rfl⟩ := p.surjective y
    exact Set.mem_iUnion.mpr ⟨ConnectedComponents.mk x, (hmem _ _).mpr rfl⟩
  have hdisjoint : ∀ ⦃i j : I⦄, i ≠ j → Disjoint (W i : Set Y) (W j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro y hi hj
    obtain ⟨x, rfl⟩ := p.surjective y
    exact hij (((hmem i x).mp hi).symm.trans ((hmem j x).mp hj))
  have hclosed (i : I) : IsClosed (W i : Set Y) := by
    rw [← isOpen_compl_iff]
    have heq : (W i : Set Y)ᶜ = ⋃ j : {j : I // j ≠ i}, (W j.1 : Set Y) := by
      ext y
      obtain ⟨x, rfl⟩ := p.surjective y
      simp only [Set.mem_compl_iff, Set.mem_iUnion]
      change (p x ∉ W i) ↔ ∃ j : {j : I // j ≠ i}, p x ∈ W j.1
      simp only [hmem]
      exact ⟨fun h ↦ ⟨⟨ConnectedComponents.mk x, h⟩, rfl⟩,
        fun ⟨j, hj⟩ h ↦ j.2 (hj.symm.trans h)⟩
    rw [heq]
    exact isOpen_iUnion fun j ↦ (W j.1).2
  have hci (i : I) : IsClosedImmersion (W i).ι :=
    IsClosedImmersion.of_isPreimmersion _ (by simpa using hclosed i)
  have haff (i : I) : IsAffine (W i).toScheme := by
    let := hci i
    exact isAffine_of_isAffineHom (W i).ι
  let c (i : I) := (W i).ι ≫ g
  have hcart (i : I) : IsPullback (p ∣_ W i)
      ((p ⁻¹ᵁ W i).ι ≫ pullback.snd f₀
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) (c i) b :=
    (isPullback_morphismRestrict p (W i)).paste_vert hp
  let t (i : I) := (hcart i).isoPullback
  let q (i : I) := (t i).inv ≫ (p ⁻¹ᵁ W i).ι
  let z (i : I) : (p ⁻¹ᵁ W i).toScheme :=
    ⟨r i, (hmem i (r i)).mpr (hr i)⟩
  have hqz (i : I) : q i ((t i).hom (z i)) = r i := by
    change ((t i).hom ≫ (t i).inv ≫ (p ⁻¹ᵁ W i).ι) (z i) = _
    simp [z]
  have hqr (i : I) : Set.range (q i).base = (V i : Set X) := by
    dsimp [q]
    rw [Set.range_comp, (t i).inv.surjective.range_eq,
      Set.image_univ]
    simpa using congrArg (fun U : X.Opens ↦ (U : Set X)) (hW i).symm
  have hconn (i : I) : ConnectedSpace (p ⁻¹ᵁ W i).toScheme := by
    have heq : (p ⁻¹ᵁ W i : Set X) = connectedComponent (r i) := by
      rw [← hW i, hVr]
    exact isConnected_iff_connectedSpace.mp (heq ▸ isConnected_connectedComponent)
  have hgeo (i : I) : GeometricallyConnected (c i) := by
    let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    let E := D.extensionSubfield e he
    let : Algebra E D.k := E.subtype.toAlgebra
    let : (W i).toScheme.Over (Spec (.of E)) := ⟨c i⟩
    have : ConnectedSpace ↥(pullback (c i) b) :=
      (t i).hom.homeomorph.connectedSpace_iff.mp (hconn i)
    exact (geometricallyConnected_iff_connectedSpace_of_isAlgClosed
      (k := E) (Ω := D.k) (W i).toScheme).mpr this
  refine ⟨e, he, ⟨{
    I := I
    finite_I := inferInstance
    component := fun i ↦ (W i).toScheme
    componentMap := c
    inclusion := fun i ↦ (W i).ι
    inclusion_over := fun _ ↦ rfl
    affine := haff
    nonempty := fun i ↦ ⟨⟨p (r i), (hmem i (r i)).mpr (hr i)⟩⟩
    open_closed := fun i ↦ ⟨inferInstance, hci i⟩
    cover := by simpa using hcover.symm
    pairwise_disjoint := by simpa using hdisjoint
    geometrically_connected := hgeo
    baseComponent := q
    baseComponent_fst := ?_
    baseComponent_snd := ?_
    componentPoint := fun i ↦ (t i).hom (z i)
    component_range := ?_
    components_bijective := ?_
  }⟩⟩
  · intro i
    apply (cancel_epi (t i).hom).mp
    simp only [q, Category.assoc, Iso.hom_inv_id_assoc]
    rw [(hcart i).isoPullback_hom_fst_assoc]
    rw [← Category.assoc, morphismRestrict_ι]
    rw [Category.assoc, hpfst]
  · intro i
    exact (hcart i).isoPullback_inv_snd
  · intro i
    rw [hqr, hqz, hVr]
  · have hf : (fun i : I ↦ ConnectedComponents.mk (q i ((t i).hom (z i)))) = id := by
      funext i
      exact (congrArg ConnectedComponents.mk (hqz i)).trans (hr i)
    change Function.Bijective (fun i : I ↦ ConnectedComponents.mk (q i ((t i).hom (z i))))
    rw [hf]
    exact Function.bijective_id

/-- Geometric connected components of an affine finite-type scheme over a finite field descend to a
finite constant extension.
Source: Stacks Project, varieties.tex, Tag 038E
(lemma-galois-action-connected-components-continuous), and Tag 0387
(lemma-characterize-geometrically-connected); morphisms.tex, Tags 01VB and 02NK.
Proof:
1. Identify every affine field base change with Spec of the tensor product by
   lem-weil-pbc-fibre-product-affine-spectra. Finite type survives base change by
   lem-sfb-finite-type-composition-base-change; lem-pc-affine-finite-type-algebra and
   lem-wf-affine-noetherian-components make the geometric fibre Noetherian.
2. By lem-sfb-noetherian-connected-components-open its nonempty connected components
   form a finite open partition. Each is closed since its complement is the union of
   the other opens, and quasi-compact by lem-sfb-noetherian-space-compact-subsets.
3. Descend each quasi-compact open to a finitely generated base subalgebra using
   lem-weil-pbc-descend-qc-open-fg-subalgebra. This initially asserts only openness.
4. Take the finite union of algebra generating sets. Algebraicity of the closure and
   lem-weil-pbc-algebraic-generators-finite-extension put these coefficients in one
   finite intermediate field L. Its degree e is positive, and a basis shows its
   cardinality is q^e. By lem-weil-unique-subfield-of-closure it is D.extensionSubfield.
5. Pull the descended opens up to L by lem-weil-pbc-open-immersion-base-change.
   Base-change pasting (def-pc-base-change) identifies their base changes to k with
   the original component opens, with their restricted scheme structure.
6. The projection from k to L is surjective by lem-pc-field-extension-surjective and
   lem-weil-pbc-spec-surjective-base-change. Reflect disjointness and coverage along
   this surjection. Nonemptiness upstairs gives nonemptiness downstairs; the
   complement of each descended open is the union of the others, so it is closed.
7. By lem-weil-pbc-spec-clopen-idempotent each descended clopen is a basic open of an
   idempotent; lem-weil-pbc-affine-open-section-vanishing-prime makes it affine.
   The disjoint open inclusions glue to the coproduct isomorphism with the base change.
8. The closure k is also algebraic and algebraically closed over L. Connectedness of
   the base-changed components and lem-weil-geometrically-connected-algebraic-closure
   give geometric connectedness. Their ranges identify exactly the connected components.
   If the original scheme is empty, take e = 1 and the empty component index.
9. Smooth relative dimension d survives base change by
   lem-sbc-smooth-relative-dimension-permanence. The inclusions are etale by
   lem-weil-pbc-open-immersion-etale, thus smooth of dimension zero. Composition in
   the same permanence lemma gives smooth relative dimension 0 + d = d.
(blueprint: lem-zl-affine-geometric-components-finite-extension). -/
theorem exists_affine_geometric_components_finite_extension
    (D : WeilConjectures.FiniteFieldDatum.{u}) {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (CommRingCat.of D.k₀)) [IsAffine X₀]
    [LocallyOfFiniteType f₀] [QuasiCompact f₀] :
    ∃ (e : ℕ) (he : 1 ≤ e),
      ∃ (H : AffineGeometricComponentDecomposition D f₀ e he),
        ∀ (d : ℕ), SmoothOfRelativeDimension d f₀ →
          ∀ (i : H.I), SmoothOfRelativeDimension d (H.componentMap i) := by
  obtain ⟨e, he, ⟨H⟩⟩ := exists_affine_geometric_component_decomposition D f₀
  refine ⟨e, he, H, ?_⟩
  intro d hd i
  let := hd
  let := (H.open_closed i).1
  have hbase : SmoothOfRelativeDimension d
      (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (D.extensionEmbedding e he)))) := by
    let := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
    exact MorphismProperty.pullback_snd _ _ hd
  let := hbase
  have hopen : SmoothOfRelativeDimension 0 (H.inclusion i) := inferInstance
  let := hopen
  rw [← H.inclusion_over i]
  simpa [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d (H.inclusion i)
    (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (D.extensionEmbedding e he))))

end AlgebraicGeometry
