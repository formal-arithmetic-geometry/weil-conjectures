/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCoverConstruction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
public import Mathlib.CategoryTheory.Limits.Final
public import Sheaf.AlgebraicGeometry.FundamentalGroup.ProfiniteProductMaps
import Mathlib.Topology.Homeomorph.Lemmas
import all Sheaf.AlgebraicGeometry.ProfiniteSchemeProductComponents
import Sheaf.AlgebraicGeometry.FundamentalGroup.PointedGaloisLimitGeometry
import Sheaf.AlgebraicGeometry.FundamentalGroup.NormalizedPointedLimitCech
import all Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitFiniteSplitting

/-! # The pointed finite étale limit and its consecutive Čech coordinates

Source: Bhatt–Scholze, The pro-étale topology for schemes, §7.4, and Stacks 0BND,
01YX, 01Z2, 01Z4, 097D (blueprint: lem-sfb-pointed-finite-etale-limit-cover).
The limit, point and finite-cover maps are the existing `UniversalCover` construction.
`IsFundamentalGroup` permits any small profinite model of the finite fibre functor's
natural automorphism group, with its evaluation topology; it introduces no new group.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
open CategoryTheory Limits Opposite PreGaloisCategory

namespace AlgebraicGeometry.Scheme.UniversalCover

/-- The finite-cover splitting map, with its summands fixed by their value at the marked point.
Source: Stacks 0BND (blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
noncomputable def finiteSplitMap {X : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) (Y : X.FiniteEtale) :
    (∐ fun _ : (FiniteEtale.fiber x).obj Y ↦ cover x) ⟶ pullback (proj x) Y.obj.hom :=
  Sigma.desc fun s ↦ pullback.lift (𝟙 _) (toObj x Y s) (by simp)

/-- The right deck transformation normalized by left monodromy on finite fibres.
Source: Stacks 0BND (blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
noncomputable def rightDeck {X : Scheme.{u}} [ConnectedSpace X] [CompactSpace X]
    [QuasiSeparatedSpace X] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (G : ProfiniteGrp.{u})
    [∀ Y, MulAction G ((FiniteEtale.fiber x).obj Y)]
    [IsFundamentalGroup (FiniteEtale.fiber x) G] (g : G) : cover x ≅ cover x :=
  transport (toAut (FiniteEtale.fiber x) G g).symm

/-- The actual q-th Čech term, including q = 0. Source: Stacks 01YX
(blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
noncomputable abbrev cechTerm {X : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) (q : ℕ) :
    Scheme.{u} := (Arrow.mk (proj x)).cechNerve.obj (op (SimplexCategory.mk q))

/-- Vertex projection from the Čech term. Source: Stacks 01YX
(blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
noncomputable abbrev cechVertex {X : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (q : ℕ) (i : Fin (q + 1)) : cechTerm x q ⟶ cover x :=
  WidePullback.π (fun _ : Fin (q + 1) ↦ proj x) i

/-- All the asserted coordinate data and their normalization. Every field is either
actual data or a property, with no choice of an unconstrained comparison map.
Source: Bhatt–Scholze §7.4; Stacks 0BND, 01YX, 097D
(blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
structure PointedLimitCechCoordinates {X : Scheme.{u}} [ConnectedSpace X]
    [CompactSpace X] [QuasiSeparatedSpace X] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (G : ProfiniteGrp.{u})
    [∀ Y, MulAction G ((FiniteEtale.fiber x).obj Y)]
    [IsFundamentalGroup (FiniteEtale.fiber x) G] where
  /-- Connectedness includes nonemptiness. -/
  connected : ConnectedSpace (cover x)
  /-- Affineness of the structure map. -/
  affine : IsAffineHom (proj x)
  /-- Faithful flatness: the flatness part. -/
  flat : Flat (proj x)
  /-- Faithful flatness: surjectivity on spectra. -/
  surjective : Surjective (proj x)
  /-- Flatness of the diagonal as well as of the map. -/
  weaklyEtale : WeaklyEtale (proj x)
  /-- The singleton is a pro-étale covering. -/
  covering : Presieve.singleton (proj x) ∈ proetalePrecoverage X
  /-- The compatible marked point lies above x. -/
  point_over : pt x ≫ proj x = x
  /-- Every marked point of the indexing diagram is recovered. -/
  point_stage : ∀ j : Index x, pt x ≫ limit.π (diagram x) j = (point x j).left
  /-- The same cone computes any small cofinal subsystem. -/
  cofinal : ∀ (J : Type u) [Category.{u} J] (F : J ⥤ Index x) [Functor.Initial F],
    Nonempty (IsLimit ((limit.cone (diagram x)).whisker F))
  /-- The finite-cover splitting is the specified map. -/
  splitting : ∀ Y : X.FiniteEtale, IsIso (finiteSplitMap x Y)
  /-- Splitting sections have their prescribed marked value. -/
  splitting_point : ∀ (Y : X.FiniteEtale) (s : (FiniteEtale.fiber x).obj Y),
    pt x ≫ toObj x Y s = s.left
  /-- The splitting is natural in the finite cover. -/
  splitting_natural : ∀ {Y Z : X.FiniteEtale} (a : Y ⟶ Z)
    (s : (FiniteEtale.fiber x).obj Y),
    toObj x Y s ≫ a.hom.left = toObj x Z ((FiniteEtale.fiber x).map a s)
  /-- Normalization by the finite fibre functor's LEFT action. This includes every coset cover. -/
  monodromy : ∀ (Y : X.FiniteEtale) (s : (FiniteEtale.fiber x).obj Y) (g : G),
    (rightDeck x G g).hom ≫ toObj x Y s = toObj x Y (g • s)
  /-- The deck maps are a right action. -/
  deck_mul : ∀ g h : G,
    (rightDeck x G g).hom ≫ (rightDeck x G h).hom = (rightDeck x G (g * h)).hom
  /-- The identity label fixes the first vertex. -/
  deck_one : (rightDeck x G 1).hom = 𝟙 _
  /-- Scheme, rather than only topological, Čech identifications in every degree. -/
  iso : ∀ q : ℕ, profiniteProduct (cover x) (Profinite.of (Fin q → G)) ≅ cechTerm x q
  /-- The first coordinate really is the first vertex. -/
  first_vertex : ∀ q : ℕ, (iso q).hom ≫ cechVertex x q 0 =
    profiniteProductBase (cover x) (Profinite.of (Fin q → G))
  /-- All vertices have the cumulative-label formula as SCHEME maps. -/
  vertices : ∀ (q : ℕ) (g : Fin q → G) (i : Fin (q + 1)),
    profiniteProductSection (cover x) (Profinite.of (Fin q → G)) g ≫
      (iso q).hom ≫ cechVertex x q i = (rightDeck x G (cumulativeLabel g i.val)).hom
  /-- Compatibility with every face and degeneracy. In particular the middle face
  of a 2-simplex multiplies consecutive labels in the order g*h. -/
  simplicial : ∀ (m n : ℕ) (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (g : Fin m → G),
    profiniteProductSection (cover x) (Profinite.of (Fin m → G)) g ≫
      (iso m).hom ≫ (Arrow.mk (proj x)).cechNerve.map φ.op =
    (rightDeck x G (cumulativeLabel g (φ.toOrderHom 0).val)).hom ≫
      profiniteProductSection (cover x) (Profinite.of (Fin n → G))
        (restrictedLabels φ g) ≫ (iso n).hom
  /-- The stipulated finite-quotient inverse system. -/
  quotientProjections : ∀ q : ℕ,
    (Functor.const (OpenNormalSubgroup G)).obj
      (profiniteProduct (cover x) (Profinite.of (Fin q → G))) ⟶
      finiteLabelDiagram (cover x) G q
  /-- This cone is a limit, not an arbitrary collection of finite maps. -/
  quotient_limit : ∀ q : ℕ, IsLimit
    (⟨profiniteProduct (cover x) (Profinite.of (Fin q → G)), quotientProjections q⟩ :
      Cone (finiteLabelDiagram (cover x) G q))
  /-- The finite quotient maps are over T. -/
  quotient_base : ∀ (q : ℕ) (N : OpenNormalSubgroup G),
    (quotientProjections q).app N ≫
      Sigma.desc (fun _ : Fin q → G ⧸ N.toSubgroup ↦ 𝟙 (cover x)) =
        profiniteProductBase (cover x) (Profinite.of (Fin q → G))
  /-- Their labels are the actual quotient images, in every coordinate. -/
  quotient_labels : ∀ (q : ℕ) (N : OpenNormalSubgroup G) (g : Fin q → G),
    profiniteProductSection (cover x) (Profinite.of (Fin q → G)) g ≫
      (quotientProjections q).app N =
        Sigma.ι (fun _ : Fin q → G ⧸ N.toSubgroup ↦ cover x)
          (fun i ↦ QuotientGroup.mk (g i))
  /-- Components have precisely the quotient topology. -/
  components : ∀ q : ℕ, ConnectedComponents (cechTerm x q) ≃ₜ (Fin q → G)
  /-- Fix the component identifications by the same consecutive labels. -/
  component_labels : ∀ (q : ℕ) (g : Fin q → G) (z : cover x),
    components q (ConnectedComponents.mk
      ((iso q).hom (profiniteProductSection (cover x) (Profinite.of (Fin q → G)) g z))) = g

/-- The pointed finite étale limit and all its normalized Čech coordinates exist.
Source: Bhatt–Scholze §7.4 and Stacks 0BND, 01YX, 01Z2, 01Z4, 097D
(blueprint: lem-sfb-pointed-finite-etale-limit-cover).

Proof: (1) The finite Galois equivalence and open-subgroup correspondence identify
pointed Galois covers with open normal subgroups, with unique pointed arrows and
common refinement by intersection. Small models and initial functors preserve the limit.
(2) Finite maps are affine and separated; hence the stages are qcqs. The affine-transition
limit theorem constructs the existing cover and its affine projections.
(3) Finite étale degree is positive for every pointed connected cover. Apply the nonempty
limit theorem to each fibre to get surjectivity of all projections.
(4) On an affine base chart the ring is a filtered colimit of finite étale algebras,
hence ind-étale and weakly étale; surjectivity and affineness give the singleton covering.
(5) The compatible marked points give pt by the limit universal property.
(6) Descend complementary compact clopens to a common stage; surjectivity makes them
a partition, and connectedness of the stage proves connectedness of the limit.
(7) The equivariant finite bijection (aN,s) ↦ (aN,as) gives the splitting.
(8) Common refinements and full faithfulness prove independence and naturality; a section
of a finite disjoint union over connected T has one label, proving marked uniqueness.
(9) The maps to all finite covers define right deck maps; testing against each projection
proves their action law and left-monodromy normalization.
(10) Evaluation kernels give the open normal basis and G = lim G/N topologically.
(11) Take limits of the finite splittings, using fibre-product compatibility.
(12) Iterate, replacing first-vertex labels by consecutive labels using cumulative products.
(13) On Spec A the ring is colim A^((G/N)^q) = LC(G^q,A); the locally-constant spectrum
homeomorphism identifies the underlying space with |T| × G^q.
(14) The connected components are its fibres over G^q; the projection is an open quotient.
(15) Omitting vertices and repeating vertices gives the asserted group-nerve formulas.
(16) Pull finite covers back along a pointed morphism; their marked sections define the
map of limits and intertwine labels through the fundamental-group homomorphism. -/
theorem nonempty_pointedLimitCechCoordinates {X : Scheme.{u}} [ConnectedSpace X]
    [CompactSpace X] [QuasiSeparatedSpace X] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (G : ProfiniteGrp.{u})
    [∀ Y, MulAction G ((FiniteEtale.fiber x).obj Y)]
    [IsFundamentalGroup (FiniteEtale.fiber x) G] :
    Nonempty (PointedLimitCechCoordinates x G) := by
  classical
  obtain ⟨E, e, he, hes, het, hsub, harrow, haut, hlim, hover, hcofinal,
    hstage, htransition, hpoint, hbase, hconnected, hcompact, hqs,
    haffine, hflat, hsurj, hweak, hcharts, hcover⟩ :=
    exists_pointedGaloisLimitGeometry x G
  let S : PointedCosetSystem x G :=
    { covers := E.functor ⋙ obj x
      connected := fun N ↦ (hstage N).1
      label := fun N ↦ (e N).symm
      label_smul := by
        intro N a b
        apply (e N).injective
        change (e N) ((e N).symm (QuotientGroup.mk (a * b))) =
          (e N) (a • (e N).symm (QuotientGroup.mk b))
        calc
          _ = QuotientGroup.mk (a * b) := (e N).apply_symm_apply _
          _ = QuotientGroup.mk a * (e N) ((e N).symm (QuotientGroup.mk b)) := by
            rw [(e N).apply_symm_apply]
            rfl
          _ = _ := (hes N a _).symm
      transition := by
        intro M N h a
        apply (e N).injective
        change (e N) ((FiniteEtale.fiber x).map
          ((obj x).map (E.functor.map (homOfLE h))) ((e M).symm (QuotientGroup.mk a))) =
            (e N) ((e N).symm (QuotientGroup.mk a))
        rw [het, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        rfl }
  let cone : Cone (S.covers ⋙ finiteEtaleOver X) :=
    { pt := Over.mk (proj x)
      π :=
        { app := fun N ↦ Over.homMk (limit.π (diagram x) (E.functor.obj N)) (π_p x _)
          naturality := by
            intro M N f
            apply Over.OverMorphism.ext
            exact (Category.id_comp _).trans (limit.w (diagram x) (E.functor.map f)).symm } }
  let L : PointedCosetLimit x G S :=
    { cone := cone
      isLimit := by
        exact (Functor.Initial.isLimitWhiskerEquiv E.functor _).symm hover.some
      point := pt x
      point_base := pt_proj x
      point_leg := by
        intro N
        change pt x ≫ limit.π (diagram x) (E.functor.obj N) = _
        rw [pt_π]
        congr 1
        apply (e N).injective
        change (e N) (point x (E.functor.obj N)) = (e N) ((e N).symm 1)
        rw [he, Equiv.apply_symm_apply]
        rfl
      connected := hconnected }
  clear hsub harrow haut hlim hcofinal htransition hpoint hbase hcompact hqs hcharts
  have : ConnectedSpace (cover x) := hconnected
  obtain ⟨B⟩ := exists_pointedLimitSplitting L
  obtain ⟨C⟩ := PointedLimitCech.exists_coordinates B
  obtain ⟨P⟩ := profinite_scheme_product_components.{u}
  have hs (Y : X.FiniteEtale) (s : (FiniteEtale.fiber x).obj Y) :
      (B.sectionMap Y s).left = toObj x Y s :=
    eq_toObj x Y s _ (Over.w _) (B.section_point Y s)
  have hd (g : G) : (B.deck g).hom.left = (rightDeck x G g).hom := by
    apply hom_ext x
    intro Y s
    calc
      _ = (B.sectionMap Y (g • s)).left := by
        rw [← hs Y s]
        exact B.section_deck Y s g
      _ = toObj x Y (g • s) := hs Y (g • s)
      _ = _ := by
        symm
        change transportHom (toAut (FiniteEtale.fiber x) G g).symm ≫ toObj x Y s = _
        rw [transportHom_toObj]
        rfl
  let a (q : ℕ) : profiniteProduct (cover x) (Profinite.of (Fin q → G)) ≅
      (C.cone q).pt := (P.scheme_limit (cover x) G q).conePointUniqueUpToIso (C.isLimit q)
  have aq (q : ℕ) (N : OpenNormalSubgroup G) :
      (a q).hom ≫ (C.cone q).π.app N = (P.projections (cover x) G q).app N :=
    (P.scheme_limit (cover x) G q).conePointUniqueUpToIso_hom_comp (C.isLimit q) N
  have ac (q : ℕ) (g : Fin q → G) :
      profiniteProductSection (cover x) (Profinite.of (Fin q → G)) g ≫ (a q).hom =
        C.constant q g := by
    apply (C.isLimit q).hom_ext
    intro N
    rw [Category.assoc, aq, P.projection_section, C.constant_quotient]
    rfl
  let iso (q : ℕ) := a q ≪≫ C.iso q
  let components (q : ℕ) : ConnectedComponents (cechTerm x q) ≃ₜ (Fin q → G) := by
    let f := (Scheme.homeoOfIso (iso q)).symm
    exact (f.isQuotientMap.isCoinducing.connectedComponentsHomeomorph
      (fun z ↦ f.isConnected_preimage.mpr isConnected_singleton)).trans (P.components (cover x) G q)
  refine ⟨{
    connected := hconnected
    affine := haffine
    flat := hflat
    surjective := hsurj
    weaklyEtale := hweak
    covering := hcover
    point_over := pt_proj x
    point_stage := pt_π x
    cofinal := fun J _ F _ ↦
      ⟨(Functor.Initial.isLimitWhiskerEquiv F _).symm (limit.isLimit _)⟩
    splitting := ?_
    splitting_point := pt_toObj x
    splitting_natural := fun b s ↦ toObj_comp x b s
    monodromy := ?_
    deck_mul := ?_
    deck_one := ?_
    iso := iso
    first_vertex := ?_
    vertices := ?_
    simplicial := ?_
    quotientProjections := P.projections (cover x) G
    quotient_limit := P.scheme_limit (cover x) G
    quotient_base := P.projection_base (cover x) G
    quotient_labels := P.projection_section (cover x) G
    components := components
    component_labels := ?_
  }⟩
  · intro Y
    have h := B.splitting Y
    rw [Cofan.nonempty_isColimit_iff_isIso_sigmaDesc] at h
    change IsIso (Sigma.desc (fun s : (FiniteEtale.fiber x).obj Y ↦
      pullback.lift (f := proj x) (g := Y.obj.hom)
        (𝟙 (cover x)) (B.sectionMap Y s).left _)) at h
    simpa only [finiteSplitMap, hs] using h
  · intro Y s g
    rw [← hd, ← hs, B.section_deck, hs]
  · intro g h
    have h' := congrArg (fun f ↦ f.left) (B.deck_mul g h)
    change (B.deck g).hom.left ≫ (B.deck h).hom.left = (B.deck (g * h)).hom.left at h'
    simpa only [hd] using h' 
  · have h := congrArg (fun f : Aut L.cone.pt ↦ f.hom.left) B.deck_one
    change (B.deck 1).hom.left = 𝟙 (cover x) at h
    simpa only [hd] using h
  · intro q
    change (a q).hom ≫ (C.iso q).hom ≫ _ = _
    have hf := C.first_vertex q
    change (C.iso q).hom ≫ cechVertex x q 0 = _ at hf
    rw [hf]
    let N : OpenNormalSubgroup G := ⟨⟨⊤, isOpen_univ⟩, inferInstance⟩
    rw [← C.quotient_base q N, ← Category.assoc, aq]
    change (P.projections (cover x) G q).app N ≫
      Sigma.desc (fun _ : Fin q → G ⧸ N.toSubgroup ↦ 𝟙 (cover x)) = _
    exact P.projection_base (cover x) G q N
  · intro q g i
    change _ ≫ (a q).hom ≫ (C.iso q).hom ≫ _ = _
    rw [← Category.assoc, ac]
    have hh := C.vertices q g i
    change C.constant q g ≫ (C.iso q).hom ≫ cechVertex x q i = _ at hh
    rw [hh, hd]
    rfl
  · intro m n φ g
    change _ ≫ (a m).hom ≫ (C.iso m).hom ≫ _ =
      _ ≫ _ ≫ (a n).hom ≫ (C.iso n).hom
    rw [← Category.assoc, ac]
    have hh := C.constant_simplicial m n φ g
    change C.constant m g ≫ (C.iso m).hom ≫ (Arrow.mk (proj x)).cechNerve.map φ.op = _
      at hh
    rw [hh]
    change (B.deck (cumulativeLabel g (φ.toOrderHom 0).val)).hom.left ≫
      C.constant n (restrictedLabels φ g) ≫ (C.iso n).hom = _
    rw [hd, ← ac]
    simp only [Category.assoc]
  · intro q g z
    dsimp only [components, Homeomorph.trans_apply]
    change P.components (cover x) G q (ConnectedComponents.mk
      ((iso q).inv ((iso q).hom
        (profiniteProductSection (cover x) (Profinite.of (Fin q → G)) g z)))) = g
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    change P.components (cover x) G q (ConnectedComponents.mk
      (profiniteProductSection (cover x) (Profinite.of (Fin q → G)) g z)) = g
    rw [P.components_mk, P.space_section]

private theorem product_finiteEtale_ext (T : Scheme.{u}) (G : ProfiniteGrp.{u}) (q : ℕ)
    {X : Scheme.{u}} (Y : X.FiniteEtale)
    (a b : profiniteProduct T (Profinite.of (Fin q → G)) ⟶ Y.obj.left)
    (hab : a ≫ Y.obj.hom = b ≫ Y.obj.hom)
    (h : ∀ g : Fin q → G,
      profiniteProductSection T (Profinite.of (Fin q → G)) g ≫ a =
        profiniteProductSection T (Profinite.of (Fin q → G)) g ≫ b) : a = b := by
  classical
  have : Etale Y.obj.hom := Y.obj.prop
  let v := pullback.lift a b hab
  let δ := pullback.diagonal Y.obj.hom
  let j := pullback.fst v δ
  have : IsOpenImmersion j := inferInstance
  have hj : Surjective j := by
    obtain ⟨P⟩ := profinite_scheme_product_components.{u}
    constructor
    intro z
    let t := (P.space T G q z).1
    let g := (P.space T G q z).2
    have hz' : profiniteProductSection T (Profinite.of (Fin q → G)) g t = z := by
      apply (P.space T G q).injective
      rw [P.space_section]
    let k := profiniteProductSection T (Profinite.of (Fin q → G)) g
    let l : T ⟶ pullback v δ := pullback.lift k (k ≫ a) (by
      apply pullback.hom_ext <;> simp [v, δ, k, Category.assoc, h g])
    refine ⟨l t, ?_⟩
    change (l ≫ j) t = z
    rw [show l ≫ j = k from pullback.lift_fst _ _ _]
    exact hz'
  have : IsIso j := (isIso_iff_isOpenImmersion_and_surjective j).mpr ⟨inferInstance, hj⟩
  apply (cancel_epi j).mp
  have hh := pullback.condition (f := v) (g := δ)
  have h₁ := congrArg (fun f ↦ f ≫ pullback.fst Y.obj.hom Y.obj.hom) hh
  have h₂ := congrArg (fun f ↦ f ≫ pullback.snd Y.obj.hom Y.obj.hom) hh
  simp only [v, δ, Category.assoc, pullback.lift_fst, pullback.lift_snd,
    pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id] at h₁ h₂
  exact h₁.trans h₂.symm

/-- Pointed naturality is compatible with the canonical limit map, and hence acts on
all consecutive Čech labels by the induced continuous fundamental-group homomorphism.
Source: Stacks 0BND (3) (blueprint: lem-sfb-pointed-finite-etale-limit-cover).

Proof: Pull back a finite cover, use its marked splitting section upstairs, and project
to the original cover. These maps form the defining cone of `UniversalCover.map`.
The fibre base-change isomorphism intertwines monodromy by `fundamentalGroupMap_smul`.
Uniqueness of marked finite-cover sections gives equivariance of deck maps. Test on
every limit projection to get equality of limit maps, then apply the same calculation
in each Čech vertex. The cumulative products are preserved by the group homomorphism,
so the normalized coordinate isomorphisms agree in every degree. Identity and composite
pointed maps agree by the same projectionwise uniqueness. -/
theorem pointedLimitCechCoordinates_natural {X X' : Scheme.{u}}
    [ConnectedSpace X] [CompactSpace X] [QuasiSeparatedSpace X]
    [ConnectedSpace X'] [CompactSpace X'] [QuasiSeparatedSpace X']
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (f : X' ⟶ X)
    (x' : Spec (.of Ω) ⟶ X') (G H : ProfiniteGrp.{u})
    [∀ Y, MulAction G ((FiniteEtale.fiber (x' ≫ f)).obj Y)]
    [IsFundamentalGroup (FiniteEtale.fiber (x' ≫ f)) G]
    [∀ Y, MulAction H ((FiniteEtale.fiber x').obj Y)]
    [IsFundamentalGroup (FiniteEtale.fiber x') H]
    (C : PointedLimitCechCoordinates (x' ≫ f) G)
    (C' : PointedLimitCechCoordinates x' H) :
    ∀ q : ℕ,
      (C'.iso q).hom ≫ (Arrow.mapCechNerve
        (Arrow.homMk (map f x') f (map_proj f x'))).app (op (SimplexCategory.mk q)) =
      profiniteProductMap (map f x')
        (labelMap G H (FiniteEtale.fundamentalGroupMap
          (FiniteEtale.pullbackFiberIso f x') H G)
          (FiniteEtale.continuous_fundamentalGroupMap
            (FiniteEtale.pullbackFiberIso f x') H G) q) ≫ (C.iso q).hom := by
  classical
  let ρ := FiniteEtale.fundamentalGroupMap (FiniteEtale.pullbackFiberIso f x') H G
  have hd (g : H) : (rightDeck x' H g).hom ≫ map f x' =
      map f x' ≫ (rightDeck (x' ≫ f) G (ρ g)).hom := by
    apply UniversalCover.hom_ext (x' ≫ f)
    intro Y s
    have hm : pullbackPoint f x' Y (ρ g • s) = g • pullbackPoint f x' Y s := by
      let τ := FiniteEtale.pullbackFiberIso f x'
      have h := FiniteEtale.fundamentalGroupMap_smul τ H G g Y (τ.inv.app Y s)
      have hh := congrArg (fun t ↦ τ.inv.app Y t) h
      have hi (a : (FiniteEtale.fiber x').obj ((FiniteEtale.pullback f).obj Y)) :
          τ.inv.app Y (τ.hom.app Y a) = a :=
        ConcreteCategory.congr_hom (τ.hom_inv_id_app Y) a
      have hj : τ.hom.app Y (τ.inv.app Y s) = s :=
        ConcreteCategory.congr_hom (τ.inv_hom_id_app Y) s
      simpa only [hi, hj, pullbackPoint, ρ, τ] using hh
    change transportHom (toAut (FiniteEtale.fiber x') H g).symm ≫
        map f x' ≫ toObj (x' ≫ f) Y s =
      map f x' ≫ transportHom (toAut (FiniteEtale.fiber (x' ≫ f)) G (ρ g)).symm ≫
        toObj (x' ≫ f) Y s
    rw [map_toObj, transportHom_toObj_assoc, transportHom_toObj, map_toObj]
    simp only [Iso.symm_inv, toAut_hom_app_apply, hm]
  have hv {Y : Scheme.{u}} [ConnectedSpace Y] [CompactSpace Y] [QuasiSeparatedSpace Y]
      (y : Spec (.of Ω) ⟶ Y) (K : ProfiniteGrp.{u})
      [∀ Z, MulAction K ((FiniteEtale.fiber y).obj Z)]
      [IsFundamentalGroup (FiniteEtale.fiber y) K]
      (D : PointedLimitCechCoordinates y K) (q : ℕ) (i : Fin (q + 1)) :
      (D.iso q).hom ≫ cechVertex y q i ≫ proj y =
        profiniteProductBase (cover y) (Profinite.of (Fin q → K)) ≫ proj y := by
    rw [WidePullback.π_arrow, ← D.first_vertex q]
    rw [Category.assoc, WidePullback.π_arrow]
  intro q
  let b := profiniteProductMap (map f x')
    (labelMap G H ρ (FiniteEtale.continuous_fundamentalGroupMap
      (FiniteEtale.pullbackFiberIso f x') H G) q)
  let a := (Arrow.mapCechNerve (Arrow.homMk
    (f := Arrow.mk (proj x')) (g := Arrow.mk (proj (x' ≫ f)))
      (map f x') f (map_proj f x'))).app
    (op (SimplexCategory.mk q))
  have he (i : Fin (q + 1)) :
      ((C'.iso q).hom ≫ a) ≫ cechVertex (x' ≫ f) q i =
        (b ≫ (C.iso q).hom) ≫ cechVertex (x' ≫ f) q i := by
    have hai : a ≫ cechVertex (x' ≫ f) q i = cechVertex x' q i ≫ map f x' := by
      exact WidePullback.lift_π _ _ _ _ i
    rw [Category.assoc, hai, ← Category.assoc]
    apply UniversalCover.hom_ext (x' ≫ f)
    intro Y s
    apply product_finiteEtale_ext (cover x') H q Y
    · change ((C'.iso q).hom ≫ cechVertex x' q i ≫ map f x' ≫ toObj _ Y s) ≫ _ =
        (b ≫ (C.iso q).hom ≫ cechVertex (x' ≫ f) q i ≫ toObj _ Y s) ≫ _
      simp only [Category.assoc, toObj_hom (x' ≫ f) Y s]
      rw [map_proj f x']
      calc
        _ = (profiniteProductBase (cover x') (Profinite.of (Fin q → H)) ≫
            proj x') ≫ f := by
          simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ f) (hv x' H C' q i)
        _ = _ := by
          rw [hv (x' ≫ f) G C q i, ← Category.assoc, productMap_base]
          simp only [Category.assoc, map_proj f x']
    · intro g
      change _ ≫ (C'.iso q).hom ≫ cechVertex x' q i ≫ map f x' ≫ toObj _ Y s =
        (_ ≫ b) ≫ (C.iso q).hom ≫ cechVertex (x' ≫ f) q i ≫ toObj _ Y s
      rw [show profiniteProductSection (cover x') (Profinite.of (Fin q → H)) g ≫ b =
        map f x' ≫ profiniteProductSection (cover (x' ≫ f)) (Profinite.of (Fin q → G))
          (fun i ↦ ρ (g i)) from productMap_section _ _ _]
      have hρ : cumulativeLabel (fun i ↦ ρ (g i)) i.val =
          ρ (cumulativeLabel g i.val) := by
        simp only [cumulativeLabel, map_list_prod, List.map_take, List.map_ofFn,
          Function.comp_def]
      have h₁ := C'.vertices q g i
      have h₂ := C.vertices q (fun i ↦ ρ (g i)) i
      rw [hρ] at h₂
      calc
        _ = ((rightDeck x' H (cumulativeLabel g i.val)).hom ≫ map f x') ≫
            toObj (x' ≫ f) Y s := by rw [← h₁]; simp only [Category.assoc]
        _ = (map f x' ≫ (rightDeck (x' ≫ f) G (ρ (cumulativeLabel g i.val))).hom) ≫
            toObj (x' ≫ f) Y s := by rw [hd]
        _ = _ := by rw [← h₂]; simp only [Category.assoc]
  change (C'.iso q).hom ≫ a = b ≫ (C.iso q).hom
  apply WidePullback.hom_ext (arrows := fun _ : Fin (q + 1) ↦ proj (x' ≫ f))
  · exact he
  · have hh := congrArg (fun k ↦ k ≫ proj (x' ≫ f)) (he 0)
    simpa only [Category.assoc, WidePullback.π_arrow] using hh

/-- The right-torsor cocycle equation, with coefficient sections pulled to the triple
overlap. Here p₀,p₁ are the two vertices and p₀₁,p₁₂,p₀₂ the three edges.
This sectionwise statement applies to an arbitrary (possibly nonconstant, noncommutative)
group sheaf on the pro-étale site; its sheaf and local-nonemptiness conditions are not
needed once the section e is fixed.
Source: the explicit right-torsor calculation in Bhatt–Scholze §7.4
(blueprint: lem-sfb-pointed-finite-etale-limit-cover).

Proof: Pull e(z·g)=e(z)c(z,g) back along the edges 01, 12 and 02.
The vertex equalities identify the two expressions for the third vertex. Naturality
of the action moves every coefficient to the triple overlap. Associativity of the
right action combines c₀₁ and c₁₂ in that order. Freeness cancels the common first
section, giving c₀₂=c₀₁*c₁₂. Under the consecutive-label coordinates these are exactly
c(z,gh), c(z,g) and c(z·g,h). -/
theorem right_torsor_cech_cocycle {D : Type u} [Category.{v} D]
    (A : Dᵒᵖ ⥤ GrpCat.{w}) (P : Dᵒᵖ ⥤ Type z)
    (act : ∀ U : Dᵒᵖ, P.obj U → A.obj U → P.obj U)
    (act_mul : ∀ (U : Dᵒᵖ) (s : P.obj U) (a b : A.obj U),
      act U (act U s a) b = act U s (a * b))
    (act_free : ∀ (U : Dᵒᵖ) (s : P.obj U), Function.Injective (act U s))
    (act_natural : ∀ {U V : Dᵒᵖ} (a : U ⟶ V) (s : P.obj U) (g : A.obj U),
      P.map a (act U s g) = act V (P.map a s) ((A.map a).hom g))
    {T T₂ T₃ : D} (p₀ p₁ : T₂ ⟶ T) (p₀₁ p₁₂ p₀₂ : T₃ ⟶ T₂)
    (h₀ : p₀₂ ≫ p₀ = p₀₁ ≫ p₀) (h₁ : p₀₁ ≫ p₁ = p₁₂ ≫ p₀)
    (h₂ : p₀₂ ≫ p₁ = p₁₂ ≫ p₁) (e : P.obj (op T))
    (c : A.obj (op T₂))
    (hc : P.map p₁.op e = act (op T₂) (P.map p₀.op e) c) :
    (A.map p₀₂.op).hom c = (A.map p₀₁.op).hom c * (A.map p₁₂.op).hom c := by
  have edge (p : T₃ ⟶ T₂) :
      P.map (p ≫ p₁).op e = act (op T₃)
        (P.map (p ≫ p₀).op e) ((A.map p.op).hom c) := by
    simpa only [op_comp, P.map_comp, types_comp_apply, act_natural] using
      congrArg (P.map p.op) hc
  apply act_free (op T₃) (P.map (p₀₂ ≫ p₀).op e)
  rw [← edge p₀₂, ← act_mul, h₀, ← edge p₀₁, h₁, ← edge p₁₂, h₂]

/-- When the transition coefficient depends only on the group label, the shifted
right-torsor equation specializes to c(gh)=c(g)c(h), with that order of factors.
Source: the right-torsor calculation in Bhatt–Scholze §7.4
(blueprint: lem-sfb-pointed-finite-etale-limit-cover).

Proof: Substitute the label-only expression for c at all three vertices of the cocycle
equation just stated. The shift z·g disappears because c has no dependence on z.
Nonemptiness of T permits evaluation at one z for every pair g,h. -/
theorem label_only_cocycle {Z : Type u} [Nonempty Z] {G : Type v} [Group G]
    {A : Type w} [Group A] (move : Z → G → Z) (c : Z → G → A) (b : G → A)
    (hc : ∀ (z : Z) (g h : G), c z (g * h) = c z g * c (move z g) h)
    (hb : ∀ (z : Z) (g : G), c z g = b g) :
    ∀ g h : G, b (g * h) = b g * b h := by
  intro g h
  simpa only [hb] using hc (Classical.arbitrary Z) g h

private theorem pointed_map_unique {X Y : Scheme.{u}}
    [ConnectedSpace X] [CompactSpace X] [QuasiSeparatedSpace X]
    [ConnectedSpace Y] [CompactSpace Y] [QuasiSeparatedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y) (f : X ⟶ Y)
    (h : x ≫ f = y) (F : cover x ⟶ cover y)
    (hF : F ≫ proj y = proj x ≫ f) (hpt : pt x ≫ F = pt y) :
    HEq (map f x) F := by
  subst y
  apply heq_of_eq
  apply UniversalCover.hom_ext (x ≫ f)
  intro P s
  apply AlgebraicGeometry.Scheme.finiteEtale_point_ext (X := Y) (T := cover x) (pt x) (proj x ≫ f) P
  · rw [Category.assoc, toObj_hom (x ≫ f) P s, map_proj f x]
  · rw [Category.assoc, toObj_hom (x ≫ f) P s, hF]
  · rw [← Category.assoc, pt_map, ← Category.assoc, hpt]

/-- Identity and composition for pointed limit maps. Heterogeneous equality records
only the reassociation of the base geometric point in their codomains.
Source: Stacks 0BND (3) (blueprint: lem-sfb-pointed-finite-etale-limit-cover).

Proof: For an identity map, composing with every finite-cover section leaves its marked
value unchanged, so marked uniqueness and limit extensionality give the identity.
For f followed by g, the two pullbacks of any finite cover agree through the canonical
pullback-composition isomorphism. Its marked point is the same pair of marked points.
Naturality of splitting sections therefore makes the two maps equal after every limit
projection, hence equal by limit extensionality. -/
theorem pointedLimitMap_identity_composition {X Y Z : Scheme.{u}}
    [ConnectedSpace X] [CompactSpace X] [QuasiSeparatedSpace X]
    [ConnectedSpace Y] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [ConnectedSpace Z] [CompactSpace Z] [QuasiSeparatedSpace Z]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    HEq (map (𝟙 X) x) (𝟙 (cover x)) ∧
      HEq (map (f ≫ g) x) (map f x ≫ map g (x ≫ f)) := by
  constructor
  · apply pointed_map_unique x x (𝟙 X) (Category.comp_id x) (𝟙 (cover x))
    · simp
    · simp
  · apply pointed_map_unique x ((x ≫ f) ≫ g) (f ≫ g)
      (Category.assoc x f g).symm (map f x ≫ map g (x ≫ f))
    · rw [Category.assoc, map_proj, ← Category.assoc, map_proj, Category.assoc]
    · rw [← Category.assoc, pt_map, pt_map]

end AlgebraicGeometry.Scheme.UniversalCover
