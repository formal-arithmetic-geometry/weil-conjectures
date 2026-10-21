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
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.OpenSubgroups
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceDegree
import WeilConjectures.AlgebraicGeometry.LimitFibreProducts
import Sheaf.RingTheory.IndEtaleUniverseTransport
import Sheaf.AlgebraicGeometry.EtaleComparison
import Sheaf.AlgebraicGeometry.FiniteEtaleFiniteLimits

/-! # The pointed finite étale limit and its consecutive Čech coordinates

Source: Bhatt–Scholze, The pro-étale topology for schemes, §7.4, and Stacks 0BND,
01YX, 01Z2, 01Z4, 097D (blueprint: lem-sfb-pointed-finite-etale-limit-cover).
The limit, point and finite-cover maps are the existing `UniversalCover` construction.
`IsFundamentalGroup` permits any small profinite model of the finite fibre functor's
natural automorphism group, with its evaluation topology; it introduces no new group.
-/

@[expose] public section
set_option autoImplicit false
universe u v w z
open CategoryTheory Limits Opposite PreGaloisCategory

namespace AlgebraicGeometry.Scheme.UniversalCover

/-- The finite-cover splitting map, with its summands fixed by their value at the marked point.
Source: Stacks 0BND (blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
noncomputable def finiteSplitMap {X : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) (Y : X.FiniteEtale) :
    (∐ fun _ : (FiniteEtale.fiber x).obj Y ↦ cover x) ⟶ pullback (proj x) Y.obj.hom :=
  Sigma.desc fun s ↦ pullback.lift (𝟙 _) (toObj x Y s) (by simp)

/-- The actual scheme `T × P`, using the existing profinite test object, not a product
of underlying sets. Source: Stacks 097D
(blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
noncomputable abbrev profiniteProduct (T : Scheme.{u}) (P : Profinite.{u}) : Scheme.{u} :=
  ((ProEtale.profiniteToProEtOf T).obj P).left

/-- The first projection of the profinite product. Source: Stacks 097D
(blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
noncomputable abbrev profiniteProductBase (T : Scheme.{u}) (P : Profinite.{u}) :
    profiniteProduct T P ⟶ T :=
  ((ProEtale.profiniteToProEtOf T).obj P).hom

/-- The constant-label section as a scheme morphism, by evaluation of locally constant
integer functions. Source: Stacks 097D
(blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
noncomputable def profiniteProductSection (T : Scheme.{u}) (P : Profinite.{u}) (p : P) :
    T ⟶ profiniteProduct T P :=
  pullback.lift
    (ProEtale.toSpecZ T ≫ Spec.map (CommRingCat.ofHom
      (ULift.ringEquiv.symm.toRingHom.comp (LocallyConstant.evalRingHom p))))
    (𝟙 T) (by exact (ProEtale.comp_toSpecZ _).trans (Category.id_comp _).symm)

/-- The q-th power of a finite label set. Source: the consecutive-label construction in
§7.4 (blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
def labelPower (q : ℕ) : Type u ⥤ Type u where
  obj A := Fin q → A
  map f := ↾fun a ↦ f ∘ a

/-- The prescribed inverse system `N ↦ ∐_(G/N)^q T`, with quotient transition maps.
Source: Stacks 097D (blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
noncomputable def finiteLabelDiagram (T : Scheme.{u}) (G : ProfiniteGrp.{u}) (q : ℕ) :
    OpenNormalSubgroup G ⥤ Scheme.{u} :=
  ProfiniteGrp.toFiniteQuotientFunctor G ⋙ CategoryTheory.forget FiniteGrp ⋙ labelPower q ⋙
    (sigmaConst.obj T)

/-- Consecutive labels up to the i-th vertex, in their stated order.
Source: the cumulative-label formula in §7.4
(blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
def cumulativeLabel {G : Type u} [Group G] {q : ℕ} (g : Fin q → G) (i : ℕ) : G :=
  ((List.ofFn g).take i).prod

/-- Restrict a consecutive-label list along an arbitrary simplex map.
Source: the group-nerve construction in §7.4
(blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
def restrictedLabels {G : Type u} [Group G] {m n : ℕ}
    (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) (g : Fin m → G) : Fin n → G :=
  fun i ↦ (cumulativeLabel g (φ.toOrderHom i.castSucc).val)⁻¹ *
    cumulativeLabel g (φ.toOrderHom i.succ).val

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

/-- The continuous map of q labels induced by a pointed scheme morphism.
Source: Stacks 0BND (3) (blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
noncomputable def labelMap (G H : ProfiniteGrp.{u}) (ρ : H →* G)
    (hρ : Continuous ρ) (q : ℕ) :
    Profinite.of (Fin q → H) ⟶ Profinite.of (Fin q → G) :=
  ConcreteCategory.ofHom (ContinuousMap.piMap (fun _ : Fin q ↦ ⟨ρ, hρ⟩))

/-- Map of profinite products over a scheme morphism, using the existing test functor.
Source: Stacks 097D and 0BND (3)
(blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
noncomputable def profiniteProductMap {T T' : Scheme.{u}} (f : T' ⟶ T)
    {P P' : Profinite.{u}} (a : P' ⟶ P) :
    profiniteProduct T' P' ⟶ profiniteProduct T P :=
  pullback.map _ _ _ _ (ProEtale.profiniteToScheme.map a) f
    (𝟙 ProEtale.specZ) (by
      change ProEtale.toSpecZ _ ≫ 𝟙 _ = _ ≫ ProEtale.toSpecZ _
      rw [Category.comp_id]
      exact (ProEtale.comp_toSpecZ _).symm)
    (by
      change ProEtale.toSpecZ T' ≫ 𝟙 _ = f ≫ ProEtale.toSpecZ T
      exact (Category.comp_id _).trans (ProEtale.comp_toSpecZ f).symm)

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end AlgebraicGeometry.Scheme.UniversalCover
