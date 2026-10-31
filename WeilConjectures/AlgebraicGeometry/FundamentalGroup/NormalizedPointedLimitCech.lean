/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PointedLimitFiniteSplitting
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteCechLabels
public import WeilConjectures.AlgebraicGeometry.Limits.AffineOverLimitProperties
public import WeilConjectures.CategoryTheory.Sites.ProEtaleRightTorsor
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Consecutive Čech coordinates on a given pointed finite-cover limit

Source: Stacks Project, Tag 0BND (1), (3), and the finite-label universal-property
calculations (blueprint: lem-sfb-pointed-limit-cech-coordinates).

The limit and splitting here are arbitrary supplied ones, rather than just the
`UniversalCover.cover` construction. Finite-labelled opens are scheme pullbacks of
coproduct inclusions. In particular the first face is specified on those opens with
its actual new base vertex; no fixed-quotient descent of that vertex is assumed.
The label functors and cumulative-label operations of `FiniteCechLabels` are reused.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory Limits Opposite PreGaloisCategory
namespace AlgebraicGeometry.Scheme.PointedLimitCech
open FiniteCechLabels

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {x : Spec (.of Ω) ⟶ X} {G : ProfiniteGrp.{u}}
    [∀ Y, MulAction G ((FiniteEtale.fiber x).obj Y)]
    {S : PointedCosetSystem x G} {L : PointedCosetLimit x G S}

/-- The given limit is an object of the actual small pro-etale site. Its weak
etaleness is obtained from the existing affine-etale inverse-limit theorem, so
no additional assumption is made when evaluating a group sheaf on T.
Source: Stacks 097N and 0BND (blueprint: lem-sfb-pointed-limit-cech-coordinates). -/
def proEtObject (L : PointedCosetLimit x G S) : X.ProEt := by
  letI : Nonempty (OpenNormalSubgroup G) :=
    ⟨⟨⟨⊤, isOpen_univ⟩, inferInstance⟩⟩
  letI : CategoryTheory.IsConnected (OpenNormalSubgroup G) := IsCofiltered.isConnected _
  let D := S.covers ⋙ finiteEtaleOver X ⋙ Over.forget X
  letI (N : OpenNormalSubgroup G) : IsFinite (S.covers.obj N).obj.hom :=
    (S.covers.obj N).property
  letI (N : OpenNormalSubgroup G) : Etale (S.covers.obj N).obj.hom :=
    (S.covers.obj N).obj.prop
  letI (N : OpenNormalSubgroup G) : IsAffineHom (S.covers.obj N).obj.hom := inferInstance
  exact MorphismProperty.Over.mk ⊤ L.cone.pt.hom
    (weaklyEtale_of_isLimit D (isLimitOfPreserves (Over.forget X) L.isLimit)
      (fun N ↦ (S.covers.obj N).obj.hom)
      (fun b ↦ Over.w ((finiteEtaleOver X).map (S.covers.map b)))
      L.cone.pt.hom (fun N ↦ Over.w (L.cone.π.app N)))

/-- A Cech term computed in schemes weakly etale over X, so that group-sheaf
sections can be evaluated on it. Products here are over X.
Source: Stacks 0BND and 098K (blueprint: lem-sfb-pointed-limit-cech-coordinates). -/
abbrev siteTerm (T : X.ProEt) (q : ℕ) : X.ProEt :=
  ∏ᶜ fun _ : Fin (q + 1) ↦ T

/-- The vertex projection of the Cech term in the small pro-etale site.
Source: Stacks 0BND (blueprint: lem-sfb-pointed-limit-cech-coordinates). -/
abbrev siteVertex (T : X.ProEt) (q : ℕ) (i : Fin (q + 1)) : siteTerm T q ⟶ T :=
  Limits.Pi.π (fun _ : Fin (q + 1) ↦ T) i

/-- The indicated edge of the triple overlap, as an actual site morphism.
Source: the right-torsor calculation (blueprint: lem-sfb-pointed-limit-cech-coordinates). -/
def siteEdge (T : X.ProEt) (i j : Fin 3) : siteTerm T 2 ⟶ siteTerm T 1 :=
  Limits.Pi.lift (Fin.cases (siteVertex T 2 i) (fun _ ↦ siteVertex T 2 j))

/-- Every inverse and comparison is pinned by finite summands, not only by points or
constant-label sections. The `faces` equation includes all faces and degeneracies.
Source: Stacks 0BND and the finite-label permutation calculation
(blueprint: lem-sfb-pointed-limit-cech-coordinates). -/
structure Coordinates (B : PointedLimitSplitting L) where
  cone : ∀ q : ℕ, Cone (finiteLabelDiagram L.cone.pt.left G q)
  isLimit : ∀ q : ℕ, IsLimit (cone q)
  base : ∀ q : ℕ, (cone q).pt ⟶ L.cone.pt.left
  quotient_base : ∀ (q : ℕ) (N : OpenNormalSubgroup G),
    (cone q).π.app N ≫ Sigma.desc (fun _ : Fin q → G ⧸ N.toSubgroup ↦
      𝟙 L.cone.pt.left) = base q
  zero : (cone 0).pt = L.cone.pt.left
  relative : ∀ q : ℕ, (cone q).pt ≅
    (Arrow.mk L.cone.pt.hom).cechNerve.obj (op (SimplexCategory.mk q))
  relative_first : ∀ q : ℕ,
    (relative q).hom ≫ WidePullback.π (fun _ : Fin (q + 1) ↦ L.cone.pt.hom) 0 = base q
  relative_vertices : ∀ (q : ℕ) (N : OpenNormalSubgroup G)
    (a : Fin q → G ⧸ N.toSubgroup) (i : Fin q),
    pullback.fst ((cone q).π.app N) (Sigma.ι (fun _ : Fin q → G ⧸ N.toSubgroup ↦
      L.cone.pt.left) a) ≫ (relative q).hom ≫
        WidePullback.π (fun _ : Fin (q + 1) ↦ L.cone.pt.hom) i.succ ≫
          (L.cone.π.app N).left =
    pullback.fst ((cone q).π.app N) (Sigma.ι (fun _ : Fin q → G ⧸ N.toSubgroup ↦
      L.cone.pt.left) a) ≫ base q ≫
        (B.sectionMap (S.covers.obj N) (S.label N (a i))).left
  change : ∀ q : ℕ, (cone q).pt ≅ (cone q).pt
  change_quotient : ∀ (q : ℕ) (N : OpenNormalSubgroup G),
    (change q).hom ≫ (cone q).π.app N =
      (cone q).π.app N ≫ Sigma.desc (fun a : Fin q → G ⧸ N.toSubgroup ↦
        Sigma.ι (fun _ : Fin q → G ⧸ N.toSubgroup ↦ L.cone.pt.left)
          (fun i ↦ cumulativeLabel a (i.val + 1)))
  change_inverse_quotient : ∀ (q : ℕ) (N : OpenNormalSubgroup G),
    (change q).inv ≫ (cone q).π.app N =
      (cone q).π.app N ≫ Sigma.desc (fun a : Fin q → G ⧸ N.toSubgroup ↦
        Sigma.ι (fun _ : Fin q → G ⧸ N.toSubgroup ↦ L.cone.pt.left)
          (fun i ↦ (if i.val = 0 then 1 else
            a ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩)⁻¹ * a i))
  iso : ∀ q : ℕ, (cone q).pt ≅
    (Arrow.mk L.cone.pt.hom).cechNerve.obj (op (SimplexCategory.mk q))
  normalization : ∀ q : ℕ, iso q = change q ≪≫ relative q
  siteIso : ∀ q : ℕ, (cone q).pt ≅ (siteTerm (proEtObject L) q).left
  site_vertices : ∀ (q : ℕ) (i : Fin (q + 1)),
    (siteIso q).hom ≫ (siteVertex (proEtObject L) q i).left =
      (iso q).hom ≫ WidePullback.π (fun _ : Fin (q + 1) ↦ L.cone.pt.hom) i
  first_vertex : ∀ q : ℕ,
    (iso q).hom ≫ WidePullback.π (fun _ : Fin (q + 1) ↦ L.cone.pt.hom) 0 = base q
  zero_identity : (iso 0).hom ≫
    WidePullback.π (fun _ : Fin 1 ↦ L.cone.pt.hom) 0 = eqToHom zero
  constant : ∀ (q : ℕ), (Fin q → G) → (L.cone.pt.left ⟶ (cone q).pt)
  constant_quotient : ∀ (q : ℕ) (g : Fin q → G) (N : OpenNormalSubgroup G),
    constant q g ≫ (cone q).π.app N =
      Sigma.ι (fun _ : Fin q → G ⧸ N.toSubgroup ↦ L.cone.pt.left)
        (fun i ↦ QuotientGroup.mk (g i))
  vertices : ∀ (q : ℕ) (g : Fin q → G) (i : Fin (q + 1)),
    constant q g ≫ (iso q).hom ≫
      WidePullback.π (fun _ : Fin (q + 1) ↦ L.cone.pt.hom) i =
        (B.deck (cumulativeLabel g i.val)).hom.left
  faces : ∀ (m n : ℕ) (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (N : OpenNormalSubgroup G) (g : Fin m → G ⧸ N.toSubgroup),
    pullback.fst ((cone m).π.app N) (Sigma.ι (fun _ : Fin m → G ⧸ N.toSubgroup ↦
      L.cone.pt.left) g) ≫ (iso m).hom ≫
        (Arrow.mk L.cone.pt.hom).cechNerve.map φ.op ≫ (iso n).inv ≫
          (cone n).π.app N =
    pullback.fst ((cone m).π.app N) (Sigma.ι (fun _ : Fin m → G ⧸ N.toSubgroup ↦
      L.cone.pt.left) g) ≫ (iso m).hom ≫
        WidePullback.π (fun _ : Fin (m + 1) ↦ L.cone.pt.hom) (φ.toOrderHom 0) ≫
          Sigma.ι (fun _ : Fin n → G ⧸ N.toSubgroup ↦ L.cone.pt.left)
            (restrictedLabels φ g)
  constant_simplicial : ∀ (m n : ℕ)
    (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) (g : Fin m → G),
    constant m g ≫ (iso m).hom ≫ (Arrow.mk L.cone.pt.hom).cechNerve.map φ.op =
      (B.deck (cumulativeLabel g (φ.toOrderHom 0).val)).hom.left ≫
        constant n (restrictedLabels φ g) ≫ (iso n).hom
  finite_sections : ∀ (Y : X.FiniteEtale) (N : OpenNormalSubgroup G)
    (k : ∀ (a : N.toSubgroup) (s : (FiniteEtale.fiber x).obj Y), (a : G) • s = s)
    (s : (FiniteEtale.fiber x).obj Y) (g : G),
    (B.sectionMap (S.covers.obj N) (S.label N (QuotientGroup.mk g))).left ≫
      (B.finiteStage Y N k s).hom.left = (B.sectionMap Y (g • s)).left
  overlap_sections : ∀ (Y : X.FiniteEtale) (s : (FiniteEtale.fiber x).obj Y) (g : G),
    constant 1 (fun _ ↦ g) ≫ (iso 1).hom ≫
      WidePullback.π (fun _ : Fin 2 ↦ L.cone.pt.hom) 1 ≫ (B.sectionMap Y s).left =
    constant 1 (fun _ ↦ g) ≫ (iso 1).hom ≫
      WidePullback.π (fun _ : Fin 2 ↦ L.cone.pt.hom) 0 ≫ (B.sectionMap Y (g • s)).left

/-- The normalized coordinate presentation exists for every given pointed connected
limit and every supplied normalized splitting, in every degree including zero.
Source: Stacks 0BND (1), (3)
(blueprint: lem-sfb-pointed-limit-cech-coordinates).

Proof (node steps 1--9). Distribute finite coproducts over products over T using
lem-sc-etale-fibre-product-coproduct and lem-weil-pbc-scheme-coproduct-family.
The summand indexed by a has vertices (id,f_a1,...,f_aq). Naturality makes these
comparisons compatible with quotient transitions. The Cech term is a limit of these
products: each compatible last coordinate lifts uniquely through L.isLimit; the first
coordinate is its supplied base map. Transport that cone through the finite splittings.
At degree zero choose T itself, with its identity base map. Cumulative multiplication
of finite labels is a permutation, with inverse a1,a1^-1*a2,...; homomorphisms preserve
both formulas. Limit uniqueness gives change and its inverse. Set alpha=change≫relative.
The constant-label cone and deck_leg give the cumulative vertex equations. For every
cover killed by N, marked uniqueness and the finite-stage formula give f_s,N f_a=f_as.
Check all simplex operators on the clopen pullbacks of finite summands. Their new
consecutive labels are differences of the retained cumulative labels. Their base is
the retained first vertex, which need not descend to the finite quotient coproduct.
For the first face use finite factorization and section_deck to calculate those
labels with the new base vertex. The other faces multiply adjacent increments or
drop the last, and degeneracies insert 1. Glue on the clopen cover; limit uniqueness
gives equalities of scheme morphisms. Simplicial identities follow from vertexwise
uniqueness. The empty label list gives the identity under the canonical degree-zero
identifications. No general existence of arbitrary scheme limits is used. -/
theorem exists_coordinates [ConnectedSpace X] [CompactSpace X] [QuasiSeparatedSpace X]
    [IsFundamentalGroup (FiniteEtale.fiber x) G] (B : PointedLimitSplitting L) :
    Nonempty (Coordinates B) := by
  sorry

/-- Transport the actual vertexwise Cech map through the normalized scheme isomorphisms.
This defines a scheme morphism, not a map on labels or on underlying points.
Source: Stacks 0BND (3) (blueprint: lem-sfb-pointed-limit-cech-coordinates). -/
def map {X' : Scheme.{u}} {x' : Spec (.of Ω) ⟶ X'} {G' : ProfiniteGrp.{u}}
    [∀ Y, MulAction G' ((FiniteEtale.fiber x').obj Y)]
    {S' : PointedCosetSystem x' G'} {L' : PointedCosetLimit x' G' S'}
    {B' : PointedLimitSplitting L'} {B : PointedLimitSplitting L}
    (C' : Coordinates B') (C : Coordinates B) (f : X' ⟶ X)
    (F : L'.cone.pt.left ⟶ L.cone.pt.left)
    (hF : F ≫ L.cone.pt.hom = L'.cone.pt.hom ≫ f) (q : ℕ) :
    (C'.cone q).pt ⟶ (C.cone q).pt :=
  (C'.iso q).hom ≫ (Arrow.mapCechNerve (Arrow.homMk F f hF)).app
    (op (SimplexCategory.mk q)) ≫ (C.iso q).inv

/-- Pointed naturality on every finite-labelled open, for every permissible refinement.
The homomorphism rho is required to be exactly the induced fundamental-group map;
M may be its open normal inverse image of N, or any further open normal refinement.
Source: Stacks 0BND (3) (blueprint: lem-sfb-pointed-limit-cech-coordinates).

Proof (node steps 11--12). Put rho=f_* from lem-galois-pi1-functoriality. Its continuity
makes rho^-1 N an allowed open normal index. On the M-labelled summand send hM to
rho(h)N and use F on the copy of T'. Preservation of the marked sections and the
base-change fibre bijections identify every target vertex after p_N with F applied
to the source vertex. The finiteStage formula makes this an equality on the whole
clopen summand, not only its marked point. These equations are compatible with all
refinements, so the limiting cone gives the coordinate map. Limit uniqueness makes
it the vertexwise Cech map defined above. Products commute with rho, so cumulative
and consecutive labels give the same result. This uses no surjectivity of rho. -/
theorem map_quotient {X' : Scheme.{u}}
    [ConnectedSpace X] [CompactSpace X] [QuasiSeparatedSpace X]
    [ConnectedSpace X'] [CompactSpace X'] [QuasiSeparatedSpace X']
    (f : X' ⟶ X) (x' : Spec (.of Ω) ⟶ X') (G' : ProfiniteGrp.{u})
    [∀ Y, MulAction G' ((FiniteEtale.fiber x').obj Y)]
    [∀ Y, MulAction G ((FiniteEtale.fiber (x' ≫ f)).obj Y)]
    [IsFundamentalGroup (FiniteEtale.fiber x') G']
    [IsFundamentalGroup (FiniteEtale.fiber (x' ≫ f)) G]
    {S' : PointedCosetSystem x' G'} {L' : PointedCosetLimit x' G' S'}
    {S₀ : PointedCosetSystem (x' ≫ f) G} {L₀ : PointedCosetLimit (x' ≫ f) G S₀}
    {B' : PointedLimitSplitting L'} {B₀ : PointedLimitSplitting L₀}
    (C' : Coordinates B') (C₀ : Coordinates B₀)
    (F : L'.cone.pt.left ⟶ L₀.cone.pt.left)
    (hF : F ≫ L₀.cone.pt.hom = L'.cone.pt.hom ≫ f)
    (hs : ∀ (Y : X.FiniteEtale) (s : (FiniteEtale.fiber (x' ≫ f)).obj Y),
      F ≫ (B₀.sectionMap Y s).left =
        (B'.sectionMap ((FiniteEtale.pullback f).obj Y)
          ((FiniteEtale.pullbackFiberIso f x').inv.app Y s)).left ≫
            pullback.fst Y.obj.hom f)
    (ρ : G' →* G)
    (hρ : ρ = FiniteEtale.fundamentalGroupMap (FiniteEtale.pullbackFiberIso f x') G' G)
    : (∀ (q : ℕ) (M : OpenNormalSubgroup G') (N : OpenNormalSubgroup G)
        (hMN : M.toSubgroup ≤ N.toSubgroup.comap ρ) (g : Fin q → G' ⧸ M.toSubgroup),
    pullback.fst ((C'.cone q).π.app M) (Sigma.ι (fun _ : Fin q → G' ⧸ M.toSubgroup ↦
      L'.cone.pt.left) g) ≫ map C' C₀ f F hF q ≫ (C₀.cone q).π.app N =
    pullback.fst ((C'.cone q).π.app M) (Sigma.ι (fun _ : Fin q → G' ⧸ M.toSubgroup ↦
      L'.cone.pt.left) g) ≫ C'.base q ≫ F ≫
        Sigma.ι (fun _ : Fin q → G ⧸ N.toSubgroup ↦ L₀.cone.pt.left)
          (fun i ↦ QuotientGroup.map M.toSubgroup N.toSubgroup ρ hMN (g i))) ∧
      (∀ (q : ℕ) (g : Fin q → G'), C'.constant q g ≫ map C' C₀ f F hF q =
        F ≫ C₀.constant q (fun i ↦ ρ (g i))) := by
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- The identity pointed map induces the identity in every coordinate degree.
Source: Stacks 0BND (3) (blueprint: lem-sfb-pointed-limit-cech-coordinates).
Proof (node step 13): the identity Cech map fixes every vertex. Conjugating by the
same normalized comparison gives the identity. Marked-section and limit uniqueness
identify the pointed comparison over the identity with this map. -/
theorem map_identity [ConnectedSpace X] [CompactSpace X] [QuasiSeparatedSpace X]
    [IsFundamentalGroup (FiniteEtale.fiber x) G]
    {B : PointedLimitSplitting L} (C : Coordinates B) (q : ℕ) :
    map C C (𝟙 X) (𝟙 L.cone.pt.left)
      ((Category.id_comp _).trans (Category.comp_id _).symm) q = 𝟙 _ := by
  have h : Arrow.homMk (𝟙 L.cone.pt.left) (𝟙 X)
      ((Category.id_comp _).trans (Category.comp_id _).symm) =
      𝟙 (Arrow.mk L.cone.pt.hom) := by ext <;> rfl
  unfold map
  rw [h]
  change (C.iso q).hom ≫
    (SimplicialObject.cechNerve.map (𝟙 (Arrow.mk L.cone.pt.hom))).app _ ≫ _ = _
  rw [CategoryTheory.Functor.map_id]
  change (C.iso q).hom ≫ 𝟙 _ ≫ (C.iso q).inv = _
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Composition of pointed maps is composition of the maps on consecutive coordinates.
The square is provided as an arrow so reassociation involves no extra hypothesis.
Source: Stacks 0BND (3) (blueprint: lem-sfb-pointed-limit-cech-coordinates).
Proof (node step 13): the composite vertexwise Cech map has the composites of the
vertex maps as vertices. The middle comparison and its inverse cancel. The resulting
map equals the map for the composite by the fibre-product universal property. On
finite fibres the base-change bijections compose; equivariance characterizes the
induced homomorphisms, so the labels compose in that same order. -/
theorem map_composition {X₁ X₂ X₃ : Scheme.{u}}
    [ConnectedSpace X₁] [CompactSpace X₁] [QuasiSeparatedSpace X₁]
    [ConnectedSpace X₂] [CompactSpace X₂] [QuasiSeparatedSpace X₂]
    [ConnectedSpace X₃] [CompactSpace X₃] [QuasiSeparatedSpace X₃]
    (x₁ : Spec (.of Ω) ⟶ X₁) (x₂ : Spec (.of Ω) ⟶ X₂) (x₃ : Spec (.of Ω) ⟶ X₃)
    (G₁ G₂ G₃ : ProfiniteGrp.{u})
    [∀ Y, MulAction G₁ ((FiniteEtale.fiber x₁).obj Y)]
    [∀ Y, MulAction G₂ ((FiniteEtale.fiber x₂).obj Y)]
    [∀ Y, MulAction G₃ ((FiniteEtale.fiber x₃).obj Y)]
    [IsFundamentalGroup (FiniteEtale.fiber x₁) G₁]
    [IsFundamentalGroup (FiniteEtale.fiber x₂) G₂]
    [IsFundamentalGroup (FiniteEtale.fiber x₃) G₃]
    {S₁ : PointedCosetSystem x₁ G₁} {L₁ : PointedCosetLimit x₁ G₁ S₁}
    {S₂ : PointedCosetSystem x₂ G₂} {L₂ : PointedCosetLimit x₂ G₂ S₂}
    {S₃ : PointedCosetSystem x₃ G₃} {L₃ : PointedCosetLimit x₃ G₃ S₃}
    {B₁ : PointedLimitSplitting L₁} {B₂ : PointedLimitSplitting L₂}
    {B₃ : PointedLimitSplitting L₃}
    (C₁ : Coordinates B₁) (C₂ : Coordinates B₂) (C₃ : Coordinates B₃)
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (hf : x₁ ≫ f = x₂) (hg : x₂ ≫ g = x₃)
    (F : L₁.cone.pt.left ⟶ L₂.cone.pt.left) (H : L₂.cone.pt.left ⟶ L₃.cone.pt.left)
    (hF : F ≫ L₂.cone.pt.hom = L₁.cone.pt.hom ≫ f)
    (hH : H ≫ L₃.cone.pt.hom = L₂.cone.pt.hom ≫ g)
    (q : ℕ) :
    map C₁ C₃ (f ≫ g) (F ≫ H)
      (by rw [Category.assoc, hH, ← Category.assoc, hF, Category.assoc]) q =
        map C₁ C₂ f F hF q ≫ map C₂ C₃ g H hH q := by
  have _ := hf
  have _ := hg
  have h : Arrow.homMk (F ≫ H) (f ≫ g)
      (by
        change (F ≫ H) ≫ L₃.cone.pt.hom = L₁.cone.pt.hom ≫ (f ≫ g)
        rw [Category.assoc, hH, ← Category.assoc, hF, Category.assoc]) =
      (Arrow.homMk F f hF : Arrow.mk L₁.cone.pt.hom ⟶ Arrow.mk L₂.cone.pt.hom) ≫
        (Arrow.homMk H g hH : Arrow.mk L₂.cone.pt.hom ⟶ Arrow.mk L₃.cone.pt.hom) :=
    by ext <;> rfl
  unfold map
  rw [h]
  change (C₁.iso q).hom ≫
    (SimplicialObject.cechNerve.map (Arrow.homMk F f hF ≫
      (Arrow.homMk H g hH : Arrow.mk L₂.cone.pt.hom ⟶
        Arrow.mk L₃.cone.pt.hom))).app _ ≫ _ = _
  rw [CategoryTheory.Functor.map_comp]
  simp only [NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- The fundamental-group homomorphism for the identity pointed morphism is the
identity, using the canonical identity comparison of geometric fibre functors.
Source: Stacks 0BND (3) (blueprint: lem-sfb-pointed-limit-cech-coordinates).
Proof (node step 13): on every finite cover the identity base-change fibre bijection
commutes with every monodromy element. The equivariance characterization in
lem-galois-pi1-functoriality identifies the two actions, and faithfulness of the
action on all finite fibres identifies the homomorphisms. -/
theorem fundamentalGroupMap_identity [ConnectedSpace X] [CompactSpace X]
    [QuasiSeparatedSpace X] [IsFundamentalGroup (FiniteEtale.fiber x) G] :
    FiniteEtale.fundamentalGroupMap
      (FiniteEtale.pullbackFiberIso (𝟙 X) x ≪≫
        eqToIso (congrArg (fun y : Spec (.of Ω) ⟶ X ↦ FiniteEtale.fiber y)
          (Category.comp_id x))) G G = MonoidHom.id G := by
  let τ := FiniteEtale.pullbackFiberIso (𝟙 X) x ≪≫
    eqToIso (congrArg (fun y : Spec (.of Ω) ⟶ X ↦ FiniteEtale.fiber y)
      (Category.comp_id x))
  ext g
  apply (toAut_bijective (FiniteEtale.fiber x) G).injective
  ext Y s
  change FiniteEtale.fundamentalGroupMap τ G G g • s = g • s
  let φ : (FiniteEtale.pullback (𝟙 X)).obj Y ⟶ Y :=
    ObjectProperty.homMk (MorphismProperty.Over.homMk
      (pullback.fst Y.obj.hom (𝟙 X)) (by
        simpa using (pullback.condition (f := Y.obj.hom) (g := 𝟙 X))))
  have hτ (a : (FiniteEtale.fiber x).obj ((FiniteEtale.pullback (𝟙 X)).obj Y)) :
      τ.hom.app Y a = (FiniteEtale.fiber x).map φ a := by
    apply FiniteEtale.fiber_ext x
    simp only [τ, Iso.trans_hom, NatTrans.comp_app, ConcreteCategory.comp_apply,
      FiniteEtale.fiber_map_left]
    rfl
  obtain ⟨a, rfl⟩ : ∃ a, τ.hom.app Y a = s :=
    ⟨τ.inv.app Y s, ConcreteCategory.congr_hom (τ.inv_hom_id_app Y) s⟩
  rw [FiniteEtale.fundamentalGroupMap_smul, hτ, hτ, IsNaturalSMul.naturality]

set_option backward.isDefEq.respectTransparency false in
/-- Fundamental-group homomorphisms for pointed scheme morphisms compose. The last
fibre-functor comparison accounts only for associativity of the geometric base point.
Source: Stacks 0BND (3) (blueprint: lem-sfb-pointed-limit-cech-coordinates).
Proof (node step 13): the base-change fibre bijections for f followed by g compose.
Both homomorphisms therefore have the same equivariance formula on every finite
fibre, by lem-galois-pi1-functoriality. Evaluation on all finite fibres is faithful,
so they are equal. This covers nonsurjective homomorphisms as well. -/
theorem fundamentalGroupMap_composition {X₁ X₂ X₃ : Scheme.{u}}
    [ConnectedSpace X₁] [CompactSpace X₁] [QuasiSeparatedSpace X₁]
    [ConnectedSpace X₂] [CompactSpace X₂] [QuasiSeparatedSpace X₂]
    [ConnectedSpace X₃] [CompactSpace X₃] [QuasiSeparatedSpace X₃]
    (x₁ : Spec (.of Ω) ⟶ X₁) (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (G₁ G₂ G₃ : ProfiniteGrp.{u})
    [∀ Y, MulAction G₁ ((FiniteEtale.fiber x₁).obj Y)]
    [∀ Y, MulAction G₂ ((FiniteEtale.fiber (x₁ ≫ f)).obj Y)]
    [∀ Y, MulAction G₃ ((FiniteEtale.fiber ((x₁ ≫ f) ≫ g)).obj Y)]
    [IsFundamentalGroup (FiniteEtale.fiber x₁) G₁]
    [IsFundamentalGroup (FiniteEtale.fiber (x₁ ≫ f)) G₂]
    [IsFundamentalGroup (FiniteEtale.fiber ((x₁ ≫ f) ≫ g)) G₃] :
    FiniteEtale.fundamentalGroupMap
      (FiniteEtale.pullbackFiberIso (f ≫ g) x₁ ≪≫
        eqToIso (congrArg (fun y : Spec (.of Ω) ⟶ X₃ ↦ FiniteEtale.fiber y)
          (Category.assoc x₁ f g).symm)) G₁ G₃ =
      (FiniteEtale.fundamentalGroupMap
        (FiniteEtale.pullbackFiberIso g (x₁ ≫ f)) G₂ G₃).comp
          (FiniteEtale.fundamentalGroupMap (FiniteEtale.pullbackFiberIso f x₁) G₁ G₂) := by
  let τ₁ := FiniteEtale.pullbackFiberIso f x₁
  let τ₂ := FiniteEtale.pullbackFiberIso g (x₁ ≫ f)
  let τ₃ := FiniteEtale.pullbackFiberIso (f ≫ g) x₁ ≪≫
    eqToIso (congrArg
      (fun y : Spec (.of Ω) ⟶ X₃ ↦ FiniteEtale.fiber y) (Category.assoc x₁ f g).symm)
  ext a
  apply (toAut_bijective (FiniteEtale.fiber ((x₁ ≫ f) ≫ g)) G₃).injective
  ext Y s
  change FiniteEtale.fundamentalGroupMap τ₃ G₁ G₃ a • s =
    FiniteEtale.fundamentalGroupMap τ₂ G₂ G₃
      (FiniteEtale.fundamentalGroupMap τ₁ G₁ G₂ a) • s
  let Y₂ := (FiniteEtale.pullback g).obj Y
  let Y₁ := (FiniteEtale.pullback f).obj Y₂
  let φ : Y₁ ⟶ (FiniteEtale.pullback (f ≫ g)).obj Y :=
    ObjectProperty.homMk (MorphismProperty.Over.homMk
      (pullback.lift (f := Y.obj.hom) (g := f ≫ g)
        (pullback.fst Y₂.obj.hom f ≫ pullback.fst Y.obj.hom g)
        (pullback.snd Y₂.obj.hom f) (by
          rw [Category.assoc, pullback.condition, ← Category.assoc]
          exact (congrArg (· ≫ g)
            (pullback.condition (f := Y₂.obj.hom) (g := f))).trans
              (Category.assoc _ _ _))) (by
          exact pullback.lift_snd _ _ _))
  have hτ (b : (FiniteEtale.fiber x₁).obj Y₁) :
      τ₃.hom.app Y ((FiniteEtale.fiber x₁).map φ b) =
        τ₂.hom.app Y (τ₁.hom.app Y₂ b) := by
    apply FiniteEtale.fiber_ext
    simp only [τ₃, Iso.trans_hom, NatTrans.comp_app, ConcreteCategory.comp_apply]
    change (b.left ≫ pullback.lift _ _ _) ≫ _ = _
    simp only [Category.assoc, pullback.lift_fst, τ₁, τ₂,
      FiniteEtale.pullbackFiberIso_hom_app_left]
  let b : (FiniteEtale.fiber x₁).obj Y₁ :=
    τ₁.inv.app Y₂ (τ₂.inv.app Y s)
  have hb : τ₂.hom.app Y (τ₁.hom.app Y₂ b) = s := by
    have h₁ := ConcreteCategory.congr_hom (τ₁.inv_hom_id_app Y₂)
      (τ₂.inv.app Y s)
    have h₂ := ConcreteCategory.congr_hom (τ₂.inv_hom_id_app Y) s
    simp only [ConcreteCategory.comp_apply, FintypeCat.id_apply] at h₁ h₂
    exact (congrArg (τ₂.hom.app Y) h₁).trans h₂
  rw [← hb]
  calc
    _ = FiniteEtale.fundamentalGroupMap τ₃ G₁ G₃ a •
        τ₃.hom.app Y ((FiniteEtale.fiber x₁).map φ b) := by rw [hτ]
    _ = τ₃.hom.app Y (a • (FiniteEtale.fiber x₁).map φ b) :=
      FiniteEtale.fundamentalGroupMap_smul τ₃ G₁ G₃ a Y _
    _ = τ₂.hom.app Y (τ₁.hom.app Y₂ (a • b)) := by
      rw [← IsNaturalSMul.naturality, hτ]
    _ = _ := by rw [FiniteEtale.fundamentalGroupMap_smul,
      FiniteEtale.fundamentalGroupMap_smul]

/-- The transition section on the double overlap of a right torsor trivialized on T.
Source: Stacks 03AH and the right-torsor calculation
(blueprint: lem-sfb-pointed-limit-cech-coordinates). -/
def torsorCoefficient (H : Sheaf (ProEt.topology X) GrpCat.{v})
    (P : Sheaf.ProEtaleRightTorsor.{u, v, w} X H) (T : X.ProEt)
    (e : P.sheaf.obj.obj (op T)) : H.obj.obj (op (siteTerm T 1)) :=
  P.transition (P.sheaf.obj.map (siteVertex T 1 0).op e)
    (P.sheaf.obj.map (siteVertex T 1 1).op e)

private theorem transition_spec (H : Sheaf (ProEt.topology X) GrpCat.{v})
    (P : Sheaf.ProEtaleRightTorsor.{u, v, w} X H) {U : X.ProEtᵒᵖ}
    (s t : P.sheaf.obj.obj U) : P.act U s (P.transition s t) = t :=
  (Equiv.ofBijective (P.act U s) (P.bijective U s)).apply_symm_apply t

private theorem transition_natural (H : Sheaf (ProEt.topology X) GrpCat.{v})
    (P : Sheaf.ProEtaleRightTorsor.{u, v, w} X H) {U V : X.ProEtᵒᵖ}
    (f : U ⟶ V) (s t : P.sheaf.obj.obj U) :
    (H.obj.map f).hom (P.transition s t) =
      P.transition (P.sheaf.obj.map f s) (P.sheaf.obj.map f t) := by
  apply (P.bijective V (P.sheaf.obj.map f s)).injective
  rw [← P.natural, transition_spec, transition_spec]

private theorem transition_mul (H : Sheaf (ProEt.topology X) GrpCat.{v})
    (P : Sheaf.ProEtaleRightTorsor.{u, v, w} X H) {U : X.ProEtᵒᵖ}
    (r s t : P.sheaf.obj.obj U) :
    P.transition r t = P.transition r s * P.transition s t := by
  apply (P.bijective U r).injective
  rw [← P.act_mul, transition_spec, transition_spec, transition_spec]

private theorem edge_section (H : Sheaf (ProEt.topology X) GrpCat.{v})
    (P : Sheaf.ProEtaleRightTorsor.{u, v, w} X H) (T : X.ProEt)
    (e : P.sheaf.obj.obj (op T)) (i j : Fin 3) (k : Fin 2) :
    P.sheaf.obj.map (siteEdge T i j).op (P.sheaf.obj.map (siteVertex T 1 k).op e) =
      P.sheaf.obj.map (siteVertex T 2 (Fin.cases i (fun _ ↦ j) k)).op e := by
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp, ← op_comp]
  simp only [siteEdge, siteVertex, Pi.lift_π]
  fin_cases k <;> rfl

/-- The canonical transition section of a right torsor obeys the shifted Cech cocycle.
The `Coordinates.siteIso` and `site_vertices` fields identify these actual site terms
and edges with the same scheme overlaps as the consecutive-coordinate faces above.
Source: Stacks 03AH and the right-torsor calculation, node step 10
(blueprint: lem-sfb-pointed-limit-cech-coordinates).

Proof: simple transitivity gives the transition coefficient as the inverse of the
right action on the two pullbacks of e. Its defining equation is e1=e0*c01. Pull this
equation along all three edges. Naturality of the action and the vertex identities
give e2=e0*(c01*c12) and e2=e0*c02. Associativity of the right action and its freeness
give c02=c01*c12. The coordinate faces identify the three edge labels with (z,g),
(z.g,h), and (z,gh). This is c(z,gh)=c(z,g)c(z.g,h), with every coefficient pullback
retained. The companion label_only_cocycle below supplies its label-only
specialization, with no commutativity assumption. Weak etaleness of the supplied
limit, needed for the site object, is derived by proEtObject, not hypothesized. -/
theorem torsor_transition_cocycle (L : PointedCosetLimit x G S)
    (H : Sheaf (ProEt.topology X) GrpCat.{v})
    (P : Sheaf.ProEtaleRightTorsor.{u, v, w} X H)
    (e : P.sheaf.obj.obj (op (proEtObject L))) :
    P.sheaf.obj.map (siteVertex (proEtObject L) 1 1).op e =
      P.act (op (siteTerm (proEtObject L) 1))
        (P.sheaf.obj.map (siteVertex (proEtObject L) 1 0).op e)
        (torsorCoefficient H P (proEtObject L) e) ∧
    (H.obj.map (siteEdge (proEtObject L) 0 2).op).hom
        (torsorCoefficient H P (proEtObject L) e) =
      (H.obj.map (siteEdge (proEtObject L) 0 1).op).hom
          (torsorCoefficient H P (proEtObject L) e) *
        (H.obj.map (siteEdge (proEtObject L) 1 2).op).hom
          (torsorCoefficient H P (proEtObject L) e) := by
  constructor
  · exact (transition_spec H P _ _).symm
  · simp only [torsorCoefficient, transition_natural, edge_section]
    exact transition_mul H P _ _ _

/-- When the transition coefficient depends only on the group label, the shifted
right-torsor equation specializes to c(gh)=c(g)c(h), with that order of factors.
Source: the right-torsor calculation in Bhatt–Scholze §7.4
(blueprint: lem-sfb-pointed-limit-cech-coordinates).

Proof: Substitute the label-only expression for c at all three vertices of the cocycle
equation just stated. The shift z·g disappears because c has no dependence on z.
Nonemptiness of T permits evaluation at one z for every pair g,h. -/
theorem label_only_cocycle {Z : Type u} [Nonempty Z] {G : Type v} [Group G]
    {A : Type w} [Group A] (move : Z → G → Z) (c : Z → G → A) (b : G → A)
    (hc : ∀ (z : Z) (g h : G), c z (g * h) = c z g * c (move z g) h)
    (hb : ∀ (z : Z) (g : G), c z g = b g) :
    ∀ g h : G, b (g * h) = b g * b h := by
  intro g h
  obtain ⟨z⟩ := ‹Nonempty Z›
  simpa only [hb] using hc z g h

end AlgebraicGeometry.Scheme.PointedLimitCech
