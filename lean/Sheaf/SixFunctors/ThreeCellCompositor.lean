/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Sheaf.SixFunctors.AmbientProperOpenPasting
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Tactic.CategoryTheory.Slice

/-! # Three-cell compact-support comparisons

Source: Stacks Project, Tag 0F7K, `lemma-pseudo-functor`, its A,B,C grid and final
pasting calculation; the ambient and simultaneous-system extension in the DAG
(blueprint: lem-sf-three-cell-compositor).

The helpers spell out the supplied staircase, its actual mate words, the canonical
contractions, and directed proper refinement maps. They use the published ambient
calculus, without assuming its raw comparisons invertible.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u g h v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.AmbientProperOpen.ThreeCell

variable {G : Type g} [Category.{h} G] {geo : G ⥤ Scheme.{u}}

/-- The supplied three Cartesian cells, including the outside open and proper arrows.
The quasi-compact fields are automatic for finite-type schemes over a field.
Source: Stacks 0F7K, A,B,C grid (blueprint: lem-sf-three-cell-compositor). -/
structure Staircase (geo : G ⥤ Scheme.{u}) (X Y Z T : G) where
  U : G
  V : G
  W : G
  Xbar : G
  Ybar : G
  Zbar : G
  l : X ⟶ U
  a : U ⟶ V
  b : V ⟶ Xbar
  d : Y ⟶ W
  k : W ⟶ Ybar
  i : Z ⟶ Zbar
  m : U ⟶ Y
  r : V ⟶ W
  p : Xbar ⟶ Ybar
  q : W ⟶ Z
  s : Ybar ⟶ Zbar
  t : Zbar ⟶ T
  [open_l : IsOpenImmersion (geo.map l)]
  [open_a : IsOpenImmersion (geo.map a)]
  [open_b : IsOpenImmersion (geo.map b)]
  [open_d : IsOpenImmersion (geo.map d)]
  [open_k : IsOpenImmersion (geo.map k)]
  [open_i : IsOpenImmersion (geo.map i)]
  [qc_l : QuasiCompact (geo.map l)]
  [qc_a : QuasiCompact (geo.map a)]
  [qc_b : QuasiCompact (geo.map b)]
  [qc_d : QuasiCompact (geo.map d)]
  [qc_k : QuasiCompact (geo.map k)]
  [qc_i : QuasiCompact (geo.map i)]
  [proper_m : IsProper (geo.map m)]
  [proper_r : IsProper (geo.map r)]
  [proper_p : IsProper (geo.map p)]
  [proper_q : IsProper (geo.map q)]
  [proper_s : IsProper (geo.map s)]
  [proper_t : IsProper (geo.map t)]
  commA : a ≫ r = m ≫ d
  commB : b ≫ p = r ≫ k
  commC : k ≫ s = q ≫ i
  cartesianA : IsPullback (geo.map a) (geo.map m) (geo.map r) (geo.map d)
  cartesianB : IsPullback (geo.map b) (geo.map r) (geo.map p) (geo.map k)
  cartesianC : IsPullback (geo.map k) (geo.map q) (geo.map s) (geo.map i)

attribute [instance] Staircase.open_l Staircase.open_a Staircase.open_b
  Staircase.open_d Staircase.open_k Staircase.open_i Staircase.qc_l Staircase.qc_a
  Staircase.qc_b Staircase.qc_d Staircase.qc_k Staircase.qc_i Staircase.proper_m
  Staircase.proper_r Staircase.proper_p Staircase.proper_q Staircase.proper_s Staircase.proper_t

variable (c : Calculus.{u, g, h, v, w} G geo)

/-- A binary raw comparison, with its outside proper functor and both contractions.
Source: Stacks 0F7K, binary rectangles (blueprint: lem-sf-three-cell-compositor). -/
def binary {X U V Y W Z : G}
    (l : X ⟶ U) (a : U ⟶ V) (d : Y ⟶ W)
    (m : U ⟶ Y) (r : V ⟶ W) (q : W ⟶ Z)
    [IsOpenImmersion (geo.map l)] [IsOpenImmersion (geo.map a)]
    [IsOpenImmersion (geo.map d)] [QuasiCompact (geo.map a)]
    [QuasiCompact (geo.map d)] [IsProper (geo.map m)] [IsProper (geo.map r)]
    (comm : a ≫ r = m ≫ d) (K : c.D X) :=
  (c.S q).map ((c.gamma a m r d comm).app ((c.J l).obj K)) ≫
    (c.sComp r q).hom.app ((c.J a).obj ((c.J l).obj K)) ≫
    (c.S (r ≫ q)).map ((c.jComp l a).hom.app K)

variable {X Y Z T : G} (D : Staircase geo X Y Z T)

/-- The expanded word L, in diagrammatic composition order.
Source: Stacks 0F7K, final calculation (blueprint: lem-sf-three-cell-compositor). -/
def expandedLeft (K : c.D X) :=
  (c.S D.t).map ((c.J D.i).map ((c.S D.q).map
    ((c.gamma D.a D.m D.r D.d D.commA).app ((c.J D.l).obj K)))) ≫
  (c.S D.t).map ((c.gamma D.k D.q D.s D.i D.commC).app
    ((c.S D.r).obj ((c.J D.a).obj ((c.J D.l).obj K)))) ≫
  (c.S D.t).map ((c.S D.s).map ((c.gamma D.b D.r D.p D.k D.commB).app
    ((c.J D.a).obj ((c.J D.l).obj K))))

/-- The expanded word R, which moves C before A.
Source: Stacks 0F7K, final calculation (blueprint: lem-sf-three-cell-compositor). -/
def expandedRight (K : c.D X) :=
  (c.S D.t).map ((c.gamma D.k D.q D.s D.i D.commC).app
    ((c.J D.d).obj ((c.S D.m).obj ((c.J D.l).obj K)))) ≫
  (c.S D.t).map ((c.S D.s).map ((c.J D.k).map
    ((c.gamma D.a D.m D.r D.d D.commA).app ((c.J D.l).obj K)))) ≫
  (c.S D.t).map ((c.S D.s).map ((c.gamma D.b D.r D.p D.k D.commB).app
    ((c.J D.a).obj ((c.J D.l).obj K))))

/-- The common contraction of the expanded target, by the specified c and e.
Source: Stacks 0F7K, compositor identifications (blueprint: lem-sf-three-cell-compositor). -/
def contraction (K : c.D X) :=
  (c.S D.t).map ((c.S D.s).map ((c.S D.p).map
    ((c.J D.b).map ((c.jComp D.l D.a).hom.app K) ≫
      (c.jComp (D.l ≫ D.a) D.b).hom.app K))) ≫
  (c.S D.t).map ((c.sComp D.p D.s).hom.app
    ((c.J ((D.l ≫ D.a) ≫ D.b)).obj K)) ≫
  (c.sComp (D.p ≫ D.s) D.t).hom.app ((c.J ((D.l ≫ D.a) ≫ D.b)).obj K)

/-- The actual path comparing (g,f) and then (h,gf).
Source: Stacks 0F7K, A then B+C (blueprint: lem-sf-three-cell-compositor). -/
def leftPath (K : c.D X) :=
  (c.J D.i ⋙ c.S D.t).map (binary c D.l D.a D.d D.m D.r D.q D.commA K) ≫
    binary c (D.l ≫ D.a) D.b D.i (D.r ≫ D.q) (D.p ≫ D.s) D.t
      (by rw [← Category.assoc, D.commB, Category.assoc, D.commC,
        ← Category.assoc]) K

/-- The other binary path, transported from its right-associated final factorization
using the canonical equality transports, so both paths have exactly the same target.
Source: Stacks 0F7K, C then A+B (blueprint: lem-sf-three-cell-compositor). -/
def rightPath (K : c.D X) :=
  binary c D.d D.k D.i D.q D.s D.t D.commC ((c.S D.m).obj ((c.J D.l).obj K)) ≫
    binary c D.l (D.a ≫ D.b) (D.d ≫ D.k) D.m D.p (D.s ≫ D.t)
      (by rw [Category.assoc, D.commB, ← Category.assoc, D.commA,
        Category.assoc]) K ≫
    (c.S (D.p ≫ (D.s ≫ D.t))).map
      ((c.jCongr (Category.assoc D.l D.a D.b)).inv.app K) ≫
    (c.sCongr (Category.assoc D.p D.s D.t)).inv.app
      ((c.J ((D.l ≫ D.a) ≫ D.b)).obj K)

/-- A directed candidate map for a proper refinement, with the unit normalization
and canonical direct-image compositor. The direction is from the coarser candidate
to the finer candidate; its data are exactly the two refinement triangles.
Source: Stacks 0F7K; ambient refinement squares
(blueprint: lem-sf-three-cell-compositor). -/
def candidateMap {X U U' Y : G}
    (j : X ⟶ U) (j' : X ⟶ U') (v : U' ⟶ U) (p : U ⟶ Y) (p' : U' ⟶ Y)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map j')]
    [QuasiCompact (geo.map j)] [QuasiCompact (geo.map j')]
    [IsProper (geo.map v)]
    (hj : j' ≫ v = j) (hp : v ≫ p = p') (K : c.D X) :=
  (c.S p).map ((c.J j).map ((c.sId X).inv.app K) ≫
    (c.gamma j' (𝟙 X) v j (hj.trans (Category.id_comp j).symm)).app K) ≫
  (c.sComp v p).hom.app ((c.J j').obj K) ≫
  (c.sCongr hp).hom.app ((c.J j').obj K)

/-- A compatible proper refinement of every ambient and intermediate scheme, fixing
X,Y,Z,T. The squares between ambient schemes need not be Cartesian.
Source: Stacks 0F7K, refinement of the grid; ambient extension in the DAG
(blueprint: lem-sf-three-cell-compositor). -/
structure Refinement (D' D : Staircase geo X Y Z T) where
  u : D'.U ⟶ D.U
  v : D'.V ⟶ D.V
  w : D'.W ⟶ D.W
  x : D'.Xbar ⟶ D.Xbar
  y : D'.Ybar ⟶ D.Ybar
  z : D'.Zbar ⟶ D.Zbar
  [proper_u : IsProper (geo.map u)]
  [proper_v : IsProper (geo.map v)]
  [proper_w : IsProper (geo.map w)]
  [proper_x : IsProper (geo.map x)]
  [proper_y : IsProper (geo.map y)]
  [proper_z : IsProper (geo.map z)]
  l_comm : D'.l ≫ u = D.l
  a_comm : D'.a ≫ v = u ≫ D.a
  b_comm : D'.b ≫ x = v ≫ D.b
  d_comm : D'.d ≫ w = D.d
  k_comm : D'.k ≫ y = w ≫ D.k
  i_comm : D'.i ≫ z = D.i
  m_comm : u ≫ D.m = D'.m
  r_comm : v ≫ D.r = D'.r ≫ w
  p_comm : x ≫ D.p = D'.p ≫ y
  q_comm : w ≫ D.q = D'.q
  s_comm : y ≫ D.s = D'.s ≫ z
  t_comm : z ≫ D.t = D'.t

attribute [instance] Refinement.proper_u Refinement.proper_v Refinement.proper_w
  Refinement.proper_x Refinement.proper_y Refinement.proper_z

variable {D} {D' : Staircase geo X Y Z T} (ρ : Refinement D' D)

/-- Horizontal composite of the three directed input candidate maps.
Source: Stacks 0F7K, directed refinement calculation
(blueprint: lem-sf-three-cell-compositor). -/
def sourceMap (K : c.D X) :=
  (c.J D.i ⋙ c.S D.t).map ((c.J D.d ⋙ c.S D.q).map
    (candidateMap c D.l D'.l ρ.u D.m D'.m ρ.l_comm ρ.m_comm K)) ≫
  (c.J D.i ⋙ c.S D.t).map
    (candidateMap c D.d D'.d ρ.w D.q D'.q ρ.d_comm ρ.q_comm
      ((c.S D'.m).obj ((c.J D'.l).obj K))) ≫
  candidateMap c D.i D'.i ρ.z D.t D'.t ρ.i_comm ρ.t_comm
    ((c.S D'.q).obj ((c.J D'.d).obj ((c.S D'.m).obj ((c.J D'.l).obj K))))

/-- The final directed candidate map for the composite compactification.
Source: Stacks 0F7K, directed refinement calculation
(blueprint: lem-sf-three-cell-compositor). -/
def targetMap (K : c.D X) :=
  candidateMap c ((D.l ≫ D.a) ≫ D.b) ((D'.l ≫ D'.a) ≫ D'.b) ρ.x
    ((D.p ≫ D.s) ≫ D.t) ((D'.p ≫ D'.s) ≫ D'.t)
    (by rw [Category.assoc, ρ.b_comm, ← Category.assoc, Category.assoc D'.l,
      ρ.a_comm, ← Category.assoc, ρ.l_comm])
    (by rw [← Category.assoc, ← Category.assoc, ρ.p_comm, Category.assoc D'.p,
      ρ.s_comm, Category.assoc, Category.assoc D'.p, Category.assoc D'.s,
      ρ.t_comm, ← Category.assoc]) K

/-- All three-cell equations, including the actual binary path expansions and both
exterior directed refinement squares. They are equations on c.D itself.
Source: Stacks 0F7K; ambient proper/open extension in the DAG
(blueprint: lem-sf-three-cell-compositor). -/
structure Coherent (c : Calculus.{u, g, h, v, w} G geo) : Prop where
  expanded : ∀ {X Y Z T : G} (D : Staircase geo X Y Z T) (K : c.D X),
    expandedLeft c D K = expandedRight c D K
  left_expansion : ∀ {X Y Z T : G} (D : Staircase geo X Y Z T) (K : c.D X),
    leftPath c D K = expandedLeft c D K ≫ contraction c D K
  right_expansion : ∀ {X Y Z T : G} (D : Staircase geo X Y Z T) (K : c.D X),
    rightPath c D K = expandedRight c D K ≫ contraction c D K
  contracted : ∀ {X Y Z T : G} (D : Staircase geo X Y Z T) (K : c.D X),
    leftPath c D K = rightPath c D K
  refinement : ∀ {X Y Z T : G} {D' D : Staircase geo X Y Z T}
    (ρ : Refinement D' D) (K : c.D X),
    (leftPath c D K ≫ targetMap c ρ K = sourceMap c ρ K ≫ leftPath c D' K) ∧
    (rightPath c D K ≫ targetMap c ρ K = sourceMap c ρ K ≫ rightPath c D' K)

private def sCompose {A B C : G} (f : A ⟶ B) (g : B ⟶ C) (fg : A ⟶ C)
    (hfg : f ≫ g = fg) : c.S f ⋙ c.S g ≅ c.S fg :=
  c.sComp f g ≪≫ c.sCongr hfg

private theorem sCompose_refl {A B C : G} (f : A ⟶ B) (g : B ⟶ C) :
    sCompose c f g (f ≫ g) rfl = c.sComp f g := by
  simp [sCompose, Calculus.sCongr]

private theorem sCompose_assoc (hc : Laws c) {A B C E : G}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ E)
    (fg : A ⟶ C) (gh : B ⟶ E) (fgh : A ⟶ E)
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hL : fg ≫ h = fgh) (hR : f ≫ gh = fgh) (M : c.D A) :
    (c.S h).map ((sCompose c f g fg hfg).hom.app M) ≫
        (sCompose c fg h fgh hL).hom.app M =
      (sCompose c g h gh hgh).hom.app ((c.S f).obj M) ≫
        (sCompose c f gh fgh hR).hom.app M := by
  subst fg gh fgh
  simpa [sCompose, Calculus.sCongr] using hc.s_assoc f g h M

private theorem gamma_vertical_comp (hc : Laws c) {A B C E H I : G}
    (k : A ⟶ B) (i : C ⟶ E) (j : H ⟶ I)
    (r₁ : A ⟶ C) (r₂ : C ⟶ H) (p₁ : B ⟶ E) (p₂ : E ⟶ I)
    (r₁₂ : A ⟶ H) (p₁₂ : B ⟶ I)
    [IsOpenImmersion (geo.map k)] [IsOpenImmersion (geo.map i)]
    [IsOpenImmersion (geo.map j)]
    [QuasiCompact (geo.map k)] [QuasiCompact (geo.map i)] [QuasiCompact (geo.map j)]
    [IsProper (geo.map r₁)] [IsProper (geo.map r₂)]
    [IsProper (geo.map p₁)] [IsProper (geo.map p₂)]
    [IsProper (geo.map r₁₂)] [IsProper (geo.map p₁₂)]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (hr : r₁ ≫ r₂ = r₁₂) (hp : p₁ ≫ p₂ = p₁₂)
    (hout : k ≫ p₁₂ = r₁₂ ≫ j) (M : c.D A) :
    (c.gamma i r₂ p₂ j h₂).app ((c.S r₁).obj M) ≫
        (c.S p₂).map ((c.gamma k r₁ p₁ i h₁).app M) ≫
        (sCompose c p₁ p₂ p₁₂ hp).hom.app ((c.J k).obj M) =
      (c.J j).map ((sCompose c r₁ r₂ r₁₂ hr).hom.app M) ≫
        (c.gamma k r₁₂ p₁₂ j hout).app M := by
  subst r₁₂ p₁₂
  have hv := hc.gamma_vertical k i j r₁ r₂ p₁ p₂ h₁ h₂ hout M
  have hv' := congrArg
    (fun f ↦ f ≫ (c.sComp p₁ p₂).hom.app ((c.J k).obj M)) hv
  simp only [Category.assoc, Iso.inv_hom_id_app] at hv'
  simpa [sCompose, Calculus.sCongr] using hv'.symm

private def openRefinement {A B B' : G}
    (j : A ⟶ B) (j' : A ⟶ B') (v : B' ⟶ B)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map j')]
    [QuasiCompact (geo.map j)] [QuasiCompact (geo.map j')]
    [IsProper (geo.map v)] (hj : j' ≫ v = j) (M : c.D A) :=
  (c.J j).map ((c.sId A).inv.app M) ≫
    (c.gamma j' (𝟙 A) v j (hj.trans (Category.id_comp j).symm)).app M

private theorem candidateMap_naturality {A B B' C : G}
    (j : A ⟶ B) (j' : A ⟶ B') (v : B' ⟶ B) (p : B ⟶ C) (p' : B' ⟶ C)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map j')]
    [QuasiCompact (geo.map j)] [QuasiCompact (geo.map j')]
    [IsProper (geo.map v)] (hj : j' ≫ v = j) (hp : v ≫ p = p')
    {M N : c.D A} (f : M ⟶ N) :
    (c.J j ⋙ c.S p).map f ≫ candidateMap c j j' v p p' hj hp N =
      candidateMap c j j' v p p' hj hp M ≫ (c.J j' ⋙ c.S p').map f := by
  let η : c.J j ⟶ c.J j' ⋙ c.S v :=
    Functor.whiskerRight (c.sId A).inv (c.J j) ≫
      c.gamma j' (𝟙 A) v j (hj.trans (Category.id_comp j).symm)
  let θ : c.J j ⋙ c.S p ⟶ c.J j' ⋙ c.S p' :=
    Functor.whiskerRight η (c.S p) ≫ Functor.whiskerLeft (c.J j') (sCompose c v p p' hp).hom
  simpa only [θ, η, candidateMap, sCompose, Iso.trans_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc] using θ.naturality f

private theorem openRefinement_horizontal (hc : Laws c) {A B B' C C' : G}
    (l : A ⟶ B) (l' : A ⟶ B') (a : B ⟶ C) (a' : B' ⟶ C')
    (u : B' ⟶ B) (v : C' ⟶ C)
    [IsOpenImmersion (geo.map l)] [IsOpenImmersion (geo.map l')]
    [IsOpenImmersion (geo.map a)] [IsOpenImmersion (geo.map a')]
    [QuasiCompact (geo.map l)] [QuasiCompact (geo.map l')]
    [QuasiCompact (geo.map a)] [QuasiCompact (geo.map a')]
    [IsProper (geo.map u)] [IsProper (geo.map v)]
    (hl : l' ≫ u = l) (ha : a' ≫ v = u ≫ a)
    (hla : (l' ≫ a') ≫ v = l ≫ a) (M : c.D A) :
    (c.J a).map (openRefinement c l l' u hl M) ≫
        (c.gamma a' u v a ha).app ((c.J l').obj M) ≫
        (c.S v).map ((c.jComp l' a').hom.app M) =
      (c.jComp l a).hom.app M ≫ openRefinement c (l ≫ a) (l' ≫ a') v hla M := by
  have hh := hc.gamma_horizontal l' a' l a (𝟙 A) u v
    (hl.trans (Category.id_comp l).symm) ha
    (hla.trans (Category.id_comp (l ≫ a)).symm) M
  have hh' := (Iso.comp_inv_eq ((c.S v).mapIso ((c.jComp l' a').app M))).mp
    (by simpa only [← Category.assoc, Iso.app_inv, Functor.mapIso_inv] using hh)
  simp only [Functor.mapIso_hom, Iso.app_hom, Category.assoc] at hh'
  unfold openRefinement
  simp only [Functor.map_comp, Category.assoc]
  rw [← hh']
  exact (c.jComp l a).hom.naturality_assoc ((c.sId A).inv.app M) _

private theorem gamma_refinement_rectangle (hc : Laws c) {U U' V V' Y W W' : G}
    (a : U ⟶ V) (a' : U' ⟶ V') (d : Y ⟶ W) (d' : Y ⟶ W')
    (m : U ⟶ Y) (m' : U' ⟶ Y) (r : V ⟶ W) (r' : V' ⟶ W')
    (u : U' ⟶ U) (v : V' ⟶ V) (w : W' ⟶ W)
    [IsOpenImmersion (geo.map a)] [IsOpenImmersion (geo.map a')]
    [IsOpenImmersion (geo.map d)] [IsOpenImmersion (geo.map d')]
    [QuasiCompact (geo.map a)] [QuasiCompact (geo.map a')]
    [QuasiCompact (geo.map d)] [QuasiCompact (geo.map d')]
    [IsProper (geo.map m)] [IsProper (geo.map m')]
    [IsProper (geo.map r)] [IsProper (geo.map r')]
    [IsProper (geo.map u)] [IsProper (geo.map v)] [IsProper (geo.map w)]
    (hA : a ≫ r = m ≫ d) (hA' : a' ≫ r' = m' ≫ d')
    (ha : a' ≫ v = u ≫ a) (hd : d' ≫ w = d)
    (hm : u ≫ m = m') (hr : v ≫ r = r' ≫ w) (M : c.D U') :
    (c.gamma a m r d hA).app ((c.S u).obj M) ≫
        (c.S r).map ((c.gamma a' u v a ha).app M) ≫
        (c.sComp v r).hom.app ((c.J a').obj M) =
      (c.J d).map ((sCompose c u m m' hm).hom.app M) ≫
        openRefinement c d d' w hd ((c.S m').obj M) ≫
        (c.S w).map ((c.gamma a' m' r' d' hA').app M) ≫
        (sCompose c r' w (v ≫ r) hr.symm).hom.app ((c.J a').obj M) := by
  have hout : a' ≫ (v ≫ r) = m' ≫ d := by
    rw [← Category.assoc, ha, Category.assoc, hA, ← Category.assoc, hm]
  have htop := gamma_vertical_comp c hc a' a d u m v r m' (v ≫ r)
    ha hA hm rfl hout M
  have hbottom := gamma_vertical_comp c hc a' d' d m' (𝟙 Y) r' w m' (v ≫ r)
    hA' (hd.trans (Category.id_comp d).symm) (Category.comp_id m') hr.symm hout M
  have hunit := (hc.s_unit m' M).2
  have hnorm : (sCompose c m' (𝟙 Y) m' (Category.comp_id m')).hom.app M =
      (c.sId Y).hom.app ((c.S m').obj M) := hunit
  dsimp only [sCompose, Iso.trans_hom, NatTrans.comp_app] at htop
  simp only [Calculus.sCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id] at htop
  rw [htop]
  unfold openRefinement
  simp only [Functor.map_comp, Category.assoc]
  rw [hbottom, hnorm]
  simp only [← Functor.map_comp_assoc, sCompose, Iso.trans_hom, NatTrans.comp_app,
    Calculus.sCongr]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  congr 1
  congr 1
  simp only [Functor.id_obj]
  simpa only [Category.assoc, Calculus.sCongr] using
    (Category.comp_id ((c.sComp u m).hom.app M ≫ (c.sCongr hm).hom.app M)).symm

private theorem candidateMap_eq {A B B' C : G}
    (j : A ⟶ B) (j' : A ⟶ B') (v : B' ⟶ B) (p : B ⟶ C) (p' : B' ⟶ C)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map j')]
    [QuasiCompact (geo.map j)] [QuasiCompact (geo.map j')]
    [IsProper (geo.map v)] (hj : j' ≫ v = j) (hp : v ≫ p = p') (M : c.D A) :
    candidateMap c j j' v p p' hj hp M =
      (c.S p).map (openRefinement c j j' v hj M) ≫
        (sCompose c v p p' hp).hom.app ((c.J j').obj M) := rfl

private theorem binary_refinement (hc : Laws c) {X U U' V V' Y W W' Z : G}
    (l : X ⟶ U) (l' : X ⟶ U') (a : U ⟶ V) (a' : U' ⟶ V')
    (d : Y ⟶ W) (d' : Y ⟶ W') (m : U ⟶ Y) (m' : U' ⟶ Y)
    (r : V ⟶ W) (r' : V' ⟶ W') (q : W ⟶ Z) (q' : W' ⟶ Z)
    (u : U' ⟶ U) (v : V' ⟶ V) (w : W' ⟶ W)
    [IsOpenImmersion (geo.map l)] [IsOpenImmersion (geo.map l')]
    [IsOpenImmersion (geo.map a)] [IsOpenImmersion (geo.map a')]
    [IsOpenImmersion (geo.map d)] [IsOpenImmersion (geo.map d')]
    [QuasiCompact (geo.map l)] [QuasiCompact (geo.map l')]
    [QuasiCompact (geo.map a)] [QuasiCompact (geo.map a')]
    [QuasiCompact (geo.map d)] [QuasiCompact (geo.map d')]
    [IsProper (geo.map m)] [IsProper (geo.map m')]
    [IsProper (geo.map r)] [IsProper (geo.map r')]
    [IsProper (geo.map u)] [IsProper (geo.map v)] [IsProper (geo.map w)]
    (hA : a ≫ r = m ≫ d) (hA' : a' ≫ r' = m' ≫ d')
    (hl : l' ≫ u = l) (ha : a' ≫ v = u ≫ a) (hd : d' ≫ w = d)
    (hm : u ≫ m = m') (hr : v ≫ r = r' ≫ w) (hq : w ≫ q = q')
    (hla : (l' ≫ a') ≫ v = l ≫ a)
    (hrq : v ≫ (r ≫ q) = r' ≫ q') (K : c.D X) :
    binary c l a d m r q hA K ≫
        candidateMap c (l ≫ a) (l' ≫ a') v (r ≫ q) (r' ≫ q') hla hrq K =
      (c.J d ⋙ c.S q).map (candidateMap c l l' u m m' hl hm K) ≫
        candidateMap c d d' w q q' hd hq ((c.S m').obj ((c.J l').obj K)) ≫
        binary c l' a' d' m' r' q' hA' K := by
  have hh := openRefinement_horizontal c hc l l' a a' u v hl ha hla K
  have hv := gamma_refinement_rectangle c hc a a' d d' m m' r r' u v w
    hA hA' ha hd hm hr ((c.J l').obj K)
  have hs₁ := sCompose_assoc c hc v r q (v ≫ r) (r ≫ q) (r' ≫ q')
    rfl rfl (by rw [hr, Category.assoc, hq]) hrq ((c.J a').obj ((c.J l').obj K))
  have hs₂ := sCompose_assoc c hc r' w q (v ≫ r) q' (r' ≫ q')
    hr.symm hq (by rw [hr, Category.assoc, hq]) rfl
      ((c.J a').obj ((c.J l').obj K))
  have hn₁ := (c.sComp r q).hom.naturality
    ((c.J a).map (openRefinement c l l' u hl K))
  have hn₂ := (c.sComp r q).hom.naturality
    ((c.gamma a' u v a ha).app ((c.J l').obj K))
  have hn₃ := (sCompose c w q q' hq).hom.naturality
    ((c.gamma a' m' r' d' hA').app ((c.J l').obj K))
  have hnA := (c.gamma a m r d hA).naturality (openRefinement c l l' u hl K)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hnA
  have hn₄ := (sCompose c v (r ≫ q) (r' ≫ q') hrq).hom.naturality
    ((c.jComp l' a').hom.app K)
  simp only [Functor.comp_map] at hn₁ hn₂ hn₃ hn₄
  simp only [sCompose_refl] at hs₁ hs₂
  simp only [candidateMap_eq, binary, Functor.comp_map, Functor.map_comp, Category.assoc]
  slice_lhs 3 4 =>
    rw [← Functor.map_comp, ← hh, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  try simp only [Functor.comp_map, Category.assoc]
  slice_lhs 5 6 => rw [hn₄]
  rw [← reassoc_of% hn₁]
  try simp only [Functor.comp_map, Category.assoc]
  rw [← reassoc_of% hn₂]
  try simp only [Functor.comp_map, Category.assoc]
  simp only [Functor.comp_obj, Functor.id_obj]
  rw [← reassoc_of% hs₁]
  try simp only [Functor.comp_map, Category.assoc]
  slice_lhs 1 2 => rw [← Functor.map_comp, ← hnA, Functor.map_comp]
  simp only [Category.assoc]
  slice_lhs 2 4 =>
    rw [← Functor.map_comp, ← Functor.map_comp, hv, Functor.map_comp,
      Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hs₂]
  rw [← reassoc_of% hn₃]
  try simp only [Functor.comp_map, Category.assoc]

private theorem expanded_eq (K : c.D X) :
    expandedLeft c D K = expandedRight c D K := by
  unfold expandedLeft expandedRight
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  congr 1
  exact congrArg (c.S D.t).map
    ((c.gamma D.k D.q D.s D.i D.commC).naturality
      ((c.gamma D.a D.m D.r D.d D.commA).app ((c.J D.l).obj K)))

private theorem left_expansion (hc : Laws c) (K : c.D X) :
    leftPath c D K = expandedLeft c D K ≫ contraction c D K := by
  have hv := hc.gamma_vertical D.b D.k D.i D.r D.q D.p D.s
    D.commB D.commC
    (by rw [← Category.assoc, D.commB, Category.assoc, D.commC,
      ← Category.assoc]) ((c.J D.a).obj ((c.J D.l).obj K))
  have hv' := (Iso.comp_inv_eq ((c.sComp D.p D.s).app
    ((c.J D.b).obj ((c.J D.a).obj ((c.J D.l).obj K))))).mp
      (by simpa only [← Category.assoc, Iso.app_inv] using hv)
  have hvT := congrArg (c.S D.t).map hv'
  simp only [Functor.map_comp, Category.assoc, Iso.app_hom, Functor.comp_obj] at hvT
  have hs₁ := congrArg (c.S D.t).map
    ((c.sComp D.p D.s).hom.naturality
      ((c.J D.b).map ((c.jComp D.l D.a).hom.app K)))
  have hs₂ := congrArg (c.S D.t).map
    ((c.sComp D.p D.s).hom.naturality
      ((c.jComp (D.l ≫ D.a) D.b).hom.app K))
  simp only [Functor.comp_map, Functor.map_comp] at hs₁ hs₂
  unfold leftPath binary expandedLeft contraction
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  congr 1
  slice_lhs 2 3 =>
    rw [← Functor.map_comp]
    exact congrArg (c.S D.t).map
      ((c.gamma D.b (D.r ≫ D.q) (D.p ≫ D.s) D.i
        (by rw [← Category.assoc, D.commB, Category.assoc, D.commC,
          ← Category.assoc])).naturality ((c.jComp D.l D.a).hom.app K))
  simp only [Functor.comp_map, Functor.comp_obj, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hvT]
  rw [← (c.sComp (D.p ≫ D.s) D.t).hom.naturality]
  simp only [Functor.comp_obj]
  rw [← reassoc_of% hs₁]
  simp only [Functor.comp_map]
  rw [← reassoc_of% hs₂]

private theorem right_expansion (hc : Laws c) (K : c.D X) :
    rightPath c D K = expandedRight c D K ≫ contraction c D K := by
  have hh := hc.gamma_horizontal D.a D.b D.d D.k D.m D.r D.p
    D.commA D.commB
    (by rw [Category.assoc, D.commB, ← Category.assoc, D.commA,
      Category.assoc]) ((c.J D.l).obj K)
  have hh' := (Iso.comp_inv_eq ((c.S D.p).mapIso
    ((c.jComp D.a D.b).app ((c.J D.l).obj K)))).mp
      (by simpa only [← Category.assoc, Iso.app_inv, Functor.mapIso_inv] using hh)
  simp only [Functor.mapIso_hom, Iso.app_hom, Category.assoc] at hh'
  have hj := hc.j_assoc D.l D.a D.b K
  have hs := hc.s_assoc D.p D.s D.t ((c.J ((D.l ≫ D.a) ≫ D.b)).obj K)
  unfold rightPath binary expandedRight contraction
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  slice_lhs 2 3 => rw [← Functor.map_comp, hh', Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% (c.sComp D.p (D.s ≫ D.t)).hom.naturality
      ((c.jComp D.l (D.a ≫ D.b)).hom.app K)]
  rw [← reassoc_of% (c.sComp D.p (D.s ≫ D.t)).hom.naturality
      ((c.jCongr (Category.assoc D.l D.a D.b)).inv.app K)]
  try simp only [Functor.mapIso_hom, Iso.app_hom]
  slice_lhs 4 6 =>
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      ← Functor.map_comp, ← hj]
    simp only [Functor.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% (c.sComp D.s D.t).hom.naturality
    ((c.J D.k).map ((c.gamma D.a D.m D.r D.d D.commA).app ((c.J D.l).obj K)))]
  rw [← reassoc_of% (c.sComp D.s D.t).hom.naturality
    ((c.gamma D.b D.r D.p D.k D.commB).app ((c.J D.a).obj ((c.J D.l).obj K)))]
  try simp only [Functor.comp_map]
  congr 1
  congr 1
  rw [← reassoc_of% (c.sComp D.s D.t).hom.naturality
    ((c.S D.p).map ((c.J D.b).map ((c.jComp D.l D.a).hom.app K)))]
  rw [← reassoc_of% (c.sComp D.s D.t).hom.naturality
    ((c.S D.p).map ((c.jComp (D.l ≫ D.a) D.b).hom.app K))]
  try simp only [Functor.comp_map]
  rw [← hs]

private theorem contracted_eq (hc : Laws c) (K : c.D X) :
    leftPath c D K = rightPath c D K := by
  rw [left_expansion c (D := D) hc, right_expansion c (D := D) hc, expanded_eq c (D := D)]

private theorem left_refinement (hc : Laws c) (K : c.D X) :
    leftPath c D K ≫ targetMap c ρ K = sourceMap c ρ K ≫ leftPath c D' K := by
  have hla : (D'.l ≫ D'.a) ≫ ρ.v = D.l ≫ D.a := by
    rw [Category.assoc, ρ.a_comm, ← Category.assoc, ρ.l_comm]
  have hrq : ρ.v ≫ (D.r ≫ D.q) = D'.r ≫ D'.q := by
    rw [← Category.assoc, ρ.r_comm, Category.assoc, ρ.q_comm]
  have hps : ρ.x ≫ (D.p ≫ D.s) = (D'.p ≫ D'.s) ≫ ρ.z := by
    rw [← Category.assoc, ρ.p_comm, Category.assoc, ρ.s_comm, Category.assoc]
  have hlab : ((D'.l ≫ D'.a) ≫ D'.b) ≫ ρ.x = (D.l ≫ D.a) ≫ D.b := by
    rw [Category.assoc, ρ.b_comm, ← Category.assoc, hla]
  have hpst : ρ.x ≫ ((D.p ≫ D.s) ≫ D.t) = (D'.p ≫ D'.s) ≫ D'.t := by
    rw [← Category.assoc, hps, Category.assoc, ρ.t_comm]
  have hB : D.b ≫ (D.p ≫ D.s) = (D.r ≫ D.q) ≫ D.i := by
    rw [← Category.assoc, D.commB, Category.assoc, D.commC, ← Category.assoc]
  have hB' : D'.b ≫ (D'.p ≫ D'.s) = (D'.r ≫ D'.q) ≫ D'.i := by
    rw [← Category.assoc, D'.commB, Category.assoc, D'.commC, ← Category.assoc]
  have h₁ := binary_refinement c hc D.l D'.l D.a D'.a D.d D'.d
    D.m D'.m D.r D'.r D.q D'.q ρ.u ρ.v ρ.w D.commA D'.commA
    ρ.l_comm ρ.a_comm ρ.d_comm ρ.m_comm ρ.r_comm ρ.q_comm hla hrq K
  have h₂ := binary_refinement c hc (D.l ≫ D.a) (D'.l ≫ D'.a) D.b D'.b
    D.i D'.i (D.r ≫ D.q) (D'.r ≫ D'.q) (D.p ≫ D.s) (D'.p ≫ D'.s)
    D.t D'.t ρ.v ρ.x ρ.z hB hB' hla ρ.b_comm ρ.i_comm hrq hps
    ρ.t_comm hlab hpst K
  have hn := candidateMap_naturality c D.i D'.i ρ.z D.t D'.t
    ρ.i_comm ρ.t_comm (binary c D'.l D'.a D'.d D'.m D'.r D'.q D'.commA K)
  unfold leftPath targetMap sourceMap
  simp only [Category.assoc]
  rw [h₂, ← Functor.map_comp_assoc, h₁]
  simp only [Functor.map_comp, Category.assoc]
  simp only [Functor.comp_map] at hn ⊢
  rw [reassoc_of% hn]

private theorem coherent_of_laws (hc : Laws c) : Coherent c where
  expanded D K := expanded_eq c (D := D) K
  left_expansion D K := left_expansion c (D := D) hc K
  right_expansion D K := right_expansion c (D := D) hc K
  contracted D K := contracted_eq c (D := D) hc K
  refinement ρ K := by
    have h := left_refinement c ρ hc K
    exact ⟨h, by simpa only [contracted_eq c hc] using h⟩

/-- Three-cell equality and proper-refinement naturality in both actual coefficient
settings. Positive finite levels are indexed by n+1, exactly as in the ambient calculus.
No separated structure map, inverse comparison, projection arrow, boundedness or
normalization of a coefficient system is assumed.
Source: Stacks Project, Tag 0F7K, A,B,C grid and final calculation; the simultaneous
semilinear-system and refinement extension in the DAG
(blueprint: lem-sf-three-cell-compositor).

Proof:
1. The supplied staircase carries the quasi-compact-open and proper hypotheses.
   Apply lem-sf-ambient-proper-open-pasting in each of its two actual realizations.
2. Its vertical equation expands B+C, and its horizontal equation expands A+B.
   Whiskering by the outside S_t,J_l gives exactly expandedLeft and expandedRight.
3. Naturality of C at A evaluated on J_l K interchanges the first two factors.
   Apply S_t and postcompose with S_t S_s B. This gives expanded at every K;
   natural transformation extensionality gives the equality of transformations.
4. Associativity and naturality of the canonical sComp and jComp identify each
   binary path with its expansion followed by contraction. This gives contracted.
   No tensor is used, so existing tensor associators are carried through unchanged.
5. In a refining binary tower let D be the mate of its top refinement square,
   E that of its bottom refinement square, and H_l,H_al those of the initial and
   composite-open refinement squares. Horizontal pasting gives
   H_al=(D J_l')(J_a H_l), with jComp inserted.
6. The two vertical factorizations of the same outer refinement rectangle give
   (S_r D)(A S_u)=(S_w A')(E S_m'). Whisker by J_l' and precompose with
   J_d S_m H_l. Naturality of A and E, followed by step 5 and sComp, gives the
   binary refinement square with the directed candidateMap defined above.
7. Apply that square to A and to the vertically pasted B+C square. Paste using
   naturality of the outer candidate map to obtain the leftPath refinement square,
   with precisely sourceMap and targetMap. The contracted equality for both
   staircases gives the rightPath square. No refinement square is assumed Cartesian.
8. Every equation is formed in the actual ordinary unbounded derived category,
   including the intrinsic category of semilinear systems. No evaluation or
   total limit is taken, so every quotient transition is retained.
-/
theorem threeCellCompositor (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    Coherent (ordinary F (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) ∧
    Coherent (systems F (WeilConjectures.IntegralSystemRealization.scalarRings l E)
      (WeilConjectures.IntegralSystemRealization.scalarTransitions l E)) := by
  have h := ambientProperOpenPasting F l _hl E n
  exact ⟨coherent_of_laws _ h.1, coherent_of_laws _ h.2.2.1⟩

end AlgebraicGeometry.ProEtale.AmbientProperOpen.ThreeCell
