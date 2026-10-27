/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q77
-/
module

public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Homology.Homotopy
import Sheaf.CategoryTheory.InternalBarCoefficientTransfer

/-! # Finite-index transfer on internal condensed bar double complexes

Source: blueprint, six-functors direct-image proof, paragraph (3), internal scalar
bar auxiliary argument (blueprint: lem-sfb-internal-bar-row-finite-index-transfer).
The bar models are the evaluation-normalized models of the recorded bar-data definition.
All coefficients and all nonnegative equivariant complexes are allowed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.CondensedBar

variable {A : Ring.{u}} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- An open subgroup of a profinite group is compact since it is closed.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-internal-bar-row-finite-index-transfer). -/
instance barTransferSubgroupCompact (H : OpenSubgroup G) : CompactSpace H.toSubgroup :=
  isCompact_iff_compactSpace.mp H.isClosed.isCompact

/-- The continuous inclusion defining the restricted coefficient action.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-internal-bar-row-finite-index-transfer). -/
def barTransferInclusion (H : OpenSubgroup G) : H.toSubgroup →ₜ* G :=
  { H.toSubgroup.subtype with continuous_toFun := continuous_subtype_val }

/-- Inclusion on the profinite parameters of inhomogeneous cochains.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-internal-bar-row-finite-index-transfer). -/
def barTransferPowerInclusion (H : OpenSubgroup G) (p : ℕ) :
    C(power H.toSubgroup p, power G p) :=
  ⟨fun x i ↦ (x i : G), continuous_pi fun i ↦ continuous_subtype_val.comp
    (continuous_apply i)⟩

/-- Restriction of the action followed by the specified subgroup bar functor.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-internal-bar-row-finite-index-transfer). -/
def restrictedBarCochains (H : OpenSubgroup G) {F : InternalFunctions A}
    (B : BarDiagram (G := H.toSubgroup) F) : Equivariant A G ⥤ CochainComplex (Modules A) ℕ :=
  Profinite.CondensedAction.inflate (R := A.toMon) (barTransferInclusion H) ⋙ cochains B

/-- Restricting the coefficient action retains addition of all underlying maps.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-internal-bar-row-finite-index-transfer). -/
instance restrictedBarCochainsAdditive (H : OpenSubgroup G) {F : InternalFunctions A}
    (B : BarDiagram (G := H.toSubgroup) F) : (restrictedBarCochains H B).Additive where
  map_add := by
    intros N P f g
    exact (Functor.mapAddHom (cochains B)).map_add
      ((Profinite.CondensedAction.inflate (R := A.toMon) (barTransferInclusion H)).map f)
      ((Profinite.CondensedAction.inflate (R := A.toMon) (barTransferInclusion H)).map g)

/-- Apply a coefficient bar functor to a complex, with bar degree outermost.
Its value for the group bar functor is exactly the recorded `doubleComplex`.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-internal-bar-row-finite-index-transfer). -/
def barTransferDouble (B : Equivariant A G ⥤ CochainComplex (Modules A) ℕ)
    [B.Additive] : CochainComplex (Equivariant A G) ℕ ⥤
      HomologicalComplex₂ (Modules A) (.up ℕ) (.up ℕ) :=
  B.mapHomologicalComplex (.up ℕ) ⋙
    HomologicalComplex₂.flipFunctor (Modules A) (.up ℕ) (.up ℕ)

/-- Internal vertical cohomology followed termwise, retaining the horizontal differential.
These are sheaf kernels and images in the internal module category, before evaluation.
Source: blueprint paragraph (3), and the double-complex convention
(blueprint: lem-sfb-internal-bar-row-finite-index-transfer). -/
def barTransferVerticalCohomology (A : Ring.{u}) (q : ℕ) :
    HomologicalComplex₂ (Modules A) (.up ℕ) (.up ℕ) ⥤ CochainComplex (Modules A) ℕ :=
  (HomologicalComplex.homologyFunctor (Modules A) (.up ℕ) q).mapHomologicalComplex (.up ℕ)

private def transferDoubleMap
    {B C : Equivariant A G ⥤ CochainComplex (Modules A) ℕ}
    [B.Additive] [C.Additive] (r : B ⟶ C) : barTransferDouble B ⟶ barTransferDouble C :=
  Functor.whiskerRight (NatTrans.mapHomologicalComplex r (.up ℕ))
    (HomologicalComplex₂.flipFunctor (Modules A) (.up ℕ) (.up ℕ))

private def transferDoubleHomotopy
    {B C : Equivariant A G ⥤ CochainComplex (Modules A) ℕ}
    [B.Additive] [C.Additive] (r : B ⟶ C) (t : C ⟶ B) (n : ℕ)
    (h : ∀ N, Homotopy (r.app N ≫ t.app N) (n • 𝟙 (B.obj N)))
    (hn : ∀ (N P : Equivariant A G) (f : N ⟶ P) (i j : ℕ),
      (B.map f).f i ≫ (h P).hom i j = (h N).hom i j ≫ (B.map f).f j)
    (I : CochainComplex (Equivariant A G) ℕ) :
    Homotopy ((transferDoubleMap r).app I ≫ (transferDoubleMap t).app I)
      (n • 𝟙 ((barTransferDouble B).obj I)) where
  hom i j :=
    { f := fun q ↦ (h (I.X q)).hom i j
      comm' := by
        intro q q' _
        exact (hn _ _ (I.d q q') i j).symm }
  zero i j hij := by
    apply HomologicalComplex.hom_ext
    intro q
    exact (h (I.X q)).zero i j hij
  comm i := by
    apply HomologicalComplex.hom_ext
    intro q
    simpa [transferDoubleMap, barTransferDouble, dNext, prevD,
      HomologicalComplex₂.flipFunctor, HomologicalComplex₂.flip,
      Functor.mapHomologicalComplex] using (h (I.X q)).comm i

/-- Finite-index internal restriction, transfer and horizontal homotopy, naturally in
all equivariant coefficient complexes. The restriction is fixed by its evaluation formula.
The transfer is a bicomplex map, and the horizontal homotopy has vertical chain-map
components: these express respectively d_h t = t d_h, d_v t = t d_v and d_v h = h d_v.
`Homotopy.comm` expresses t r - index = d_h h + h d_h, including degree zero.
Every component is an internal module morphism, hence commutes with all profinite test
restrictions. The last clauses give the induced horizontal homotopy and index identity
on internal vertical, then horizontal, cohomology.

Source: blueprint direct-image proof paragraph (3), scalar tame-kernel auxiliary argument
(blueprint: lem-sfb-internal-bar-row-finite-index-transfer).
Proof: (1) Use lem-sfb-internal-homogeneous-cochain-coordinates to change to homogeneous
coordinates, and the transversal S and retraction rho of
lem-sfb-finite-coset-homogeneous-averaging. (2) Define transfer by the finite sum of
s inverse acting on F(rho(s x_0),...,rho(s x_p)). Right-coset reindexing proves
homogeneity; for variable group sections use the finite clopen partition by the coset
permutation. Deletion commutes with this substitution, and T R is the sum of a_s pullbacks.
(3) Sum the prisms P_{1,a_s} of lem-sfb-internal-function-vertex-prism. Its boundary is
T R minus the index; coset reindexing also shows that this sum preserves homogeneity.
(4) Conjugate transfer and prism by the homogeneous coordinate maps. All operations
commute with coefficient maps, hence with the vertical differential and chain maps.
(5) Apply internal kernel/image quotients vertically, preserving the identity and
homotopy. On horizontal cycles the homotopy identity is a boundary, giving the stated
index identity on horizontal cohomology. All sums are finite integral sums; no inverse
index, injectivity, resolution, norm or completeness assumption is used. For H=G take
the singleton transversal and zero homotopy. The zero ring and zero complex are included.
-/
theorem internal_bar_finite_index_transfer (A : Ring.{u}) (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] (H : OpenSubgroup G) (F : InternalFunctions A)
    (B : BarDiagram (G := G) F) (BH : BarDiagram (G := H.toSubgroup) F) :
    ∃ r : barTransferDouble (cochains B) ⟶ barTransferDouble (restrictedBarCochains H BH),
    ∃ t : barTransferDouble (restrictedBarCochains H BH) ⟶ barTransferDouble (cochains B),
    ∃ h : ∀ I : CochainComplex (Equivariant A G) ℕ,
      Homotopy (r.app I ≫ t.app I)
        (H.toSubgroup.index • 𝟙 ((barTransferDouble (cochains B)).obj I)),
      (∀ (I : CochainComplex (Equivariant A G) ℕ) (p q : ℕ) (S : Profinite.{u})
        (x : sections A ((F.functor (power G p)).obj (I.X q).module) S)
        (T : Profinite.{u}) (f : T ⟶ S) (g : C(T, power H.toSubgroup p)),
        (F.evaluate (power H.toSubgroup p) S (I.X q).module
          (((B.term (I.X q) p).inv ≫ ((r.app I).f p).f q ≫
            (BH.term ((Profinite.CondensedAction.inflate (R := A.toMon)
              (barTransferInclusion H)).obj (I.X q)) p).hom).hom.hom.app (op S) x)).val
                T f g =
        (F.evaluate (power G p) S (I.X q).module x).val T f
          ((barTransferPowerInclusion H p).comp g)) ∧
      (∀ (I J : CochainComplex (Equivariant A G) ℕ) (f : I ⟶ J) (i j : ℕ),
        ((barTransferDouble (cochains B)).map f).f i ≫ (h J).hom i j =
          (h I).hom i j ≫ ((barTransferDouble (cochains B)).map f).f j) ∧
      (∀ (I : CochainComplex (Equivariant A G) ℕ) (q : ℕ),
        ∃ hv : Homotopy
          ((barTransferVerticalCohomology A q).map (r.app I) ≫
            (barTransferVerticalCohomology A q).map (t.app I))
          (H.toSubgroup.index •
            𝟙 ((barTransferVerticalCohomology A q).obj
              ((barTransferDouble (cochains B)).obj I))),
          ∀ i j : ℕ, hv.hom i j = HomologicalComplex.homologyMap ((h I).hom i j) q) ∧
      (∀ (I : CochainComplex (Equivariant A G) ℕ) (p q : ℕ),
        HomologicalComplex.homologyMap
            ((barTransferVerticalCohomology A q).map (r.app I)) p ≫
          HomologicalComplex.homologyMap
            ((barTransferVerticalCohomology A q).map (t.app I)) p =
          H.toSubgroup.index •
            𝟙 (((barTransferVerticalCohomology A q).obj
              ((barTransferDouble (cochains B)).obj I)).homology p)) := by
  obtain ⟨r, t, h, hr, hn⟩ := internal_bar_coefficient_transfer A G H F B BH
  let R := transferDoubleMap (C := restrictedBarCochains H BH) r
  let T := transferDoubleMap (B := restrictedBarCochains H BH) t
  let K := transferDoubleHomotopy (C := restrictedBarCochains H BH)
    r t H.toSubgroup.index h hn
  have hv (I : CochainComplex (Equivariant A G) ℕ) (q : ℕ) :
      ∃ hh : Homotopy
        ((barTransferVerticalCohomology A q).map (R.app I) ≫
          (barTransferVerticalCohomology A q).map (T.app I))
        (H.toSubgroup.index • 𝟙 ((barTransferVerticalCohomology A q).obj
          ((barTransferDouble (cochains B)).obj I))),
        ∀ i j, hh.hom i j = HomologicalComplex.homologyMap ((K I).hom i j) q := by
    let V := HomologicalComplex.homologyFunctor (Modules A) (.up ℕ) q
    let hk := V.mapHomotopy (K I)
    refine ⟨{ hom := hk.hom, zero := hk.zero, comm := ?_ }, ?_⟩
    · intro i
      have hc := hk.comm i
      simpa only [Functor.map_comp, Functor.map_nsmul, Functor.map_id,
        barTransferVerticalCohomology, V, R, T] using hc
    · intro i j
      rfl
  refine ⟨R, T, K, ?_, ?_, hv, ?_⟩
  · intro I p q S x T' f g
    exact hr (I.X q) p S x T' f g
  · intro I J f i j
    apply HomologicalComplex.hom_ext
    intro q
    exact hn (I.X q) (J.X q) (f.f q) i j
  · intro I p q
    obtain ⟨hh, _⟩ := hv I q
    rw [← HomologicalComplex.homologyMap_comp, hh.homologyMap_eq]
    change (HomologicalComplex.homologyFunctor (Modules A) (.up ℕ) p).map
      (H.toSubgroup.index • 𝟙 _) = _
    simp only [Functor.map_nsmul, Functor.map_id]
    rfl

end CategoryTheory.CondensedBar
