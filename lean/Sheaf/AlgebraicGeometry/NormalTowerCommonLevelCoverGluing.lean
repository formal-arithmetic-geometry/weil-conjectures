module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Sober

public import Sheaf.AlgebraicGeometry.NormalTowerCoverGluingData
import Sheaf.AlgebraicGeometry.NormalTowerOverlapSystem
import Sheaf.AlgebraicGeometry.NormalTowerOverlapDescent
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Fintype.EquivFin

/-! # Common-level gluing of finite étale covers on a normal tower

Source: ILO, IX Proposition 2.1, printed pp.133--134; the explicit common-level
assembly in the DAG proof; Stacks Tags 0BQM, 033M, 01JB and 01JC
(blueprint: lem-sfb-normal-tower-common-level-cover-gluing).

The auxiliary definitions are canonical chart maps and pullback transports used to
spell out the specified identifications, overlap uniqueness, and cocycle equations.
Finite étale covers use exactly `(@IsFinite ⊓ @Etale).Over ⊤`, as recorded in
`def-weil-pbc-finite-etale-category`. No normalization/base-change comparison is used.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits



namespace AlgebraicGeometry.Scheme

open NormalTowerCoverGluing

/-- Local finite étale extensions with their specified dense-open identifications glue
at the product of a finite subfamily of prime-to-`p` tower levels.

Source: ILO IX Proposition 2.1, printed pp.133--134, locality and extension of graphs;
the DAG's explicit common-level assembly; Stacks Tags 0BQM, 033M, 01JB and 01JC
(blueprint: lem-sfb-normal-tower-common-level-cover-gluing).

Proof:
1. Quasi-compactness gives finitely many `W v`. Their levels have a positive product
   prime to `p`; every selected level divides it. Pull each local cover and specified
   identification back to that level. Finite and étale morphisms are stable under
   base change (`lem-weil-pbc-finite-morphism-permanence`,
   `lem-weil-pbc-etale-scheme-base-change`). The tower maps are over `V`, so the
   inverse image of the prescribed open is exactly the corresponding open chart.
2. Apply `rem-pc-regular-normal` to split the common level into its finitely many
   clopen normal integral components. A nonempty open in a component contains its
   generic point, as does its intersection with the prescribed open. On each
   nonempty component of an overlap, extend the map `θ_j⁻¹ θ_i` uniquely from the
   generic point by `lem-sbc-normal-integral-generic-hom-full`. Its restriction
   agrees with the original map by generic faithfulness on that open. Glue these
   extensions over the disjoint component domains with
   `lem-weil-pbc-scheme-morphism-gluing`.
3. Generic uniqueness gives uniqueness of every overlap extension. The diagonal,
   inverse and triple-overlap equations hold on the prescribed open by cancellation
   of the specified identifications. Generic uniqueness on each component and
   gluing give them on the entire overlaps. The reverse transitions are inverses.
4. Apply `lem-weil-pbc-glue-schemes` to the local covers and their overlap
   isomorphisms. Glue their structural maps using
   `lem-weil-pbc-scheme-morphism-gluing`. The inverse image of each base chart is
   its glued local cover: a point in another chart lying over this base chart
   belongs to their overlap and is identified there by the transition. Thus the
   resulting chart isomorphisms induce precisely the specified transitions.
5. Finiteness and étaleness are local on the target by
   `lem-weil-pbc-closed-finite-etale-zariski-local`, so the global cover is finite
   étale. The specified identifications, and their inverses, agree on overlaps
   by construction; glue both using `lem-weil-pbc-scheme-morphism-gluing`.
   Their composites are identities locally, hence globally. This gives `θ` and
   its compatibility with every specified local identification.
6. If `V` is empty, select no points and take level `1` and the empty cover.
   Empty common levels, local covers, and overlaps have their unique empty maps.
   If the prescribed open at the common level is empty, generic-point containment
   forces that level to be empty. No comparison with integral closure under the
   transition maps is used. -/
theorem finiteEtale_normalTower_commonLevel_cover_gluing
    (p : ℕ) (hp : p.Prime) (V : Scheme.{u}) [CompactSpace V] (U : V.Opens)
    (P : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ U.toScheme)
    (X : {m : ℕ // 0 < m ∧ Nat.Coprime m p} → Over V)
    [hNoeth : ∀ m : {m : ℕ // 0 < m ∧ Nat.Coprime m p},
      IsLocallyNoetherian (X m).left]
    [hCompact : ∀ m : {m : ℕ // 0 < m ∧ Nat.Coprime m p}, CompactSpace (X m).left]
    (hNormal : ∀ (m : {m : ℕ // 0 < m ∧ Nat.Coprime m p}) (x : (X m).left),
      IsDomain ((X m).left.presheaf.stalk x) ∧
      IsIntegrallyClosed ((X m).left.presheaf.stalk x))
    (q : ∀ (a b : {m : ℕ // 0 < m ∧ Nat.Coprime m p}) (_ : a.val ∣ b.val), X b ⟶ X a)
    (q_id : ∀ a : {m : ℕ // 0 < m ∧ Nat.Coprime m p}, q a a dvd_rfl = 𝟙 (X a))
    (q_comp : ∀ (a b c : {m : ℕ // 0 < m ∧ Nat.Coprime m p})
      (hab : a.val ∣ b.val) (hbc : b.val ∣ c.val),
      q b c hbc ≫ q a b hab = q a c (hab.trans hbc))
    (hGeneric : ∀ (m : {m : ℕ // 0 < m ∧ Nat.Coprime m p})
      (C : Set (X m).left), C ∈ irreducibleComponents (X m).left →
      ∀ η : (X m).left, IsGenericPoint η C → (X m).hom η ∈ U)
    (W : V → V.Opens) (hW : ∀ v : V, v ∈ W v)
    (m : V → {m : ℕ // 0 < m ∧ Nat.Coprime m p})
    (Y : ∀ v : V,
      (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ (chart (X (m v)) (W v)))
    (θlocal : ∀ v : V,
      (MorphismProperty.Over.pullback _ ⊤
        (chartInclusion (X (m v)) (inf_le_left : W v ⊓ U ≤ W v))).obj (Y v) ≅
      (MorphismProperty.Over.pullback _ ⊤
        (chartToOpen (X (m v)) (inf_le_right : W v ⊓ U ≤ U))).obj P) :
    ∃ (s : ℕ) (v : Fin s → V) (n : {n : ℕ // 0 < n ∧ Nat.Coprime n p})
      (hd : ∀ j : Fin s, (m (v j)).val ∣ n.val),
      (⨆ j : Fin s, W (v j)) = ⊤ ∧
      n.val = ∏ j : Fin s, (m (v j)).val ∧
      Nonempty (Gluing (X n) U P (fun j ↦ X (m (v j))) (fun j ↦ W (v j))
        (fun j ↦ q (m (v j)) n (hd j)) (fun j ↦ Y (v j)) (fun j ↦ θlocal (v j))) := by
  classical
  have _ := hp
  have _ := q_id
  have _ := q_comp
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun v : V ↦ (W v : Set V)) (fun v ↦ (W v).isOpen)
    (fun v _ ↦ Set.mem_iUnion.mpr ⟨v, hW v⟩)
  let v : Fin t.card → V := fun j ↦ (t.equivFin.symm j).val
  have hcover : (⨆ j : Fin t.card, W (v j)) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨w, hw, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨t.equivFin ⟨w, hw⟩, ?_⟩
    simpa [v] using hx
  let n : {n : ℕ // 0 < n ∧ Nat.Coprime n p} :=
    ⟨∏ j : Fin t.card, (m (v j)).val,
      Finset.prod_pos (fun j _ ↦ (m (v j)).property.1),
      Nat.coprime_prod_left_iff.mpr (fun j _ ↦ (m (v j)).property.2)⟩
  have hd (j : Fin t.card) : (m (v j)).val ∣ n.val :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  obtain ⟨d⟩ := normalTower_overlap_system (X n) U P
    (fun j ↦ X (m (v j))) (fun j ↦ W (v j))
    (fun j ↦ q (m (v j)) n (hd j)) (fun j ↦ Y (v j)) (fun j ↦ θlocal (v j))
    (hNormal n) (hGeneric n)
  obtain ⟨g⟩ := normalTower_overlap_descent (X n) U P
    (fun j ↦ X (m (v j))) (fun j ↦ W (v j))
    (fun j ↦ q (m (v j)) n (hd j)) (fun j ↦ Y (v j)) (fun j ↦ θlocal (v j))
    hcover d
  refine ⟨t.card, v, n, hd, hcover, rfl, ⟨?_⟩⟩
  exact
    { Z := g.Z
      θ := g.θ
      e := g.e
      identification := g.identification
      α := d.α
      overlap_identification := d.overlap_identification
      overlap_unique := d.overlap_unique
      identity := d.identity
      cocycle := d.cocycle
      induces := g.induces }

end AlgebraicGeometry.Scheme
