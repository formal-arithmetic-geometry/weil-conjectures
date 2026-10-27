module

public import Sheaf.AlgebraicGeometry.FiniteAffineRefinementCollection

/-!
# Existence of finite affine refinement collections

Source: Stacks Project, Schemes, Tags 01IT and 01KO; Limits, Tag 01ZR, first proof.
(blueprint: lem-trf-finite-affine-refinement-existence).
-/

@[expose] public section
set_option autoImplicit false

universe u v

open TopologicalSpace

namespace AlgebraicGeometry

private theorem pack_finite_affine_refinements {X : Scheme.{u}}
    {A : Type v} [Finite A] (U : A → X.affineOpens)
    (hU : (⨆ a, (U a).1) = ⊤)
    (P : X.affineOpens → X.affineOpens → Finset X.affineOpens)
    (hP : ∀ V W, (⨆ r ∈ P V W, r.1) = V.1 ⊓ W.1)
    (T : X.affineOpens → X.affineOpens → X.affineOpens → Finset X.affineOpens)
    (hT : ∀ V W Z, (⨆ t ∈ T V W Z, t.1) = V.1 ⊓ W.1 ⊓ Z.1) :
    ∃ (K : FiniteAffineRefinementShape) (C : Fin K.size → X.Opens), K.Valid C := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let PairLabel := Σ a : A, Σ b : A, ↥(P (U a) (U b))
  let pOpen (r : PairLabel) : X.affineOpens := r.2.2.val
  let OverlapLabel := Σ r : PairLabel, Σ s : PairLabel, ↥(P (pOpen r) (pOpen s))
  let Triple (a b c : A) := Σ r : ↥(P (U a) (U b)),
    Σ s : ↥(P (U a) (U c)), Σ t : ↥(P (U b) (U c)), ↥(T r.val s.val t.val)
  let TripleLabel := Σ a : A, Σ b : A, Σ c : A, Triple a b c
  let L := A ⊕ (PairLabel ⊕ (OverlapLabel ⊕ TripleLabel))
  let V : L → X.affineOpens := Sum.elim U
    (Sum.elim pOpen (Sum.elim (fun r : OverlapLabel ↦ r.2.2.val)
      (fun t : TripleLabel ↦ t.2.2.2.2.2.2.val)))
  let e : Fin (Fintype.card L) ≃ L := (Fintype.equivFin L).symm
  let aLabel (a : A) := e.symm (.inl a)
  let pLabel (r : PairLabel) := e.symm (.inr (.inl r))
  let oLabel (r : OverlapLabel) := e.symm (.inr (.inr (.inl r)))
  let tLabel (t : TripleLabel) := e.symm (.inr (.inr (.inr t)))
  let C (d : Fin (Fintype.card L)) := (V (e d)).1
  let K : FiniteAffineRefinementShape :=
    { size := Fintype.card L
      main := Finset.univ.image aLabel
      pair := fun a b ↦ match e a, e b with
        | .inl a, .inl b => Finset.univ.image (fun r ↦ pLabel ⟨a, b, r⟩)
        | _, _ => ∅
      overlap := fun r s ↦ match e r, e s with
        | .inr (.inl r), .inr (.inl s) =>
          Finset.univ.image (fun t ↦ oLabel ⟨r, s, t⟩)
        | _, _ => ∅
      triple := fun a b c ↦ match e a, e b, e c with
        | .inl a, .inl b, .inl c =>
          Finset.univ.image (fun t : Triple a b c ↦ tLabel ⟨a, b, c, t⟩)
        | _, _, _ => ∅
      subordinate := fun _ _ _ d ↦ match e d with
        | .inr (.inr (.inr ⟨a, b, c, r, s, t, _⟩)) =>
          (pLabel ⟨a, b, r⟩, pLabel ⟨a, c, s⟩, pLabel ⟨b, c, t⟩)
        | _ => (d, d, d)
      incidence := ∅ }
  have hCA (a : A) : C (aLabel a) = (U a).1 := by simp [C, aLabel, V]
  have hCP (r : PairLabel) : C (pLabel r) = (pOpen r).1 := by simp [C, pLabel, V]
  have hCO (r : OverlapLabel) : C (oLabel r) = r.2.2.val.1 := by simp [C, oLabel, V]
  have hCT (t : TripleLabel) : C (tLabel t) = t.2.2.2.2.2.2.val.1 := by
    simp [C, tLabel, V]
  have hmain (d) : d ∈ K.main ↔ ∃ a, aLabel a = d := by simp [K]
  have hpair (a b : A) : K.pair (aLabel a) (aLabel b) =
      Finset.univ.image (fun r : ↥(P (U a) (U b)) ↦ pLabel ⟨a, b, r⟩) := by
    simp [K, aLabel]
  have hoverlap (r s : PairLabel) : K.overlap (pLabel r) (pLabel s) =
      Finset.univ.image (fun t : ↥(P (pOpen r) (pOpen s)) ↦ oLabel ⟨r, s, t⟩) := by
    simp [K, pLabel]
  have htriple (a b c : A) : K.triple (aLabel a) (aLabel b) (aLabel c) =
      Finset.univ.image (fun t : Triple a b c ↦ tLabel ⟨a, b, c, t⟩) := by
    simp [K, aLabel]
  have hsub (a b c : A) (t : Triple a b c) :
      K.subordinate (aLabel a) (aLabel b) (aLabel c) (tLabel ⟨a, b, c, t⟩) =
        (pLabel ⟨a, b, t.1⟩, pLabel ⟨a, c, t.2.1⟩, pLabel ⟨b, c, t.2.2.1⟩) := by
    rcases t with ⟨r, s, t, z⟩
    simp [K, tLabel]
  have hP' (V W : X.affineOpens) : (⨆ r : ↥(P V W), r.val.1) = V.1 ⊓ W.1 := by
    simpa only [iSup_subtype] using hP V W
  have hT' (V W Z : X.affineOpens) :
      (⨆ t : ↥(T V W Z), t.val.1) = V.1 ⊓ W.1 ⊓ Z.1 := by
    simpa only [iSup_subtype] using hT V W Z
  refine ⟨K, C, ?_⟩
  refine ⟨fun d ↦ (V (e d)).2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (⨆ d ∈ Finset.univ.image aLabel, C d) = ⊤
    simpa only [Finset.iSup_finset_image, Finset.mem_univ, iSup_true, hCA] using hU
  · intro a ha b hb
    obtain ⟨a, rfl⟩ := (hmain _).mp ha
    obtain ⟨b, rfl⟩ := (hmain _).mp hb
    rw [hpair, hCA, hCA]
    simpa only [Finset.iSup_finset_image, Finset.mem_univ, iSup_true, hCP, pOpen] using
      hP' (U a) (U b)
  · intro a ha b hb r hr s hs
    obtain ⟨a, rfl⟩ := (hmain _).mp ha
    obtain ⟨b, rfl⟩ := (hmain _).mp hb
    rw [hpair] at hr hs
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hs
    rw [hoverlap, hCP, hCP]
    simpa only [Finset.iSup_finset_image, Finset.mem_univ, iSup_true, hCO] using
      hP' (pOpen ⟨a, b, r⟩) (pOpen ⟨a, b, s⟩)
  · intro a ha b hb c hc
    obtain ⟨a, rfl⟩ := (hmain _).mp ha
    obtain ⟨b, rfl⟩ := (hmain _).mp hb
    obtain ⟨c, rfl⟩ := (hmain _).mp hc
    rw [htriple, hCA, hCA, hCA]
    simp only [Finset.iSup_finset_image, Finset.mem_univ, iSup_true, hCT]
    change (⨆ t : Triple a b c, t.2.2.2.val.1) = _
    simp only [Triple, iSup_sigma]
    simp_rw [hT']
    calc
      _ = ((⨆ r : ↥(P (U a) (U b)), r.val.1) ⊓
          (⨆ s : ↥(P (U a) (U c)), s.val.1)) ⊓
          (⨆ t : ↥(P (U b) (U c)), t.val.1) := by
        ext x
        change (x ∈ (⨆ r : ↥(P (U a) (U b)),
          ⨆ s : ↥(P (U a) (U c)), ⨆ t : ↥(P (U b) (U c)),
            r.val.1 ⊓ s.val.1 ⊓ t.val.1)) ↔
          x ∈ (((⨆ r : ↥(P (U a) (U b)), r.val.1) ⊓
            (⨆ s : ↥(P (U a) (U c)), s.val.1)) ⊓
            (⨆ t : ↥(P (U b) (U c)), t.val.1))
        simp only [Opens.mem_iSup, Opens.mem_inf]
        constructor
        · rintro ⟨r, s, t, ⟨hr, hs⟩, ht⟩
          exact ⟨⟨⟨r, hr⟩, ⟨s, hs⟩⟩, ⟨t, ht⟩⟩
        · rintro ⟨⟨⟨r, hr⟩, ⟨s, hs⟩⟩, ⟨t, ht⟩⟩
          exact ⟨r, s, t, ⟨hr, hs⟩, ht⟩
      _ = _ := by
        rw [hP', hP', hP']
        apply le_antisymm
        · exact le_inf
            (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left))
              (inf_le_right.trans inf_le_left))
            (inf_le_right.trans inf_le_right)
        · exact le_inf
            (le_inf inf_le_left (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
            (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  · intro a ha b hb c hc t ht
    obtain ⟨a, rfl⟩ := (hmain _).mp ha
    obtain ⟨b, rfl⟩ := (hmain _).mp hb
    obtain ⟨c, rfl⟩ := (hmain _).mp hc
    rw [htriple] at ht
    obtain ⟨⟨r, s, t, z⟩, _, rfl⟩ := Finset.mem_image.mp ht
    have hz : z.val.1 ≤ r.val.1 ⊓ s.val.1 ⊓ t.val.1 := by
      rw [← hT r.val s.val t.val]
      exact le_iSup_of_le z.val (le_iSup_of_le z.property le_rfl)
    rw [hsub]
    change pLabel ⟨a, b, r⟩ ∈ K.pair (aLabel a) (aLabel b) ∧
      pLabel ⟨a, c, s⟩ ∈ K.pair (aLabel a) (aLabel c) ∧
      pLabel ⟨b, c, t⟩ ∈ K.pair (aLabel b) (aLabel c) ∧ _
    rw [hpair, hpair, hpair, hCT, hCP, hCP, hCP]
    exact ⟨Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩,
      Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩,
      Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩,
      hz.trans (inf_le_left.trans inf_le_left),
      hz.trans (inf_le_left.trans inf_le_right), hz.trans inf_le_right⟩
  · simp only [K, Finset.notMem_empty, false_implies, implies_true]

private theorem finite_affine_cover_of_compact {X : Scheme.{u}} (U : X.Opens)
    (hU : IsCompact (U : Set X)) :
    ∃ s : Finset X.affineOpens, (⨆ V ∈ s, V.1) = U := by
  classical
  obtain ⟨s, hs, he⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hU
  exact ⟨hs.toFinset, by simpa only [Set.Finite.mem_toFinset] using he.symm⟩

/-- A quasi-compact quasi-separated scheme admits the finite collection of affine
charts, pair covers, pair-chart overlap covers and subordinate triple covers used
for Zariski gluing.

Source: Stacks Project, Schemes, Tags 01IT and 01KO; Limits, Tag 01ZR, first proof.
(blueprint: lem-trf-finite-affine-refinement-existence).

Proof: Choose a finite affine cover U_a of X. Each U_a is quasi-compact. By
quasi-separatedness, U_a intersect U_b is quasi-compact, so choose a finite affine
cover W_ab,r of that intersection. For every pair of members of each such cover,
their intersection is again quasi-compact; choose a finite affine cover of it.
For a triple a,b,c, the finitely many intersections W_ab,r intersect W_ac,s
intersect W_bc,t cover U_a intersect U_b intersect U_c: choose a pair chart
containing a given point in each of the three pair intersections. Each of these
threefold intersections is quasi-compact, so choose a finite affine cover of it.
Its members are subordinate to the three pair charts by construction. Combine
all these finite label sets by disjoint union and identify their union with
Fin n. The main, pair, overlap and triple finsets are the images of their
respective label sets, and the subordinate function records the three pair
labels. Set the additional incidence finset to empty. The covers just chosen
verify every Valid field. For an empty open use the empty cover, including when
X is empty. Repeated opens carry distinct labels, so no uniqueness of labels
or nonemptiness of an index set is required. -/
theorem exists_finiteAffineRefinementCollection (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ (K : FiniteAffineRefinementShape) (C : Fin K.size → X.Opens), K.Valid C := by
  classical
  have hinter (V W : X.affineOpens) : IsCompact (V.1 ⊓ W.1 : Set X) :=
    QuasiSeparatedSpace.inter_isCompact _ _ V.1.isOpen V.2.isCompact W.1.isOpen W.2.isCompact
  obtain ⟨s, hs⟩ := finite_affine_cover_of_compact (⊤ : X.Opens) isCompact_univ
  choose P hP using fun V W : X.affineOpens ↦
    finite_affine_cover_of_compact (V.1 ⊓ W.1) (hinter V W)
  choose T hT using fun V W Z : X.affineOpens ↦
    finite_affine_cover_of_compact (V.1 ⊓ W.1 ⊓ Z.1)
      (QuasiSeparatedSpace.inter_isCompact _ _ (V.1 ⊓ W.1).isOpen
        (hinter V W) Z.1.isOpen Z.2.isCompact)
  exact pack_finite_affine_refinements (fun a : s ↦ a.val)
    (by simpa only [iSup_subtype] using hs) P hP T hT

end AlgebraicGeometry
