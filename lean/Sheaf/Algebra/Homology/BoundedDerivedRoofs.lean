module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-!
# Bounded representatives and bounded roofs in the derived category

Source: Stacks Project, `derived.tex`, Tags 05RW and 05RT--05RV
(blueprint: lem-kun-bounded-derived-roofs).
-/

@[expose] public section

universe u v w

open CategoryTheory Category Limits

namespace DerivedCategory

/--
The right-fraction criterion in the homotopy category, specialized to complexes of
`R`-modules.  It supplies an unbounded common refinement of two equal derived roofs.
The conclusion records the quasi-isomorphism of each refinement map and of the common
denominator; the equalities are represented by chain homotopies.
Source: Stacks Project, `derived.tex`, Tags 05RT and 05RU; Mathlib's
`MorphismProperty.RightFraction.map_eq_iff`.
(blueprint: lem-kun-bounded-derived-roofs)
-/
private theorem unboundedCommonRefinement
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (K L M₁ M₂ : CochainComplex (ModuleCat.{v} R) ℤ)
    (s₁ : M₁ ⟶ K) (g₁ : M₁ ⟶ L)
    (s₂ : M₂ ⟶ K) (g₂ : M₂ ⟶ L)
    [hs₁ : QuasiIso s₁] [hs₂ : QuasiIso s₂]
    (h : inv (DerivedCategory.Q.map s₁) ≫ DerivedCategory.Q.map g₁ =
      inv (DerivedCategory.Q.map s₂) ≫ DerivedCategory.Q.map g₂) :
    ∃ (Z : CochainComplex (ModuleCat.{v} R) ℤ)
      (t₁ : Z ⟶ M₁) (t₂ : Z ⟶ M₂),
      QuasiIso t₁ ∧ QuasiIso t₂ ∧
      QuasiIso (t₁ ≫ s₁) ∧ QuasiIso (t₂ ≫ s₂) ∧
      Nonempty (Homotopy (t₁ ≫ s₁) (t₂ ≫ s₂)) ∧
      Nonempty (Homotopy (t₁ ≫ g₁) (t₂ ≫ g₂)) := by
  let q := HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)
  let W := HomotopyCategory.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ)
  have hqs₁ : W (q.map s₁) := (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr hs₁
  have hqs₂ : W (q.map s₂) := (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr hs₂
  let φ := MorphismProperty.RightFraction.mk (q.map s₁) hqs₁ (q.map g₁)
  let ψ := MorphismProperty.RightFraction.mk (q.map s₂) hqs₂ (q.map g₂)
  have heq : φ.map Qh (Localization.inverts Qh W) =
      ψ.map Qh (Localization.inverts Qh W) := by
    have : IsIso (Qh.map (q.map s₁)) := Localization.inverts Qh W _ hqs₁
    have : IsIso (Qh.map (q.map s₂)) := Localization.inverts Qh W _ hqs₂
    change inv (Qh.map (q.map s₁)) ≫ Qh.map (q.map g₁) =
      inv (Qh.map (q.map s₂)) ≫ Qh.map (q.map g₂)
    apply (cancel_mono ((quotientCompQhIso (ModuleCat.{v} R)).hom.app L)).mp
    simp only [Category.assoc]
    rw [quotientCompQhIso_hom_naturality g₁, quotientCompQhIso_hom_naturality g₂]
    have hn₁ := quotientCompQhIso_hom_naturality s₁
    have hn₂ := quotientCompQhIso_hom_naturality s₂
    have hi₁ : inv (Qh.map (q.map s₁)) ≫
        (quotientCompQhIso (ModuleCat.{v} R)).hom.app M₁ =
        (quotientCompQhIso (ModuleCat.{v} R)).hom.app K ≫ inv (Q.map s₁) := by
      apply (cancel_epi (Qh.map (q.map s₁))).mp
      rw [IsIso.hom_inv_id_assoc, ← Category.assoc, hn₁]
      simp
    have hi₂ : inv (Qh.map (q.map s₂)) ≫
        (quotientCompQhIso (ModuleCat.{v} R)).hom.app M₂ =
        (quotientCompQhIso (ModuleCat.{v} R)).hom.app K ≫ inv (Q.map s₂) := by
      apply (cancel_epi (Qh.map (q.map s₂))).mp
      rw [IsIso.hom_inv_id_assoc, ← Category.assoc, hn₂]
      simp
    rw [← Category.assoc, ← Category.assoc, hi₁, hi₂]
    simpa only [Category.assoc] using
      congrArg ((quotientCompQhIso (ModuleCat.{v} R)).hom.app K ≫ ·) h
  obtain ⟨Z, t₁, t₂, hst, hgt, ht⟩ :=
    (MorphismProperty.RightFraction.map_eq_iff Qh W φ ψ).mp heq
  obtain ⟨Z, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  obtain ⟨t₁, rfl⟩ := q.map_surjective t₁
  obtain ⟨t₂, rfl⟩ := q.map_surjective t₂
  have hst' : q.map (t₁ ≫ s₁) = q.map (t₂ ≫ s₂) := by
    simpa only [Functor.map_comp] using hst
  have hgt' : q.map (t₁ ≫ g₁) = q.map (t₂ ≫ g₂) := by
    simpa only [Functor.map_comp] using hgt
  have h₁ : QuasiIso (t₁ ≫ s₁) := by
    apply (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mp
    simpa only [Functor.map_comp] using ht
  have h₂ : QuasiIso (t₂ ≫ s₂) := by
    apply (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mp
    rw [← hst']
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr h₁
  have := h₁
  have := h₂
  exact ⟨Z, t₁, t₂, quasiIso_of_comp_right t₁ s₁,
    quasiIso_of_comp_right t₂ s₂, h₁, h₂,
    ⟨HomotopyCategory.homotopyOfEq _ _ hst'⟩,
    ⟨HomotopyCategory.homotopyOfEq _ _ hgt'⟩⟩

private theorem homotopy_descend_epi
    {R : Type u} [CommRing R]
    {T P K : CochainComplex (ModuleCat.{v} R) ℤ}
    (q : T ⟶ P) (a : ℤ) [K.IsStrictlyGE (a + 1)]
    (hepi : ∀ i, Epi (q.f i)) (hiso : ∀ i, a < i → IsIso (q.f i))
    {f g : P ⟶ K} (h : Homotopy (q ≫ f) (q ≫ g)) :
    Nonempty (Homotopy f g) := by
  classical
  let H (i j : ℤ) : P.X i ⟶ K.X j :=
    if hi : a < i then
      have := hiso i hi
      inv (q.f i) ≫ h.hom i j else 0
  have hH (i j : ℤ) : q.f i ≫ H i j = h.hom i j := by
    dsimp only [H]
    split_ifs with hi
    · have := hiso i hi
      simp
    · rw [comp_zero]
      by_cases hij : (ComplexShape.up ℤ).Rel j i
      · exact (K.isZero_of_isStrictlyGE (a + 1) j (by
          change j + 1 = i at hij
          lia)).eq_of_tgt _ _
      · exact (h.zero i j hij).symm
  refine ⟨{ hom := H, zero := ?_, comm := ?_ }⟩
  · intro i j hij
    have := hepi i
    apply (cancel_epi (q.f i)).mp
    rw [hH, comp_zero, h.zero i j hij]
  · intro i
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)]
    have := hepi i
    apply (cancel_epi (q.f i)).mp
    simp only [Preadditive.comp_add]
    rw [← Category.assoc (q.f i) (P.d i (i + 1)), q.comm i (i + 1),
      Category.assoc, hH, ← Category.assoc (q.f i) (H i (i - 1)), hH]
    simpa only [HomologicalComplex.comp_f,
      dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)] using h.comm i

private theorem isIso_πTruncGE_f_above
    {R : Type u} [CommRing R] (T : CochainComplex (ModuleCat.{v} R) ℤ)
    (a i : ℤ) (hi : a < i) : IsIso ((T.πTruncGE a).f i) := by
  let e := ComplexShape.embeddingUpIntGE a
  have hei : e.f (i - a).natAbs = i := by
    change a + ((i - a).natAbs : ℤ) = i
    rw [Int.natAbs_of_nonneg (by lia)]
    lia
  change IsIso ((HomologicalComplex.πTruncGE T e).f i)
  dsimp only [HomologicalComplex.πTruncGE]
  rw [e.isIso_liftExtend_f_iff _ _ hei]
  apply T.isIso_restrictionToTruncGE' e _
  rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
  intro h
  have : i - a = 0 := Int.natAbs_eq_zero.mp h
  lia

/--
A common refinement in the homotopy category can be made bounded by applying the
upper and lower canonical truncations to its source.  The maps from the original
source to the two bounded roofs are quasi-isomorphisms and preserve both homotopies.
Source: Stacks Project, `homology.tex`, Tag 0118, and `derived.tex`, Tag 05RV;
this is the explicit truncation construction in Steps 4--7 of the blueprint proof.
(blueprint: lem-kun-bounded-derived-roofs)
-/
private theorem boundedRefinementOfCommonRefinement
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (K L M₁ M₂ Z : CochainComplex (ModuleCat.{v} R) ℤ)
    (s₁ : M₁ ⟶ K) (g₁ : M₁ ⟶ L)
    (s₂ : M₂ ⟶ K) (g₂ : M₂ ⟶ L)
    (t₁ : Z ⟶ M₁) (t₂ : Z ⟶ M₂)
    [ht₁ : QuasiIso t₁] [ht₂ : QuasiIso t₂]
    (hK₀ : ∃ a b : ℤ, a ≤ b ∧ K.IsStrictlyGE a ∧ K.IsStrictlyLE b ∧
      L.IsStrictlyGE a ∧ L.IsStrictlyLE b ∧ M₁.IsStrictlyGE a ∧
      M₁.IsStrictlyLE b ∧ M₂.IsStrictlyGE a ∧ M₂.IsStrictlyLE b)
    (h₁ : Nonempty (Homotopy (t₁ ≫ s₁) (t₂ ≫ s₂)))
    (h₂ : Nonempty (Homotopy (t₁ ≫ g₁) (t₂ ≫ g₂))) :
    ∃ (P : CochainComplex (ModuleCat.{v} R) ℤ)
      (v₁ : P ⟶ M₁) (v₂ : P ⟶ M₂),
      (∃ c d : ℤ, c ≤ d ∧ P.IsStrictlyGE c ∧ P.IsStrictlyLE d) ∧
      QuasiIso v₁ ∧ QuasiIso v₂ ∧
      Nonempty (Homotopy (v₁ ≫ s₁) (v₂ ≫ s₂)) ∧
      Nonempty (Homotopy (v₁ ≫ g₁) (v₂ ≫ g₂)) := by
  classical
  obtain ⟨a, b, hab, hKa, hKb, hLa, hLb, hM₁a, hM₁b, hM₂a, hM₂b⟩ := hK₀
  have := hKa
  have := hLa
  have := hM₁a
  have := hM₁b
  have := hM₂a
  have : Z.IsLE b :=
    (HomologicalComplex.isSupported_iff_of_quasiIso t₁ _).mpr inferInstance
  let T := Z.truncLE b
  let j : T ⟶ Z := Z.ιTruncLE b
  have : QuasiIso j := inferInstanceAs (QuasiIso (Z.ιTruncLE b))
  have : T.IsGE a :=
    (HomologicalComplex.isSupported_iff_of_quasiIso (j ≫ t₁) _).mpr inferInstance
  let c := a - 1
  have : T.IsGE c := CochainComplex.isGE_of_ge T c a (by dsimp [c]; lia)
  have : M₁.IsStrictlyGE c := CochainComplex.isStrictlyGE_of_ge M₁ c a (by dsimp [c]; lia)
  have : M₂.IsStrictlyGE c := CochainComplex.isStrictlyGE_of_ge M₂ c a (by dsimp [c]; lia)
  have : K.IsStrictlyGE (c + 1) := by simpa [c] using hKa
  have : L.IsStrictlyGE (c + 1) := by simpa [c] using hLa
  let P := T.truncGE c
  let q : T ⟶ P := T.πTruncGE c
  have : QuasiIso q := inferInstanceAs (QuasiIso (T.πTruncGE c))
  let v₁ : P ⟶ M₁ := CochainComplex.truncGEMap (j ≫ t₁) c ≫ inv (M₁.πTruncGE c)
  let v₂ : P ⟶ M₂ := CochainComplex.truncGEMap (j ≫ t₂) c ≫ inv (M₂.πTruncGE c)
  have hv₁ : q ≫ v₁ = j ≫ t₁ := by simp [q, v₁]
  have hv₂ : q ≫ v₂ = j ≫ t₂ := by simp [q, v₂]
  have : QuasiIso (q ≫ v₁) := by rw [hv₁]; infer_instance
  have : QuasiIso (q ≫ v₂) := by rw [hv₂]; infer_instance
  have hq (i : ℤ) : Epi (q.f i) := by
    change Epi ((HomologicalComplex.πTruncGE T (ComplexShape.embeddingUpIntGE c)).f i)
    infer_instance
  have hi (i : ℤ) (hci : c < i) : IsIso (q.f i) := isIso_πTruncGE_f_above T c i hci
  obtain ⟨H₁⟩ := h₁
  obtain ⟨H₂⟩ := h₂
  have H₁' : Homotopy (q ≫ (v₁ ≫ s₁)) (q ≫ (v₂ ≫ s₂)) := by
    simpa only [← Category.assoc, hv₁, hv₂] using H₁.compLeft j
  have H₂' : Homotopy (q ≫ (v₁ ≫ g₁)) (q ≫ (v₂ ≫ g₂)) := by
    simpa only [← Category.assoc, hv₁, hv₂] using H₂.compLeft j
  exact ⟨P, v₁, v₂, ⟨c, b, by dsimp [c]; lia, inferInstance, inferInstance⟩,
    quasiIso_of_comp_left q v₁, quasiIso_of_comp_left q v₂,
    homotopy_descend_epi q c hq hi H₁', homotopy_descend_epi q c hq hi H₂'⟩


set_option linter.unusedVariables false in
/--
(blueprint: lem-kun-bounded-derived-roofs)
Source: Stacks Project, `derived.tex`, Tags 05RT, 05RU, 05RV, 05RW and `homology.tex`
Tag 0118 (section-truncations).

Let `R` be a commutative ring and let `D^b(R)` be the bounded derived category of
`R`-modules.  The localization `Q` factors through the homotopy category `K(R)`; every
`C ∈ D^b(R)` has a cochain representative `K` supported in some `[a, b]`, `a ≤ b`; every
`u : C ⟶ C'` between bounded representatives is a bounded roof `K ← M → L` with `M ⟶ K`
a quasi-isomorphism, after transport along the chosen isomorphisms; two such roofs with
the same derived morphism have a bounded common refinement `P` by quasi-isomorphisms
`vᵢ : P ⟶ Mᵢ` with `v₁ ≫ s₁ ≃ v₂ ≫ s₂` and `v₁ ≫ g₁ ≃ v₂ ≫ g₂` chain homotopic.  The
equivalence of roofs is taken in `K(R)`; strict chain-map refinements need not exist.

Proof (the node's steps).
1. (def-weil-pbc-bounded-derived-subcategories, lem-sfb-bounded-representative;
   Tags 05RW, 05RV) `C ∈ D^b(R)` has cohomology zero below some `a` and above some `b`;
   enlarge to `a ≤ b`.  A bounded representative `K` supported in `[a, b]` with
   `C ≅ Q(K)` exists (`DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`); zero objects
   allow any interval.  Likewise for `C'`.
2. (lem-kun-derived-bounded-roof-factorization, def-weil-abstract-derived-category;
   Tag 05RW) For representatives `K, L` with `K` in `[a, b]` and `L` zero below `a`,
   transport `u` to `f : Q(K) ⟶ Q(L)`.  The bounded right factorization
   (`DerivedCategory.right_fac_of_isStrictlyLE_of_isStrictlyGE`) gives `M` in `[a, b]`,
   `s : M ⟶ K`, `g : M ⟶ L` with `f = Q(s)⁻¹ ≫ Q(g)`.  `Q(s)` invertible makes every
   `Hⁿ(s)` invertible since `Hⁿ` factors through `Q`, so `s` is a quasi-isomorphism.
3. (lem-pc-quasi-isomorphisms-multiplicative-system,
   lem-pc-right-fraction-common-refinement; Tags 05RT, 05RU) If two roofs give the same
   morphism, work in `K(R)`: quasi-isomorphisms there have a right calculus of fractions
   with localization `D(R)`, and the right-fraction criterion gives `Z` and chain maps
   `tᵢ : Z ⟶ Mᵢ` with `s₁t₁ = s₂t₂` and `g₁t₁ = g₂t₂` in `K(R)` (chain homotopies) and
   the common denominator `s₁t₁` a quasi-isomorphism.  No calculus of fractions in
   `CoCh(R)` is asserted.
4. (def-weil-abstract-derived-category; elementary) Each `tᵢ` is a quasi-isomorphism:
   `Hⁿ(tᵢ) = Hⁿ(sᵢ)⁻¹ Hⁿ(sᵢtᵢ)`.  Choose `a < b` with `M₁, M₂, K, L` vanishing outside
   `[a, b]`; then `Hⁿ(Z) = 0` outside `[a, b]`.
5. (def-kun-truncations; homology Tag 0118) Put `T = τ_{≤b} Z`, `P = τ_{≥a} T`, with
   canonical `j : T ⟶ Z` and `q : T ⟶ P`.  By the cohomology of the truncations and
   Step 4, `j` and `q` are quasi-isomorphisms, and `P` is supported in `[a, b]`.
6. (def-kun-truncations; elementary) `rᵢ = tᵢ ∘ j` factors as `vᵢ ∘ q`: above `a` use
   `rᵢⁿ`, below `a` zero, in degree `a` the map from `Tᵃ / im d_T^{a-1}` induced by `rᵢᵃ`
   (it exists as `Mᵢ^{a-1} = 0`).  `Hⁿ(vᵢ) = Hⁿ(rᵢ) Hⁿ(q)⁻¹`, so `vᵢ` is a
   quasi-isomorphism.
7. (def-kun-truncations; elementary) Restrict the homotopy between `s₁t₁` and `s₂t₂`
   along `j` (at degree `b`, `d_Z^b` vanishes on `Tᵇ = ker d_Z^b`), and descend it along
   `q` (its degree-`a` component has target `K^{a-1} = 0`; the equation in degree `a`
   follows by precomposing with the surjection `qᵃ`).  This gives `s₁v₁ ≃ s₂v₂`; the same
   construction with target `L` gives `g₁v₁ ≃ g₂v₂`.  Homotopic maps have the same class
   in `K(R)`, so localization gives the same fraction; for other representative
   isomorphisms transport the endpoints as in Step 2.
-/
theorem boundedDerivedRoofs
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)] :
    (Nonempty
        ((HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh) ≅ DerivedCategory.Q)) ∧
      (∀ (C : DerivedCategory.Bounded (ModuleCat.{v} R)),
        ∃ (a b : ℤ) (K : CochainComplex (ModuleCat.{v} R) ℤ),
          a ≤ b ∧ K.IsStrictlyGE a ∧ K.IsStrictlyLE b ∧
            Nonempty (C.1 ≅ DerivedCategory.Q.obj K)) ∧
      (∀ (C C' : DerivedCategory (ModuleCat.{v} R))
          (a b : ℤ) (K L : CochainComplex (ModuleCat.{v} R) ℤ),
        K.IsStrictlyGE a → K.IsStrictlyLE b →
        L.IsStrictlyGE a → L.IsStrictlyLE b →
        a ≤ b →
        ∀ (eC : C ≅ DerivedCategory.Q.obj K)
          (eC' : C' ≅ DerivedCategory.Q.obj L) (u : C ⟶ C'),
          ∃ (M : CochainComplex (ModuleCat.{v} R) ℤ)
            (_ : M.IsStrictlyGE a) (_ : M.IsStrictlyLE b)
            (s : M ⟶ K) (_ : QuasiIso s)
            (g : M ⟶ L),
            u = eC.hom ≫ inv (DerivedCategory.Q.map s) ≫
              DerivedCategory.Q.map g ≫ eC'.inv) ∧
      (∀ (K L M₁ M₂ : CochainComplex (ModuleCat.{v} R) ℤ)
          (s₁ : M₁ ⟶ K) (g₁ : M₁ ⟶ L)
          (s₂ : M₂ ⟶ K) (g₂ : M₂ ⟶ L)
          [hs₁ : QuasiIso s₁]
          [hs₂ : QuasiIso s₂],
        (∃ (a b : ℤ),
          a ≤ b ∧ K.IsStrictlyGE a ∧ K.IsStrictlyLE b ∧
            L.IsStrictlyGE a ∧ L.IsStrictlyLE b ∧
            M₁.IsStrictlyGE a ∧ M₁.IsStrictlyLE b ∧
            M₂.IsStrictlyGE a ∧ M₂.IsStrictlyLE b) →
        inv (DerivedCategory.Q.map s₁) ≫ DerivedCategory.Q.map g₁ =
          inv (DerivedCategory.Q.map s₂) ≫ DerivedCategory.Q.map g₂ →
        ∃ (P : CochainComplex (ModuleCat.{v} R) ℤ)
          (v₁ : P ⟶ M₁) (v₂ : P ⟶ M₂),
          (∃ (c d : ℤ), c ≤ d ∧ P.IsStrictlyGE c ∧ P.IsStrictlyLE d) ∧
          QuasiIso v₁ ∧
          QuasiIso v₂ ∧
          Nonempty (Homotopy (v₁ ≫ s₁) (v₂ ≫ s₂)) ∧
          Nonempty (Homotopy (v₁ ≫ g₁) (v₂ ≫ g₂))) := by
  classical
  refine ⟨⟨quotientCompQhIso _⟩, ?_, ?_, ?_⟩
  · intro C
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := C.2
    have : C.1.IsGE a := ha
    have : C.1.IsLE (max a b) := TStructure.t.isLE_of_le C.1 b (max a b) (le_max_right _ _)
    obtain ⟨K, hK, hK', e⟩ := exists_iso_Q_obj_of_isGE_of_isLE C.1 a (max a b)
    exact ⟨a, max a b, K, le_max_left _ _, hK, hK', e⟩
  · intro C C' a b K L hKa hKb hLa _ _ eC eC' u
    have := hKa
    have := hKb
    have := hLa
    obtain ⟨M, hMa, hMb, s, hs, g, hg⟩ :=
      right_fac_of_isStrictlyLE_of_isStrictlyGE a b (eC.inv ≫ u ≫ eC'.hom)
    have hsq : QuasiIso s := (isIso_Q_map_iff_quasiIso (ModuleCat R) s).mp hs
    refine ⟨M, hMa, hMb, s, hsq, g, ?_⟩
    rw [← cancel_mono eC'.hom]
    rw [← cancel_epi eC.inv]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
      Iso.inv_hom_id, comp_id] using hg
  · intro K L M₁ M₂ s₁ g₁ s₂ g₂ hs₁ hs₂ hb he
    have := hs₁
    have := hs₂
    obtain ⟨Z, t₁, t₂, ht₁, ht₂, _, _, h₁, h₂⟩ :=
      unboundedCommonRefinement R K L M₁ M₂ s₁ g₁ s₂ g₂ he
    have := ht₁
    have := ht₂
    obtain ⟨P, v₁, v₂, hP, hv₁, hv₂, hvst, hvg⟩ :=
      boundedRefinementOfCommonRefinement R K L M₁ M₂ Z s₁ g₁ s₂ g₂ t₁ t₂ hb h₁ h₂
    exact ⟨P, v₁, v₂, hP, hv₁, hv₂, hvst, hvg⟩

end DerivedCategory
