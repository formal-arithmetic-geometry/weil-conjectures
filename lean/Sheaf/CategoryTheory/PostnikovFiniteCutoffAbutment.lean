module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
public import WeilConjectures.CategoryTheory.CanonicalFiltration
import WeilConjectures.CategoryTheory.HalfPlaneConvergence
import WeilConjectures.CategoryTheory.DerivedCoupleFunctoriality

/-! # Shifted Postnikov cutoff and actual abutment

Source: Stacks Project, derived.tex, Tag 08J5, and homology.tex, Tags 011T and 012U;
blueprint half-plane convergence, proof paragraphs 1--2.
(blueprint: lem-per-postnikov-finite-cutoff-abutment).

The couple is expressed in translated coordinates `(P,Q)=(p+r,q)`. Its layer is
`tau_{>=q} tau_{<=q} L`, the canonical realization of `H^q(L)[-q]`. The isomorphisms
`d` and `e` only change representatives; all three maps are prescribed below.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w uB vB

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type uB} [Category.{vB} B] [Abelian B]

/-- The shifted value `T^n`, with the tautological coherent shifts.
Source: Stacks Tag 0147 (blueprint: lem-per-postnikov-finite-cutoff-abutment). -/
abbrev postnikovValue (T : DerivedCategory A ⥤ B) (n : ℤ) : DerivedCategory A ⥤ B :=
  shiftFunctor (DerivedCategory A) n ⋙ T

/-- The translated D-term as a functor of the original object.
Source: Stacks Tag 08J5 (blueprint: lem-per-postnikov-finite-cutoff-abutment). -/
abbrev postnikovD (T : DerivedCategory A ⥤ B) (r P Q : ℤ) : DerivedCategory A ⥤ B :=
  TStructure.t.truncLE Q ⋙ postnikovValue T (P + Q - r)

/-- The translated E-term, using the canonical single-degree truncation layer.
This is `T^(P+Q-r)(H^Q(-)[-Q])` in its canonical truncation representative.
Source: Stacks Tag 08J5 (blueprint: lem-per-postnikov-finite-cutoff-abutment). -/
abbrev postnikovE (T : DerivedCategory A ⥤ B) (r P Q : ℤ) : DerivedCategory A ⥤ B :=
  TStructure.t.truncGELT Q (Q + 1) ⋙ postnikovValue T (P + Q - r)

/-- The next truncation inclusion, with the equality of total degrees inserted.
Source: Stacks Tag 08J5 (blueprint: lem-per-postnikov-finite-cutoff-abutment). -/
def postnikovAlpha (T : DerivedCategory A ⥤ B) (r P Q : ℤ) (L : DerivedCategory A) :
    (postnikovD T r P Q).obj L ⟶ (postnikovD T r (P - 1) (Q + 1)).obj L :=
  (postnikovValue T (P + Q - r)).map
    ((TStructure.t.natTransTruncLEOfLE Q (Q + 1) (by omega)).app L) ≫
      eqToHom (congrArg (fun n : ℤ ↦
        (postnikovValue T n).obj ((TStructure.t.truncLE (Q + 1)).obj L)) (by omega))

/-- The canonical quotient onto the single-degree truncation layer.
Source: Stacks Tag 08J5 (blueprint: lem-per-postnikov-finite-cutoff-abutment). -/
def postnikovG (T : DerivedCategory A ⥤ B) (r P Q : ℤ) (L : DerivedCategory A) :
    (postnikovD T r P Q).obj L ⟶ (postnikovE T r P Q).obj L :=
  (postnikovValue T (P + Q - r)).map
    (((TStructure.t.triangleLTLTGELT Q (Q + 1) (by omega)).obj L).mor₂)

/-- The boundary of the successive truncation triangle, with the canonical shift
comparison `[1][P+Q-r] = [(P+2)+(Q-1)-r]`.
Source: Stacks Tags 08J5 and 0147 (blueprint: lem-per-postnikov-finite-cutoff-abutment). -/
def postnikovF (T : DerivedCategory A ⥤ B) (r P Q : ℤ) (L : DerivedCategory A) :
    (postnikovE T r P Q).obj L ⟶ (postnikovD T r (P + 2) (Q - 1)).obj L :=
  T.map ((((TStructure.t.triangleLTLTGELT Q (Q + 1) (by omega)).obj L).mor₃)⟦P + Q - r⟧' ≫
    (shiftFunctorAdd' (DerivedCategory A) 1 (P + Q - r)
      ((P + 2) + (Q - 1) - r) (by omega)).inv.app
        ((TStructure.t.truncLT Q).obj L)) ≫
      eqToHom (congrArg (fun m : ℤ ↦
        (postnikovValue T ((P + 2) + (Q - 1) - r)).obj
          ((TStructure.t.truncLT m).obj L)) (by omega))

/-- The canonical map from a cutoff to the actual value, in any degree.
Source: Stacks Tag 08J5 (blueprint: lem-per-postnikov-finite-cutoff-abutment). -/
def postnikovCutoffMap (T : DerivedCategory A ⥤ B) (n m : ℤ) (L : DerivedCategory A) :
    (postnikovValue T n).obj ((TStructure.t.truncLE m).obj L) ⟶
      (postnikovValue T n).obj L :=
  (postnikovValue T n).map ((TStructure.t.truncLEι m).app L)

/-- The full category of objects with the given lower cohomological bound.
Source: standard t-structure, Stacks Tag 08J5
(blueprint: lem-per-postnikov-finite-cutoff-abutment). -/
abbrev postnikovLowerCategory (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (c : ℤ) :=
  ObjectProperty.FullSubcategory (fun L : DerivedCategory A ↦ L.IsGE c)

set_option backward.isDefEq.respectTransparency false in
private theorem cutoff_iso (T : DerivedCategory A ⥤ B) [T.IsHomological] (r : ℤ)
    (hamp : ∀ (b n : ℤ) (M : DerivedCategory A), M.IsGE b → n < b - r →
      IsZero ((postnikovValue T n).obj M))
    (n m : ℤ) (L : DerivedCategory A) (h : n + r ≤ m) :
    IsIso (postnikovCutoffMap T n m L) := by
  let := Functor.ShiftSequence.tautological T ℤ
  let Δ := (TStructure.t.triangleLEGE m (m + 1) rfl).obj L
  have hΔ := TStructure.t.triangleLEGE_distinguished m (m + 1) rfl L
  have hz (i : ℤ) (hi : i ≤ n) : IsZero ((T.shift i).obj Δ.obj₃) :=
    hamp (m + 1) i _ (by
      change TStructure.t.IsGE ((TStructure.t.truncGE (m + 1)).obj L) (m + 1)
      infer_instance) (by omega)
  have hm : Mono ((T.shift n).map Δ.mor₁) :=
    (T.homologySequence_mono_shift_map_mor₁_iff Δ hΔ (n - 1) n (by omega)).2
      ((hz (n - 1) (by omega)).eq_zero_of_src _)
  have he : Epi ((T.shift n).map Δ.mor₁) :=
    (T.homologySequence_epi_shift_map_mor₁_iff Δ hΔ n).2
      ((hz n le_rfl).eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi ((T.shift n).map Δ.mor₁)

set_option backward.isDefEq.respectTransparency false in
private theorem cutoff_naturality {B : Type uB} [Category.{vB} B]
    (T : DerivedCategory A ⥤ B)
    {L M : DerivedCategory A} (u : L ⟶ M) (n m : ℤ) :
    (postnikovValue T n).map ((TStructure.t.truncLE m).map u) ≫
        postnikovCutoffMap T n m M =
      postnikovCutoffMap T n m L ≫ (postnikovValue T n).map u := by
  simp only [postnikovCutoffMap, ← Functor.map_comp]
  exact congrArg ((postnikovValue T n).map) ((TStructure.t.truncLEι m).naturality u)

set_option backward.isDefEq.respectTransparency false in
private theorem trunc_zero (L : DerivedCategory A) (c q : ℤ)
    (hL : L.IsGE c) (hq : q < c) : IsZero ((TStructure.t.truncLE q).obj L) := by
  let := hL
  have : L.IsGE (q + 1) := TStructure.t.isGE_of_ge L (q + 1) c (by omega)
  exact TStructure.t.isZero_truncLE_obj_of_isGE q (q + 1) rfl L

set_option backward.isDefEq.respectTransparency false in
private theorem initial_zero (T : DerivedCategory A ⥤ B) [T.IsHomological] (r c : ℤ)
    (hamp : ∀ (b n : ℤ) (M : DerivedCategory A), M.IsGE b → n < b - r →
      IsZero ((postnikovValue T n).obj M))
    (L : DerivedCategory A) (hL : L.IsGE c) (P Q : ℤ) (h : P < 0 ∨ Q < c) :
    IsZero ((postnikovE T r P Q).obj L) := by
  rcases h with h | h
  · exact hamp Q (P + Q - r) _ (by infer_instance) (by omega)
  · apply (postnikovValue T (P + Q - r)).map_isZero
    change IsZero ((TStructure.t.truncGE Q).obj ((TStructure.t.truncLT (Q + 1)).obj L))
    exact (TStructure.t.truncGE Q).map_isZero (trunc_zero L c Q hL h)

set_option backward.isDefEq.respectTransparency false in
private theorem alpha_cutoff {B : Type uB} [Category.{vB} B]
    (T : DerivedCategory A ⥤ B) (r P Q : ℤ)
    (L : DerivedCategory A) :
    postnikovAlpha T r P Q L ≫
        postnikovCutoffMap T ((P - 1) + (Q + 1) - r) (Q + 1) L =
      postnikovCutoffMap T (P + Q - r) Q L ≫
        eqToHom (congrArg (fun n : ℤ ↦ (postnikovValue T n).obj L) (by omega)) := by
  dsimp only [postnikovAlpha]
  rw [Category.assoc,
    ← eqToHom_naturality (fun n : ℤ ↦ postnikovCutoffMap T n (Q + 1) L)
      (show P + Q - r = (P - 1) + (Q + 1) - r by omega),
    ← Category.assoc]
  congr 1
  simp only [postnikovCutoffMap, ← Functor.map_comp]
  rw [TStructure.t.natTransTruncLEOfLE_ι_app]

set_option backward.isDefEq.respectTransparency false in
private theorem diagonal_cocone (T : DerivedCategory A ⥤ B) (r N : ℤ)
    (L : DerivedCategory A) (X : CategoryTheory.BigradedExactCouple B 0)
    (d : ∀ P Q : ℤ, X.D P Q ≅ (postnikovD T r P Q).obj L)
    (ha : ∀ P Q : ℤ, X.alpha P Q ≫ (d (P - 1) (Q + 1)).hom =
      (d P Q).hom ≫ postnikovAlpha T r P Q L) (P : ℤ) :
    X.alphaDiagonal N P ≫ ((d P (N - P)).hom ≫
        eqToHom (congrArg (fun n : ℤ ↦
          (postnikovValue T n).obj ((TStructure.t.truncLE (N - P)).obj L))
            (show P + (N - P) - r = N - r by omega)) ≫
        postnikovCutoffMap T (N - r) (N - P) L) =
      (d (P + 1) (N - (P + 1))).hom ≫
        eqToHom (congrArg (fun n : ℤ ↦
          (postnikovValue T n).obj ((TStructure.t.truncLE (N - (P + 1))).obj L))
            (by omega)) ≫ postnikovCutoffMap T (N - r) (N - (P + 1)) L := by
  dsimp only [CategoryTheory.BigradedExactCouple.alphaDiagonal]
  rw [Category.assoc, ← Category.assoc (eqToHom _),
    ← eqToHom_naturality (fun pq : ℤ × ℤ ↦ (d pq.1 pq.2).hom)
      (show (P + 1 - 1, N - (P + 1) + 1) = (P, N - P) by ext <;> omega)]
  simp only [Category.assoc, eqToHom_trans_assoc]
  rw [← Category.assoc (X.alpha _ _), ha, Category.assoc]
  rw [← eqToHom_naturality
    (fun nm : ℤ × ℤ ↦ postnikovCutoffMap T nm.1 nm.2 L)
    (show ((P + 1 - 1) + (N - (P + 1) + 1) - r, N - (P + 1) + 1) =
      (N - r, N - P) by ext <;> omega)]
  rw [← Category.assoc (postnikovAlpha _ _ _ _ _), alpha_cutoff]
  simp only [Category.assoc, eqToHom_trans]
  rw [eqToHom_naturality (fun n : ℤ ↦
    postnikovCutoffMap T n (N - (P + 1)) L)
      (show (P + 1) + (N - (P + 1)) - r = N - r by omega)]

set_option backward.isDefEq.respectTransparency false in
private theorem all_page_zero (X : CategoryTheory.BigradedExactCouple B 0) (c : ℤ)
    (hE : ∀ p q : ℤ, p < 0 ∨ q < c → IsZero (X.E p q))
    (s : ℕ) (p q : ℤ) (h : p < 0 ∨ q < c) : IsZero ((X.pageCouple s).E p q) := by
  induction s with
  | zero => exact hE p q h
  | succ s ih =>
    have : Epi ((X.pageCouple s).derivedEProjection p q) := by
      dsimp [CategoryTheory.BigradedExactCouple.derivedEProjection]
      infer_instance
    exact IsZero.of_epi ((X.pageCouple s).derivedEProjection p q)
      (IsZero.of_mono (kernel.ι ((X.pageCouple s).d p q)) ih)

set_option backward.isDefEq.respectTransparency false in
private theorem transport_graded {U V : B} (G : PBCDecreasingFiltration U)
    (F : DecreasingFiltration V) (b : U ≅ V) (P p : ℤ)
    (h : ∀ i j : ℤ, i - P = j - p →
      Subobject.mk ((G.step i).arrow ≫ b.hom) = F.F j) :
    ∃ (v : G.gradedPiece P ≅ F.gradedPiece p)
      (s : (G.step P : B) ≅ (F.F p : B)),
      s.hom ≫ (F.F p).arrow = (G.step P).arrow ≫ b.hom ∧
      cokernel.π (Subobject.ofLE _ _ (G.antitone_step (show P ≤ P + 1 by omega))) ≫
          v.hom = s.hom ≫ cokernel.π (Subobject.ofLE _ _ (F.F_succ_le p)) := by
  let s (i j : ℤ) (hh : i - P = j - p) :=
    Subobject.isoOfMkEq ((G.step i).arrow ≫ b.hom) (F.F j) (h i j hh)
  have hs (i j : ℤ) (hh : i - P = j - p) :
      (s i j hh).hom ≫ (F.F j).arrow = (G.step i).arrow ≫ b.hom := by
    simp [s]
  have hc : Subobject.ofLE _ _ (G.antitone_step (show P ≤ P + 1 by omega)) ≫
        (s P p (by omega)).hom =
      (s (P + 1) (p + 1) (by omega)).hom ≫ Subobject.ofLE _ _ (F.F_succ_le p) := by
    apply (cancel_mono (F.F p).arrow).1
    simp only [Category.assoc, hs, Subobject.ofLE_arrow_assoc, Subobject.ofLE_arrow]
  refine ⟨cokernel.mapIso _ _ (s (P + 1) (p + 1) (by omega))
    (s P p (by omega)) hc, s P p (by omega), hs P p (by omega), ?_⟩
  simp only [cokernel.mapIso_hom, cokernel.map, cokernel.π_desc]

set_option backward.isDefEq.respectTransparency false in
private theorem quotient_iso {U V W : B} (k : U ⟶ V) [Mono k]
    (f : V ⟶ W) [Epi f] (hk : kernelSubobject f = Subobject.mk k) :
    ∃ e : W ≅ cokernel k, f ≫ e.hom = cokernel.π k := by
  have hz : k ≫ f = 0 := by
    apply (kernelSubobject_factors_iff f k).mp
    rw [hk]
    exact Subobject.mk_factors_self k
  have hw : kernel.ι f ≫ cokernel.π k = 0 := by
    have hfac : (Subobject.mk k).Factors (kernel.ι f) := by
      rw [← hk]
      exact kernelSubobject_factors f _ (kernel.condition f)
    obtain ⟨t, ht⟩ := (Subobject.mk_factors_iff k _).mp hfac
    change t ≫ k = kernel.ι f at ht
    rw [← ht, Category.assoc, cokernel.condition, comp_zero]
  refine ⟨{ hom := Abelian.epiDesc f (cokernel.π k) hw
            inv := cokernel.desc k f hz
            hom_inv_id := ?_
            inv_hom_id := ?_ }, Abelian.comp_epiDesc f _ hw⟩
  · apply (cancel_epi f).1
    simp
  · apply (cancel_epi (cokernel.π k)).1
    simp

set_option backward.isDefEq.respectTransparency false in
private theorem stable_comparison (X : BigradedExactCouple B 0) (c : ℤ)
    (hE : ∀ p q : ℤ, p < 0 ∨ q < c → IsZero (X.E p q))
    (L : X.LimitSubobjects) (s : ℕ) (p q : ℤ)
    (hs : (s : ℤ) + 2 > max (q - c + 1) p) :
    ∃ z : (L.Z p q : B) ⟶ (X.cycleBoundaryTower.Z s p q : B),
    ∃ v : (X.pageCouple s).E p q ≅ X.pageInfinity L p q,
      z ≫ (X.cycleBoundaryTower.Z s p q).arrow = (L.Z p q).arrow ∧
      z ≫ X.cycleBoundaryTower.projection s p q ≫ v.hom =
        cokernel.π (Subobject.ofLE _ _ (X.limitBoundary_le_cycle L p q)) := by
  let T := X.cycleBoundaryTower
  have hstep (t : ℕ) (ht : s ≤ t) :
      T.Z (t + 1) p q = T.Z t p q ∧ T.B (t + 1) p q = T.B t p q := by
    have ho : (X.pageCouple t).d p q = 0 :=
      (all_page_zero X c hE t _ _ (Or.inr (by omega))).eq_zero_of_tgt _
    have hi : (X.pageCouple t).dInto p q = 0 :=
      (all_page_zero X c hE t _ _ (Or.inl (by omega))).eq_zero_of_src _
    have hker : (Subobject.pullback (T.projection t p q)).obj ⊥ =
        kernelSubobject (T.projection t p q) := by
      apply le_antisymm
      · apply Subobject.le_of_factors
        apply kernelSubobject_factors
        have hw := (Subobject.isPullback (T.projection t p q) (⊥ : Subobject _)).w
        simpa using hw.symm
      · apply Subobject.le_of_factors
        apply pullback_factors
        rw [kernelSubobject_arrow_comp]
        exact Subobject.factors_zero
    constructor
    · rw [T.Z_succ, ho, kernelSubobject_zero, Subobject.pullback_top,
        Subobject.exists_iso_map, Subobject.map_top, Subobject.mk_arrow]
    · rw [T.B_succ, hi, imageSubobject_zero, hker, T.projection_kernel,
        Subobject.exists_iso_map, Subobject.map_mk]
      simp only [Subobject.ofLE_arrow, Subobject.mk_arrow]
  have htail (t : ℕ) (ht : s ≤ t) : T.Z t p q = T.Z s p q ∧ T.B t p q = T.B s p q := by
    induction t, ht using Nat.le_induction with
    | base => exact ⟨rfl, rfl⟩
    | succ t ht ih => exact ⟨(hstep t ht).1.trans ih.1, (hstep t ht).2.trans ih.2⟩
  have hZ : L.Z p q = T.Z s p q := by
    apply le_antisymm ((L.Z_glb p q).1 ⟨s, rfl⟩)
    apply (L.Z_glb p q).2
    rintro _ ⟨t, rfl⟩
    by_cases ht : s ≤ t
    · exact le_of_eq (htail t ht).1.symm
    · exact antitone_nat_of_succ_le (f := fun t ↦ T.Z t p q)
        (fun t ↦ T.Z_decreasing t p q) (by omega)
  have hB : L.B p q = T.B s p q := by
    apply le_antisymm
    · apply (L.B_lub p q).2
      rintro _ ⟨t, rfl⟩
      by_cases ht : s ≤ t
      · exact le_of_eq (htail t ht).2
      · exact monotone_nat_of_le_succ (f := fun t ↦ T.B t p q)
          (fun t ↦ T.B_increasing t p q) (by omega)
    · exact (L.B_lub p q).1 ⟨s, rfl⟩
  have := T.projection_epi s p q
  obtain ⟨e, he⟩ := quotient_iso (Subobject.ofLE _ _ (T.B_le_Z s p q))
    (T.projection s p q) (T.projection_kernel s p q)
  let j : cokernel (Subobject.ofLE _ _ (T.B_le_Z s p q)) ≅ X.pageInfinity L p q :=
    cokernel.mapIso _ _ (eqToIso (congrArg Subobject.underlying.obj hB.symm))
      (eqToIso (congrArg Subobject.underlying.obj hZ.symm)) (by
        apply (cancel_mono (L.Z p q).arrow).1
        simp only [eqToIso.hom, Category.assoc]
        rw [Subobject.arrow_congr _ _ hZ.symm]
        simp only [Subobject.ofLE_arrow]
        exact (Subobject.arrow_congr _ _ hB.symm).symm)
  refine ⟨eqToHom (congrArg Subobject.underlying.obj hZ), e ≪≫ j, ?_, ?_⟩
  · exact Subobject.arrow_congr _ _ hZ
  · have hjπ : cokernel.π (Subobject.ofLE _ _ (T.B_le_Z s p q)) ≫ j.hom =
        eqToHom (congrArg Subobject.underlying.obj hZ.symm) ≫
          cokernel.π (Subobject.ofLE _ _ (X.limitBoundary_le_cycle L p q)) := by
      exact cokernel.π_desc _ _ _
    change eqToHom (congrArg Subobject.underlying.obj hZ) ≫
      T.projection s p q ≫ e.hom ≫ j.hom = _
    rw [← Category.assoc (T.projection s p q), he, hjπ]
    simp

set_option backward.isDefEq.respectTransparency false in
private theorem alpha_naturality {B : Type uB} [Category.{vB} B]
    (T : DerivedCategory A ⥤ B) (r P Q : ℤ)
    {L M : DerivedCategory A} (u : L ⟶ M) :
    postnikovAlpha T r P Q L ≫ (postnikovD T r (P - 1) (Q + 1)).map u =
      (postnikovD T r P Q).map u ≫ postnikovAlpha T r P Q M := by
  dsimp only [postnikovAlpha]
  rw [Category.assoc, ← eqToHom_naturality
    (fun n : ℤ ↦ (TStructure.t.truncLE (Q + 1) ⋙ postnikovValue T n).map u)
    (show P + Q - r = P - 1 + (Q + 1) - r by omega), ← Category.assoc]
  simp only [← Category.assoc]
  apply congrArg (fun f : (postnikovD T r P Q).obj L ⟶
      (postnikovValue T (P + Q - r)).obj ((TStructure.t.truncLE (Q + 1)).obj M) ↦
    f ≫ eqToHom (congrArg (fun n : ℤ ↦
      (postnikovValue T n).obj ((TStructure.t.truncLE (Q + 1)).obj M))
        (show P + Q - r = P - 1 + (Q + 1) - r by omega)))
  change (postnikovValue T (P + Q - r)).map _ ≫
      (postnikovValue T (P + Q - r)).map _ =
    (postnikovValue T (P + Q - r)).map _ ≫
      (postnikovValue T (P + Q - r)).map _
  simp only [← Functor.map_comp]
  exact congrArg ((postnikovValue T (P + Q - r)).map)
    ((TStructure.t.natTransTruncLEOfLE Q (Q + 1) (by omega)).naturality u).symm

set_option backward.isDefEq.respectTransparency false in
private theorem g_naturality {B : Type uB} [Category.{vB} B]
    (T : DerivedCategory A ⥤ B) (r P Q : ℤ)
    {L M : DerivedCategory A} (u : L ⟶ M) :
    postnikovG T r P Q L ≫ (postnikovE T r P Q).map u =
      (postnikovD T r P Q).map u ≫ postnikovG T r P Q M := by
  change (postnikovValue T (P + Q - r)).map _ ≫
      (postnikovValue T (P + Q - r)).map _ =
    (postnikovValue T (P + Q - r)).map _ ≫
      (postnikovValue T (P + Q - r)).map _
  simp only [← Functor.map_comp]
  exact congrArg ((postnikovValue T (P + Q - r)).map)
    (((TStructure.t.triangleLTLTGELT Q (Q + 1) (by omega)).map u).comm₂)

set_option backward.isDefEq.respectTransparency false in
private theorem f_naturality {B : Type uB} [Category.{vB} B]
    (T : DerivedCategory A ⥤ B) (r P Q : ℤ)
    {L M : DerivedCategory A} (u : L ⟶ M) :
    postnikovF T r P Q L ≫ (postnikovD T r (P + 2) (Q - 1)).map u =
      (postnikovE T r P Q).map u ≫ postnikovF T r P Q M := by
  dsimp only [postnikovF, postnikovD, Triangulated.TStructure.truncLE]
  rw [Category.assoc, ← eqToHom_naturality
    (fun m : ℤ ↦ (TStructure.t.truncLT m ⋙
      postnikovValue T ((P + 2) + (Q - 1) - r)).map u)
    (show Q = Q - 1 + 1 by omega), ← Category.assoc]
  simp only [← Category.assoc]
  apply congrArg (fun f : (postnikovE T r P Q).obj L ⟶
      (postnikovValue T (P + 2 + (Q - 1) - r)).obj ((TStructure.t.truncLT Q).obj M) ↦
    f ≫ eqToHom (congrArg (fun m : ℤ ↦
      (postnikovValue T (P + 2 + (Q - 1) - r)).obj ((TStructure.t.truncLT m).obj M))
        (show Q = Q - 1 + 1 by omega)))
  change T.map _ ≫ T.map _ = T.map _ ≫ T.map _
  simp only [← Functor.map_comp]
  apply congrArg T.map
  simp only [Category.assoc]
  rw [← (shiftFunctorAdd' (DerivedCategory A) 1 (P + Q - r)
    (P + 2 + (Q - 1) - r) (by omega)).inv.naturality]
  dsimp only [Functor.comp_map]
  simp only [← Category.assoc]
  apply congrArg (fun f :
      (shiftFunctor (DerivedCategory A) (P + Q - r)).obj
        ((TStructure.t.truncGELT Q (Q + 1)).obj L) ⟶
      (shiftFunctor (DerivedCategory A) 1 ⋙
        shiftFunctor (DerivedCategory A) (P + Q - r)).obj ((TStructure.t.truncLT Q).obj M) ↦
    f ≫ (shiftFunctorAdd' (DerivedCategory A) 1 (P + Q - r)
      (P + 2 + (Q - 1) - r) (by omega)).inv.app ((TStructure.t.truncLT Q).obj M))
  simp only [← Functor.map_comp]
  exact congrArg ((shiftFunctor (DerivedCategory A) (P + Q - r)).map)
    (((TStructure.t.triangleLTLTGELT Q (Q + 1) (by omega)).map u).comm₃)

set_option backward.isDefEq.respectTransparency false in
/-- Finite cutoff, canonical actual image filtration, and natural graded comparisons.
The family `X` is the reindexing of the assumed Postnikov couples. The equations for
`alpha`, `g`, and `f` prescribe respectively the inclusion, quotient, and boundary;
no arbitrary comparison map or completeness of the derived category is assumed.
The index `s : Nat` denotes page `s+2`.

Source: Stacks Tags 011T, 012U, 08J5 and 0147, and the blueprint half-plane proof.
(blueprint: lem-per-postnikov-finite-cutoff-abutment).

Proof:
1. If Q<c, tau_{<=Q}L has zero cohomology in every degree, hence is zero in D(A).
   Additivity makes its T-values zero. The single-degree layer is >=Q, so the
   amplitude hypothesis gives E=0 for P<0. Kernel/image iteration preserves zeros.
2. Apply thm-sp-half-plane-convergence to the translated couple with lower bound c.
   Original degree n becomes N=n+r and the canonical abutment is D(0,N). Its
   support and stabilization bound become c<=q<=n+r and s+2>max(q-c+1,p+r).
3. For m>=n+r, the canonical tail triangle has tail >=m+1. Its T^(n-1) and T^n
   vanish by the amplitude bound. The long exact sequence of
   lem-sp-long-exact-of-triangle makes the cutoff map mono and epi, hence an iso.
   Naturality of truncation inclusions gives the comparison square for every u.
4. Transport the half-plane image filtration along this iso and translate its
   index by r. For P=p+r>=0 the alpha iterate is the inclusion at cutoff n-p.
   For P<=0 that inclusion is an iso by step 3. This proves the image formula
   for every integer p. It is top for p<=-r and bottom for p>=n-c+1, giving
   finiteness, exhaustiveness, and separatedness. Empty support implies T^n(L)=0.
   The canonical quotient comparisons give the stable-page/graded isomorphisms;
   their equations with the epimorphic maps from D make them coherent.
5. Apply lem-sp-couple-morphism to the translated couples and conjugate the
   canonical abutment map by the comparisons of step 3. It is exactly T^n(u).
   Naturality at every cutoff restricts this map to the displayed images.
   Passing the adjacent image squares to their cokernels gives the graded map,
   which intertwines the canonical infinite-page comparisons. The maps on cycles
   and their quotients are characterized by their inclusions and projections.
-/
theorem postnikov_finite_cutoff_abutment
    (T : DerivedCategory A ⥤ B) [T.IsHomological] (r c : ℤ)
    (hamp : ∀ (b n : ℤ) (M : DerivedCategory A), M.IsGE b → n < b - r →
      IsZero ((postnikovValue T n).obj M))
    (X : postnikovLowerCategory A c → CategoryTheory.BigradedExactCouple B 0)
    (d : ∀ (K : postnikovLowerCategory A c) (P Q : ℤ),
      (X K).D P Q ≅ (postnikovD T r P Q).obj K.obj)
    (e : ∀ (K : postnikovLowerCategory A c) (P Q : ℤ),
      (X K).E P Q ≅ (postnikovE T r P Q).obj K.obj)
    (ha : ∀ (K : postnikovLowerCategory A c) (P Q : ℤ),
      (X K).alpha P Q ≫ (d K (P - 1) (Q + 1)).hom =
        (d K P Q).hom ≫ postnikovAlpha T r P Q K.obj)
    (hg : ∀ (K : postnikovLowerCategory A c) (P Q : ℤ),
      (X K).initialG P Q ≫ (e K P Q).hom =
        (d K P Q).hom ≫ postnikovG T r P Q K.obj)
    (hf : ∀ (K : postnikovLowerCategory A c) (P Q : ℤ),
      (X K).f P Q ≫ (d K (P + 2) (Q - 1)).hom =
        (e K P Q).hom ≫ postnikovF T r P Q K.obj) :
    (∀ (K : postnikovLowerCategory A c) (n m : ℤ), n + r ≤ m →
      IsIso (postnikovCutoffMap T n m K.obj)) ∧
    (∀ (K K' : postnikovLowerCategory A c) (u : K ⟶ K') (n m : ℤ),
      (postnikovValue T n).map ((TStructure.t.truncLE m).map u.hom) ≫
          postnikovCutoffMap T n m K'.obj =
        postnikovCutoffMap T n m K.obj ≫ (postnikovValue T n).map u.hom) ∧
    (∀ (K : postnikovLowerCategory A c) (n : ℤ), n < c - r →
      IsZero ((postnikovValue T n).obj K.obj)) ∧
    (∀ (K : postnikovLowerCategory A c) (P Q : ℤ), Q < c → IsZero ((X K).D P Q)) ∧
    (∀ (K : postnikovLowerCategory A c) (s : ℕ) (p q : ℤ),
      p < -r ∨ q < c → IsZero (((X K).pageCouple s).E (p + r) q)) ∧
    (∀ (K : postnikovLowerCategory A c) (s : ℕ) (n p q : ℤ), p + q = n →
      ¬ IsZero (((X K).pageCouple s).E (p + r) q) → c ≤ q ∧ q ≤ n + r) ∧
    (∀ (K : postnikovLowerCategory A c) (s : ℕ) (p q : ℤ),
      (s : ℤ) + 2 > max (q - c + 1) (p + r) →
      ∃ z : ((X K).pageCouple s).E (p + r) q ≅
          ((X K).pageCouple (s + 1)).E (p + r) q,
        kernel.ι (((X K).pageCouple s).d (p + r) q) ≫ z.hom =
          ((X K).pageCouple s).derivedEProjection (p + r) q) ∧
    ∃ lim : ∀ K : postnikovLowerCategory A c,
        CategoryTheory.BigradedExactCouple.LimitSubobjects (X K),
    ∃ ab : ∀ (K : postnikovLowerCategory A c) (N : ℤ),
        CategoryTheory.BigradedExactCouple.AlphaColimit (X K) N,
    ∃ hAb : ∀ (K : postnikovLowerCategory A c) (N : ℤ),
        (ab K N).obj = (X K).D 0 N,
    ∃ a : ∀ (K : postnikovLowerCategory A c) (N : ℤ),
        (ab K N).obj ≅ (postnikovValue T (N - r)).obj K.obj,
    ∃ F : ∀ (K : postnikovLowerCategory A c) (n : ℤ),
        DecreasingFiltration ((postnikovValue T n).obj K.obj),
    ∃ hF : ∀ (K : postnikovLowerCategory A c) (n p : ℤ),
        (F K n).F p = imageSubobject (postnikovCutoffMap T n (n - p) K.obj),
    ∃ g : ∀ (K : postnikovLowerCategory A c) (p q : ℤ),
        (X K).pageInfinity (lim K) (p + r) q ≅ (F K (p + q)).gradedPiece p,
      (∀ (K : postnikovLowerCategory A c) (N : ℤ),
        (ab K N).ι 0 ≫ eqToHom (hAb K N) = eqToHom (by congr 1; omega)) ∧
      (∀ (K : postnikovLowerCategory A c) (N P : ℤ),
        (ab K N).ι P ≫ (a K N).hom =
          (d K P (N - P)).hom ≫
            eqToHom (congrArg (fun n : ℤ ↦
              (postnikovValue T n).obj ((TStructure.t.truncLE (N - P)).obj K.obj))
                (by omega)) ≫
              postnikovCutoffMap T (N - r) (N - P) K.obj) ∧
      (∀ K : postnikovLowerCategory A c,
        (X K).IsComplete ∧ (X K).ConvergesTo (lim K) (ab K)) ∧
      (∀ (K : postnikovLowerCategory A c) (n p : ℤ),
        (F K n).F p =
          (Subobject.«exists» ((a K (n + r)).hom ≫
            eqToHom (congrArg (fun k : ℤ ↦ (postnikovValue T k).obj K.obj)
              (by omega)))).obj
              (((X K).imageFiltration (n + r) (ab K (n + r))).step (p + r))) ∧
      (∀ (K : postnikovLowerCategory A c) (n : ℤ),
        (F K n).IsFinite ∧ (F K n).IsExhaustive ∧ (F K n).IsSeparated) ∧
      (∀ (K : postnikovLowerCategory A c) (n p : ℤ), p ≤ -r → (F K n).F p = ⊤) ∧
      (∀ (K : postnikovLowerCategory A c) (n p : ℤ),
        n - c + 1 ≤ p → (F K n).F p = ⊥) ∧
      (∀ (K : postnikovLowerCategory A c) (p q : ℤ),
        (X K).toPageInfinity (lim K) (p + r) q ≫ (g K p q).hom =
          (d K (p + r) q).hom ≫
            eqToHom (congrArg (fun n : ℤ ↦
              (postnikovValue T n).obj ((TStructure.t.truncLE q).obj K.obj)) (by omega)) ≫
              factorThruImageSubobject (postnikovCutoffMap T (p + q) q K.obj) ≫
                eqToHom (congrArg Subobject.underlying.obj
                  ((hF K (p + q) p).trans
                    (congrArg (fun k : ℤ ↦
                      imageSubobject (postnikovCutoffMap T (p + q) k K.obj))
                        (by omega))).symm) ≫ cokernel.π
                    (Subobject.ofLE _ _ ((F K (p + q)).F_succ_le p))) ∧
      (∀ (K : postnikovLowerCategory A c) (s : ℕ) (p q : ℤ),
        (s : ℤ) + 2 > max (q - c + 1) (p + r) →
        ∃ z : ((lim K).Z (p + r) q : B) ⟶
            ((X K).cycleBoundaryTower.Z s (p + r) q : B),
        ∃ v : ((X K).pageCouple s).E (p + r) q ≅
            (X K).pageInfinity (lim K) (p + r) q,
          z ≫ ((X K).cycleBoundaryTower.Z s (p + r) q).arrow =
            ((lim K).Z (p + r) q).arrow ∧
          z ≫ (X K).cycleBoundaryTower.projection s (p + r) q ≫ v.hom =
            cokernel.π (Subobject.ofLE _ _
              (CategoryTheory.BigradedExactCouple.limitBoundary_le_cycle
                (X K) (lim K) (p + r) q))) ∧
      (∀ (K K' : postnikovLowerCategory A c) (u : K ⟶ K'),
        ∃ f : ∀ N : ℤ, (ab K N).obj ⟶ (ab K' N).obj,
        ∃ lift : ∀ n p : ℤ, ((F K n).F p : B) ⟶ ((F K' n).F p : B),
        ∃ gr : ∀ p q : ℤ,
            (F K (p + q)).gradedPiece p ⟶ (F K' (p + q)).gradedPiece p,
        ∃ z : ∀ p q : ℤ,
            ((lim K).Z (p + r) q : B) ⟶ ((lim K').Z (p + r) q : B),
        ∃ tInf : ∀ p q : ℤ,
            (X K).pageInfinity (lim K) (p + r) q ⟶
              (X K').pageInfinity (lim K') (p + r) q,
          (∀ N : ℤ, f N ≫ (a K' N).hom =
            (a K N).hom ≫ (postnikovValue T (N - r)).map u.hom) ∧
          (∀ N P : ℤ, (ab K N).ι P ≫ f N =
            (d K P (N - P)).hom ≫
              (postnikovD T r P (N - P)).map u.hom ≫
                (d K' P (N - P)).inv ≫ (ab K' N).ι P) ∧
          (∀ n p : ℤ, lift n p ≫ ((F K' n).F p).arrow =
            ((F K n).F p).arrow ≫ (postnikovValue T n).map u.hom) ∧
          (∀ p q : ℤ,
            cokernel.π (Subobject.ofLE _ _ ((F K (p + q)).F_succ_le p)) ≫ gr p q =
              lift (p + q) p ≫
                cokernel.π (Subobject.ofLE _ _ ((F K' (p + q)).F_succ_le p))) ∧
          (∀ p q : ℤ, z p q ≫ ((lim K').Z (p + r) q).arrow =
            ((lim K).Z (p + r) q).arrow ≫ (e K (p + r) q).hom ≫
              (postnikovE T r (p + r) q).map u.hom ≫ (e K' (p + r) q).inv) ∧
          (∀ p q : ℤ,
            cokernel.π (Subobject.ofLE _ _
              (CategoryTheory.BigradedExactCouple.limitBoundary_le_cycle
                (X K) (lim K) (p + r) q)) ≫ tInf p q =
              z p q ≫ cokernel.π (Subobject.ofLE _ _
                (CategoryTheory.BigradedExactCouple.limitBoundary_le_cycle
                  (X K') (lim K') (p + r) q))) ∧
          (∀ p q : ℤ, (g K p q).hom ≫ gr p q =
            tInf p q ≫ (g K' p q).hom)) := by
  classical
  have hD (K : postnikovLowerCategory A c) (P Q : ℤ) (hQ : Q < c) :
      IsZero ((X K).D P Q) :=
    ((postnikovValue T (P + Q - r)).map_isZero
      (trunc_zero K.obj c Q K.property hQ)).of_iso (d K P Q)
  have hE (K : postnikovLowerCategory A c) (P Q : ℤ) (h : P < 0 ∨ Q < c) :
      IsZero ((X K).E P Q) :=
    (initial_zero T r c hamp K.obj K.property P Q h).of_iso (e K P Q)
  choose lim ab hAb hnorm hsupp hstab htop hfinite hgraded hcomplete hconv using
    fun K ↦ (X K).halfPlaneConvergence c (hD K) (hE K)
  refine ⟨fun K n m h ↦ cutoff_iso T r hamp n m K.obj h,
    fun K K' u n m ↦ cutoff_naturality T u.hom n m,
    fun K n h ↦ hamp c n K.obj K.property h, hD, ?_, ?_, ?_, ?_⟩
  · intro K s p q h
    exact all_page_zero (X K) c (hE K) s (p + r) q
      (h.imp (fun h ↦ by omega) id)
  · intro K s n p q hn hne
    exact hsupp K s (n + r) (p + r) q (by omega) hne
  · exact fun K s p q h ↦ hstab K s (p + r) q h
  · let j (K : postnikovLowerCategory A c) (N P : ℤ) :
        (X K).D P (N - P) ⟶ (postnikovValue T (N - r)).obj K.obj :=
      (d K P (N - P)).hom ≫
        eqToHom (congrArg (fun n : ℤ ↦
          (postnikovValue T n).obj ((TStructure.t.truncLE (N - P)).obj K.obj))
            (by omega)) ≫ postnikovCutoffMap T (N - r) (N - P) K.obj
    have hj (K : postnikovLowerCategory A c) (N P : ℤ) :
        (X K).alphaDiagonal N P ≫ j K N P = j K N (P + 1) :=
      diagonal_cocone T r N K.obj (X K) (d K) (ha K) P
    choose aMap haMap _ using fun K N ↦
      (ab K N).isColimit _ (j K N) (hj K N)
    have haIso (K : postnikovLowerCategory A c) (N : ℤ) : IsIso (aMap K N) := by
      have hi : IsIso ((ab K N).ι 0) := by
        have : IsIso ((ab K N).ι 0 ≫ eqToHom (hAb K N)) := by
          rw [hnorm K N]
          infer_instance
        exact IsIso.of_isIso_comp_right _ (eqToHom (hAb K N))
      have : IsIso (j K N 0) := by
        have := cutoff_iso T r hamp (N - r) (N - 0) K.obj (by omega)
        dsimp [j]
        infer_instance
      have : IsIso ((ab K N).ι 0 ≫ aMap K N) := by rw [haMap]; infer_instance
      exact IsIso.of_isIso_comp_left ((ab K N).ι 0) _
    let a (K : postnikovLowerCategory A c) (N : ℤ) :=
      @asIso _ _ _ _ (aMap K N) (haIso K N)
    let F (K : postnikovLowerCategory A c) (n : ℤ) :
        DecreasingFiltration ((postnikovValue T n).obj K.obj) :=
      { F p := imageSubobject (postnikovCutoffMap T n (n - p) K.obj)
        F_succ_le p := by
          let f := (postnikovValue T n).map
            ((TStructure.t.natTransTruncLEOfLE (n - (p + 1)) (n - p) (by omega)).app
              K.obj)
          have hh : f ≫ postnikovCutoffMap T n (n - p) K.obj =
              postnikovCutoffMap T n (n - (p + 1)) K.obj := by
            dsimp only [f, postnikovCutoffMap]
            rw [← Functor.map_comp, TStructure.t.natTransTruncLEOfLE_ι_app]
          rw [← hh]
          exact imageSubobject_comp_le _ _ }
    have hF (K : postnikovLowerCategory A c) (n p : ℤ) :
        (F K n).F p = imageSubobject (postnikovCutoffMap T n (n - p) K.obj) := rfl
    have hFtop (K : postnikovLowerCategory A c) (n p : ℤ) (hp : p ≤ -r) :
        (F K n).F p = ⊤ := by
      have := cutoff_iso T r hamp n (n - p) K.obj (by omega)
      rw [hF, imageSubobject_mono]
      exact Subobject.mk_eq_top_of_isIso _
    have hFbot (K : postnikovLowerCategory A c) (n p : ℤ) (hp : n - c + 1 ≤ p) :
        (F K n).F p = ⊥ := by
      have hz := (postnikovValue T n).map_isZero
        (trunc_zero K.obj c (n - p) K.property (by omega))
      rw [hF, hz.eq_zero_of_src (postnikovCutoffMap T n (n - p) K.obj),
        imageSubobject_zero]
    have htransport (K : postnikovLowerCategory A c) (N n P p : ℤ)
        (hn : N - r = n) (hp : P - r = p) :
        Subobject.mk ((((X K).imageFiltration N (ab K N)).step P).arrow ≫
          (a K N).hom ≫ eqToHom (congrArg
            (fun n : ℤ ↦ (postnikovValue T n).obj K.obj) hn)) = (F K n).F p := by
      have he := haMap K N P
      change (ab K N).ι P ≫ (a K N).hom = j K N P at he
      let b := (a K N).hom ≫ eqToHom (congrArg
        (fun n : ℤ ↦ (postnikovValue T n).obj K.obj) hn)
      have hh : Subobject.mk ((imageSubobject ((ab K N).ι P)).arrow ≫ b) =
          imageSubobject ((ab K N).ι P ≫ b) := by
        rw [← imageSubobject_mono]
        simpa only [imageSubobject_arrow_comp_assoc] using
          (imageSubobject_comp_eq_of_epi (factorThruImageSubobject ((ab K N).ι P))
            ((imageSubobject ((ab K N).ι P)).arrow ≫ b)).symm
      change Subobject.mk ((imageSubobject ((ab K N).ι P)).arrow ≫ b) = _
      rw [hh]
      dsimp only [b]
      simp only [← Category.assoc, he]
      let pre := (d K P (N - P)).hom ≫
        eqToHom (congrArg (fun k : ℤ ↦
          (postnikovValue T k).obj ((TStructure.t.truncLE (N - P)).obj K.obj))
            (show P + (N - P) - r = n by omega))
      have hw : j K N P ≫ eqToHom (congrArg
          (fun k : ℤ ↦ (postnikovValue T k).obj K.obj) hn) =
            pre ≫ postnikovCutoffMap T n (N - P) K.obj := by
        dsimp only [j, pre]
        simp only [Category.assoc]
        rw [eqToHom_naturality (fun k : ℤ ↦ postnikovCutoffMap T k (N - P) K.obj) hn]
        simp only [eqToHom_trans_assoc]
      calc
        _ = imageSubobject (pre ≫ postnikovCutoffMap T n (N - P) K.obj) :=
          congrArg (fun f : (X K).D P (N - P) ⟶ (postnikovValue T n).obj K.obj ↦
            imageSubobject f) hw
        _ = imageSubobject (postnikovCutoffMap T n (N - P) K.obj) :=
          imageSubobject_iso_comp pre _
        _ = (F K n).F p := by
          exact (congrArg (fun k : ℤ ↦ imageSubobject
            (postnikovCutoffMap T n k K.obj)) (show N - P = n - p by omega)).trans
              (hF K n p).symm
    choose ε hε using hgraded
    let b (K : postnikovLowerCategory A c) (p q : ℤ) :
        (ab K (p + r + q)).obj ≅ (postnikovValue T (p + q)).obj K.obj :=
      a K (p + r + q) ≪≫ eqToIso (congrArg
        (fun n : ℤ ↦ (postnikovValue T n).obj K.obj) (by omega))
    have hb (K : postnikovLowerCategory A c) (p q i j : ℤ)
        (hij : i - (p + r) = j - p) :
        Subobject.mk ((((X K).imageFiltration (p + r + q)
          (ab K (p + r + q))).step i).arrow ≫ (b K p q).hom) =
            (F K (p + q)).F j := by
      exact htransport K (p + r + q) (p + q) i j (by omega) (by omega)
    choose v step hstep hv using fun K p q ↦ transport_graded
      ((X K).imageFiltration (p + r + q) (ab K (p + r + q)))
      (F K (p + q)) (b K p q) (p + r) p (hb K p q)
    let g (K : postnikovLowerCategory A c) (p q : ℤ) := ε K (p + r) q ≪≫ v K p q
    have hcanon (K : postnikovLowerCategory A c) (p q : ℤ) :
        (X K).toPageInfinity (lim K) (p + r) q ≫ (g K p q).hom =
          (d K (p + r) q).hom ≫
            eqToHom (congrArg (fun n : ℤ ↦
              (postnikovValue T n).obj ((TStructure.t.truncLE q).obj K.obj)) (by omega)) ≫
              factorThruImageSubobject (postnikovCutoffMap T (p + q) q K.obj) ≫
                eqToHom (congrArg Subobject.underlying.obj
                  ((hF K (p + q) p).trans
                    (congrArg (fun k : ℤ ↦
                      imageSubobject (postnikovCutoffMap T (p + q) k K.obj))
                        (by omega))).symm) ≫
                  cokernel.π (Subobject.ofLE _ _ ((F K (p + q)).F_succ_le p)) := by
      dsimp only [g, Iso.trans_hom]
      rw [← Category.assoc, hε]
      dsimp only [CategoryTheory.BigradedExactCouple.toGradedPiece]
      rw [Category.assoc, Category.assoc, hv]
      simp only [← Category.assoc]
      apply congrArg (fun f : (X K).D (p + r) q ⟶ ((F K (p + q)).F p : B) ↦
        f ≫ cokernel.π (Subobject.ofLE _ _ ((F K (p + q)).F_succ_le p)))
      apply (cancel_mono ((F K (p + q)).F p).arrow).1
      simp only [Category.assoc, hstep]
      change (eqToHom _ ≫ factorThruImageSubobject ((ab K (p + r + q)).ι (p + r)) ≫
        (imageSubobject ((ab K (p + r + q)).ι (p + r))).arrow ≫ (b K p q).hom) = _
      rw [imageSubobject_arrow_comp_assoc]
      dsimp only [b, Iso.trans_hom, eqToIso.hom]
      rw [← Category.assoc, ← Category.assoc]
      change ((eqToHom (congrArg ((X K).D (p + r))
        (show q = p + r + q - (p + r) by omega)) ≫
          (ab K (p + r + q)).ι (p + r)) ≫ (a K (p + r + q)).hom) ≫
            eqToHom (congrArg (fun n : ℤ ↦ (postnikovValue T n).obj K.obj)
              (show p + r + q - r = p + q by omega)) = _
      have hleg := haMap K (p + r + q) (p + r)
      change (ab K (p + r + q)).ι (p + r) ≫ (a K (p + r + q)).hom =
        j K (p + r + q) (p + r) at hleg
      rw [Category.assoc (eqToHom _), hleg]
      dsimp only [j]
      simp only [Category.assoc]
      rw [← eqToHom_naturality_assoc (fun pq : ℤ × ℤ ↦ (d K pq.1 pq.2).hom)
        (show (p + r, q) = (p + r, p + r + q - (p + r)) by ext <;> omega)]
      simp only [eqToHom_trans_assoc]
      rw [eqToHom_naturality (fun nm : ℤ × ℤ ↦
        postnikovCutoffMap T nm.1 nm.2 K.obj)
        (show (p + r + q - r, p + r + q - (p + r)) = (p + q, q) by ext <;> omega)]
      simp only [eqToHom_trans_assoc]
      rw [Subobject.arrow_congr _ _
        ((hF K (p + q) p).trans
          (congrArg (fun k : ℤ ↦ imageSubobject
            (postnikovCutoffMap T (p + q) k K.obj)) (by omega))).symm]
      simp
    refine ⟨lim, ab, hAb, a, F, hF, g, hnorm, haMap,
      fun K ↦ ⟨hcomplete K, hconv K⟩, ?_, ?_, hFtop, hFbot, hcanon, ?_, ?_⟩
    · intro K n p
      rw [Subobject.exists_iso_map, ← Subobject.mk_arrow
        (((X K).imageFiltration (n + r) (ab K (n + r))).step (p + r)),
        Subobject.map_mk]
      exact (htransport K (n + r) n (p + r) p (by omega) (by omega)).symm
    · intro K n
      refine ⟨⟨-r, n - c + 1, hFtop K n (-r) le_rfl,
        hFbot K n (n - c + 1) le_rfl⟩, ?_, ?_⟩
      · intro S hS
        exact top_unique ((hFtop K n (-r) le_rfl) ▸ hS (-r))
      · intro S hS
        exact bot_unique ((hFbot K n (n - c + 1) le_rfl) ▸ hS (n - c + 1))
    · exact fun K s p q h ↦ stable_comparison (X K) c (hE K) (lim K) s (p + r) q h
    · intro K K' u
      let tD (P Q : ℤ) := (d K P Q).hom ≫ (postnikovD T r P Q).map u.hom ≫
        (d K' P Q).inv
      let tE (P Q : ℤ) := (e K P Q).hom ≫ (postnikovE T r P Q).map u.hom ≫
        (e K' P Q).inv
      let U : CategoryTheory.BigradedExactCouple.CoupleMorphism (X K) (X K') :=
        { tD := tD
          tE := tE
          alpha_comm P Q := by
            apply (cancel_mono (d K' (P - 1) (Q + 1)).hom).1
            simp only [tD, Category.assoc]
            rw [ha K']
            simp only [Iso.inv_hom_id_assoc]
            rw [← alpha_naturality, ← Category.assoc (d K P Q).hom, ← ha K]
            simp
          f_comm P Q := by
            apply (cancel_mono (d K' (P + 2) (Q - 1)).hom).1
            simp only [tD, tE, Category.assoc]
            rw [hf K']
            simp only [Iso.inv_hom_id_assoc]
            rw [← f_naturality, ← Category.assoc (e K P Q).hom, ← hf K]
            simp
          g_comm P Q := by
            have hgi : tD P Q ≫ (X K').initialG P Q =
                (X K).initialG P Q ≫ tE P Q := by
              apply (cancel_mono (e K' P Q).hom).1
              simp only [tD, tE, Category.assoc, Iso.inv_hom_id, Category.comp_id]
              rw [hg K']
              simp only [Iso.inv_hom_id_assoc]
              rw [← Category.assoc ((X K).initialG P Q), hg K,
                Category.assoc, g_naturality]
            have w : (P + (0 : ℕ), Q - (0 : ℕ)) = (P, Q) := by
              ext <;> simp
            apply (cancel_mono (eqToHom (congrArg
              (fun pq : ℤ × ℤ ↦ (X K').E pq.1 pq.2) w))).1
            simp only [Category.assoc]
            rw [eqToHom_naturality (fun pq : ℤ × ℤ ↦ tE pq.1 pq.2) w]
            simpa only [CategoryTheory.BigradedExactCouple.initialG,
              Category.assoc] using hgi }
      obtain ⟨_, hInf⟩ := CategoryTheory.BigradedExactCouple.derivedCoupleFunctoriality
        (X K) (X K') U
      choose tInf z hz ht using (hInf (lim K) (lim K')).2
      let f (N : ℤ) := (a K N).hom ≫ (postnikovValue T (N - r)).map u.hom ≫ (a K' N).inv
      have hfleg (N P : ℤ) : (ab K N).ι P ≫ f N = tD P (N - P) ≫ (ab K' N).ι P := by
        apply (cancel_mono (a K' N).hom).1
        dsimp only [f, tD]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        have hhK := haMap K N P
        change (ab K N).ι P ≫ (a K N).hom = j K N P at hhK
        rw [← Category.assoc, hhK]
        have hh := haMap K' N P
        change (ab K' N).ι P ≫ (a K' N).hom = j K' N P at hh
        rw [hh]
        dsimp only [j]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [← cutoff_naturality T u.hom (N - r) (N - P)]
        rw [eqToHom_naturality_assoc
          (fun n : ℤ ↦ (TStructure.t.truncLE (N - P) ⋙ postnikovValue T n).map u.hom)
          (show P + (N - P) - r = N - r by omega)]
        rfl
      let lift (n p : ℤ) : ((F K n).F p : B) ⟶ ((F K' n).F p : B) :=
        imageSubobjectMap (Arrow.homMk
          ((postnikovValue T n).map ((TStructure.t.truncLE (n - p)).map u.hom))
          ((postnikovValue T n).map u.hom) (cutoff_naturality T u.hom n (n - p)))
      have hlift (n p : ℤ) : lift n p ≫ ((F K' n).F p).arrow =
          ((F K n).F p).arrow ≫ (postnikovValue T n).map u.hom :=
        imageSubobjectMap_arrow _
      have hadj (n p : ℤ) :
          Subobject.ofLE _ _ ((F K n).F_succ_le p) ≫ lift n p =
            lift n (p + 1) ≫ Subobject.ofLE _ _ ((F K' n).F_succ_le p) := by
        apply (cancel_mono ((F K' n).F p).arrow).1
        simp only [Category.assoc, hlift, Subobject.ofLE_arrow_assoc, Subobject.ofLE_arrow]
      let gr (p q : ℤ) : (F K (p + q)).gradedPiece p ⟶ (F K' (p + q)).gradedPiece p :=
        cokernel.map _ _ (lift (p + q) (p + 1)) (lift (p + q) p) (hadj (p + q) p)
      have hgr (p q : ℤ) :
          cokernel.π (Subobject.ofLE _ _ ((F K (p + q)).F_succ_le p)) ≫ gr p q =
            lift (p + q) p ≫
              cokernel.π (Subobject.ofLE _ _ ((F K' (p + q)).F_succ_le p)) :=
        cokernel.π_desc _ _ _
      refine ⟨f, lift, gr, (fun p q ↦ z (p + r) q),
        (fun p q ↦ tInf (p + r) q), ?_, ?_, hlift, hgr, ?_, ?_, ?_⟩
      · intro N
        simp [f]
      · intro N P
        simpa only [tD, Category.assoc] using hfleg N P
      · intro p q
        exact (hz (p + r) q).symm
      · intro p q
        exact (ht (p + r) q).symm
      · intro p q
        change (g K p q).hom ≫ gr p q = tInf (p + r) q ≫ (g K' p q).hom
        have hepi : Epi ((X K).toPageInfinity (lim K) (p + r) q) :=
          ((hconv K).2.1.1 (p + r) q).1
        have hpage : (X K).toPageInfinity (lim K) (p + r) q ≫ tInf (p + r) q =
            tD (p + r) q ≫ (X K').toPageInfinity (lim K') (p + r) q := by
          dsimp only [CategoryTheory.BigradedExactCouple.toPageInfinity]
          rw [Category.assoc, ← ht, ← Category.assoc, ← Category.assoc]
          congr 1
          apply (cancel_mono ((lim K').Z (p + r) q).arrow).1
          simp only [Category.assoc, ← hz, Subobject.factorThru_arrow]
          rw [← Category.assoc, Subobject.factorThru_arrow]
          change (X K).initialG (p + r) q ≫ tE (p + r) q =
            tD (p + r) q ≫ (X K').initialG (p + r) q
          apply (cancel_mono (e K' (p + r) q).hom).1
          simp only [tD, tE, Category.assoc, Iso.inv_hom_id, Category.comp_id]
          rw [hg K']
          simp only [Iso.inv_hom_id_assoc]
          rw [← Category.assoc, hg K, Category.assoc, g_naturality]
        apply (cancel_epi ((X K).toPageInfinity (lim K) (p + r) q)).1
        rw [← Category.assoc, hcanon]
        rw [← Category.assoc _ (tInf (p + r) q), hpage,
          Category.assoc (tD (p + r) q), hcanon]
        simp only [Category.assoc, hgr, tD, Iso.inv_hom_id_assoc]
        congr 1
        rw [eqToHom_naturality_assoc
          (fun n : ℤ ↦ (TStructure.t.truncLE q ⋙ postnikovValue T n).map u.hom)
          (show p + r + q - r = p + q by omega)]
        congr 1
        simp only [← Category.assoc]
        congr 1
        apply (cancel_mono ((F K' (p + q)).F p).arrow).1
        simp only [Category.assoc, hlift]
        rw [← Category.assoc _ _ ((postnikovValue T (p + q)).map u.hom)]
        rw [Subobject.arrow_congr _ _
          ((hF K (p + q) p).trans
            (congrArg (fun k : ℤ ↦ imageSubobject
              (postnikovCutoffMap T (p + q) k K.obj)) (by omega))).symm]
        rw [Subobject.arrow_congr _ _
          ((hF K' (p + q) p).trans
            (congrArg (fun k : ℤ ↦ imageSubobject
              (postnikovCutoffMap T (p + q) k K'.obj)) (by omega))).symm]
        simp only [imageSubobject_arrow_comp_assoc, imageSubobject_arrow_comp]
        exact (cutoff_naturality T u.hom (p + q) q).symm

end DerivedCategory
