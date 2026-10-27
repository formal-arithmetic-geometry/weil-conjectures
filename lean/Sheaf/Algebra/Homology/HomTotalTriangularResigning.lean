/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
import Mathlib.Algebra.Category.Grp.Zero

/-! # Triangular resigning of the bounded Hom complex

Source: blueprint, six-functors basics, direct-image stability proof, paragraph (3),
internal-bar roof-adjunction normalization; Stacks Tags 010V, 011G, 012Y, 012Z and 05RU.
(blueprint: lem-sfb-hom-total-triangular-resigning)

The Hom complex and commuting bicomplex total are the existing Mathlib constructions.
The auxiliary definitions specify the Hom bicomplex, its coordinates, the triangular
multipliers and the families attached to maps and homotopies, without choosing any data.
-/

@[expose] public noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {E : Type u} [Category.{v} E] [Abelian E]

/-- The commuting Hom bicomplex, with horizontal precomposition and vertical
postcomposition. Source: Stacks Tags 012Y and 012Z, and the internal-bar normalization
(blueprint: lem-sfb-hom-total-triangular-resigning). The structure equations are exactly
bilinearity, associativity and the two input complex equations. -/
def homTotalBicomplex (P I : CochainComplex E ℤ) :
    HomologicalComplex₂ AddCommGrpCat.{v} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  HomologicalComplex₂.ofGradedObject _ _
    (fun pr ↦ AddCommGrpCat.of (P.X (-pr.1) ⟶ I.X pr.2))
    (fun p p' r ↦ AddCommGrpCat.ofHom (Preadditive.leftComp (I.X r) (P.d (-p') (-p))))
    (fun p r r' ↦ AddCommGrpCat.ofHom (Preadditive.rightComp (P.X (-p)) (I.d r r')))
    (by
      intro p p' h r
      ext x
      change P.d (-p') (-p) ≫ x = 0
      rw [P.shape (-p') (-p) (by simp only [ComplexShape.up_Rel] at *; omega)]
      exact zero_comp)
    (by
      intro p r r' h
      ext x
      change x ≫ I.d r r' = 0
      rw [I.shape r r' h]
      exact comp_zero)
    (by
      intro p p' p'' r
      ext x
      change P.d (-p'') (-p') ≫ (P.d (-p') (-p) ≫ x) = 0
      rw [← Category.assoc, HomologicalComplex.d_comp_d, zero_comp])
    (by
      intro p r r' r''
      ext x
      change (x ≫ I.d r r') ≫ I.d r' r'' = 0
      rw [Category.assoc, HomologicalComplex.d_comp_d, comp_zero])
    (by
      intro p p' r r'
      ext x
      exact Category.assoc _ _ _)

/-- The integer unit multiplying bidegree `(p,r)`. Source: the triangular sign
calculation in the internal-bar normalization
(blueprint: lem-sfb-hom-total-triangular-resigning). -/
def homTotalTriangularSign (p r : ℤ) : ℤˣ :=
  (p * r + p * (p + 1) / 2).negOnePow

/-- Restrict a Hom cochain to its nonpositive source degrees. Source: the finite-diagonal
identification in the internal-bar normalization, Stacks Tag 010V
(blueprint: lem-sfb-hom-total-triangular-resigning). Its inverse, when `P` vanishes in
positive degrees, inserts the unique zero maps in those degrees. -/
def homTotalRestriction (P I : CochainComplex E ℤ) (n : ℤ) :
    (HomComplex P I).X n ⟶
      AddCommGrpCat.of (∀ p : ℕ, P.X (-(p : ℤ)) ⟶ I.X (n - p)) :=
  AddCommGrpCat.ofHom
    { toFun := fun x p ↦ x.v (-(p : ℤ)) (n - p) (by omega)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

/-- The canonical projection from a diagonal total to its `(p,r)` summand, using zero
on every other summand. Source: Stacks Tag 012Z, finite-diagonal total
(blueprint: lem-sfb-hom-total-triangular-resigning). -/
def homTotalProjection (P I : CochainComplex E ℤ) (n p r : ℤ) :
    ((homTotalBicomplex P I).total (ComplexShape.up ℤ)).X n ⟶
      AddCommGrpCat.of (P.X (-p) ⟶ I.X r) :=
  (homTotalBicomplex P I).totalDesc (fun p' r' _ ↦
    if h : p' = p ∧ r' = r then
      eqToHom (by
        simp only [homTotalBicomplex, HomologicalComplex₂.ofGradedObject]
        rw [h.1, h.2]) else 0)

/-- The same family as a cochain map into the shift, regarded as a degree-`n` Hom
cochain. Source: Stacks Tag 011G, shift convention
(blueprint: lem-sfb-hom-total-triangular-resigning). -/
def homTotalMapFamily {P I : CochainComplex E ℤ} (n : ℤ) (f : P ⟶ I⟦n⟧) :
    HomComplex.Cochain P I n :=
  (HomComplex.Cochain.ofHom f).rightUnshift n (zero_add n)

/-- The same family as a homotopy into `I[n]`, regarded as a degree-`n-1` Hom cochain.
Source: Stacks Tags 010V and 011G, homotopy and shift conventions
(blueprint: lem-sfb-hom-total-triangular-resigning). -/
def homTotalHomotopyFamily {P I : CochainComplex E ℤ} (n : ℤ)
    {f g : P ⟶ I⟦n⟧} (H : Homotopy f g) : HomComplex.Cochain P I (n - 1) :=
  (HomComplex.Cochain.ofHomotopy H).rightUnshift (n - 1) (by omega)

/-- The finite diagonal sum with triangular multipliers. Source: the finite-diagonal
construction in steps 1 and 3 of the internal-bar normalization
(blueprint: lem-sfb-hom-total-triangular-resigning). This is an explicit additive map. -/
private def homTotalSignedMap (P I : CochainComplex E ℤ) (n : ℤ) :
    (HomComplex P I).X n ⟶ ((homTotalBicomplex P I).total (ComplexShape.up ℤ)).X n :=
  AddCommGrpCat.ofHom
    (∑ p ∈ Finset.Icc (0 : ℤ) n,
      ((homTotalBicomplex P I).ιTotalOrZero (ComplexShape.up ℤ) p (n - p) n).hom.comp
        { toFun := fun x ↦ homTotalTriangularSign p (n - p) •
            x.v (-p) (n - p) (by omega)
          map_zero' := by simp
          map_add' := by intros; simp [smul_add] })

/-- Signed coordinate projections, in every source degree. Source: steps 1 and 5 of
internal-bar normalization (blueprint: lem-sfb-hom-total-triangular-resigning). Coordinates
outside the first quadrant are zero because their source or target is zero. -/
private def homTotalSignedInverse (P I : CochainComplex E ℤ) (n : ℤ) :
    ((homTotalBicomplex P I).total (ComplexShape.up ℤ)).X n ⟶ (HomComplex P I).X n :=
  AddCommGrpCat.ofHom
    { toFun := fun y ↦ HomComplex.Cochain.mk (fun a b _ ↦
        homTotalTriangularSign (-a) b •
          (eqToHom (congrArg P.X (neg_neg a).symm) ≫
            (homTotalProjection P I n (-a) b) y))
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp [Preadditive.comp_add, smul_add] }

private theorem restriction_isIso (P I : CochainComplex E ℤ)
    (hP : ∀ i : ℤ, 0 < i → IsZero (P.X i)) (n : ℤ) :
    IsIso (homTotalRestriction P I n) := by
  classical
  apply (ConcreteCategory.isIso_iff_bijective _).2
  constructor
  · intro x y h
    apply HomComplex.Cochain.ext
    intro a b hab
    by_cases ha : 0 < a
    · exact (hP a ha).eq_of_src _ _
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, a = -(p : ℤ) :=
        ⟨(-a).toNat, by omega⟩
      have hb : b = n - p := by omega
      revert hab
      rw [hb]
      intro hab
      exact congrFun h p
  · intro y
    refine ⟨HomComplex.Cochain.mk (fun a b hab ↦ if ha : 0 < a then 0 else ?_), ?_⟩
    · have he : ((-a).toNat : ℤ) = -a := Int.toNat_of_nonneg (by omega)
      have hb : n - -a = b := by omega
      simpa only [he, neg_neg, hb] using y (-a).toNat
    · funext p
      cases p <;> rfl

private theorem negative_hom_isZero (P I : CochainComplex E ℤ)
    (hP : ∀ i : ℤ, 0 < i → IsZero (P.X i))
    (hI : ∀ r : ℤ, r < 0 → IsZero (I.X r)) (n : ℤ) (hn : n < 0) :
    IsZero ((HomComplex P I).X n) := by
  have : Subsingleton ((HomComplex P I).X n) := ⟨fun x y ↦ by
    apply HomComplex.Cochain.ext
    intro a b hab
    by_cases ha : 0 < a
    · exact (hP a ha).eq_of_src _ _
    · exact (hI b (by omega)).eq_of_tgt _ _⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

private theorem hom_bicomplex_firstQuadrant (P I : CochainComplex E ℤ)
    (hP : ∀ i : ℤ, 0 < i → IsZero (P.X i))
    (hI : ∀ r : ℤ, r < 0 → IsZero (I.X r))
    (p r : ℤ) (h : p < 0 ∨ r < 0) :
    IsZero (((homTotalBicomplex P I).X p).X r) := by
  have : Subsingleton (((homTotalBicomplex P I).X p).X r) := ⟨fun x y ↦ by
    rcases h with hp | hr
    · exact (hP (-p) (by omega)).eq_of_src _ _
    · exact (hI r hr).eq_of_tgt _ _⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

private theorem triangular_sign_recurrences (p r : ℤ) :
    homTotalTriangularSign p (r + 1) = p.negOnePow * homTotalTriangularSign p r ∧
    (p + r + 1).negOnePow * homTotalTriangularSign (p + 1) r =
      homTotalTriangularSign p r := by
  have he : (p + 1) * (p + 1 + 1) = p * (p + 1) + 2 * (p + 1) := by ring
  have hd : (p + 1) * (p + 1 + 1) / 2 = p * (p + 1) / 2 + p + 1 := by
    rw [he]
    omega
  constructor
  · dsimp only [homTotalTriangularSign]
    rw [← Int.negOnePow_add]
    congr 1
    ring
  · dsimp only [homTotalTriangularSign]
    rw [hd, ← Int.negOnePow_add]
    have hs : p + r + 1 + ((p + 1) * r + (p * (p + 1) / 2 + p + 1)) =
        2 * (p + r + 1) + (p * r + p * (p + 1) / 2) := by ring
    rw [hs, Int.negOnePow_add, Int.negOnePow_two_mul, one_mul]

private theorem map_family_cocycle (P I : CochainComplex E ℤ) (n : ℤ)
    (x : HomComplex.Cochain P I n) :
    HomComplex.δ n (n + 1) x = 0 ↔ ∃ f : P ⟶ I⟦n⟧, homTotalMapFamily n f = x := by
  constructor
  · intro hx
    let z := HomComplex.Cocycle.mk x (n + 1) rfl hx
    refine ⟨HomComplex.Cocycle.equivHomShift.symm z, ?_⟩
    change (HomComplex.Cocycle.equivHomShift
      (HomComplex.Cocycle.equivHomShift.symm z)).1 = x
    rw [AddEquiv.apply_symm_apply]
    rfl
  · rintro ⟨f, rfl⟩
    exact HomComplex.Cocycle.δ_eq_zero (HomComplex.Cocycle.equivHomShift f) _

private theorem homotopy_family_boundary {P I : CochainComplex E ℤ} (n : ℤ)
    {f g : P ⟶ I⟦n⟧} (H : Homotopy f g) :
    homTotalMapFamily n f - homTotalMapFamily n g =
      n.negOnePow • HomComplex.δ (n - 1) n (homTotalHomotopyFamily n H) := by
  rw [homTotalHomotopyFamily,
    HomComplex.Cochain.δ_rightUnshift _ (n - 1) (by omega) n 0 (by omega),
    HomComplex.δ_ofHomotopy, smul_smul, Int.units_mul_self, one_smul]
  simp only [sub_eq_add_neg, HomComplex.Cochain.rightUnshift_add,
    HomComplex.Cochain.rightUnshift_neg, homTotalMapFamily]

private theorem signed_map_apply (P I : CochainComplex E ℤ) (n : ℤ)
    (x : HomComplex.Cochain P I n) :
    homTotalSignedMap P I n x = ∑ p ∈ Finset.Icc (0 : ℤ) n,
      ((homTotalBicomplex P I).ιTotalOrZero (ComplexShape.up ℤ) p (n - p) n)
        (homTotalTriangularSign p (n - p) • x.v (-p) (n - p) (by omega)) := by
  simp [homTotalSignedMap]

private theorem inclusion_projection_same (P I : CochainComplex E ℤ) (n p : ℤ) :
    (homTotalBicomplex P I).ιTotalOrZero (ComplexShape.up ℤ) p (n - p) n ≫
      homTotalProjection P I n p (n - p) = 𝟙 _ := by
  classical
  rw [HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ (by
    change p + (n - p) = n; omega)]
  simp [homTotalProjection]

private theorem inclusion_projection_ne (P I : CochainComplex E ℤ) (n p q r : ℤ)
    (h : p ≠ q) :
    (homTotalBicomplex P I).ιTotalOrZero (ComplexShape.up ℤ) p (n - p) n ≫
      homTotalProjection P I n q r = 0 := by
  classical
  rw [HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ (by
    change p + (n - p) = n; omega)]
  simp [homTotalProjection, h]

private theorem signed_map_projection (P I : CochainComplex E ℤ) (n p : ℤ)
    (hp : p ∈ Finset.Icc (0 : ℤ) n) (x : HomComplex.Cochain P I n) :
    homTotalProjection P I n p (n - p) (homTotalSignedMap P I n x) =
      homTotalTriangularSign p (n - p) • x.v (-p) (n - p) (by omega) := by
  rw [signed_map_apply, map_sum]
  rw [Finset.sum_eq_single p]
  · exact ConcreteCategory.congr_hom (inclusion_projection_same P I n p) _
  · intro q _ hq
    exact ConcreteCategory.congr_hom (inclusion_projection_ne P I n q p (n - p) hq) _
  · exact fun h ↦ (h hp).elim

private theorem projection_transport (P I : CochainComplex E ℤ) (n p q r : ℤ)
    (h : p = q) (y : ((homTotalBicomplex P I).total (ComplexShape.up ℤ)).X n) :
    eqToHom (congrArg (fun s : ℤ ↦ P.X (-s)) h.symm) ≫
      homTotalProjection P I n p r y = homTotalProjection P I n q r y := by
  subst q
  simp

private theorem signed_inverse_v (P I : CochainComplex E ℤ) (n p r : ℤ)
    (h : -p + n = r)
    (y : ((homTotalBicomplex P I).total (ComplexShape.up ℤ)).X n) :
    (homTotalSignedInverse P I n y).v (-p) r h =
      homTotalTriangularSign p r • homTotalProjection P I n p r y := by
  change homTotalTriangularSign (- -p) r •
    (eqToHom (congrArg P.X (neg_neg (-p)).symm) ≫
      homTotalProjection P I n (- -p) r y) = _
  simp only [neg_neg]
  exact congrArg (fun z ↦ homTotalTriangularSign p r • z)
    (projection_transport P I n (- -p) p r (neg_neg p) y)

private theorem signed_inverse_inclusion_same (P I : CochainComplex E ℤ) (n p : ℤ)
    (x : P.X (-p) ⟶ I.X (n - p)) :
    (homTotalSignedInverse P I n
      ((homTotalBicomplex P I).ιTotalOrZero (ComplexShape.up ℤ) p (n - p) n x)).v
        (-p) (n - p) (by omega) = homTotalTriangularSign p (n - p) • x := by
  rw [signed_inverse_v]
  have hv := ConcreteCategory.congr_hom (inclusion_projection_same P I n p) x
  change homTotalProjection P I n p (n - p)
    ((homTotalBicomplex P I).ιTotalOrZero (ComplexShape.up ℤ) p (n - p) n x) = x at hv
  rw [hv]

private theorem signed_inverse_inclusion_ne (P I : CochainComplex E ℤ) (n p q : ℤ)
    (h : p ≠ q) (x : P.X (-p) ⟶ I.X (n - p)) :
    (homTotalSignedInverse P I n
      ((homTotalBicomplex P I).ιTotalOrZero (ComplexShape.up ℤ) p (n - p) n x)).v
        (-q) (n - q) (by omega) = 0 := by
  rw [signed_inverse_v]
  have hv := ConcreteCategory.congr_hom (inclusion_projection_ne P I n p q (n - q) h) x
  change homTotalProjection P I n q (n - q)
    ((homTotalBicomplex P I).ιTotalOrZero (ComplexShape.up ℤ) p (n - p) n x) = 0 at hv
  rw [hv, smul_zero]

/-- The explicit signed diagonal sum and signed projections are mutually inverse.
Source: steps 1, 3 and 5 of the internal-bar roof-adjunction normalization, with
Stacks Tag 012Z (blueprint: lem-sfb-hom-total-triangular-resigning).

Proof: project the finite sum onto one bidegree. All other inclusions vanish under
the projection; the matching inclusion gives the identity. Each sign squares to one,
so the inverse followed by the sum is the identity on every surviving Hom component.
A component outside the finite diagonal has either zero source or zero target.
For the other composite, use the total coproduct universal property: on a surviving
diagonal summand the inverse has exactly one nonzero component, so the sum returns
that summand. Outside the first quadrant the summand itself is zero. This works for
negative total degree as well: then every diagonal summand is zero. -/
private theorem homTotalSignedEquivalence (P I : CochainComplex E ℤ)
    (hP : ∀ i : ℤ, 0 < i → IsZero (P.X i))
    (hI : ∀ r : ℤ, r < 0 → IsZero (I.X r)) (n : ℤ) :
    homTotalSignedMap P I n ≫ homTotalSignedInverse P I n = 𝟙 _ ∧
      homTotalSignedInverse P I n ≫ homTotalSignedMap P I n = 𝟙 _ := by
  constructor
  · ext x
    apply HomComplex.Cochain.ext
    intro a b hab
    change (homTotalSignedInverse P I n (homTotalSignedMap P I n x)).v a b hab =
      x.v a b hab
    by_cases ha : 0 < a
    · exact (hP a ha).eq_of_src _ _
    by_cases hb : b < 0
    · exact (hI b hb).eq_of_tgt _ _
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, a = -p := ⟨-a, by omega⟩
    have hb' : b = n - p := by omega
    revert hab
    rw [hb']
    intro hab
    change (homTotalSignedInverse P I n (homTotalSignedMap P I n x)).v
      (-p) (n - p) _ = x.v (-p) (n - p) _
    rw [signed_inverse_v,
      signed_map_projection P I n p (Finset.mem_Icc.mpr ⟨by omega, by omega⟩),
      smul_smul]
    simp only [homTotalTriangularSign, Int.units_mul_self, one_smul]
  · apply HomologicalComplex₂.total.hom_ext
    intro p r hpr
    change p + r = n at hpr
    have hr : r = n - p := by omega
    subst r
    by_cases hp : p < 0
    · have hz : IsZero (((homTotalBicomplex P I).X p).X (n - p)) := by
        have : Subsingleton (((homTotalBicomplex P I).X p).X (n - p)) :=
          ⟨fun x y ↦ (hP (-p) (by omega)).eq_of_src x y⟩
        exact AddCommGrpCat.isZero_of_subsingleton _
      exact hz.eq_of_src _ _
    by_cases hr : n - p < 0
    · have hz : IsZero (((homTotalBicomplex P I).X p).X (n - p)) := by
        have : Subsingleton (((homTotalBicomplex P I).X p).X (n - p)) :=
          ⟨fun x y ↦ (hI (n - p) hr).eq_of_tgt x y⟩
        exact AddCommGrpCat.isZero_of_subsingleton _
      exact hz.eq_of_src _ _
    rw [← HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ hpr]
    ext x
    change homTotalSignedMap P I n (homTotalSignedInverse P I n
      ((homTotalBicomplex P I).ιTotalOrZero (ComplexShape.up ℤ) p (n - p) n x)) =
      (homTotalBicomplex P I).ιTotalOrZero (ComplexShape.up ℤ) p (n - p) n x
    rw [signed_map_apply, Finset.sum_eq_single p]
    · rw [signed_inverse_inclusion_same, smul_smul]
      simp only [homTotalTriangularSign, Int.units_mul_self, one_smul]
    · intro q _ hq
      rw [signed_inverse_inclusion_ne P I n p q (by omega)]
      simp
    · intro h
      exact (h (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).elim

private theorem inverse_inclusion_same (P I : CochainComplex E ℤ) (n p r : ℤ)
    (h : p + r = n) (x : P.X (-p) ⟶ I.X r) :
    (homTotalSignedInverse P I n
      ((homTotalBicomplex P I).ιTotal (ComplexShape.up ℤ) p r n h x)).v
        (-p) r (by omega) = homTotalTriangularSign p r • x := by
  rw [signed_inverse_v]
  have hh : (homTotalBicomplex P I).ιTotal (ComplexShape.up ℤ) p r n h ≫
      homTotalProjection P I n p r = 𝟙 _ := by
    classical
    simp [homTotalProjection]
  have hv := ConcreteCategory.congr_hom hh x
  change homTotalProjection P I n p r
    ((homTotalBicomplex P I).ιTotal (ComplexShape.up ℤ) p r n h x) = x at hv
  rw [hv]

private theorem inverse_inclusion_ne (P I : CochainComplex E ℤ) (n p r q s : ℤ)
    (h : p + r = n) (hqs : -q + n = s) (hpq : p ≠ q)
    (x : P.X (-p) ⟶ I.X r) :
    (homTotalSignedInverse P I n
      ((homTotalBicomplex P I).ιTotal (ComplexShape.up ℤ) p r n h x)).v
        (-q) s hqs = 0 := by
  rw [signed_inverse_v]
  have hh : (homTotalBicomplex P I).ιTotal (ComplexShape.up ℤ) p r n h ≫
      homTotalProjection P I n q s = 0 := by
    classical
    simp [homTotalProjection, hpq]
  have hv := ConcreteCategory.congr_hom hh x
  change homTotalProjection P I n q s
    ((homTotalBicomplex P I).ιTotal (ComplexShape.up ℤ) p r n h x) = 0 at hv
  rw [hv, smul_zero]

private theorem inclusion_d (P I : CochainComplex E ℤ) (p r : ℤ) :
    (homTotalBicomplex P I).ιTotal (ComplexShape.up ℤ) p r (p + r) rfl ≫
      ((homTotalBicomplex P I).total (ComplexShape.up ℤ)).d (p + r) (p + r + 1) =
    AddCommGrpCat.ofHom (Preadditive.leftComp (I.X r) (P.d (-(p + 1)) (-p))) ≫
      (homTotalBicomplex P I).ιTotal (ComplexShape.up ℤ) (p + 1) r (p + r + 1)
        (by change p + 1 + r = p + r + 1; omega) +
    p.negOnePow •
      (AddCommGrpCat.ofHom (Preadditive.rightComp (P.X (-p)) (I.d r (r + 1))) ≫
        (homTotalBicomplex P I).ιTotal (ComplexShape.up ℤ) p (r + 1) (p + r + 1)
          (by change p + (r + 1) = p + r + 1; omega)) := by
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
    HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.up ℤ).Rel p (p + 1) by rfl)
      r (p + r + 1) (by change p + 1 + r = p + r + 1; omega),
    HomologicalComplex₂.d₂_eq _ _ p (show (ComplexShape.up ℤ).Rel r (r + 1) by rfl)
      (p + r + 1) (by change p + (r + 1) = p + r + 1; omega)]
  change (1 : ℤˣ) • _ + _ = _
  rw [one_smul]
  rfl

/-- Signed coordinate projections intertwine the total differential and the Hom
complex differential. Source: steps 3 and 4 of the internal-bar normalization,
Stacks Tags 010V and 012Z (blueprint: lem-sfb-hom-total-triangular-resigning).

Proof: it suffices to test the identity on each total coproduct inclusion. A generator
in bidegree (p,r) contributes only to (p,r+1) and (p+1,r). For the first output the
identity is t(p,r)=(-1)^p t(p,r+1). For the second it is
(-1)^(p+r+1)t(p,r)=t(p+1,r). Both follow from the triangular exponent recurrences
and the fact that each sign squares to one. All other output coordinates vanish
on both sides. Thus the equality holds without any boundedness assumption. -/
private theorem homTotalSignedInverse_comm (P I : CochainComplex E ℤ) (n : ℤ) :
    homTotalSignedInverse P I n ≫ (HomComplex P I).d n (n + 1) =
      ((homTotalBicomplex P I).total (ComplexShape.up ℤ)).d n (n + 1) ≫
        homTotalSignedInverse P I (n + 1) := by
  apply HomologicalComplex₂.total.hom_ext
  intro p r hpr
  change p + r = n at hpr
  subst n
  simp only [← Category.assoc]
  rw [inclusion_d]
  simp only [Preadditive.add_comp, CategoryTheory.Linear.units_smul_comp, Category.assoc]
  ext x
  apply HomComplex.Cochain.ext
  intro a b hab
  obtain ⟨q, rfl⟩ : ∃ q : ℤ, a = -q := ⟨-a, by omega⟩
  change (HomComplex.δ (p + r) (p + r + 1)
    (homTotalSignedInverse P I (p + r)
      ((homTotalBicomplex P I).ιTotal (ComplexShape.up ℤ) p r (p + r) rfl x))).v
        (-q) b hab = _
  change _ =
    (homTotalSignedInverse P I (p + r + 1)
      ((homTotalBicomplex P I).ιTotal (ComplexShape.up ℤ) (p + 1) r (p + r + 1) _
        (P.d (-(p + 1)) (-p) ≫ x))).v (-q) b hab +
    p.negOnePow • (homTotalSignedInverse P I (p + r + 1)
      ((homTotalBicomplex P I).ιTotal (ComplexShape.up ℤ) p (r + 1) (p + r + 1) _
        (x ≫ I.d r (r + 1)))).v (-q) b hab
  by_cases hq : q = p
  · subst q
    have hb : b = r + 1 := by omega
    obtain rfl : b = r + 1 := hb
    rw [HomComplex.δ_v _ _ rfl _ (-p) (r + 1) hab r (-(p - 1))
        (by omega) (by omega), inverse_inclusion_same,
      inverse_inclusion_ne P I (p + r) p r (p - 1) (r + 1) rfl (by omega) (by omega),
      inverse_inclusion_ne P I (p + r + 1) (p + 1) r p (r + 1) (by omega)
        (by omega) (by omega), inverse_inclusion_same]
    simp only [CategoryTheory.Limits.comp_zero, smul_zero, add_zero, zero_add,
      CategoryTheory.Linear.units_smul_comp, smul_smul, (triangular_sign_recurrences p r).1,
      ← mul_assoc, Int.units_mul_self, one_mul]
  · by_cases hq' : q = p + 1
    · subst q
      obtain rfl : r = b := by omega
      rw [HomComplex.δ_v _ _ rfl _ (-(p + 1)) r hab (r - 1) (-p)
          (by omega) (by omega), inverse_inclusion_ne P I (p + r) p r (p + 1) (r - 1) rfl
          (by omega) (by omega), inverse_inclusion_same, inverse_inclusion_same,
        inverse_inclusion_ne P I (p + r + 1) p (r + 1) (p + 1) r (by omega)
          (by omega) (by omega)]
      simp only [CategoryTheory.Limits.zero_comp, zero_add, smul_zero, add_zero,
        CategoryTheory.Linear.comp_units_smul, smul_smul]
      rw [← (triangular_sign_recurrences p r).2, ← mul_assoc, Int.units_mul_self, one_mul]
    · rw [HomComplex.δ_v _ _ rfl _ (-q) b hab (b - 1) (-(q - 1)) rfl (by omega),
        inverse_inclusion_ne P I (p + r) p r q (b - 1) rfl (by omega) (by omega),
        inverse_inclusion_ne P I (p + r) p r (q - 1) b rfl (by omega) (by omega),
        inverse_inclusion_ne P I (p + r + 1) (p + 1) r q b (by omega) hab (by omega),
        inverse_inclusion_ne P I (p + r + 1) p (r + 1) q b (by omega) hab (by omega)]
      simp

/-- Triangular resigning identifies the Hom complex with the commuting Hom total,
including its specified derived isomorphism and the map/homotopy interpretation.
Source: internal-bar roof-adjunction normalization in paragraph (3) of the blueprint's
six-functors direct-image proof; Stacks Tags 010V, 011G, 012Y, 012Z and 05RU
(blueprint: lem-sfb-hom-total-triangular-resigning).

Proof (the seven steps of the node):
1. Bilinearity and associativity give the Hom bicomplex. The bounds imply first-quadrant
vanishing. Restricting cochains to nonpositive source degrees is invertible by inserting
zero maps. Only `0 ≤ p ≤ n` remain, so the diagonal product is the finite diagonal sum;
negative diagonals are zero. This uses def-sp-abelian, def-weil-preadditive-category,
def-weil-size-convention, def-weil-abstract-derived-category and def-sp-double-complex-total.
2. Mathlib's `HomComplex.δ_δ` proves square-zero. Its calculation gives the two
square-zero terms and mixed coefficient `-((-1)^n + (-1)^(n+1)) = 0`.
3. For `e(p,r)=pr+p(p+1)/2`, its vertical difference is `p` and horizontal difference is
`p+r+1`. Thus the two displayed sign recurrences hold and each multiplier squares to one.
4. Check the signed projection map on each total coproduct inclusion. Only its vertical
and horizontal output coordinates can be nonzero; the two recurrences give precisely
the Hom differential at those coordinates. All other coordinates vanish.
5. The signed sum and projection maps are inverse because their multiplier squares are one.
Composing the inverse's cochain identity with these inverse maps gives the forward
identity. Package the degreewise isomorphisms with `isoOfComponents`, then apply
`DerivedCategory.Q.mapIso` to obtain the specified derived isomorphism.
6. Mathlib's `Cocycle.equivHomShift` identifies degree-n cocycles with maps to `I[n]`.
Its underlying cochain is exactly `homTotalMapFamily`; this uses the shift of Stacks 011G.
7. Combine `δ_ofHomotopy` and `δ_rightUnshift` to obtain `f-g=(-1)^n δH`.
Apply the additive comparison and its cochain identity for the total formula.
When `n=0`, every homotopy component is zero, including positive source degrees;
thus `C^(-1)=0` and `f=g`. No exactness or projectivity/injectivity is used. -/
theorem hom_total_triangular_resigning
    [HasDerivedCategory.{w} AddCommGrpCat.{v}]
    (P I : CochainComplex E ℤ)
    (hP : ∀ i : ℤ, 0 < i → IsZero (P.X i))
    (hI : ∀ r : ℤ, r < 0 → IsZero (I.X r)) :
    (∀ n : ℤ, IsIso (homTotalRestriction P I n)) ∧
    (∀ n : ℤ, n < 0 → IsZero ((HomComplex P I).X n)) ∧
    (∀ p r : ℤ, p < 0 ∨ r < 0 → IsZero (((homTotalBicomplex P I).X p).X r)) ∧
    (∀ n : ℤ, ∀ x : HomComplex.Cochain P I n, ∀ p : ℕ,
      n < (p : ℤ) → x.v (-(p : ℤ)) (n - p) (by omega) = 0) ∧
    (∀ n : ℤ, ∀ x : HomComplex.Cochain P I n,
      HomComplex.δ (n + 1) (n + 2) (HomComplex.δ n (n + 1) x) = 0) ∧
    (∀ p r : ℤ, 0 ≤ p → 0 ≤ r →
      homTotalTriangularSign p (r + 1) = p.negOnePow * homTotalTriangularSign p r ∧
      (p + r + 1).negOnePow * homTotalTriangularSign (p + 1) r =
        homTotalTriangularSign p r) ∧
    ∃ T : HomComplex P I ≅ (homTotalBicomplex P I).total (ComplexShape.up ℤ),
      (∀ n : ℤ, ∀ x : HomComplex.Cochain P I n,
        (T.hom.f n) x = ∑ p ∈ Finset.Icc (0 : ℤ) n,
          ((homTotalBicomplex P I).ιTotalOrZero (ComplexShape.up ℤ) p (n - p) n)
            (homTotalTriangularSign p (n - p) • x.v (-p) (n - p) (by omega))) ∧
      (∀ p r : ℤ, 0 ≤ p → 0 ≤ r →
        ∀ y : ((homTotalBicomplex P I).total (ComplexShape.up ℤ)).X (p + r),
          ((T.inv.f (p + r)) y).v (-p) r (by omega) =
            homTotalTriangularSign p r • (homTotalProjection P I (p + r) p r) y) ∧
      (∀ n : ℤ, ∀ x : HomComplex.Cochain P I n,
        (T.hom.f (n + 1)) (HomComplex.δ n (n + 1) x) =
          ((homTotalBicomplex P I).total (ComplexShape.up ℤ)).d n (n + 1)
            ((T.hom.f n) x)) ∧
      (∃ e : (DerivedCategory.Q.obj (HomComplex P I)) ≅
          DerivedCategory.Q.obj ((homTotalBicomplex P I).total (ComplexShape.up ℤ)),
        e.hom = DerivedCategory.Q.map T.hom ∧ e.inv = DerivedCategory.Q.map T.inv) ∧
      (∀ n : ℤ, 0 ≤ n → ∀ x : HomComplex.Cochain P I n,
        HomComplex.δ n (n + 1) x = 0 ↔ ∃ f : P ⟶ I⟦n⟧, homTotalMapFamily n f = x) ∧
      (∀ n : ℤ, 0 ≤ n → ∀ (f g : P ⟶ I⟦n⟧) (H : Homotopy f g),
        homTotalMapFamily n f - homTotalMapFamily n g =
          n.negOnePow • HomComplex.δ (n - 1) n (homTotalHomotopyFamily n H) ∧
        (T.hom.f n) (homTotalMapFamily n f) - (T.hom.f n) (homTotalMapFamily n g) =
          n.negOnePow •
            ((homTotalBicomplex P I).total (ComplexShape.up ℤ)).d (n - 1) n
              ((T.hom.f (n - 1)) (homTotalHomotopyFamily n H))) := by
  let e : ∀ n : ℤ, (HomComplex P I).X n ≅
      ((homTotalBicomplex P I).total (ComplexShape.up ℤ)).X n := fun n ↦
    { hom := homTotalSignedMap P I n
      inv := homTotalSignedInverse P I n
      hom_inv_id := (homTotalSignedEquivalence P I hP hI n).1
      inv_hom_id := (homTotalSignedEquivalence P I hP hI n).2 }
  have hc (n : ℤ) : homTotalSignedMap P I n ≫
      ((homTotalBicomplex P I).total (ComplexShape.up ℤ)).d n (n + 1) =
      (HomComplex P I).d n (n + 1) ≫ homTotalSignedMap P I (n + 1) := by
    calc
      _ = (homTotalSignedMap P I n ≫
          ((homTotalBicomplex P I).total (ComplexShape.up ℤ)).d n (n + 1)) ≫
          (homTotalSignedInverse P I (n + 1) ≫ homTotalSignedMap P I (n + 1)) := by
        rw [(homTotalSignedEquivalence P I hP hI (n + 1)).2, Category.comp_id]
      _ = homTotalSignedMap P I n ≫
          (((homTotalBicomplex P I).total (ComplexShape.up ℤ)).d n (n + 1) ≫
            homTotalSignedInverse P I (n + 1)) ≫ homTotalSignedMap P I (n + 1) := by
        simp only [Category.assoc]
      _ = homTotalSignedMap P I n ≫
          (homTotalSignedInverse P I n ≫ (HomComplex P I).d n (n + 1)) ≫
            homTotalSignedMap P I (n + 1) := by
        rw [← homTotalSignedInverse_comm]
      _ = _ := by
        simp only [← Category.assoc]
        rw [(homTotalSignedEquivalence P I hP hI n).1, Category.id_comp]
  let T : HomComplex P I ≅ (homTotalBicomplex P I).total (ComplexShape.up ℤ) :=
    HomologicalComplex.Hom.isoOfComponents e (by
      intro i j hij
      change i + 1 = j at hij
      subst j
      exact hc i)
  have htc (n : ℤ) (x : HomComplex.Cochain P I n) :
      (T.hom.f (n + 1)) (HomComplex.δ n (n + 1) x) =
        ((homTotalBicomplex P I).total (ComplexShape.up ℤ)).d n (n + 1)
          ((T.hom.f n) x) :=
    (ConcreteCategory.congr_hom (hc n) x).symm
  refine ⟨restriction_isIso P I hP, negative_hom_isZero P I hP hI,
    hom_bicomplex_firstQuadrant P I hP hI, ?_,
    (fun n x ↦ HomComplex.δ_δ n (n + 1) (n + 2) x),
    (fun p r _ _ ↦ triangular_sign_recurrences p r), T, ?_, ?_, htc, ?_,
    (fun n _ x ↦ map_family_cocycle P I n x), ?_⟩
  · intro n x p hp
    exact (hI (n - p) (by omega)).eq_zero_of_tgt _
  · intro n x
    change homTotalSignedMap P I n x = _
    simp [homTotalSignedMap]
  · intro p r _ _ y
    change (homTotalSignedInverse P I (p + r) y).v (-p) r _ = _
    exact signed_inverse_v P I (p + r) p r (by omega) y
  · exact ⟨DerivedCategory.Q.mapIso T, rfl, rfl⟩
  · intro n _ f g H
    refine ⟨homotopy_family_boundary n H, ?_⟩
    have ht := htc (n - 1) (homTotalHomotopyFamily n H)
    rw [show n - 1 + 1 = n by omega] at ht
    rw [← map_sub, homotopy_family_boundary n H]
    change (T.hom.f n) ((n.negOnePow : ℤ) • _) = (n.negOnePow : ℤ) • _
    rw [map_zsmul, ht]

end CochainComplex
