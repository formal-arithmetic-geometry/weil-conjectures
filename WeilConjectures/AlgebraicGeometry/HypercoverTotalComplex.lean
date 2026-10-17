/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover

/-!
# The total complex of sections of a complex of sheaves over a hypercover

Let `U` be a split étale hypercover of `X` and `L` a cochain complex of sheaves on `X_ét`.
The sections `L^r(U_p)` form a double complex, with horizontal differential the alternating
coface map of the hypercover and vertical differential induced by `L`. We define its total
complex `Tot(U, L)` (with the sign `(-1)^p` on the vertical differential), the augmentation
`Γ(X, L) ⟶ Tot(U, L)` along the column `p = 0`, and, for a map `F ⟶ L^0` killed by the
differential, the map `C(U, F) ⟶ Tot(U, L)` along the row `r = 0`. These are the maps
compared in the proof of Verdier's hypercovering theorem
(blueprint `thm-weil-pbc-hypercover-cohomology`).
-/

@[expose] public section

universe u u'

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace AlgebraicGeometry.SplitEtaleHypercover

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (U : SplitEtaleHypercover X)
  {A : Type u'} [Category.{u + 1} A] [Abelian A]
  (L : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ)

attribute [local instance] Abelian.hasFiniteBiproducts

/-- The term `L^r(U_p)` of the double complex. -/
abbrev dObj (p r : ℕ) : A := (L.X r).obj.obj (op (U.simplicial _⦋p⦌))

/-- The horizontal (Čech) differential `L^r(U_p) ⟶ L^r(U_{p+1})`. -/
noncomputable abbrev dHor (p r : ℕ) : U.dObj L p r ⟶ U.dObj L (p + 1) r :=
  ((AlgebraicTopology.alternatingCofaceMapComplex A).obj
    (U.simplicial.rightOp ⋙ (L.X r).obj)).d p (p + 1)

/-- The vertical differential `L^r(U_p) ⟶ L^{r+1}(U_p)`. -/
noncomputable abbrev dVert (p r : ℕ) : U.dObj L p r ⟶ U.dObj L p (r + 1) :=
  (L.d r (r + 1)).hom.app (op (U.simplicial _⦋p⦌))

lemma dHor_dHor (p r : ℕ) : U.dHor L p r ≫ U.dHor L (p + 1) r = 0 :=
  HomologicalComplex.d_comp_d _ _ _ _

lemma dVert_dVert (p r : ℕ) : U.dVert L p r ≫ U.dVert L p (r + 1) = 0 := by
  rw [← NatTrans.comp_app]
  change ((L.d r (r + 1)) ≫ (L.d (r + 1) (r + 1 + 1))).hom.app _ = 0
  rw [L.d_comp_d]
  rfl

lemma dHor_dVert (p r : ℕ) :
    U.dHor L p r ≫ U.dVert L (p + 1) r = U.dVert L p r ≫ U.dHor L p (r + 1) :=
  ((AlgebraicTopology.alternatingCofaceMapComplex A).map
    (Functor.whiskerLeft U.simplicial.rightOp (L.d r (r + 1)).hom)).comm p (p + 1) |>.symm

/-- The index set of the total complex in degree `n`. -/
abbrev TotIdx (n : ℕ) := ↥(Finset.antidiagonal n)

/-- The term of degree `n` of the total complex. -/
noncomputable abbrev totObj (n : ℕ) : A := ⨁ fun x : TotIdx n ↦ U.dObj L x.1.1 x.1.2

/-- The components of the differential of the total complex. -/
noncomputable def totEntry (a b : ℕ × ℕ) : U.dObj L a.1 a.2 ⟶ U.dObj L b.1 b.2 :=
  (if h : b = (a.1 + 1, a.2) then U.dHor L a.1 a.2 ≫ eqToHom (by rw [h]) else 0) +
    (if h : b = (a.1, a.2 + 1) then
      ((-1 : ℤ) ^ a.1) • U.dVert L a.1 a.2 ≫ eqToHom (by rw [h]) else 0)

/-- The differential of the total complex. -/
noncomputable def totD (n : ℕ) : U.totObj L n ⟶ U.totObj L (n + 1) :=
  biproduct.matrix fun x y ↦ U.totEntry L x.1 y.1

/-- The index `(p, r)` as an element of the index set. -/
abbrev totIdx (p r : ℕ) : TotIdx (p + r) := ⟨(p, r), Finset.mem_antidiagonal.2 rfl⟩

/-- The inclusion of the component `(p, r)` into the total complex in degree `n = p + r`. -/
noncomputable def totι (p r n : ℕ) (h : p + r = n) : U.dObj L p r ⟶ U.totObj L n :=
  biproduct.ι (fun x : TotIdx n ↦ U.dObj L x.1.1 x.1.2) ⟨(p, r), Finset.mem_antidiagonal.2 h⟩

/-- The projection to the component `(p, r)` of the total complex in degree `n = p + r`. -/
noncomputable def totπ (p r n : ℕ) (h : p + r = n) : U.totObj L n ⟶ U.dObj L p r :=
  biproduct.π (fun x : TotIdx n ↦ U.dObj L x.1.1 x.1.2) ⟨(p, r), Finset.mem_antidiagonal.2 h⟩

lemma totι_totπ (p r n : ℕ) (h : p + r = n) : U.totι L p r n h ≫ U.totπ L p r n h = 𝟙 _ :=
  biproduct.ι_π_self _ _

lemma totι_totπ_of_ne (p r p' r' n : ℕ) (h : p + r = n) (h' : p' + r' = n) (hp : p ≠ p') :
    U.totι L p r n h ≫ U.totπ L p' r' n h' = 0 :=
  biproduct.ι_π_ne _ (by
    intro e
    have := congrArg (fun x : TotIdx n ↦ x.1.1) e
    exact hp this)

lemma totι_eq_biproductι (x : TotIdx n) :
    U.totι L x.1.1 x.1.2 n (Finset.mem_antidiagonal.1 x.2) =
      biproduct.ι (fun x : TotIdx n ↦ U.dObj L x.1.1 x.1.2) x := rfl

lemma totπ_eq_biproductπ (x : TotIdx n) :
    U.totπ L x.1.1 x.1.2 n (Finset.mem_antidiagonal.1 x.2) =
      biproduct.π (fun x : TotIdx n ↦ U.dObj L x.1.1 x.1.2) x := rfl

lemma totObj_hom_ext {n : ℕ} {Z : A} {f g : U.totObj L n ⟶ Z}
    (h : ∀ p r (hpr : p + r = n), U.totι L p r n hpr ≫ f = U.totι L p r n hpr ≫ g) : f = g :=
  biproduct.hom_ext' _ _ fun x ↦ h x.1.1 x.1.2 (Finset.mem_antidiagonal.1 x.2)

lemma totObj_hom_ext' {n : ℕ} {Z : A} {f g : Z ⟶ U.totObj L n}
    (h : ∀ p r (hpr : p + r = n), f ≫ U.totπ L p r n hpr = g ≫ U.totπ L p r n hpr) : f = g :=
  biproduct.hom_ext _ _ fun x ↦ h x.1.1 x.1.2 (Finset.mem_antidiagonal.1 x.2)

lemma totι_π (p r n : ℕ) (h : p + r = n) (x : TotIdx n) :
    U.totι L p r n h ≫ biproduct.π (fun x : TotIdx n ↦ U.dObj L x.1.1 x.1.2) x =
      if hx : (p, r) = x.1 then eqToHom (by rw [← hx]) else 0 := by
  split_ifs with hx
  · obtain ⟨⟨p', r'⟩, hx'⟩ := x
    simp only [Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact biproduct.ι_π_self _ _
  · exact biproduct.ι_π_ne _ (fun e ↦ hx (congrArg Subtype.val e))

lemma totι_totD (p r n : ℕ) (h : p + r = n) :
    U.totι L p r n h ≫ U.totD L n =
      U.dHor L p r ≫ U.totι L (p + 1) r (n + 1) (by omega) +
        ((-1 : ℤ) ^ p) • U.dVert L p r ≫ U.totι L p (r + 1) (n + 1) (by omega) := by
  apply biproduct.hom_ext
  rintro ⟨⟨p', r'⟩, hpr'⟩
  rw [totι, totD, Category.assoc, biproduct.ι_matrix_assoc, biproduct.lift_π]
  simp only [Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc, totι_π, totEntry]
  by_cases h₁ : (p', r') = (p + 1, r)
  · simp only [Prod.mk.injEq] at h₁
    obtain ⟨rfl, rfl⟩ := h₁
    simp
  · by_cases h₂ : (p', r') = (p, r + 1)
    · simp only [Prod.mk.injEq] at h₂
      obtain ⟨rfl, rfl⟩ := h₂
      simp
    · rw [dif_neg h₁, dif_neg h₂, dif_neg (Ne.symm h₁), dif_neg (Ne.symm h₂)]
      simp

lemma totD_totD (n : ℕ) : U.totD L n ≫ U.totD L (n + 1) = 0 := by
  apply totObj_hom_ext
  intro p r h
  rw [comp_zero, ← Category.assoc, totι_totD, Preadditive.add_comp, Category.assoc,
    Preadditive.zsmul_comp, Category.assoc, totι_totD, totι_totD]
  simp only [Preadditive.comp_add, Preadditive.comp_zsmul, ← Category.assoc, dHor_dHor,
    dVert_dVert, zero_comp, smul_zero, add_zero, zero_add, dHor_dVert]
  simp [pow_succ]

end AlgebraicGeometry.SplitEtaleHypercover
