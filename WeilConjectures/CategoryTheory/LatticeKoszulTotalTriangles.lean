/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.CondensedActionModule
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.DiscreteLatticeKoszulResolution
public import WeilConjectures.CategoryTheory.CondensedDerivedRestrictionCalculus
public import WeilConjectures.CategoryTheory.LatticeKoszulTriangulatedCupComparison
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns

/-! # Signed lattice Koszul totalization and triangles

Source: current blueprint, direct-image stability proof, paragraph (3), agent lattice
expansion; Stacks Tags 012Z, 011G, 014E and 0152
(blueprint: lem-sfb-lattice-koszul-total-triangles).

The signed total and its coherent shifts are the existing `TriangulatedCup.total`
and `TriangulatedCup.totalShiftIsoApp`. They are reused, without a second construction.
The statements below give exactness, the signed homotopy and cone formulas, and a
triangulated localization carrying the canonical short-exact-sequence boundary.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace Profinite.DiscreteLattice
namespace TotalTriangles

open TriangulatedCup (total totalPlus bicomplex totalShiftIsoApp totalShiftIso)

-- The generic calculation follows the private helper in
-- WeilConjectures.AlgebraicGeometry.AlternatingCechTotalHomotopy.
private theorem signedTotalHomotopy
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [∀ B : HomologicalComplex₂ D (ComplexShape.up ℤ) (ComplexShape.up ℤ),
      B.HasTotal (ComplexShape.up ℤ)]
    (A : C ⥤ CochainComplex D ℤ) [A.Additive]
    {K L : CochainComplex C ℤ} {f g : K ⟶ L} (h : Homotopy f g) :
    let T := A.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      HomologicalComplex₂.flipFunctor D (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
      HomologicalComplex₂.totalFunctor D (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)
    ∃ H : Homotopy (T.map f) (T.map g),
      ∀ (p q t n m : ℤ) (hpq : p + q = n) (hpt : p + t = m) (_ : q = t + 1),
        ((A.mapHomologicalComplex (.up ℤ) ⋙
          HomologicalComplex₂.flipFunctor D (.up ℤ) (.up ℤ)).obj K).ιTotal
            (.up ℤ) p q n hpq ≫ H.hom n m =
          p.negOnePow • ((A.map (h.hom q t)).f p ≫
            ((A.mapHomologicalComplex (.up ℤ) ⋙
              HomologicalComplex₂.flipFunctor D (.up ℤ) (.up ℤ)).obj L).ιTotal
                (.up ℤ) p t m hpt) := by
  classical
  let B := (A.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.flipFunctor D (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K
  let E := (A.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.flipFunctor D (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj L
  let H : ∀ n m : ℤ, (B.total (ComplexShape.up ℤ)).X n ⟶
      (E.total (ComplexShape.up ℤ)).X m := fun n m ↦
    B.totalDesc (fun p q _ ↦ p.negOnePow •
      ((A.map (h.hom q (q - 1))).f p ≫ E.ιTotalOrZero (ComplexShape.up ℤ) p (q - 1) m))
  have hH (p q n m : ℤ) (hpq : p + q = n) :
      B.ιTotal (ComplexShape.up ℤ) p q n hpq ≫ H n m =
        p.negOnePow • ((A.map (h.hom q (q - 1))).f p ≫
          E.ιTotalOrZero (ComplexShape.up ℤ) p (q - 1) m) := by
    exact B.ι_totalDesc _ _ _ _
  refine ⟨{ hom := H, zero := ?_, comm := ?_ }, ?_⟩
  · intro n m hnm
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    rw [hH]
    have hz : ¬ p + (q - 1) = m := by
      change ¬ m + 1 = n at hnm
      change p + q = n at hpq
      omega
    rw [E.ιTotalOrZero_eq_zero _ _ _ _ hz]
    simp
  · intro n
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)]
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    change p + q = n at hpq
    subst n
    change B.ιTotal (ComplexShape.up ℤ) p q (p + q) rfl ≫
      (HomologicalComplex₂.total.map ((A.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.flipFunctor D (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f)
        (ComplexShape.up ℤ)).f (p + q) = _
    rw [HomologicalComplex₂.ιTotal_map]
    simp only [Preadditive.comp_add]
    change _ =
      B.ιTotal (ComplexShape.up ℤ) p q (p + q) rfl ≫
          (B.total (ComplexShape.up ℤ)).d (p + q) (p + q + 1) ≫
            H (p + q + 1) (p + q) +
        B.ιTotal (ComplexShape.up ℤ) p q (p + q) rfl ≫
          H (p + q) (p + q - 1) ≫
            (E.total (ComplexShape.up ℤ)).d (p + q - 1) (p + q) +
        B.ιTotal (ComplexShape.up ℤ) p q (p + q) rfl ≫
          (HomologicalComplex₂.total.map ((A.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.flipFunctor D (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map g)
            (ComplexShape.up ℤ)).f (p + q)
    simp only [← Category.assoc]
    rw [HomologicalComplex₂.ιTotal_map, hH]
    rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
      B.d₁_eq' (ComplexShape.up ℤ) (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl),
      B.d₂_eq' (ComplexShape.up ℤ) p (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl)]
    simp only [show ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (p, q) = 1 from rfl, one_smul]
    rw [B.ιTotalOrZero_eq _ _ _ _ (by change p + 1 + q = p + q + 1; omega),
      B.ιTotalOrZero_eq _ _ _ _ (by change p + (q + 1) = p + q + 1; omega)]
    simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc, hH]
    rw [E.ιTotalOrZero_eq (ComplexShape.up ℤ) p (q - 1) (p + q - 1)
      (by change p + (q - 1) = p + q - 1; omega)]
    rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
      E.d₁_eq' (ComplexShape.up ℤ) (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl),
      E.d₂_eq' (ComplexShape.up ℤ) p
        (show (ComplexShape.up ℤ).Rel (q - 1) q by simp)]
    simp only [show ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (p, q - 1) = 1 from rfl, one_smul,
      Linear.comp_units_smul, smul_smul,
      Preadditive.comp_add, smul_add]
    rw [show q + 1 - 1 = q by omega]
    change (A.map (f.f q)).f p ≫ E.ιTotal (ComplexShape.up ℤ) p q (p + q) rfl = _
    change _ =
      (p + 1).negOnePow • ((A.obj (K.X q)).d p (p + 1) ≫
        (A.map (h.hom q (q - 1))).f (p + 1) ≫
          E.ιTotalOrZero (ComplexShape.up ℤ) (p + 1) (q - 1) (p + q)) +
      (p.negOnePow * p.negOnePow) • ((A.map (K.d q (q + 1))).f p ≫
        (A.map (h.hom (q + 1) q)).f p ≫
          E.ιTotalOrZero (ComplexShape.up ℤ) p q (p + q)) +
      (p.negOnePow • ((A.map (h.hom q (q - 1))).f p ≫
        (A.obj (L.X (q - 1))).d p (p + 1) ≫
          E.ιTotalOrZero (ComplexShape.up ℤ) (p + 1) (q - 1) (p + q)) +
      (p.negOnePow * p.negOnePow) • ((A.map (h.hom q (q - 1))).f p ≫
        (A.map (L.d (q - 1) q)).f p ≫
          E.ιTotalOrZero (ComplexShape.up ℤ) p q (p + q))) +
      (A.map (g.f q)).f p ≫ E.ιTotal (ComplexShape.up ℤ) p q (p + q) rfl
    rw [Int.units_mul_self, one_smul,
      E.ιTotalOrZero_eq (ComplexShape.up ℤ) p q (p + q) rfl, Int.negOnePow_succ]
    rw [← (A.map (h.hom q (q - 1))).comm_assoc p (p + 1)]
    rw [Units.neg_smul, one_smul]
    have hh := congrArg (fun z ↦ (A.map z).f p) (h.comm q)
    simp only [dNext_eq _ (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (q - 1) q by simp),
      Functor.map_add, Functor.map_comp, HomologicalComplex.add_f_apply,
      HomologicalComplex.comp_f] at hh
    rw [hh]
    simp only [Preadditive.add_comp, Category.assoc]
    abel
  · intro p q t n m hpq hpt hqt
    change B.ιTotal (.up ℤ) p q n hpq ≫ H n m = _
    rw [hH]
    have ht : t = q - 1 := by omega
    subst t
    rw [E.ιTotalOrZero_eq (.up ℤ) p (q - 1) m hpt]

private def diagonalFunctor {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D]
    (A : C ⥤ CochainComplex D ℤ) (n : ℤ) :
    CochainComplex C ℤ ⥤ Discrete {ij : ℤ × ℤ // ij.1 + ij.2 = n} ⥤ D where
  obj P := Discrete.functor (fun ij ↦ (A.obj (P.X ij.val.2)).X ij.val.1)
  map f := Discrete.natTrans (fun ij ↦ (A.map (f.f ij.as.val.2)).f ij.as.val.1)
  map_id P := by ext ij; simp
  map_comp f g := by ext ij; simp

private def diagonalIso {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D]
    [∀ B : HomologicalComplex₂ D (.up ℤ) (.up ℤ), B.HasTotal (.up ℤ)]
    [HasCoproducts.{0} D] (A : C ⥤ CochainComplex D ℤ) [A.Additive] (n : ℤ) :
    A.mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex₂.flipFunctor D (.up ℤ) (.up ℤ) ⋙
        HomologicalComplex₂.totalFunctor D (.up ℤ) (.up ℤ) (.up ℤ) ⋙
          HomologicalComplex.eval D (.up ℤ) n ≅ diagonalFunctor A n ⋙ colim :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {P Q} f ↦ by
    simp only [Iso.refl_hom, Functor.comp_map, Category.comp_id, Category.id_comp]
    apply colimit.hom_ext
    rintro ⟨⟨⟨a, b⟩, hab⟩⟩
    change ((HomologicalComplex₂.flipFunctor D (.up ℤ) (.up ℤ)).obj
      ((A.mapHomologicalComplex (.up ℤ)).obj P)).ιTotal (.up ℤ) a b n hab ≫
        (HomologicalComplex₂.total.map _ (.up ℤ)).f n = _
    rw [HomologicalComplex₂.ιTotal_map]
    change _ = colimit.ι ((diagonalFunctor A n).obj P) ⟨⟨(a, b), hab⟩⟩ ≫
      colimMap ((diagonalFunctor A n).map f)
    rw [ι_colimMap]
    rfl)

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (r : ℕ)

private def termIso (K : KoszulModel R r) (a : ℤ) :
    K.functor ⋙ HomologicalComplex.eval (Modules R) (.up ℤ) a ≅
      Action.forget (Modules R) (Group r) ⋙ Functor.const (Discrete (Subsets r a)) ⋙ lim :=
  NatIso.ofComponents (fun P ↦ K.coordinates P a ≪≫ biproduct.isoProduct _ ≪≫
    Pi.isoLimit ((Functor.const (Discrete (Subsets r a))).obj P.V)) (fun {P Q} f ↦ by
      change (K.functor.map f).f a ≫
        (K.coordinates Q a ≪≫ biproduct.isoProduct _ ≪≫
          Pi.isoLimit ((Functor.const (Discrete (Subsets r a))).obj Q.V)).hom =
        (K.coordinates P a ≪≫ biproduct.isoProduct _ ≪≫
          Pi.isoLimit ((Functor.const (Discrete (Subsets r a))).obj P.V)).hom ≫
            limMap ((Functor.const (Discrete (Subsets r a))).map f.hom)
      apply (cancel_epi (K.coordinates P a).inv).1
      apply biproduct.hom_ext'
      intro I
      apply limit.hom_ext
      intro ⟨J⟩
      simp [Category.assoc, K.maps]
      by_cases h : I = J
      · subst J
        simp
      · simp [h, biproduct.ι_π_ne_assoc _ h])

private lemma term_isZero (K : KoszulModel R r) (P : Equivariant R r) (a : ℤ)
    (ha : a < 0 ∨ (r : ℤ) < a) : IsZero ((K.functor.obj P).X a) := by
  apply IsZero.of_iso ?_ (K.coordinates P a)
  apply (IsZero.iff_id_eq_zero _).2
  apply biproduct.hom_ext'
  intro I
  have hcard : I.val.card ≤ r := by
    simpa using Finset.card_le_univ I.val
  have h := I.property
  omega

/-- Each Koszul degree is an exact additive functor on the original internal modules.
Source: paragraph (3), DAG step 1
(blueprint: lem-sfb-lattice-koszul-total-triangles).
Proof: `KoszulModel.coordinates` and `KoszulModel.maps` identify this functor with the
finite biproduct of the exact action-forgetting functor indexed by `Subsets r a`.
Finite biproduct inclusions and projections identify its kernels and cokernels with
the corresponding biproducts, including the empty biproduct outside degrees 0 through r. -/
theorem terms_exact (K : KoszulModel R r) (a : ℤ) :
    (K.functor ⋙ HomologicalComplex.eval (Modules R) (.up ℤ) a).Additive ∧
      PreservesFiniteLimits (K.functor ⋙ HomologicalComplex.eval (Modules R) (.up ℤ) a) ∧
      PreservesFiniteColimits (K.functor ⋙ HomologicalComplex.eval (Modules R) (.up ℤ) a) := by
  have : PreservesFiniteColimits (lim (J := Discrete (Subsets r a)) (C := Modules R)) :=
    preservesFiniteColimits_of_natIso HasBiproductsOfShape.colimIsoLim
  exact ⟨inferInstance, preservesFiniteLimits_of_natIso (termIso R r K a).symm,
    preservesFiniteColimits_of_natIso (termIso R r K a).symm⟩

/-- The existing finite signed total is additive.
Source: paragraph (3), DAG steps 1 and 2
(blueprint: lem-sfb-lattice-koszul-total-triangles).
Proof: on every finite diagonal summand the map is K^a(f^b). The coordinate formula
for Koszul maps preserves addition, and coproduct extensionality gives the claim. -/
@[instance] theorem total_additive (K : KoszulModel R r) : (total R r K).Additive := by
  constructor
  intro P Q f g
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  simp [total, Preadditive.comp_add, Preadditive.add_comp]

/-- The total preserves the actual lower bound of the input terms.
Source: paragraph (3), DAG step 2
(blueprint: lem-sfb-lattice-koszul-total-triangles).
Proof: only Koszul degrees a between 0 and r occur. If n is below N, each input
term in total degree n has degree n-a below N; hence every diagonal summand is zero. -/
theorem total_lower_bound (K : KoszulModel R r)
    (P : CochainComplex (Equivariant R r) ℤ) (N : ℤ) [P.IsStrictlyGE N] :
    ((total R r K).obj P).IsStrictlyGE N := by
  apply (CochainComplex.isStrictlyGE_iff _ _).2
  intro n hn
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  have hab' : a + b = n := hab
  by_cases ha : a < 0
  · exact (term_isZero R r K (P.X b) a (Or.inl ha)).eq_of_src _ _
  · exact ((K.functor ⋙ HomologicalComplex.eval (Modules R) (.up ℤ) a).map_isZero
      (P.isZero_of_isStrictlyGE N b (by omega))).eq_of_src _ _

/-- An input homotopy is sent to the homotopy with sign (-1)^a in Koszul degree a.
Source: paragraph (3), DAG steps 2 and 3
(blueprint: lem-sfb-lattice-koszul-total-triangles).
Proof: apply K^a to h and multiply by (-1)^a. Equivariance cancels the horizontal
terms because consecutive Koszul degrees have opposite signs. The two vertical
terms give K(f-g). The displayed equation specifies every component of H. -/
theorem total_homotopy (K : KoszulModel R r)
    {P Q : CochainComplex (Equivariant R r) ℤ} {f g : P ⟶ Q} (h : Homotopy f g) :
    ∃ H : Homotopy ((total R r K).map f) ((total R r K).map g),
      ∀ (a b c n m : ℤ) (hab : a + b = n) (hac : a + c = m) (_hbc : b = c + 1),
        (bicomplex R r K P).ιTotal (.up ℤ) a b n hab ≫ H.hom n m =
          a.negOnePow • ((K.functor.map (h.hom b c)).f a ≫
            (bicomplex R r K Q).ιTotal (.up ℤ) a c m hac) := by
  obtain ⟨H, hH⟩ := signedTotalHomotopy K.functor h
  refine ⟨H, ?_⟩
  intro a b c n m hab hac hbc
  exact hH a b c n m hab hac hbc

/-- Finite exact Koszul columns preserve quasi-isomorphisms of bounded-below complexes.
Source: paragraph (3), DAG step 4
(blueprint: lem-sfb-lattice-koszul-total-triangles).
Proof: terms_exact and the exact-functor homology comparison show that each vertical
column map is a quasi-isomorphism. Apply total.quasiIso_map_of_finitely_many_columns
with integer column bounds 0 and r, using the Koszul coordinates for the zero columns. -/
theorem total_quasiIso (K : KoszulModel R r)
    {P Q : CochainComplex.Plus (Equivariant R r)} (f : P ⟶ Q) [QuasiIso f.hom] :
    QuasiIso ((total R r K).map f.hom) := by
  have hbound (X : CochainComplex (Equivariant R r) ℤ) (a : ℤ)
      (ha : a < 0 ∨ (r : ℤ) < a) : IsZero ((bicomplex R r K X).X a) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply HomologicalComplex.Hom.ext
    funext b
    exact (term_isZero R r K (X.X b) a ha).eq_of_src _ _
  have hge (X : CochainComplex (Equivariant R r) ℤ) :
      CochainComplex.IsStrictlyGE (bicomplex R r K X) 0 :=
    (CochainComplex.isStrictlyGE_iff _ _).2 (fun a ha ↦ hbound X a (Or.inl ha))
  have hle (X : CochainComplex (Equivariant R r) ℤ) :
      CochainComplex.IsStrictlyLE (bicomplex R r K X) (r : ℤ) :=
    (CochainComplex.isStrictlyLE_iff _ _).2 (fun a ha ↦ hbound X a (Or.inr ha))
  have : CochainComplex.IsStrictlyGE
      ((HomologicalComplex₂.flipFunctor (Modules R) (.up ℤ) (.up ℤ)).obj
        ((K.functor.mapHomologicalComplex (.up ℤ)).obj P.obj)) 0 := hge P.obj
  have : CochainComplex.IsStrictlyGE
      ((HomologicalComplex₂.flipFunctor (Modules R) (.up ℤ) (.up ℤ)).obj
        ((K.functor.mapHomologicalComplex (.up ℤ)).obj Q.obj)) 0 := hge Q.obj
  have : CochainComplex.IsStrictlyLE
      ((HomologicalComplex₂.flipFunctor (Modules R) (.up ℤ) (.up ℤ)).obj
        ((K.functor.mapHomologicalComplex (.up ℤ)).obj P.obj)) (r : ℤ) := hle P.obj
  have : CochainComplex.IsStrictlyLE
      ((HomologicalComplex₂.flipFunctor (Modules R) (.up ℤ) (.up ℤ)).obj
        ((K.functor.mapHomologicalComplex (.up ℤ)).obj Q.obj)) (r : ℤ) := hle Q.obj
  apply HomologicalComplex₂.total.quasiIso_map_of_finitely_many_columns
    ((HomologicalComplex₂.flipFunctor (Modules R) (.up ℤ) (.up ℤ)).map
      ((K.functor.mapHomologicalComplex (.up ℤ)).map f.hom)) 0 (r : ℤ)
  intro a _ _
  have := (terms_exact R r K a).2.1
  have := (terms_exact R r K a).2.2
  exact HomologicalComplex.quasiIso_map_of_preservesHomology f.hom
    (K.functor ⋙ HomologicalComplex.eval (Modules R) (.up ℤ) a)

/-- The existing coherent shift comparison has exactly the component (-1)^(a*s).
Source: paragraph (3), DAG step 5; Stacks Tag 011G
(blueprint: lem-sfb-lattice-koszul-total-triangles).
Proof: after the degreewise map/shift identification, the map is totalShift₂Iso,
whose totalDesc formula is multiplication by (a*s).negOnePow on column a. The
horizontal chain equation is s_(a+1)=(-1)^s s_a; the vertical equation is unchanged.
The existing totalShiftCoherence gives c_0=1 and c_(s+t)=c_s c_t. -/
theorem shift_coordinates (K : KoszulModel R r)
    (P : CochainComplex (Equivariant R r) ℤ) (s a b n : ℤ) (hab : a + b = n) :
    (bicomplex R r K (P⟦s⟧)).ιTotal (.up ℤ) a b n hab ≫
        (totalShiftIsoApp R r K P s).hom.f n ≫
          (CochainComplex.shiftFunctorObjXIso ((total R r K).obj P) s n (n + s) rfl).hom =
      (a * s).negOnePow •
        ((K.functor.map (CochainComplex.shiftFunctorObjXIso P s b (b + s) rfl).hom).f a ≫
          (bicomplex R r K P).ιTotal (.up ℤ) a (b + s) (n + s)
            (by dsimp; omega)) := by
  simp only [TriangulatedCup.total, TriangulatedCup.bicomplex, Functor.comp_obj]
  delta TriangulatedCup.totalShiftIsoApp
  simp only [Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.comp_f,
    HomologicalComplex₂.totalFunctor_map, Category.assoc]
  rw [HomologicalComplex₂.ιTotal_map_assoc]
  change (𝟙 _) ≫
    ((HomologicalComplex₂.shiftFunctor₂ (Modules R) s).obj (bicomplex R r K P)).ιTotal
      (.up ℤ) a b n hab ≫ ((bicomplex R r K P).totalShift₂Iso s).hom.f n ≫ _ = _
  rw [Category.id_comp]
  rw [HomologicalComplex₂.ι_totalShift₂Iso_hom_f_assoc _ s a b n hab
    (b + s) rfl (n + s) rfl]
  simp only [CochainComplex.shiftFunctor_obj_X', HomologicalComplex₂.shiftFunctor₂XXIso_refl,
    Iso.refl_hom, CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, Category.comp_id, Category.id_comp, Linear.units_smul_comp,
    smul_left_cancel_iff]
  change (bicomplex R r K P).ιTotal (.up ℤ) a (b + s) (n + s) (by dsimp; omega) ≫
      𝟙 (((bicomplex R r K P).total (.up ℤ)).X (n + s)) =
    (K.functor.map (𝟙 (P.X (b + s)))).f a ≫
      (bicomplex R r K P).ιTotal (.up ℤ) a (b + s) (n + s) (by dsimp; omega)
  have hm : (K.functor.map (𝟙 (P.X (b + s)))).f a =
      𝟙 ((K.functor.obj (P.X (b + s))).X a) :=
    congrArg (fun z : K.functor.obj (P.X (b + s)) ⟶
      K.functor.obj (P.X (b + s)) ↦ z.f a) (K.functor.map_id _)
  exact (Category.comp_id _).trans
    ((congrArg (fun z ↦ z ≫ (bicomplex R r K P).ιTotal (.up ℤ) a (b + s) (n + s)
      (by dsimp; omega)) hm).trans (Category.id_comp _)).symm

/-- The cone comparison, specified on both summand families, natural in commutative
squares, and compatible with the inclusion and the signed last arrow of the cone triangle.
Source: paragraph (3), DAG steps 5 and 6; Stacks Tag 014E
(blueprint: lem-sfb-lattice-koszul-total-triangles). -/
structure ConeComparison (K : KoszulModel R r) where
  /-- The chain isomorphism from the total of a cone to the cone of the total map. -/
  iso : ∀ {P Q : CochainComplex (Equivariant R r) ℤ} (f : P ⟶ Q),
    (total R r K).obj (CochainComplex.mappingCone f) ≅
      CochainComplex.mappingCone ((total R r K).map f)
  /-- Identity on the unshifted family of summands. -/
  inclusion : ∀ {P Q : CochainComplex (Equivariant R r) ℤ} (f : P ⟶ Q),
    (total R r K).map (CochainComplex.mappingCone.inr f) ≫ (iso f).hom =
      CochainComplex.mappingCone.inr ((total R r K).map f)
  /-- On the shifted family the scalar is precisely (-1)^a. -/
  shifted : ∀ {P Q : CochainComplex (Equivariant R r) ℤ} (f : P ⟶ Q)
    (a b b' n n' : ℤ) (hab : a + b = n) (hab' : a + b' = n')
    (hb : b' + (-1) = b) (hn : n' + (-1) = n),
    (K.functor.map ((CochainComplex.mappingCone.inl f).v b' b hb)).f a ≫
        (bicomplex R r K (CochainComplex.mappingCone f)).ιTotal (.up ℤ) a b n hab ≫
          (iso f).hom.f n =
      a.negOnePow • ((bicomplex R r K P).ιTotal (.up ℤ) a b' n' hab' ≫
        (CochainComplex.mappingCone.inl ((total R r K).map f)).v n' n hn)
  /-- This uses -p, rather than forgetting the cone triangle's last-arrow sign. -/
  lastArrow : ∀ {P Q : CochainComplex (Equivariant R r) ℤ} (f : P ⟶ Q),
    (total R r K).map (CochainComplex.mappingCone.triangle f).mor₃ ≫
        (totalShiftIsoApp R r K P 1).hom =
      (iso f).hom ≫ (CochainComplex.mappingCone.triangle ((total R r K).map f)).mor₃
  /-- Naturality for arbitrary commutative squares of cochain maps. -/
  naturality : ∀ {P Q P' Q' : CochainComplex (Equivariant R r) ℤ}
    (f : P ⟶ Q) (g : P' ⟶ Q') (v : P ⟶ P') (w : Q ⟶ Q')
    (h : f ≫ w = v ≫ g),
    (total R r K).map (CochainComplex.mappingCone.map f g v w h) ≫ (iso g).hom =
      (iso f).hom ≫ CochainComplex.mappingCone.map
        ((total R r K).map f) ((total R r K).map g)
        ((total R r K).map v) ((total R r K).map w)
        (by simpa only [Functor.map_comp] using congrArg (total R r K).map h)

/-- The signed cone comparison exists with all of its coordinate and naturality laws.
Source: paragraph (3), DAG steps 5 and 6
(blueprint: lem-sfb-lattice-koszul-total-triangles).
Proof: reorder the finite summands into the unshifted target and shifted source.
Use the identity on the first family and (-1)^a on the second. The horizontal chain
equation switches sign in the second family and the vertical chain equation is the
cone equation (dy+fx,-dx). These signs are self-inverse. Testing on the same two
families proves naturality, inclusion compatibility and compatibility with -p. -/
theorem cone_comparison (K : KoszulModel R r) : Nonempty (ConeComparison R r K) := by
  sorry

/-- Termwise short exact sequences remain termwise short exact under the finite total.
Source: paragraph (3), DAG steps 1 and 8
(blueprint: lem-sfb-lattice-koszul-total-triangles).
Proof: every total degree is a finite sum of exact Koszul-degree functors applied
to input degrees. Kernels and cokernels commute with those finite biproducts. In an
abelian category short exactness of complexes is detected degree by degree. -/
theorem total_shortExact (K : KoszulModel R r)
    (S : ShortComplex (CochainComplex (Equivariant R r) ℤ)) (hS : S.ShortExact) :
    (S.map (total R r K)).ShortExact := by
  have : IsGrothendieckAbelian.{u + 1} (Modules R) := inferInstance
  have : HasCoproducts.{u + 1} (Modules R) := fun J ↦
    HasColimitsOfShape.of_small.{u + 1, u + 1} (Modules R) (Discrete J)
  have : HasCoproducts.{0} (Modules R) := has_smallest_coproducts_of_hasCoproducts
  have : AB4OfSize.{u + 1} (Modules R) := inferInstance
  have : AB4OfSize.{0} (Modules R) := AB4OfSize_shrink (Modules R)
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let F := diagonalFunctor K.functor n
  have hlim : PreservesFiniteLimits F := by
    apply preservesFiniteLimits_of_evaluation
    rintro ⟨⟨⟨a, b⟩, hab⟩⟩
    have := (terms_exact R r K a).2.1
    exact comp_preservesFiniteLimits (HomologicalComplex.eval _ _ b)
      (K.functor ⋙ HomologicalComplex.eval _ _ a)
  have hcolim : PreservesFiniteColimits F := by
    apply preservesFiniteColimits_of_evaluation
    rintro ⟨⟨⟨a, b⟩, hab⟩⟩
    have := (terms_exact R r K a).2.2
    exact comp_preservesFiniteColimits (HomologicalComplex.eval _ _ b)
      (K.functor ⋙ HomologicalComplex.eval _ _ a)
  have : F.Additive := by
    constructor
    intro P Q f g
    apply NatTrans.ext
    funext ij
    dsimp [F, diagonalFunctor]
    simp
  let e : total R r K ⋙ HomologicalComplex.eval (Modules R) (.up ℤ) n ≅ F ⋙ colim :=
    diagonalIso K.functor n
  exact (ShortComplex.shortExact_iff_of_iso (S.mapNatIso e)).2
    ((hS.map_of_exact F).map_of_exact colim)

/-- The canonical connecting arrow in D-plus, obtained by the fully faithful inclusion
from Mathlib's ordinary derived connecting arrow. The quotient comparison and the
inclusion's shift comparison supply exactly the canonical changes of presentation.
Source: Stacks Tag 0152 (blueprint: lem-sfb-lattice-koszul-total-triangles). -/
def connectingPlus (S : ShortComplex (CochainComplex.Plus (Equivariant R r)))
    (hS : (S.map (CochainComplex.Plus.ι _)).ShortExact) :
    DerivedCategory.Plus.Q.obj S.X₃ ⟶ (DerivedCategory.Plus.Q.obj S.X₁)⟦(1 : ℤ)⟧ :=
  DerivedCategory.Plus.ι.preimage
    ((DerivedCategory.quotientCompQhIso (Equivariant R r)).hom.app S.X₃.obj ≫
      DerivedCategory.triangleOfSESδ hS ≫
      (shiftFunctor (DerivedCategory (Equivariant R r)) (1 : ℤ)).map
        ((DerivedCategory.quotientCompQhIso (Equivariant R r)).inv.app S.X₁.obj) ≫
      (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app
        (DerivedCategory.Plus.Q.obj S.X₁))

/-- A triangulated localization of the specified signed total, with the canonical
connecting-arrow equation for every short exact sequence of bounded-below complexes.
Source: paragraph (3), DAG steps 4, 7 and 8
(blueprint: lem-sfb-lattice-koszul-total-triangles). -/
structure Descent (K : KoszulModel R r) where
  /-- The induced functor between the actual ordinary bounded-below derived categories. -/
  functor : DerivedCategory.Plus (Equivariant R r) ⥤ DerivedCategory.Plus (Modules R)
  /-- Its coherent integer shift comparison. -/
  [commShift : functor.CommShift ℤ]
  /-- Distinguished triangles are preserved. -/
  triangulated : functor.IsTriangulated
  /-- It localizes the actual total on bounded-below complexes. -/
  factor : CochainComplex.Plus.ι _ ⋙ total R r K ⋙ DerivedCategory.Q.{u + 2} ≅
    DerivedCategory.Plus.Q ⋙ functor ⋙ DerivedCategory.Plus.ι
  /-- The descended shifts are those with the already specified Koszul signs. -/
  factorShift : NatTrans.CommShift factor.hom ℤ
  /-- The canonical boundary, including its sign, is carried by this comparison. -/
  connecting : ∀ (S : ShortComplex (CochainComplex.Plus (Equivariant R r)))
    (hS : (S.map (CochainComplex.Plus.ι _)).ShortExact),
    (functor ⋙ DerivedCategory.Plus.ι).map (connectingPlus R r S hS) ≫
        ((functor ⋙ DerivedCategory.Plus.ι).commShiftIso (1 : ℤ)).hom.app
          (DerivedCategory.Plus.Q.obj S.X₁) ≫
        (shiftFunctor (DerivedCategory (Modules R)) (1 : ℤ)).map (factor.inv.app S.X₁) =
      factor.inv.app S.X₃ ≫ DerivedCategory.triangleOfSESδ
        (total_shortExact R r K (S.map (CochainComplex.Plus.ι _)) hS)

/-- Signed lattice Koszul totalization induces a triangulated D-plus functor carrying
canonical connecting arrows, with the coherent shifts and cone comparison above.
Source: current blueprint direct-image stability proof, paragraph (3), agent lattice
expansion; Stacks Tags 012Z, 011G, 014E, 0152
(blueprint: lem-sfb-lattice-koszul-total-triangles).

Proof, following the eight DAG steps:
1. Forgetting the action is exact. Koszul degree a is the finite sum over Subsets r a,
so terms_exact holds, and finite diagonal sums preserve termwise short exactness.
2. The bicomplex has commuting d_K and d_P. In d_K+(-1)^a d_P the mixed terms cancel.
The existing total is additive and preserves lower bounds, since 0 <= a <= r.
3. Multiply the vertical homotopy by (-1)^a; horizontal terms cancel and vertical
terms are the original homotopy equation. Thus the total acts on the homotopy category.
4. Exact-functor homology comparison makes each column map a quasi-isomorphism;
finite-column total comparison with bounds 0,r gives total_quasiIso. Localize.
5. The shift comparison in Koszul degree a is (-1)^(a*n). The horizontal chain equation
and multiplication of these scalars give the coherent integer shift comparisons.
6. On cones use identity on the target summands and (-1)^a on shifted source summands.
The cone chain equation proves this is an isomorphism, natural and compatible with
inclusion and projection, hence also with the signed last arrow -p.
7. Distinguished triangles are localized cone triangles up to isomorphism. Step 6
therefore shows that the localization, with step 5's shift comparison, is triangulated.
8. For a short exact sequence q=(j,0):Cone(i)->C is a quasi-isomorphism by
quasiIso_descShortComplex. Its canonical boundary is Q(-p) Q(q)^(-1). The cone
comparison satisfies q_K theta=K(q) and (-p_K)theta=c_1 K(-p). Invert q and q_K to
obtain exactly Descent.connecting, with no degreewise splitting choices. -/
theorem lattice_koszul_total_triangles (K : KoszulModel R r) :
    Nonempty (Descent R r K) := by
  sorry

end TotalTriangles
end Profinite.DiscreteLattice
