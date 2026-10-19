/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.AlgebraicGeometry.IdealPowerComplement
import all Sheaf.AlgebraicGeometry.IdealPowerEvaluationAffineEventuallyZero
import all WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.Topology.GlueSheavesOfModules
import Sheaf.AlgebraicGeometry.IdealPowerAnnihilatorSystem
import Sheaf.AlgebraicGeometry.IdealPowerQuotientLocalLifting
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.Paper.DerivedHomMayerVietoris

/-! # Sections over the complement of a finite type ideal

Source: Stacks Project, Properties, Lemma 01PQ
(blueprint: lem-weil-pbc-sections-over-quasi-compact-open).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem power_mono {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι] :
    ∀ n : ℕ, Mono (idealSheafPower ι n).2 := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => dsimp [idealSheafPower]; infer_instance
  | one => exact inferInstanceAs (Mono ι)
  | more n _ ih =>
    let := ih
    let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    change Mono (idealModuleProductι ι (idealSheafPower ι (n + 1)).1 ≫
      (idealSheafPower ι (n + 1)).2)
    dsimp [idealModuleProductι]
    infer_instance

private theorem power_factor {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) {n m : ℕ} (h : n ≤ m) :
    ∃ r : (idealSheafPower ι m).1 ⟶ (idealSheafPower ι n).1,
      r ≫ (idealSheafPower ι n).2 = (idealSheafPower ι m).2 := by
  have hs (k : ℕ) :
      ∃ r : (idealSheafPower ι (k + 1)).1 ⟶ (idealSheafPower ι k).1,
        r ≫ (idealSheafPower ι k).2 = (idealSheafPower ι (k + 1)).2 := by
    cases k with
    | zero => exact ⟨ι, Category.comp_id _⟩
    | succ k => exact ⟨idealModuleProductι ι _, rfl⟩
  induction h with
  | refl => exact ⟨𝟙 _, Category.id_comp _⟩
  | @step m h ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨t, ht⟩ := hs m
    exact ⟨t ≫ r, by rw [Category.assoc, hr, ht]⟩

private noncomputable def homDiagram {X : Scheme.{u}} (P Q : ℕ → X.Modules)
    (r : ∀ (n m : ℕ), n ≤ m → (P m ⟶ P n))
    (q : ∀ (n m : ℕ), n ≤ m → (Q n ⟶ Q m))
    (rid : ∀ n, r n n le_rfl = 𝟙 _)
    (qid : ∀ n, q n n le_rfl = 𝟙 _)
    (rcomp : ∀ n m k (h : n ≤ m) (h' : m ≤ k),
      r m k h' ≫ r n m h = r n k (h.trans h'))
    (qcomp : ∀ n m k (h : n ≤ m) (h' : m ≤ k),
      q n m h ≫ q m k h' = q n k (h.trans h')) : ℕ ⥤ AddCommGrpCat.{u} where
  obj n := AddCommGrpCat.of (P n ⟶ Q n)
  map {n m} f := AddCommGrpCat.ofHom
    { toFun := fun φ ↦ r n m (leOfHom f) ≫ φ ≫ q n m (leOfHom f)
      map_zero' := by simp
      map_add' := by intros; simp only [Preadditive.comp_add, Preadditive.add_comp] }
  map_id n := by ext φ; simp [rid, qid]
  map_comp {n m k} f g := by
    ext φ
    dsimp
    rw [← rcomp n m k (leOfHom f) (leOfHom g),
      ← qcomp n m k (leOfHom f) (leOfHom g)]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem colimit_eval_injective (D : ℕ ⥤ AddCommGrpCat.{u})
    (G : AddCommGrpCat.{u}) (c : D ⟶ (Functor.const ℕ).obj G)
    (hz : ∀ n (x : D.obj n), c.app n x = 0 →
      ∃ (m : ℕ) (f : n ⟶ m), D.map f x = 0) :
    Function.Injective (colimit.desc D ⟨G, c⟩) := by
  let : PreservesFilteredColimitsOfSize.{0, 0} (CategoryTheory.forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  apply (injective_iff_map_eq_zero (colimit.desc D ⟨G, c⟩).hom).2
  intro x hx
  obtain ⟨n, x, rfl⟩ := Concrete.colimit_exists_rep D x
  have hcx : c.app n x = 0 := by
    change (c.app n).hom x = (0 : G)
    exact (ConcreteCategory.congr_hom (colimit.ι_desc (F := D) ⟨G, c⟩ n) x).symm.trans hx
  obtain ⟨m, f, hf⟩ := hz n x hcx
  calc
    colimit.ι D n x = colimit.ι D m (D.map f x) := by
      exact (ConcreteCategory.congr_hom (colimit.w D f) x).symm
    _ = 0 := by rw [hf]; exact map_zero _

set_option backward.isDefEq.respectTransparency false in
/-- Sections over the complement of a finite type quasi-coherent ideal on a quasi-compact
scheme. The open `U` is specified by surjectivity of the stalk inclusion, equivalently
by the stalk ideal being the whole local ring. The diagrams are identified with their
Hom groups by `e` and `e'`; their maps are exactly precomposition by the inclusions of
powers, and, in the quotient case, postcomposition by the induced quotient maps.
The cocones take a homomorphism to its value on the section `one n` above `1` on `U`.
In the quotient case this value is transported back through the quotient map on `U`.
The annihilator subsheaves are specified on every open, including all smaller opens.
Source: Stacks Project, Properties, Lemma 01PQ
(blueprint: lem-weil-pbc-sections-over-quasi-compact-open).

Proof:
1. By lem-weil-pbc-ideal-times-quasi-coherent-affine-sections, the powers are
quasi-coherent finite type ideals, with affine sections I^n. By
lem-weil-pbc-quasi-coherent-ideal-zero-set-affine, the complement of their zero set is U.
On opens inside U the ideal contains 1, so equals the whole structure sheaf.
2. The affine tilde/Gamma adjunction and lem-weil-pbc-spec-module-tilde-sections identify
Hom of quasi-coherent modules with Hom of their affine sections, compatibly with
composition and restriction (lem-weil-pbc-affine-tilde-gamma-adjunction).
3. Evaluation at 1 commutes with restriction along powers. On D(f) it is phi(f^n)/f^n,
so agrees with the map of lem-weil-pbc-sections-over-quasi-compact-open-in-affine.
4. Cover X by finitely many affine opens. If evaluation is zero, the affine injectivity
and lem-weil-pbc-filtered-colimit-modules-elementwise give a power on which the map
vanishes on each open. Take the maximum exponent and use uniqueness of gluing
(lem-weil-pbc-glue-sheaves-of-modules) to get global vanishing and injectivity.
5. Form the annihilator subsheaves by lem-weil-pbc-sections-annihilated-by-ideal. They
increase and vanish on U. Their cokernels are quasi-coherent by
lem-weil-pbc-quasi-coherent-module-cokernel-image. Restriction preserves cokernels
(lem-weil-pbc-module-restriction-open-immersion-colimits), so the quotient maps are
isomorphisms on U; the quotient transition maps commute with evaluation there.
6. On each affine open the second comparison is the affine bijection, by the Hom
identification and the formula phi(f^n)/f^n in the quotient, transported back on D(f).
7. The same finite-cover argument proves injectivity for this second comparison.
8. Under quasi-separatedness choose a finite affine cover with quasi-compact overlaps
(lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings). Lift a section on each affine open
using the affine bijection. Cover the overlaps by finitely many affines; equality in
their colimits gives a common exponent where all lifts agree. Take the maximum and
glue by lem-weil-pbc-glue-sheaves-of-modules. This proves surjectivity. -/
theorem sections_over_quasiCompact_open {X : Scheme.{u}} [CompactSpace X]
    {I : X.Modules} (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType] (F : X.Modules) [F.IsQuasicoherent] :
    ∃ (U : X.Opens)
      (one : ∀ n : ℕ, Γ((idealSheafPower ι n).1, U))
      (r : ∀ (n m : ℕ), n ≤ m →
        ((idealSheafPower ι m).1 ⟶ (idealSheafPower ι n).1)),
      (∀ x : X, x ∈ U ↔ Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom) ∧
      (∀ n : ℕ, Mono (idealSheafPower ι n).2) ∧
      (∀ (n : ℕ) (W : X.Opens), W ≤ U →
        Function.Bijective ((idealSheafPower ι n).2.app W)) ∧
      (∀ n : ℕ, (idealSheafPower ι n).2.app U (one n) = (1 : Γ(X, U))) ∧
      (∀ (n m : ℕ) (h : n ≤ m),
        r n m h ≫ (idealSheafPower ι n).2 = (idealSheafPower ι m).2) ∧
      (∃ (D : ℕ ⥤ AddCommGrpCat.{u})
        (e : ∀ n : ℕ, D.obj n ≅ AddCommGrpCat.of ((idealSheafPower ι n).1 ⟶ F))
        (c : D ⟶ (Functor.const ℕ).obj Γ(F, U)),
        (∀ (n m : ℕ) (h : n ≤ m) (φ : (idealSheafPower ι n).1 ⟶ F),
          (e m).hom (D.map (homOfLE h) ((e n).inv φ)) = r n m h ≫ φ) ∧
        (∀ (n : ℕ) (φ : (idealSheafPower ι n).1 ⟶ F),
          c.app n ((e n).inv φ) = φ.app U (one n)) ∧
        Function.Injective (colimit.desc D ⟨Γ(F, U), c⟩)) ∧
      (QuasiSeparatedSpace X →
        ∃ (A : ℕ → X.Modules) (a : ∀ n : ℕ, A n ⟶ F),
          (∀ n : ℕ, Mono (a n)) ∧
          (∀ (n : ℕ) (W : X.Opens) (s : Γ(F, W)),
            s ∈ Set.range ((a n).app W) ↔
              ∀ (W' : X.Opens) (h : W' ≤ W)
                (b : Γ((idealSheafPower ι n).1, W')),
                (F.smul (U := W') ((idealSheafPower ι n).2.val.app (op W') b)).hom
                  (F.presheaf.map (homOfLE h).op s) = 0) ∧
          (∀ (n m : ℕ), n ≤ m → ∃ t : A n ⟶ A m, t ≫ a m = a n) ∧
          (∀ (n : ℕ) (W : X.Opens), W ≤ U → Subsingleton Γ(A n, W)) ∧
          (∀ n : ℕ,
            IsIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map (cokernel.π (a n)))) ∧
          (∀ (n : ℕ) (W : X.Opens), W ≤ U →
            Function.Bijective ((cokernel.π (a n)).app W)) ∧
          ∃ (q : ∀ (n m : ℕ), n ≤ m → (cokernel (a n) ⟶ cokernel (a m)))
            (D' : ℕ ⥤ AddCommGrpCat.{u})
            (e' : ∀ n : ℕ, D'.obj n ≅
              AddCommGrpCat.of ((idealSheafPower ι n).1 ⟶ cokernel (a n)))
            (c' : D' ⟶ (Functor.const ℕ).obj Γ(F, U)),
            (∀ (n m : ℕ) (h : n ≤ m), cokernel.π (a n) ≫ q n m h = cokernel.π (a m)) ∧
            (∀ (n m : ℕ) (h : n ≤ m)
              (φ : (idealSheafPower ι n).1 ⟶ cokernel (a n)),
              (e' m).hom (D'.map (homOfLE h) ((e' n).inv φ)) = r n m h ≫ φ ≫ q n m h) ∧
            (∀ (n : ℕ) (φ : (idealSheafPower ι n).1 ⟶ cokernel (a n)),
              (cokernel.π (a n)).app U (c'.app n ((e' n).inv φ)) = φ.app U (one n)) ∧
            Function.Bijective (colimit.desc D' ⟨Γ(F, U), c'⟩)) := by
  classical
  -- Recover affine eventual vanishing from the surviving radical and range helpers.
  have affine_evaluation_zero
      {X : Scheme.{u}} {I : X.Modules}
      (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
      [I.IsQuasicoherent] [I.IsFiniteType]
      (F : X.Modules) [F.IsQuasicoherent]
      (U : X.Opens) (one : ∀ n : ℕ, Γ((idealSheafPower ι n).1, U))
      (r : ∀ (n m : ℕ), n ≤ m →
        ((idealSheafPower ι m).1 ⟶ (idealSheafPower ι n).1))
      (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom)
      (hone : ∀ n : ℕ, (idealSheafPower ι n).2.app U (one n) = (1 : Γ(X, U)))
      (hr : ∀ (n m : ℕ) (h : n ≤ m),
        r n m h ≫ (idealSheafPower ι n).2 = (idealSheafPower ι m).2) :
      ∀ (V : X.affineOpens) (n : ℕ) (φ : (idealSheafPower ι n).1 ⟶ F),
        φ.app U (one n) = 0 →
        ∃ (m : ℕ) (h : n ≤ m), (r n m h ≫ φ).over V.1 = 0 := by
    intro V n φ hφ
    let J : Ideal Γ(X, V.1) := LinearMap.range (ι.val.app (op V.1)).hom
    let ψ := (φ.val.app (op V.1)).hom
    obtain ⟨hfg, hrad⟩ :=
      ideal_power_evaluation_affine_radical ι F U n (one n) hU (hone n) V φ hφ
    obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hfg
    have hnm : n ≤ n + k := Nat.le_add_right n k
    have hrange : LinearMap.range ((r n (n + k) hnm).val.app (op V.1)).hom ≤
        J ^ k • (⊤ : Submodule Γ(X, V.1) Γ((idealSheafPower ι n).1, V.1)) := by
      intro t ht
      obtain ⟨s, rfl⟩ := ht
      let j := ((idealSheafPower ι n).2.val.app (op V.1)).hom
      have hinj := formalPolynomial_power_injective ι n V.1
      have hmap : Submodule.map j
          (J ^ k • (⊤ : Submodule Γ(X, V.1) Γ((idealSheafPower ι n).1, V.1))) =
          J ^ (n + k) := by
        rw [Submodule.map_smul'', Submodule.map_top, powers_range ι V n,
          Ideal.smul_eq_mul, ← pow_add, Nat.add_comm k n]
      have hmem : j (((r n (n + k) hnm).val.app (op V.1)).hom s) ∈ J ^ (n + k) := by
        have he := congrArg (fun f ↦ f.app V.1 s) (hr n (n + k) hnm)
        change (r n (n + k) hnm ≫ (idealSheafPower ι n).2).app V.1 s ∈ _
        rw [he]
        exact powers_range ι V (n + k) ▸ LinearMap.mem_range_self _ s
      rw [← hmap] at hmem
      obtain ⟨t, ht, he⟩ := hmem
      exact hinj he ▸ ht
    have hzero : ∀ s : Γ((idealSheafPower ι (n + k)).1, V.1),
        (r n (n + k) hnm ≫ φ).app V.1 s = 0 := by
      intro s
      have hmem := hrange (LinearMap.mem_range_self
        ((r n (n + k) hnm).val.app (op V.1)).hom s)
      have hker : J ^ k • (⊤ : Submodule Γ(X, V.1)
          Γ((idealSheafPower ι n).1, V.1)) ≤ LinearMap.ker ψ := by
        apply Submodule.smul_le.mpr
        intro a ha t _
        change ψ (a • t) = 0
        rw [map_smul]
        exact Submodule.mem_annihilator.mp (hk ha) _ (LinearMap.mem_range_self ψ t)
      exact hker hmem
    have := Modules.powers_qc ι (n + k)
    exact ⟨n + k, hnm, affine_hom_zero V _ hzero⟩
  -- A finite affine cover turns the local vanishing exponents into one global exponent.
  have evaluation_zero
      {X : Scheme.{u}} {I : X.Modules}
      (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
      [I.IsQuasicoherent] [I.IsFiniteType] [CompactSpace X]
      (F : X.Modules) [F.IsQuasicoherent]
      (U : X.Opens) (one : ∀ n : ℕ, Γ((idealSheafPower ι n).1, U))
      (r : ∀ (n m : ℕ), n ≤ m →
        ((idealSheafPower ι m).1 ⟶ (idealSheafPower ι n).1))
      (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom)
      (hone : ∀ n : ℕ, (idealSheafPower ι n).2.app U (one n) = (1 : Γ(X, U)))
      (hr : ∀ (n m : ℕ) (h : n ≤ m),
        r n m h ≫ (idealSheafPower ι n).2 = (idealSheafPower ι m).2) :
      ∀ (n : ℕ) (φ : (idealSheafPower ι n).1 ⟶ F),
        φ.app U (one n) = 0 →
        ∃ (m : ℕ) (h : n ≤ m), r n m h ≫ φ = 0 := by
    classical
    intro n φ hφ
    obtain ⟨S, hfin, hcover⟩ :=
      isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
        ⟨isCompact_univ (X := X), isOpen_univ⟩
    have hcover' : (⨆ V : S, V.1.1) = ⊤ := by
      ext x
      simpa using (Set.ext_iff.mp hcover x).symm
    have hlocal (V : S) :=
      affine_evaluation_zero ι F U one r hU hone hr V.1 n φ hφ
    choose k hk hzero using hlocal
    have := hfin.to_subtype
    let := Fintype.ofFinite S
    let m := max n (Finset.univ.sup k)
    have hnm : n ≤ m := le_max_left _ _
    refine ⟨m, hnm, ?_⟩
    apply (glue_sheaves_of_modules X.toRingedSpace S (fun V ↦ V.1.1) hcover').2.1
    intro V
    have hkm : k V ≤ m := (Finset.le_sup (Finset.mem_univ V)).trans (le_max_right _ _)
    have : Mono (idealSheafPower ι n).2 := formalPolynomial_power_mono ι n
    have hcomp : r (k V) m hkm ≫ r n (k V) (hk V) = r n m hnm := by
      apply (cancel_mono (idealSheafPower ι n).2).mp
      rw [Category.assoc, hr, hr, hr]
    have hz : (r n m hnm ≫ φ).over V.1.1 = 0 := by
      rw [← hcomp, Category.assoc]
      change (SheafOfModules.overFunctor X.ringCatSheaf V.1.1).map
        (r (k V) m hkm ≫ (r n (k V) (hk V) ≫ φ)) = 0
      rw [Functor.map_comp]
      change (r (k V) m hkm).over V.1.1 ≫
        (r n (k V) (hk V) ≫ φ).over V.1.1 = 0
      rw [hzero V, comp_zero]
    simpa using hz
  -- Construct the geometric data, then both Hom diagrams and their evaluation cocones.
  obtain ⟨U, hU, hbij⟩ := ideal_power_complement ι
  have hmono (n : ℕ) : Mono (idealSheafPower ι n).2 := power_mono ι n
  choose one hone using fun n ↦ (hbij n U le_rfl).2 (1 : Γ(X, U))
  let r : ∀ (n m : ℕ), n ≤ m → ((idealSheafPower ι m).1 ⟶ (idealSheafPower ι n).1) :=
    fun n m h ↦ (power_factor ι h).choose
  have hr : ∀ (n m : ℕ) (h : n ≤ m),
      r n m h ≫ (idealSheafPower ι n).2 = (idealSheafPower ι m).2 :=
    fun n m h ↦ (power_factor ι h).choose_spec
  have rid (n : ℕ) : r n n le_rfl = 𝟙 _ := by
    have := hmono n
    apply (cancel_mono (idealSheafPower ι n).2).mp
    rw [hr n n le_rfl, Category.id_comp]
  have rcomp (n m k : ℕ) (h : n ≤ m) (h' : m ≤ k) :
      r m k h' ≫ r n m h = r n k (h.trans h') := by
    have := hmono n
    apply (cancel_mono (idealSheafPower ι n).2).mp
    rw [Category.assoc, hr n m h, hr m k h', hr n k (h.trans h')]
  have rone (n m : ℕ) (h : n ≤ m) : (r n m h).app U (one m) = one n := by
    apply (hbij n U le_rfl).1
    have he := congrArg (fun f ↦ f.app U (one m)) (hr n m h)
    exact he.trans ((hone m).trans (hone n).symm)
  let D := homDiagram (fun n ↦ (idealSheafPower ι n).1) (fun _ ↦ F) r
    (fun _ _ _ ↦ 𝟙 F) rid (fun _ ↦ rfl) rcomp (by intros; simp)
  let e (n : ℕ) : D.obj n ≅ AddCommGrpCat.of ((idealSheafPower ι n).1 ⟶ F) := Iso.refl _
  let ev (n : ℕ) : ((idealSheafPower ι n).1 ⟶ F) →+ Γ(F, U) :=
    { toFun := fun φ ↦ φ.app U (one n)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  let c : D ⟶ (Functor.const ℕ).obj Γ(F, U) :=
    { app := fun n ↦ AddCommGrpCat.ofHom (ev n)
      naturality := by
        intro n m f
        ext φ
        change (r n m (leOfHom f) ≫ φ ≫ 𝟙 F).app U (one m) = φ.app U (one n)
        simp only [Category.comp_id]
        change φ.app U ((r n m (leOfHom f)).app U (one m)) = _
        rw [rone n m (leOfHom f)] }
  have hinj : Function.Injective (colimit.desc D ⟨Γ(F, U), c⟩) := by
    apply colimit_eval_injective
    intro n φ hφ
    obtain ⟨m, h, hm⟩ := evaluation_zero ι F U one r hU hone hr n φ hφ
    refine ⟨m, homOfLE h, ?_⟩
    change r n m h ≫ φ ≫ 𝟙 F = 0
    simpa using hm
  refine ⟨U, one, r, hU, hmono, hbij, hone, hr, ⟨D, e, c, ?_, ?_, hinj⟩, ?_⟩
  · intro n m h φ
    change r n m h ≫ φ ≫ 𝟙 F = r n m h ≫ φ
    simp only [Category.comp_id]
  · intros
    rfl
  · intro hqs
    have := hqs
    obtain ⟨A, a, hamono, haqc, hann, hainc, hazero, haiso, hquot⟩ :=
      ideal_power_annihilator_system ι F U hbij
    choose t ht using hainc
    let q : ∀ (n m : ℕ), n ≤ m → (cokernel (a n) ⟶ cokernel (a m)) :=
      fun n m h ↦ cokernel.desc (a n) (cokernel.π (a m)) (by
        rw [← ht n m h, Category.assoc, cokernel.condition, comp_zero])
    have hq (n m : ℕ) (h : n ≤ m) :
        cokernel.π (a n) ≫ q n m h = cokernel.π (a m) := cokernel.π_desc _ _ _
    have qid (n : ℕ) : q n n le_rfl = 𝟙 _ := by
      apply (cancel_epi (cokernel.π (a n))).mp
      rw [hq n n le_rfl, Category.comp_id]
    have qcomp (n m k : ℕ) (h : n ≤ m) (h' : m ≤ k) :
        q n m h ≫ q m k h' = q n k (h.trans h') := by
      apply (cancel_epi (cokernel.π (a n))).mp
      rw [← Category.assoc, hq n m h, hq m k h', hq n k (h.trans h')]
    let D' := homDiagram (fun n ↦ (idealSheafPower ι n).1)
      (fun n ↦ cokernel (a n)) r q rid qid rcomp qcomp
    let e' (n : ℕ) : D'.obj n ≅
        AddCommGrpCat.of ((idealSheafPower ι n).1 ⟶ cokernel (a n)) := Iso.refl _
    let eqv (n : ℕ) : Γ(F, U) ≃+ Γ(cokernel (a n), U) :=
      AddEquiv.ofBijective ((cokernel.π (a n)).app U).hom (hquot n U le_rfl)
    let ev' (n : ℕ) : ((idealSheafPower ι n).1 ⟶ cokernel (a n)) →+ Γ(F, U) :=
      eqv n |>.symm.toAddMonoidHom.comp
        { toFun := fun φ ↦ φ.app U (one n)
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
    have heval (n : ℕ) (φ : (idealSheafPower ι n).1 ⟶ cokernel (a n)) :
        (cokernel.π (a n)).app U (ev' n φ) = φ.app U (one n) :=
      (eqv n).apply_symm_apply _
    let c' : D' ⟶ (Functor.const ℕ).obj Γ(F, U) :=
      { app := fun n ↦ AddCommGrpCat.ofHom (ev' n)
        naturality := by
          intro n m f
          ext φ
          change ev' m (r n m (leOfHom f) ≫ φ ≫ q n m (leOfHom f)) = ev' n φ
          apply (hquot m U le_rfl).1
          rw [heval]
          have he := congrArg (fun g ↦ g.app U (ev' n φ)) (hq n m (leOfHom f))
          change (q n m (leOfHom f)).app U
            ((cokernel.π (a n)).app U (ev' n φ)) =
            (cokernel.π (a m)).app U (ev' n φ) at he
          rw [heval] at he
          rw [← he]
          change (q n m (leOfHom f)).app U
            (φ.app U ((r n m (leOfHom f)).app U (one m))) = _
          rw [rone n m (leOfHom f)] }
    obtain ⟨hz, hsurj⟩ := ideal_power_quotient_local_lifting
      ι F U one r hU hone hr A a hamono haqc hann hquot q hq
    have hinj' : Function.Injective (colimit.desc D' ⟨Γ(F, U), c'⟩) := by
      apply colimit_eval_injective
      intro n φ hφ
      have hv : φ.app U (one n) = 0 := by
        rw [← heval]
        change (cokernel.π (a n)).app U (c'.app n φ) = 0
        rw [hφ, map_zero]
      obtain ⟨m, h, hm⟩ := hz n φ hv
      exact ⟨m, homOfLE h, hm⟩
    have hsurj' : Function.Surjective (colimit.desc D' ⟨Γ(F, U), c'⟩) := by
      intro s
      obtain ⟨n, φ, hφ⟩ := hsurj s
      refine ⟨colimit.ι D' n φ, ?_⟩
      have he := ConcreteCategory.congr_hom (colimit.ι_desc (F := D') ⟨Γ(F, U), c'⟩ n) φ
      change (colimit.desc D' ⟨Γ(F, U), c'⟩) (colimit.ι D' n φ) = ev' n φ at he
      rw [he]
      apply (hquot n U le_rfl).1
      rw [heval, hφ]
    refine ⟨A, a, hamono, hann, (fun n m h ↦ ⟨t n m h, ht n m h⟩), hazero, haiso, hquot,
      q, D', e', c', hq, ?_, ?_, hinj', hsurj'⟩
    · intros
      rfl
    · exact heval

end AlgebraicGeometry.Scheme
