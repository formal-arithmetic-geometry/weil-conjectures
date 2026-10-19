/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G7
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.SiteDerivedConstantModuleFunctor
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Sheaf.CategoryTheory.PerfectConstantLocalLift

/-!
# Local null homotopies from bounded constant finite-projective complexes

Source: Stacks Project, Cohomology on Sites, Tags 08FN and 08FP(1).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

local instance constantAdditive (J : GrothendieckTopology C)
    (R : Type (max u v)) [CommRing R] :
    (siteConstantModuleFunctorGeneral J R).Additive :=
  (siteConstantModuleFunctorGeneral_exact J R).1

local instance overAdditive {J : GrothendieckTopology C}
    (S : Sheaf J RingCat.{max u v}) (U : C) :
    (SheafOfModules.overFunctor.{max u v} S U).Additive :=
  (ringedOverFunctor_exactGeneral S U).1

private structure AboveHomotopy
    {C : Type*} [Category C] [Preadditive C]
    {E F : CochainComplex C ℤ} (α : E ⟶ F) (k : ℤ) where
  h : Cochain E F (-1)
  comm : ∀ n : ℤ, k < n →
    α.f n = E.d n (n + 1) ≫ h.v (n + 1) n (by omega) +
      h.v n (n - 1) (by omega) ≫ F.d (n - 1) n

private def AboveHomotopy.map
    {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    {E F : CochainComplex C ℤ} {α : E ⟶ F} {k : ℤ}
    (H : AboveHomotopy α k) (R : C ⥤ D) [R.Additive] :
    AboveHomotopy ((R.mapHomologicalComplex (.up ℤ)).map α) k where
  h := H.h.map R
  comm n hn := by
    change R.map (α.f n) = _
    rw [H.comm n hn, R.map_add, R.map_comp, R.map_comp]
    simp only [Cochain.map_v]
    rfl

private def AboveHomotopy.ofNatIso
    {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    {E F : CochainComplex C ℤ} {α : E ⟶ F} {k : ℤ}
    {R S : C ⥤ D} [R.Additive] [S.Additive] (e : R ≅ S)
    (H : AboveHomotopy ((S.mapHomologicalComplex (.up ℤ)).map α) k) :
    AboveHomotopy ((R.mapHomologicalComplex (.up ℤ)).map α) k where
  h := Cochain.mk (fun n m hnm ↦
    e.hom.app (E.X n) ≫ H.h.v n m hnm ≫ e.inv.app (F.X m))
  comm n hn := by
    simp only [Cochain.mk_v]
    dsimp only [Functor.mapHomologicalComplex] at *
    have heq := H.comm n hn
    dsimp only [Functor.mapHomologicalComplex] at heq
    rw [← cancel_mono (e.hom.app (F.X n))]
    simp only [Preadditive.add_comp, Category.assoc]
    erw [e.hom.naturality (F.d (n - 1) n), e.inv_hom_id_app_assoc,
      e.inv_hom_id_app, Category.comp_id]
    erw [e.hom.naturality_assoc (E.d n (n + 1)), e.hom.naturality (α.f n)]
    rw [heq]
    simp only [Preadditive.comp_add]

private theorem AboveHomotopy.step
    {C : Type*} [Category C] [Preadditive C]
    {E F : CochainComplex C ℤ} {α : E ⟶ F} {k : ℤ}
    (H : AboveHomotopy α k) (t : E.X k ⟶ F.X (k - 1))
    (htd : t ≫ F.d (k - 1) k =
      α.f k - E.d k (k + 1) ≫ H.h.v (k + 1) k (by omega)) :
    Nonempty (AboveHomotopy α (k - 1)) := by
  classical
  let t' := t - H.h.v k (k - 1) (by omega)
  let hm := H.h + Cochain.single (K := E) (L := F) t' (-1)
  refine ⟨{ h := hm, comm := ?_ }⟩
  intro n hn
  by_cases he : n = k
  · subst n
    simp only [hm, Cochain.add_v,
      Cochain.single_v_eq_zero (K := E) (L := F) t' (-1) (k + 1) k (by omega) (by omega),
      add_zero, Cochain.single_v]
    dsimp only [t']
    have ht : H.h.v k (k - 1) (by omega) +
        (t - H.h.v k (k - 1) (by omega)) = t := by abel
    rw [ht, htd]
    abel
  · have hn' : k < n := by omega
    simpa only [hm, Cochain.add_v,
      Cochain.single_v_eq_zero (K := E) (L := F) t' (-1) (n + 1) n (by omega) (by omega),
      Cochain.single_v_eq_zero (K := E) (L := F) t' (-1) n (n - 1) (by omega) he,
      add_zero] using H.comm n hn'

private theorem cochain_comp_d_eq
    {C : Type*} [Category C] [Preadditive C]
    {E F : CochainComplex C ℤ} (h : Cochain E F (-1))
    (n m m' p : ℤ) (hm : n - 1 = m) (hm' : n - 1 = m') :
    h.v n m (by omega) ≫ F.d m p = h.v n m' (by omega) ≫ F.d m' p := by
  subst m
  subst m'
  rfl

private theorem homotopy_of_above
    {C : Type*} [Category C] [Preadditive C]
    {E F : CochainComplex C ℤ} (α : E ⟶ F) (a : ℤ)
    (hbelow : ∀ n : ℤ, n < a → IsZero (E.X n))
    (H : AboveHomotopy α (a - 1)) : Nonempty (Homotopy α 0) := by
  refine ⟨(Cochain.equivHomotopy α 0).symm ⟨H.h, ?_⟩⟩
  rw [Cochain.ofHom_zero, add_zero]
  ext n
  rw [δ_v (-1) 0 (by omega) H.h n n (by omega) (n - 1) (n + 1) (by omega) (by omega)]
  by_cases hn : a ≤ n
  · simpa only [Cochain.ofHom_v, Int.negOnePow_zero, one_smul, add_comm] using
      H.comm n (by omega)
  · exact (hbelow n (by omega)).eq_of_src _ _

section Induction

variable (J : Precoverage C) (hJ : J.IsSiteForCoverings)
  (R : Type (max u v)) [CommRing R]
  (F : CochainComplex (ModuleCat.{max u v} R) ℤ)
  [∀ q : ℤ, Module.Finite R (F.X q)] [∀ q : ℤ, Module.Projective R (F.X q)]

variable (K : CochainComplex (SheafOfModules.{max u v} ((constantSheaf J.toGrothendieck
  RingCat.{max u v}).obj (RingCat.of R))) ℤ)
  (hK : K.Acyclic) (α : (((siteConstantModuleFunctorGeneral J.toGrothendieck
    R).mapHomologicalComplex
    (.up ℤ)).obj F) ⟶ K)

local instance overLimits (U : C) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{max u v} ((constantSheaf J.toGrothendieck
      RingCat.{max u v}).obj (RingCat.of R)) U) :=
  (ringedOverFunctor_exactGeneral ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj
    (RingCat.of R)) U).2.1

local instance overColimits (U : C) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{max u v} ((constantSheaf
      J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)) U) :=
  (ringedOverFunctor_exactGeneral ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj
    (RingCat.of R)) U).2.2

local instance mapAdditive {U V : C} (f : V ⟶ U) :
    (SheafOfModules.overMap.{max u v} ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj
      (RingCat.of R)) f).Additive :=
  ⟨fun {_ _} a b ↦ by ext W x; rfl⟩

include hJ hK in
private theorem above_step (U : C) (k : ℤ)
    (H : AboveHomotopy
      (((SheafOfModules.overFunctor.{max u v} ((constantSheaf J.toGrothendieck RingCat.{max u
        v}).obj (RingCat.of R)) U).mapHomologicalComplex (.up ℤ)).map α) k) :
    ∃ Q ∈ J U, ∀ (V : C) (f : V ⟶ U), Q f →
      Nonempty (AboveHomotopy
        (((SheafOfModules.overFunctor.{max u v} ((constantSheaf J.toGrothendieck RingCat.{max u
          v}).obj (RingCat.of R)) V).mapHomologicalComplex (.up ℤ)).map α)
        (k - 1)) := by
  classical
  let TU := SheafOfModules.overFunctor.{max u v} ((constantSheaf J.toGrothendieck RingCat.{max u
    v}).obj (RingCat.of R)) U
  let EU := (TU.mapHomologicalComplex (.up ℤ)).obj (((siteConstantModuleFunctorGeneral
    J.toGrothendieck R).mapHomologicalComplex
    (.up ℤ)).obj F)
  let KU := (TU.mapHomologicalComplex (.up ℤ)).obj K
  let β := (TU.mapHomologicalComplex (.up ℤ)).map α
  let z := β.f k - EU.d k (k + 1) ≫ H.h.v (k + 1) k (by omega)
  have hz : z ≫ KU.d k (k + 1) = 0 := by
    dsimp only [z]
    rw [Preadditive.sub_comp, Category.assoc, β.comm k (k + 1)]
    have heq := H.comm (k + 1) (by omega)
    rw [cochain_comp_d_eq H.h (k + 1) (k + 1 - 1) k (k + 1) rfl (by omega)] at heq
    have heq' : H.h.v (k + 1) k (by omega) ≫ KU.d k (k + 1) =
        β.f (k + 1) - EU.d (k + 1) (k + 1 + 1) ≫
          H.h.v (k + 1 + 1) (k + 1) (by omega) := by
      exact eq_sub_iff_add_eq'.mpr heq.symm
    rw [heq', Preadditive.comp_sub, ← Category.assoc, EU.d_comp_d, zero_comp, sub_zero,
      sub_self]
  let a := KU.liftCycles z (k + 1) (by simp) hz
  have : Epi (KU.toCycles (k - 1) k) := ((hK.map TU) k).epi_toCycles _ (by simp)
  obtain ⟨Q, hQ, h⟩ := exists_perfect_constant_local_lift J hJ R (F.X k) U
    (KU.X (k - 1)) (KU.cycles k) (KU.toCycles (k - 1) k) a
  refine ⟨Q, hQ, ?_⟩
  intro V f hf
  obtain ⟨t, ht⟩ := h V f hf
  let T := SheafOfModules.overMap.{max u v} ((constantSheaf J.toGrothendieck RingCat.{max u
    v}).obj (RingCat.of R)) f
  let e := SheafOfModules.overFunctorMap.{max u v} ((constantSheaf J.toGrothendieck RingCat.{max
    u v}).obj (RingCat.of R)) f
  let t' := e.hom.app ((siteConstantModuleFunctorGeneral J.toGrothendieck R).obj (F.X k)) ≫ t
  have htd : t' ≫ T.map (KU.d (k - 1) k) = T.map z := by
    rw [← KU.toCycles_i (k - 1) k, T.map_comp]
    dsimp only [t']
    rw [Category.assoc, ← Category.assoc t, ht]
    dsimp only [e] at *
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    rw [← T.map_comp]
    exact congrArg T.map (KU.liftCycles_i z (k + 1) (by simp) hz)
  obtain ⟨Hnew⟩ := (H.map T).step t' (by
    simpa only [Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_map_f,
      AboveHomotopy.map, Cochain.map_v, z, T.map_sub, T.map_comp,
      EU, KU, β, TU] using htd)
  have Hcomp : AboveHomotopy
      ((((SheafOfModules.overFunctor.{max u v} ((constantSheaf J.toGrothendieck RingCat.{max u
        v}).obj (RingCat.of R)) U) ⋙ T).mapHomologicalComplex
        (.up ℤ)).map α) (k - 1) := Hnew
  exact ⟨AboveHomotopy.ofNatIso e.symm Hcomp⟩

include hJ hK in
private theorem above_iterate (U : C) (k : ℤ)
    (H : AboveHomotopy
      (((SheafOfModules.overFunctor.{max u v} ((constantSheaf J.toGrothendieck RingCat.{max u
        v}).obj (RingCat.of R)) U).mapHomologicalComplex (.up ℤ)).map α) k)
    (d : ℕ) :
    ∃ Q ∈ J U, ∀ (V : C) (f : V ⟶ U), Q f →
      Nonempty (AboveHomotopy
        (((SheafOfModules.overFunctor.{max u v} ((constantSheaf J.toGrothendieck RingCat.{max u
          v}).obj (RingCat.of R)) V).mapHomologicalComplex (.up ℤ)).map α)
        (k - (d : ℤ))) := by
  classical
  induction d with
  | zero =>
    have : J.HasIsos := hJ.1
    refine ⟨Presieve.singleton (𝟙 U), J.mem_coverings_of_isIso (𝟙 U), ?_⟩
    intro V f hf
    cases hf
    simpa only [Nat.cast_zero, sub_zero] using (show Nonempty (AboveHomotopy _ k) from ⟨H⟩)
  | succ d ih =>
    obtain ⟨Q, hQ, h⟩ := ih
    have hstep (V : C) (f : V ⟶ U) (hf : Q f) :=
      above_step J hJ R F K hK α V (k - (d : ℤ)) (h V f hf).some
    choose Q' hQ' h' using hstep
    refine ⟨Q.bind (fun _ f hf ↦ Q' _ f hf),
      hJ.2.1 U Q (fun _ f hf ↦ Q' _ f hf) hQ hQ', ?_⟩
    rintro V f ⟨W, g, f', hf', hg, hcomp⟩
    have hh := h' W f' hf' V g hg
    simpa only [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub] using hh

end Induction

/-- Maps from bounded constant finite-projective complexes to acyclic complexes
are locally null homotopic. No derived localization or target boundedness is needed.
Source: Stacks Project, Cohomology on Sites, Tags 08FN and 08FP(1)
(blueprint: lem-sfb-perfect-constant-local-null-homotopy).

Proof: The exact constant-module functor takes zero terms to zero. In each slice,
the degreewise local lifting theorem lifts maps from a constant finite-projective
term through any epimorphism. Its proof uses local lifts of a finite generating
family, projectivity for the surjection onto the sectionwise image, and the
universal property of constant-module sheafification. Slice restriction is exact.
Choose a finite interval [a,b] supporting F. Starting above b with zero homotopy
components, descend through b,...,a. At degree n the residual map is alpha^n
minus h^(n+1) d^n. The chain-map and previous homotopy equations show that its
composite with the target differential is zero. Factor it through the cycle
object. Acyclicity makes the preceding differential onto that cycle object epic.
The preceding local lifting construction gives h^n after refining the current
covering. Previously obtained equations survive restriction. The finite sequence
of coverings composes by the site transitivity axiom. Outside [a,b] the source
terms are zero, so all remaining homotopy equations hold automatically. Empty
coverings, zero ranks, the zero complex, and the zero ring are allowed. -/
theorem exists_perfect_constant_local_null_homotopy
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (X : C) (R : Type (max u v)) [CommRing R]
    (F : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hbounded : ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q → IsZero (F.X q))
    [∀ q : ℤ, Module.Finite R (F.X q)]
    [∀ q : ℤ, Module.Projective R (F.X q)]
    (K : CochainComplex (SheafOfModules.{max u v}
      ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R))) ℤ)
    (hK : K.Acyclic)
    (α : ((siteConstantModuleFunctorGeneral J.toGrothendieck R).mapHomologicalComplex
      (.up ℤ)).obj F ⟶ K) :
    ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i : I, U i ⟶ X),
      Presieve.ofArrows U f ∈ J X ∧
      ∀ i : I, Nonempty (Homotopy
        (((SheafOfModules.overFunctor.{max u v}
          ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R))
          (U i)).mapHomologicalComplex (.up ℤ)).map α) 0) := by
  classical
  let S := (constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)
  let T := SheafOfModules.overFunctor.{max u v} S X
  let E := ((siteConstantModuleFunctorGeneral J.toGrothendieck R).mapHomologicalComplex
    (.up ℤ)).obj F
  obtain ⟨a, b, hab, hb⟩ := hbounded
  have hE (q : ℤ) (hq : q < a ∨ b < q) : IsZero (E.X q) :=
    (siteConstantModuleFunctorGeneral J.toGrothendieck R).map_isZero (hb q hq)
  let H : AboveHomotopy ((T.mapHomologicalComplex (.up ℤ)).map α) b :=
    { h := 0
      comm := fun n hn ↦ (T.map_isZero (hE n (Or.inr hn))).eq_of_src _ _ }
  obtain ⟨Q, hQ, h⟩ := above_iterate J hJ R F K hK α X b H (b - a + 1).toNat
  obtain ⟨I, U, f, rfl⟩ := Q.exists_eq_ofArrows
  refine ⟨I, U, f, hQ, ?_⟩
  intro i
  let Ti := SheafOfModules.overFunctor.{max u v} S (U i)
  obtain ⟨Hi⟩ := h (U i) (f i) (Presieve.ofArrows.mk i)
  have Hfull : AboveHomotopy ((Ti.mapHomologicalComplex (.up ℤ)).map α) (a - 1) :=
    { h := Hi.h
      comm := fun n hn ↦ Hi.comm n (by omega) }
  exact homotopy_of_above _ a (fun n hn ↦ Ti.map_isZero (hE n (Or.inl hn))) Hfull

end CategoryTheory
