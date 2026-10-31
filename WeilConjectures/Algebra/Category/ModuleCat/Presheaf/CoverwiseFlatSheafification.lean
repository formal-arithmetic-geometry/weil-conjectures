/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.RingHom.Flat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Coverwise flatness and module sheafification

Source: Stacks Project, Modules on Sites, Tag 0GN1, lemma-flatness-sheafification-refined
(blueprint: lem-fd-coverwise-flat-presheaf-sheafification).

A locally bijective map from the ring presheaf to a sheaf presents its associated ring
sheaf. Module sheafification along this map is the associated abelian sheaf with its
induced module structure. Site and coefficient universes are independent.
-/

@[expose] public section

universe c v r

open CategoryTheory

namespace PresheafOfModules

set_option autoImplicit false

/-- Coverwise sectionwise flatness implies flatness after module sheafification.

Source: Stacks Project, `sites-modules.tex`, Tag 0GN1, lemma-flatness-sheafification-refined
(blueprint: lem-fd-coverwise-flat-presheaf-sheafification).

Proof:
1. By [lem-exc-site-local-relations-imply-flat] (Stacks Tag 08FC) it suffices to factor
   every finite relation `∑ a_p s_p = 0` in F^# locally. Let T be the sieve of arrows
   along which the restricted relation factors as `s_p = ∑ b_pq t_q` with
   `∑ a_p b_pq = 0`; semilinearity of the restrictions makes T a sieve.
2. α and the sheafification unit are locally surjective. On the intersection of the image
   sieves of the finitely many a_p and s_p, choose lifts a0_p in O and x0_p in F. By
   linearity of the unit, `∑ a0_p x0_p` maps to zero, so by local injectivity of the unit
   it vanishes on a further equalizer covering.
3. Refine by the covering of hflat. On its members F has flat sections, and the ordinary
   equational criterion of flatness [def-weil-pbc-flat-ring-map]
   (`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`) factors the lifted relation.
   Mapping the coefficients through α and the witnesses through the unit gives the two
   identities of T. Covering transitivity shows that T covers, and step 1 concludes.
-/
theorem isFlat_sheafification_of_coverwise_flat
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    (O : Cᵒᵖ ⥤ CommRingCat.{r}) (R : Sheaf J CommRingCat.{r})
    (α : O ⋙ forget₂ CommRingCat.{r} RingCat.{r} ⟶
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    (F : PresheafOfModules.{r} (O ⋙ forget₂ CommRingCat.{r} RingCat.{r}))
    (hflat : ∀ X : C, ∃ (I : Type (max c v)) (V : I → C) (f : ∀ i, V i ⟶ X),
      Sieve.generate (Presieve.ofArrows V f) ∈ J X ∧
        ∀ i, Module.Flat (O.obj (Opposite.op (V i))) (F.obj (Opposite.op (V i)))) :
    SheafOfModules.IsFlatOnSite (R := R)
      ((PresheafOfModules.sheafification α).obj F) := by
  classical
  let M := (sheafification α).obj F
  apply SheafOfModules.isFlatOnSite_of_local_equationalCriterion R M
  intro U n a s hs
  let η := (sheafificationAdjunction α).unit.app F
  let ηu := (toPresheaf _).map η
  let e (X : Cᵒᵖ) : F.obj X →+ M.val.obj X :=
    AddMonoidHom.mk' (fun x ↦ η.app X x) (fun x y ↦ (η.app X).hom.map_add x y)
  let m {X Y : Cᵒᵖ} (g : X ⟶ Y) : M.val.obj X →+ M.val.obj Y :=
    AddMonoidHom.mk' (fun x ↦ M.val.map g x) (fun x y ↦ (M.val.map g).hom.map_add x y)
  let d {X Y : Cᵒᵖ} (g : X ⟶ Y) : F.obj X →+ F.obj Y :=
    AddMonoidHom.mk' (fun x ↦ F.map g x) (fun x y ↦ (F.map g).hom.map_add x y)
  have enat {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : F.obj X) :
      e Y (d g x) = m g (e X x) := naturality_apply η g x
  have esmul (X : Cᵒᵖ) (a : O.obj X) (x : F.obj X) :
      e X (a • x) = α.app X a • e X x := (η.app X).hom.map_smul a x
  have msmul {X Y : Cᵒᵖ} (g : X ⟶ Y) (a : R.obj.obj X)
      (x : M.val.obj X) : m g (a • x) = R.obj.map g a • m g x :=
    M.val.map_smul g a x
  have dsmul {X Y : Cᵒᵖ} (g : X ⟶ Y)
      (a : (O ⋙ forget₂ CommRingCat RingCat).obj X) (x : F.obj X) :
      d g (a • x) = ((O ⋙ forget₂ CommRingCat RingCat).map g) a • d g x :=
    F.map_smul g a x
  have mcomp {X Y Z : Cᵒᵖ} (g : X ⟶ Y) (h : Y ⟶ Z) (x : M.val.obj X) :
      m (g ≫ h) x = m h (m g x) := M.val.map_comp_apply g h x
  have hηs : Presheaf.IsLocallySurjective J ηu := by
    change Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J F.presheaf)
    infer_instance
  have hηi : Presheaf.IsLocallyInjective J ηu := by
    change Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J F.presheaf)
    infer_instance
  let T : Sieve U :=
    { arrows := fun V f ↦
        ∃ (l : ℕ) (b : Fin n → Fin l → R.obj.obj (Opposite.op V))
          (t : Fin l → M.val.obj (Opposite.op V)),
          (∀ p, m f.op (s p) = ∑ q, b p q • t q) ∧
          (∀ q, ∑ p, R.obj.map f.op (a p) * b p q = 0)
      downward_closed := by
        rintro V W f ⟨l, b, t, ht, hb⟩ g
        refine ⟨l, (fun p q ↦ R.obj.map g.op (b p q)),
          (fun q ↦ m g.op (t q)), ?_, ?_⟩
        · intro p
          have hh := congrArg (m g.op) (ht p)
          simpa only [op_comp, mcomp, map_sum, msmul] using hh
        · intro q
          have hh := congrArg (R.obj.map g.op) (hb q)
          simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
            map_sum, map_mul, map_zero] using hh }
  refine ⟨T, ?_, fun V f hf ↦ hf⟩
  let S : J.Cover U := Finset.univ.inf fun p : Fin n ↦
    ⟨Presheaf.imageSieve α (a p) ⊓ Presheaf.imageSieve ηu (s p),
      J.intersection_covering (Presheaf.imageSieve_mem J α (a p))
        (Presheaf.imageSieve_mem J ηu (s p))⟩
  apply J.transitive S.property T
  intro V f hf
  have hp (p : Fin n) : S ≤
      (⟨Presheaf.imageSieve α (a p) ⊓ Presheaf.imageSieve ηu (s p),
        J.intersection_covering (Presheaf.imageSieve_mem J α (a p))
          (Presheaf.imageSieve_mem J ηu (s p))⟩ : J.Cover U) :=
    Finset.inf_le (Finset.mem_univ p)
  have hpa (p : Fin n) : ∃ a0 : O.obj (Opposite.op V),
      α.app (Opposite.op V) a0 = R.obj.map f.op (a p) := (hp p f hf).1
  have hpx (p : Fin n) : ∃ x0 : F.obj (Opposite.op V),
      e (Opposite.op V) x0 = m f.op (s p) := (hp p f hf).2
  choose a0 ha0 using hpa
  choose x0 hx0 using hpx
  have heq : ηu.app (Opposite.op V) (∑ p, a0 p • x0 p) =
      ηu.app (Opposite.op V) 0 := by
    change e (Opposite.op V) (∑ p, a0 p • x0 p) = e (Opposite.op V) 0
    rw [map_sum, map_zero]
    simp_rw [esmul, ha0, hx0]
    have hh := congrArg (m f.op) hs
    simpa only [map_sum, msmul, map_zero] using hh
  apply J.transitive (Presheaf.equalizerSieve_mem J ηu _ _ heq) (T.pullback f)
  intro W g hg
  have hrel : ∑ p, ((O ⋙ forget₂ CommRingCat RingCat).map g.op) (a0 p) •
      d g.op (x0 p) = 0 := by
    change d g.op (∑ p, a0 p • x0 p) = d g.op 0 at hg
    simpa only [map_sum, dsmul, map_zero] using hg
  obtain ⟨I, Y, k, hcov, hflatY⟩ := hflat W
  apply J.superset_covering _ hcov
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro i
  have : Module.Flat ((O ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op (Y i)))
      (F.obj (Opposite.op (Y i))) := hflatY i
  let y (p : Fin n) : F.obj (Opposite.op (Y i)) := d (k i).op (d g.op (x0 p))
  have hrel' : ∑ p, ((O ⋙ forget₂ CommRingCat RingCat).map (k i).op)
      (((O ⋙ forget₂ CommRingCat RingCat).map g.op) (a0 p)) • y p = 0 := by
    have hh := congrArg (d (k i).op) hrel
    simpa only [y, map_sum, dsmul, map_zero] using hh
  obtain ⟨l, b, t, ht, hb⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel'
  refine ⟨l, (fun p q ↦ α.app (Opposite.op (Y i)) (b p q)),
    (fun q ↦ e (Opposite.op (Y i)) (t q)), ?_, ?_⟩
  · intro p
    have hh := congrArg (e (Opposite.op (Y i))) (ht p)
    simp only [map_sum, esmul, y, enat, hx0] at hh
    simpa only [op_comp, mcomp] using hh
  · intro q
    have hh := congrArg (α.app (Opposite.op (Y i))) (hb q)
    simp only [map_sum, map_mul, map_zero, NatTrans.naturality_apply, ha0] at hh
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    exact hh

end PresheafOfModules
