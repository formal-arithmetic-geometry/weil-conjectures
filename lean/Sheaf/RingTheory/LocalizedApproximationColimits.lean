/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.AtPrime.Basic

import Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Canonical diagrams localized at contracted primes

Source: Stacks Project, Algebra, Tag 02JO, first paragraph; Tag 037D.
(blueprint: lem-pc-localized-approximation-colimits)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace Algebra

section Maps

variable {R S M N : Type*} [CommRing R] [CommRing S]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]

/-- The fraction map induced by a semilinear additive homomorphism. -/
def primeModuleMap (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (f : R →+* S) (hp : p = q.comap f) (g : M →+ N)
    (hg : ∀ r x, g (r • x) = f r • g x) :
    LocalizedModule p.primeCompl M →+ LocalizedModule q.primeCompl N where
  toFun z := z.liftOn
    (fun x => LocalizedModule.mk (g x.1) ⟨f x.2, by
      change f x.2 ∉ q
      have := x.2.property
      simpa [hp] using this⟩)
    (by
      rintro ⟨x, s⟩ ⟨y, t⟩ ⟨a, ha⟩
      apply LocalizedModule.mk_eq.mpr
      refine ⟨⟨f a, ?_⟩, ?_⟩
      · have := a.property
        simpa [hp] using this
      · simpa only [Submonoid.smul_def, hg] using congrArg g ha)
  map_zero' := by
    rw [← LocalizedModule.zero_mk (1 : p.primeCompl)]
    rw [LocalizedModule.liftOn_mk]
    simp
  map_add' := by
    intro x y
    induction x, y using LocalizedModule.induction_on₂ with
    | h x y s t =>
      rw [LocalizedModule.mk_add_mk]
      simp only [LocalizedModule.liftOn_mk, map_add]
      rw [LocalizedModule.mk_add_mk]
      congr 1
      · simp only [Submonoid.smul_def, hg]
      · apply Subtype.ext
        exact map_mul f (s : R) (t : R)

@[simp]
theorem primeModuleMap_mk (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (f : R →+* S) (hp : p = q.comap f) (g : M →+ N)
    (hg : ∀ r x, g (r • x) = f r • g x) (x : M) (s : p.primeCompl) :
    primeModuleMap p q f hp g hg (LocalizedModule.mk x s) =
      LocalizedModule.mk (g x) ⟨f s, by simpa [hp] using s.property⟩ := by
  rfl

/-- Fraction maps respect the induced map of localized scalar rings. -/
theorem primeModuleMap_smul (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (f : R →+* S) (hp : p = q.comap f) (g : M →+ N)
    (hg : ∀ r x, g (r • x) = f r • g x)
    (r : Localization.AtPrime p) (x : LocalizedModule p.primeCompl M) :
    primeModuleMap p q f hp g hg (r • x) =
      Localization.localRingHom p q f hp r • primeModuleMap p q f hp g hg x := by
  induction r using Localization.induction_on with
  | H rs =>
    rcases rs with ⟨r, s⟩
    induction x using LocalizedModule.induction_on with
    | h x t =>
      rw [LocalizedModule.mk_smul_mk, primeModuleMap_mk,
        Localization.localRingHom_mk, primeModuleMap_mk, LocalizedModule.mk_smul_mk]
      congr 1
      · exact hg r x
      · apply Subtype.ext
        exact map_mul f (s : R) (t : R)

end Maps

section Diagrams

variable {Λ : Type u} [Preorder Λ]
  {T : Type u} [CommRing T]
  (F : Λ ⥤ CommRingCat.{u})
  (κ : F ⟶ (Functor.const Λ).obj (CommRingCat.of T)) (q : PrimeSpectrum T)

/-- Naturality identifies the contracted primes along every transition. -/
theorem contractedPrime_map (i j : Λ) (f : i ⟶ j) :
    (q.asIdeal.comap (κ.app i).hom) =
      (q.asIdeal.comap (κ.app j).hom).comap (F.map f).hom := by
  rw [Ideal.comap_comap]
  congr 1
  exact congrArg CommRingCat.Hom.hom (κ.naturality f).symm

/-- Localize a ring diagram at the inverse images of a fixed prime of its cocone. -/
@[reducible]
noncomputable def primeRingDiagram : Λ ⥤ CommRingCat.{u} where
  obj i := CommRingCat.of (Localization.AtPrime (q.asIdeal.comap (κ.app i).hom))
  map {i j} f := CommRingCat.ofHom (Localization.localRingHom _ _ (F.map f).hom
    (contractedPrime_map F κ q i j f))
  map_id i := by
    ext1
    apply IsLocalization.ringHom_ext (q.asIdeal.comap (κ.app i).hom).primeCompl
    ext x
    simp
  map_comp {i j k} f g := by
    ext1
    apply IsLocalization.ringHom_ext (q.asIdeal.comap (κ.app i).hom).primeCompl
    ext x
    simp

variable {V : Type v} [AddCommGroup V] [Module T V]
  (D : Λ ⥤ AddCommGrpCat.{v})
  (ν : D ⟶ (Functor.const Λ).obj (AddCommGrpCat.of V))
  [∀ i, Module (F.obj i) (D.obj i)]
  (hscalar : ∀ (i j : Λ) (f : i ⟶ j) (b : F.obj i) (x : D.obj i),
    (D.map f).hom (b • x) = (F.map f).hom b • (D.map f).hom x)

/-- Localize the module diagram using its actual fraction maps. -/
@[reducible]
def primeModuleDiagram : Λ ⥤ AddCommGrpCat.{max u v} where
  obj i := AddCommGrpCat.of
    (LocalizedModule (q.asIdeal.comap (κ.app i).hom).primeCompl (D.obj i))
  map {i j} f := AddCommGrpCat.ofHom
    (primeModuleMap _ _ (F.map f).hom (contractedPrime_map F κ q i j f)
      (D.map f).hom (hscalar i j f))
  map_id i := by
    ext z
    induction z using LocalizedModule.induction_on with
    | h x s =>
      dsimp
      simp only [primeModuleMap_mk]
      simp
  map_comp {i j k} f g := by
    ext z
    induction z using LocalizedModule.induction_on with
    | h x s =>
      dsimp
      simp only [primeModuleMap_mk]
      simp

end Diagrams

section Comparison

variable {Λ : Type u} [Preorder Λ] {S : Type u} [CommRing S]
  (A B : Λ ⥤ CommRingCat.{u}) (η : A ⟶ B)
  (κ : B ⟶ (Functor.const Λ).obj (CommRingCat.of S)) (q : PrimeSpectrum S)

/-- The localized stage map, with the base prime defined by contraction through `η`. -/
noncomputable def primeDiagramHom (i : Λ) :
    (primeRingDiagram A (η ≫ κ) q).obj i →+* (primeRingDiagram B κ q).obj i :=
  Localization.localRingHom _ _ (η.app i).hom rfl

/-- The localized square commutes because its restrictions to the original rings do. -/
theorem primeDiagramHom_naturality (i j : Λ) (f : i ⟶ j) :
    ((primeRingDiagram B κ q).map f).hom.comp (primeDiagramHom A B η κ q i) =
      (primeDiagramHom A B η κ q j).comp ((primeRingDiagram A (η ≫ κ) q).map f).hom := by
  dsimp [primeRingDiagram, primeDiagramHom]
  apply IsLocalization.ringHom_ext
    (q.asIdeal.comap ((κ.app i).hom.comp (η.app i).hom)).primeCompl
  ext x
  simp only [RingHom.comp_apply, Localization.localRingHom_to_map]
  congr 1
  exact ConcreteCategory.congr_hom (η.naturality f).symm x

end Comparison

/-- Localization of supplied compatible colimits identifies the canonical localized
colimits and their scalar actions. No finiteness, base-change, or flatness is assumed.

Source: Stacks Project, Algebra, Tag 02JO, first paragraph, and Tag 037D.
(blueprint: lem-pc-localized-approximation-colimits)

Proof:
1. The cocone equation contracts q through η and κ to the contraction of p in A_i,
   where p is the contraction of q in R. The naturality equations show that the
   explicitly defined fraction maps give cocones with vertices R_p, S_q, and M_q.
2. Localization commutes with the ring colimits. Transport the supplied colimit
   cocones to canonical ones and apply filteredColimitLocalizationAtPrime. The
   resulting comparison maps are isomorphisms, determined by their fraction formulas.
3. For modules, represent a numerator and a denominator at a common stage using
   the supplied colimits. The lifted denominator is outside the contracted prime.
   If two fractions agree, a multiplier outside q kills their cross difference.
   Lift this multiplier and descend the zero relation to a later stage using the
   original additive-group colimit. Semilinearity makes the cross difference there
   the correct one. Joint surjectivity and eventual equality give the group colimit
   criterion, so its canonical comparison with M_q is an additive isomorphism.
4. Transport the S_q action through these canonical comparisons to the group colimit.
   On fraction representatives the action satisfies the displayed scalar equation.
   The localized stage maps likewise induce ψ. Its equation on coprojections uniquely
   determines it; joint surjectivity determines the module action from the scalar
   equation. Thus these are universal constructions, not arbitrary choices of data.
5. The comparisons intertwine ψ with the local map R_p to S_q, as checked on stage
   numerators and then on fractions. Flatness is invariant under these ring and
   module isomorphisms, giving the displayed equivalence.
-/
theorem localized_approximation_colimits
    (R S : Type u) (M : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M]
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (A B : Λ ⥤ CommRingCat.{u}) (η : A ⟶ B)
    (π : A ⟶ (Functor.const Λ).obj (CommRingCat.of R))
    (κ : B ⟶ (Functor.const Λ).obj (CommRingCat.of S))
    (D : Λ ⥤ AddCommGrpCat.{v})
    (ν : D ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M))
    [∀ i : Λ, Module (B.obj i) (D.obj i)]
    (hA : Nonempty (IsColimit (Cocone.mk (CommRingCat.of R) π)))
    (hB : Nonempty (IsColimit (Cocone.mk (CommRingCat.of S) κ)))
    (hD : Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M) ν)))
    (hη : ∀ i, η.app i ≫ κ.app i = π.app i ≫ CommRingCat.ofHom (algebraMap R S))
    (hs : ∀ (i j : Λ) (f : i ⟶ j) (b : B.obj i) (x : D.obj i),
      (D.map f).hom (b • x) = (B.map f).hom b • (D.map f).hom x)
    (hν : ∀ i (b : B.obj i) (x : D.obj i),
      (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) (b • x) =
        (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)) b •
          (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x)
    (q : PrimeSpectrum S) :
    let Aq := primeRingDiagram A (η ≫ κ) q
    let Bq := primeRingDiagram B κ q
    let Nq := primeModuleDiagram B κ q D hs
    ∃ (ψ : (colimit Aq : CommRingCat.{u}) →+* (colimit Bq : CommRingCat.{u}))
      (act : Module (colimit Bq : CommRingCat.{u})
        (colimit Nq : AddCommGrpCat.{max u v})),
      letI := act
      (∀ i, ψ.comp (colimit.ι Aq i).hom =
        (colimit.ι Bq i).hom.comp (primeDiagramHom A B η κ q i)) ∧
      (∀ (i : Λ) (b : Bq.obj i) (x : Nq.obj i),
        (colimit.ι Nq i).hom (b • x) =
          (colimit.ι Bq i).hom b • (colimit.ι Nq i).hom x) ∧
      ((letI := Module.compHom (colimit Nq : AddCommGrpCat.{max u v}) ψ
        Module.Flat (colimit Aq : CommRingCat.{u}) (colimit Nq : AddCommGrpCat.{max u v})) ↔
        @Module.Flat (Localization.AtPrime (q.asIdeal.comap (algebraMap R S)))
          (LocalizedModule q.asIdeal.primeCompl M) _ _
          (Module.compHom _ (Localization.localRingHom
            (q.asIdeal.comap (algebraMap R S)) q.asIdeal (algebraMap R S) rfl))) := by sorry

end Algebra
