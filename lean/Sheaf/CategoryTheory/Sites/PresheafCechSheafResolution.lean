/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.CategoryTheory.Sites.PresheafCechComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicTopology.SetCechNerveFreeResolution

/-!
# The augmented sheafified free presheaf Čech resolution

Source: Stacks Project, Hypercoverings, Tag 01GC, and Cohomology on Sites, Tag 079Z.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf

/-- The free abelian sheaf functor on presheaves of sets.
Source: Stacks Project, Tag 079Z.
(blueprint: lem-sc-presheaf-cech-sheaf-resolution) -/
noncomputable abbrev presheafCechFreeSheafFunctor
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] :
    (Cᵒᵖ ⥤ Type v) ⥤ Sheaf J AddCommGrpCat.{v} :=
  (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf J AddCommGrpCat

/-- The chain complex of sheafified free abelian presheaves on the Čech nerve.
Source: Stacks Project, Tags 01GC and 079Z.
(blueprint: lem-sc-presheaf-cech-sheaf-resolution) -/
noncomputable abbrev presheafCechSheafComplex
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] (f : Arrow (Cᵒᵖ ⥤ Type v)) :
    ChainComplex (Sheaf J AddCommGrpCat.{v}) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj
    (f.cechNerve ⋙ presheafCechFreeSheafFunctor J)

/-- An exact syzygy ladder for the actual sheafified free Čech chain complex.
The maps factor its differentials; the initial augmentation is the original map,
under the degree-zero identification. All data and proofs are explicit fields.
Source: Stacks Project, Tag 079Z, augmented free nerve argument.
(blueprint: lem-sc-presheaf-cech-sheaf-resolution) -/
structure PresheafCechSheafResolution
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}] (f : Arrow (Cᵒᵖ ⥤ Type v)) where
  K : ℕ → Sheaf J AddCommGrpCat.{v}
  i : ∀ n, K n ⟶ (presheafCechSheafComplex J f).X n
  p : ∀ n, (presheafCechSheafComplex J f).X (n + 1) ⟶ K n
  e₀ : (presheafCechSheafComplex J f).X 0 ≅
    (presheafCechFreeSheafFunctor J).obj f.left
  initial_zero : i 0 ≫ (e₀.hom ≫ (presheafCechFreeSheafFunctor J).map f.hom) = 0
  initial_exact : (ShortComplex.mk (i 0)
    (e₀.hom ≫ (presheafCechFreeSheafFunctor J).map f.hom) initial_zero).ShortExact
  zero : ∀ n, i (n + 1) ≫ p n = 0
  exact : ∀ n, (ShortComplex.mk (i (n + 1)) (p n) (zero n)).ShortExact
  differential : ∀ n, p n ≫ i n = (presheafCechSheafComplex J f).d (n + 1) n

/-- A locally surjective presheaf map has an exact augmented sheafified free nerve.
Source: Stacks Project, Hypercoverings, Tag 01GC, and Cohomology on Sites, Tag 079Z.
(blueprint: lem-sc-presheaf-cech-sheaf-resolution)

Proof: evaluate the free presheaf chain complex objectwise. Replace the target
set by the image of the evaluated map; this does not change the nerve. Choose
one vertex in every nonempty fibre and prefix it to tuples. The alternating
faces give a contraction, so the free presheaf chain complex is exact in positive
degrees and its degree-zero cokernel is the free abelian presheaf on the image.
Sheafification is exact. Local surjectivity identifies the sheafification of
that image with the sheafification of the target, so the augmented sheaf complex
is exact also at degree zero and the augmentation is epic. Identify the zeroth
nerve term with the source presheaf to obtain e₀. Take K₀ to be the kernel of
the augmentation and Kₙ₊₁ to be the kernel of the map onto Kₙ. Exactness factors
each differential as an epimorphism pₙ followed by the kernel inclusion iₙ;
these maps give the asserted short exact sequences and differential identities.
The kernel universal properties determine all chosen syzygies up to unique iso.
-/
theorem exists_presheafCechSheafResolution
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}] (f : Arrow (Cᵒᵖ ⥤ Type v))
    (hf : Presheaf.IsLocallySurjective J f.hom) :
    Nonempty (PresheafCechSheafResolution (J := J) f) := by sorry

end CategoryTheory.Sheaf
