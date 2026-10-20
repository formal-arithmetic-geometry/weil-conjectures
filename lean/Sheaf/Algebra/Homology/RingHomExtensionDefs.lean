/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1, SHEAF group T3
-/
module

public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.Algebra.Homology.KFlatTensorQuasiIso

/-! # Shared definitions for scalar extension of ring-site Hom complexes

Source: Stacks Project, more-algebra.tex, equation-base-change-RHom, and
sites-cohomology.tex, section-hom-complexes (Tag 0A8X).
(blueprint: def-pc-ring-hom-extension-shared-definitions)

This is a chain-level construction. It requires neither derived categories nor
perfectness, and supplies only the normalized Hom map, not derived extension data.
-/

-- Keep the chosen Hom-complex witness folded during routine conversion checks.
set_option backward.isDefEq.respectTransparency true

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory

/-- Modules on the one-object bottom-topology site with ring `A`. Source: Stacks,
more-algebra.tex, equation-base-change-RHom
(blueprint: def-pc-perfect-rhom-base-change-map). -/
abbrev RingSiteModules (A : Type u) [CommRing A] :=
  SheafOfModules.{u} ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (CochainComplex.onePointRingSheaf A))

/-- The map of constant ring sheaves induced by the given ring homomorphism. Source:
Stacks, equation-base-change-RHom (blueprint: def-pc-perfect-rhom-base-change-map). -/
def ringSiteMap {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    CochainComplex.onePointRingSheaf A ⟶ CochainComplex.onePointRingSheaf B :=
  ⟨(Functor.const _).map (CommRingCat.ofHom φ)⟩

/-- The projections of the shared Hom complex, taken from exactly the witness used in
`homComplexFunctor`, rather than from another product. Source: Stacks, sites-cohomology.tex,
0A8X (blueprint: def-pc-perfect-rhom-base-change-map). -/
noncomputable def ringHomComplexProjection {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ) (n p : ℤ) :
    (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n ⟶
      SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A)
        (P.X p) (Q.X (p + n)) :=
  (homComplex_projections_exists (R := CochainComplex.onePointRingSheaf A)).choose
    P Q n p (p + n) rfl

/-- Evaluate a product coordinate of the shared Hom complex on the unique object's slice.
Source: Stacks, 0A8X (blueprint: def-pc-perfect-rhom-base-change-map). -/
noncomputable def ringHomEvaluate {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ) (n p : ℤ)
    (U : (Discrete PUnit.{u + 1})ᵒᵖ)
    (f : (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n |>.val.obj U)
    (x : (P.X p).val.obj U) : (Q.X (p + n)).val.obj U :=
  (((ringHomComplexProjection P Q n p).val.app U f).app (op (Over.mk (𝟙 U.unop)))) x

/-- Termwise extension on complexes using the specified additive structure. Source:
Stacks, 06YY (blueprint: def-pc-perfect-rhom-base-change-map). -/
noncomputable def ringExtensionComplex {A B : Type u} [CommRing A] [CommRing B]
    (F : RingSiteModules A ⥤ RingSiteModules B) (hF : F.Additive) :
    CochainComplex (RingSiteModules A) ℤ ⥤ CochainComplex (RingSiteModules B) ℤ := by
  letI := hF
  exact F.mapHomologicalComplex (.up ℤ)

-- This tensor notation needs reduction of the constant sheaf ring instances.
set_option backward.isDefEq.respectTransparency false in
/-- The pure tensor, followed by the shared sheafification unit and the specified object
identification for extension. Source: Stacks, 03EK
(blueprint: def-pc-perfect-rhom-base-change-map). -/
noncomputable def ringExtensionPure {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (F : RingSiteModules A ⥤ RingSiteModules B)
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (M : RingSiteModules A) (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b : B) (x : M.val.obj U) :
    (F.obj M).val.obj U :=
  (eqToHom (h M).symm).val.app U
    ((toSheafify ⊥
      (SheafOfModules.changeOfRingsPresheaf (ringSiteMap φ) M).presheaf).app U
        (b ⊗ₜ[A, φ] x))

end CategoryTheory
