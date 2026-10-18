/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Global derived Hom with completed adic coefficients

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.8.12;
Stacks Project, Tag 08JA (blueprint: def-weil-pbc-adic-global-derived-hom).

## Main definitions

* `adicGlobalSections`: evaluation at the final object, with the canonical A action.
* `adicGlobalDerivedHom`: derived global sections of the recorded internal derived Hom.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The constant residue section of the finite coefficient sheaf. Source: Bhatt--Scholze,
6.8.2(1) (blueprint: def-weil-pbc-adic-global-derived-hom). -/
def adicFiniteConstant (n : ℕ) (U : T.ProEtᵒᵖ) :
    A →+* ((pbcAdicRings T d).obj (op n)).obj.obj U :=
  letI := d.quotientFinite n
  ((toSheafify (ProEt.topology T)
      (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))).app U).hom.comp
    (((AdicCoefficients.constants T (A ⧸ d.ideal ^ (n + 1))).app U).hom.comp
      (Ideal.Quotient.mk (d.ideal ^ (n + 1))))

/-- The canonical scalar homomorphism is uniquely specified by all its finite residues.
Source: Bhatt--Scholze, 6.8.2(1)
(blueprint: def-weil-pbc-adic-global-derived-hom).
Proof: the constant residue homomorphisms commute with each quotient map, since
both routes send a to its constant residue class. They form a cone on the evaluated
inverse system. Limits of ring sheaves are evaluated sectionwise, so the limit
universal property supplies the homomorphism. The projections are jointly injective,
which proves uniqueness. This argument includes the empty scheme and zero rings. -/
theorem adicScalar_exists (U : T.ProEtᵒᵖ) :
    ∃! ρ : A →+* (pbcAdicCompletion T d).obj.obj U,
      ∀ n : ℕ, ((pbcAdicProjection T d n).hom.app U).hom.comp ρ =
        adicFiniteConstant T d n U := by
  sorry

/-- The scalar map into completed sections, determined by its actual finite residues.
Source: Bhatt--Scholze, 6.8.2(1)
(blueprint: def-weil-pbc-adic-global-derived-hom). -/
def adicScalar (U : T.ProEtᵒᵖ) : A →+* (pbcAdicCompletion T d).obj.obj U :=
  (adicScalar_exists T d U).exists.choose

/-- Global sections as A-modules: evaluation at the final pro-etale object followed
by restriction along the constant completed scalar map. Source: Stacks Project,
Tag 08JA (blueprint: def-weil-pbc-adic-global-derived-hom). -/
def adicGlobalSections : pbcModules T (pbcAdicCompletion T d) ⥤ ModuleCat.{u + 1} A :=
  SheafOfModules.evaluation _ (op (⊤_ T.ProEt)) ⋙
    ModuleCat.restrictScalars (adicScalar T d (op (⊤_ T.ProEt)))

/-- Evaluation and scalar restriction are additive. Source: Stacks Project, Tag 08JA
(blueprint: def-weil-pbc-adic-global-derived-hom). -/
instance adicGlobalSections_additive : (adicGlobalSections T d).Additive := by
  dsimp [adicGlobalSections, SheafOfModules.evaluation]
  infer_instance

/-- The unbounded right derived functor of global sections, with its A-module action.
Source: Stacks Project, Tag 08JA
(blueprint: def-weil-pbc-adic-global-derived-hom). -/
def adicDerivedGlobalSections :
    DerivedCategory (pbcModules T (pbcAdicCompletion T d)) ⥤
      DerivedCategory (ModuleCat.{u + 1} A) :=
  letI :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u + 1}
      (ProEt.topology T) (pbcAdicCompletion T d)).1
  (adicGlobalSections T d).rightDerivedFunctor

/-- Global derived Hom is RΓ of internal derived Hom, in the derived category of
A-modules, without replacing the completed coefficient sheaf by a constant sheaf.
Source: Bhatt--Scholze, Lemma 6.8.12; Stacks Project, Tag 08JA
(blueprint: def-weil-pbc-adic-global-derived-hom). -/
def adicGlobalDerivedHom :
    (DerivedCategory (pbcModules T (pbcAdicCompletion T d)))ᵒᵖ ×
      DerivedCategory (pbcModules T (pbcAdicCompletion T d)) ⥤
        DerivedCategory (ModuleCat.{u + 1} A) :=
  derivedInternalHomOfUniverses.{u + 1, u, u + 1} (ProEt.topology T) (pbcAdicCompletion T d) ⋙
    adicDerivedGlobalSections T d

/-- Fix the contravariant argument of global derived Hom. Source: Bhatt--Scholze,
Lemma 6.8.12 (blueprint: def-weil-pbc-adic-global-derived-hom). -/
def adicGlobalRHom (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d))) :
    DerivedCategory (pbcModules T (pbcAdicCompletion T d)) ⥤
      DerivedCategory (ModuleCat.{u + 1} A) :=
  (Functor.curry.obj (adicGlobalDerivedHom T d)).obj (op K)

end AlgebraicGeometry.Scheme
