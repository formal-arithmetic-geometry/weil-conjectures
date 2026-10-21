/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafHom
public import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.Algebra.Homology.DiagramKFlatReplacements
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-!
# The representative normalization of the derived constant-tower comparison

Source: Stacks Project, Derived Categories, Tag 06XN, `lemma-find-existence-computes`
(dual), and the completed-pullback constant-tower subargument, Step 4
(blueprint: lem-cbc-derived-constant-tower-normalization).

The auxiliary maps below merely spell out the canonical localization identifications.
Strict towers are indexed by `ℕᵒᵖ`, with level `n` representing the paper's level `n + 1`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uA vA uB vB wA wB wTA wTB u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

section Identifications

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
  (E : A ⥤ B) [E.Additive]

/-- Termwise pullback of a constant complex is the constant complex of its pullback.
Source: the constant-tower subargument, Step 1; Stacks Tag 06XN
(blueprint: lem-cbc-derived-constant-tower-normalization).
This is `compConstIso` applied to complexes, not an independently chosen comparison. -/
def constantTowerComplexComparison :
    E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        ((whiskeringRight ℕᵒᵖ A B).obj E).mapHomologicalComplex (ComplexShape.up ℤ) :=
  NatIso.mapHomologicalComplex (compConstIso ℕᵒᵖ E) (ComplexShape.up ℤ)

/-- The constant tower of the chosen ordinary counit, transported to strict tower complexes.
Source: the constant-tower subargument, Steps 1--2; Stacks Tag 06XN
(blueprint: lem-cbc-derived-constant-tower-normalization).
The factors are associators, exact constant-functor localization, and the termwise comparison. -/
def constantTowerDerivedSourceCounit
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ L ⟶
      E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) :
    DerivedCategory.Q ⋙ (L ⋙ (const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapDerivedCategory) ⟶
      (const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (((whiskeringRight ℕᵒᵖ A B).obj E).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q) :=
  (associator _ _ _).inv ≫
    whiskerRight ε _ ≫ (associator _ _ _).hom ≫
    whiskerLeft _ (const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapDerivedCategoryFactors.hom ≫
    (associator _ _ _).inv ≫
    whiskerRight (constantTowerComplexComparison E).hom DerivedCategory.Q ≫
    (associator _ _ _).hom

/-- The chosen tower counit at a constant representative, with its source localized.
Source: the constant-tower subargument, Steps 1--2; Stacks Tag 06XN
(blueprint: lem-cbc-derived-constant-tower-normalization).
Only the canonical factorization of the exact constant functor is inserted. -/
def constantTowerDerivedTargetCounit
    (L : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory (ℕᵒᵖ ⥤ B))
    (τ : DerivedCategory.Q ⋙ L ⟶
      ((whiskeringRight ℕᵒᵖ A B).obj E).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) :
    DerivedCategory.Q ⋙ ((const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⋙ L) ⟶
      (const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (((whiskeringRight ℕᵒᵖ A B).obj E).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q) :=
  (associator _ _ _).inv ≫
    whiskerRight (const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategoryFactors.hom L ≫
    (associator _ _ _).hom ≫
    whiskerLeft ((const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)) τ


/-- The type of comparison isomorphisms between the two canonical derived tower functors.
Source: the constant-tower subargument, Step 1; Stacks Tag 06XN
(blueprint: lem-cbc-derived-constant-tower-normalization).
This transparent type uses the exact constant functors, with no chosen comparison. -/
def ConstantTowerDerivedComparison
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (Lt : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory (ℕᵒᵖ ⥤ B)) :=
  L ⋙ (const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapDerivedCategory ≅
    (const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⋙ Lt

/-- The representative counit equation and its inverse formula, with canonical transports.
Source: the constant-tower subargument, Steps 2 and 5; Stacks Tag 06XN
(blueprint: lem-cbc-derived-constant-tower-normalization).
This transparent predicate packages parallel arrows; it supplies no comparison data. -/
def IsConstantTowerRepresentativeNormalized
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ L ⟶
      E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (Lt : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory (ℕᵒᵖ ⥤ B))
    (τ : DerivedCategory.Q ⋙ Lt ⟶
      ((whiskeringRight ℕᵒᵖ A B).obj E).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    (b : ConstantTowerDerivedComparison L Lt)
    (P : CochainComplex A ℤ) : Prop :=
  b.hom.app (DerivedCategory.Q.obj P) ≫
      (constantTowerDerivedTargetCounit E Lt τ).app P =
    (constantTowerDerivedSourceCounit E L ε).app P ∧
  ∃ t : ((const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapDerivedCategory ⋙ Lt).obj
        (DerivedCategory.Q.obj P) ≅
      (((const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
        (((whiskeringRight ℕᵒᵖ A B).obj E).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q)).obj P,
    t.hom = (constantTowerDerivedTargetCounit E Lt τ).app P ∧
    b.hom.app (DerivedCategory.Q.obj P) =
      (constantTowerDerivedSourceCounit E L ε).app P ≫ t.inv

/-- Unique comparison normalized on a specified representative class.
Source: Stacks Tag 06XN and the constant-tower subargument, Steps 2--6
(blueprint: lem-cbc-derived-constant-tower-normalization).
This is the explicit existence-and-uniqueness quantifier over the comparison type,
with no additional hypothesis or data. Packaging it avoids repeating concrete
module-sheaf instance comparisons when the representative equation is specialized. -/
def HasUniqueConstantTowerNormalizedComparison
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ L ⟶
      E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (Lt : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory (ℕᵒᵖ ⥤ B))
    (τ : DerivedCategory.Q ⋙ Lt ⟶
      ((whiskeringRight ℕᵒᵖ A B).obj E).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    (W : CochainComplex A ℤ → Prop) : Prop :=
  ∃! b : ConstantTowerDerivedComparison L Lt,
    ∀ P : CochainComplex A ℤ, W P →
      IsConstantTowerRepresentativeNormalized E L ε Lt τ b P

end Identifications

end CategoryTheory.Functor

namespace CategoryTheory.RingedToposMorphism

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {T : GrothendieckTopology C} {T' : GrothendieckTopology D}
  (R : Sheaf T CommRingCat.{u}) (S : Sheaf T' CommRingCat.{u})
  [HasDerivedCategory.{wA}
    (ringedSiteModules.{u, u, u, u} ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R))]
  [HasDerivedCategory.{wB}
    (ringedSiteModules.{u, u, u, u} ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S))]
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u}
    ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R))]
  [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u}
    ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S))]

/-- The unique constant-tower comparison with its K-flat representative normalization.
Source: Stacks Project, Derived Categories, Tag 06XN, `lemma-find-existence-computes`
(dual), and the completed-pullback constant-tower subargument, Step 4
(blueprint: lem-cbc-derived-constant-tower-normalization).

The adjunction identifies `E` with inverse image followed by extension of scalars,
exactly as in `CochainComplex.diagram_pullback_quasiIso`. The two universal pairs are
arbitrary. The last existential packages the invertible transported tower counit;
its inverse gives precisely the displayed formula in the node.

Proof:
1. Towers are abelian levelwise, so the constant functors are exact. Use their
   `mapDerivedCategoryFactors` and `constantTowerComplexComparison` to identify the
   two representative targets (lem-weil-tower-category-levelwise-abelian and
   lem-weil-pbc-exact-functor-derived-factorization).
2. The diagram K-flat replacement theorem supplies resolutions, both for complexes
   and for strict towers, and pullback inverts quasi-isomorphisms in these classes.
   Apply `leftDerived_from_resolvingClass`; uniqueness of universal pairs transports
   its invertible counits to the chosen pairs. A constant K-flat flat-term complex
   belongs to the tower resolving class. Form the component by the inverse tower
   counit after the constant ordinary counit.
3. Counit naturality and cancellation of the tower counit prove naturality of these
   components on the full resolving class.
4. Use the right calculus of fractions and `exists_natTrans_from_resolvingClass`
   to extend to all complexes. For a resolution P → X, the extended component is
   conjugate to the component at P, so is invertible.
5. Lift the resulting natural isomorphism along localization (the liftNatIso clause
   of lem-weil-pbc-localization-universal-property). Its components satisfy the
   normalization, and cancellation gives the asserted inverse formula.
6. Any second normalized isomorphism agrees on resolving representatives, hence on
   all complexes by resolutions and naturality. Localization's `natTrans_ext` then
   gives equality on the derived category, proving uniqueness. -/
theorem existsUnique_derivedConstantTowerComparison
    (f : RingedToposMorphism
      ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S)
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R))
    (E : ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u, u, u, u}
        ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S))
    [E.Additive] (adj : E ⊣ f.modules)
    (L : DerivedCategory (ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)) ⥤
      DerivedCategory (ringedSiteModules.{u, u, u, u}
        ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S)))
    (ε : DerivedCategory.Q ⋙ L ⟶
      E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))]
    (Lt : DerivedCategory (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)) ⥤
      DerivedCategory (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u}
        ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S)))
    (τ : DerivedCategory.Q ⋙ Lt ⟶
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj E).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    [Lt.IsLeftDerivedFunctor τ (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))] :
    Functor.HasUniqueConstantTowerNormalizedComparison.{u + 1, u, u + 1, u,
        wA, wB, wTA, wTB}
      (A := ringedSiteModules.{u, u, u, u}
        ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R))
      (B := ringedSiteModules.{u, u, u, u}
        ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S)) E L ε Lt τ
      (fun P ↦ P.IsAcyclicTensorKFlat ∧ ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) := by
  sorry

end CategoryTheory.RingedToposMorphism
