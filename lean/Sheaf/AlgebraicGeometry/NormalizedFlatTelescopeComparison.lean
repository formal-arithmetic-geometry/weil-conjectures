/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Normalized comparison on flat telescope representatives

Source: Stacks Project, Tags 06YS and 06YJ, flat telescope models and K-flat
computation; the supplied-tensorator normalization is the parent node's step 2
(agent expansion, not a literal assertion of either Stacks lemma).
(blueprint: lem-sc-normalized-flat-telescope-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

/-- A concrete sequential telescope of bounded-above flat complexes.
The transition cone is constructed explicitly; no existence witness supplies its data.
Source: Stacks Project, Tag 06YS, telescope construction.
(blueprint: lem-sc-normalized-flat-telescope-comparison). -/
def isFlatTelescope (Y : Scheme.{u})
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) : Prop :=
  ∃ (E : ℕ → CochainComplex
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (t : ∀ n : ℕ, E n ⟶ E (n + 1)),
    (∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i)) ∧
    (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i)) ∧
    CochainComplex.mappingCone (𝟙 (∐ E) -
      Sigma.desc (fun n : ℕ ↦ t n ≫ Sigma.ι E (n + 1))) = P

/-- Homotopy objects represented by flat telescopes or their translates by one.
This predicate records actual representatives and contains no choice of data.
Source: Stacks Project, Tag 06YJ.
(blueprint: lem-sc-normalized-flat-telescope-comparison). -/
def flatTelescopeShiftRepresentative (Y : Scheme.{u})
    (X : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
    isFlatTelescope Y P ∧
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P = X ∨
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)⟦(1 : ℤ)⟧ = X)

/-- A jointly normalized comparison on the concrete flat telescopes and their
one-fold translates. Naturality is required only between objects of this class;
there is no natural transformation on the entire homotopy category here.

Source: Stacks Project, Tag 06YJ, K-flat computation; the tensorator coherence
part is the agent expansion of step 2 of the parent node, not an assertion of 06YJ.

Proof. Write P as Cone(1 - shift_t) on the countable sum of bounded-above
flat E_n. The E_n, their sum, and this cone are K-flat. Termwise tensor pullback
commutes with the sum and takes 1 - shift_t to the corresponding transition map,
so its image is the analogous concrete telescope over Z. Compute derived pullback
by these representatives. Use the constant tower on the degree-zero structure
sheaf, and its translate, for the two unit representatives. Their telescope
augmentations identify their localizations with the unit and shifted unit.

Carry out the parent's joint representative normalization on these flat models:
normalize the unshifted unit with the supplied monoidal unit map. Rewrite the
translate of a representative as the tensor of the shifted unit and that
representative by the first-variable Koszul comparison followed by the shifted
left unitor. Its comparison is the composite of the inverse supplied tensorator,
the shifted-unit comparison e tensor the representative comparison, and the
corresponding Koszul-unitor comparison over Z. Choose the unit and representative
comparisons jointly in this construction. The tensorator associativity equation
identifies successive tensor rewrites, and its two unit equations identify their
unit specializations. The same formulas on the two summands of each telescope
cone commute with its transition, inclusion, and projection maps. They therefore
identify the translated telescope comparison with the displayed composite.

Naturality of the representative construction, the termwise Koszul maps, unitors,
and supplied tensorator gives naturality for maps of these models. Common K-flat
replacement maps compare two presentations; after their images are inverted the
formulas agree. Thus the comparisons are well defined on the indicated homotopy
objects and all homotopy morphisms between them. Every representative comparison
is a composite of isomorphisms. This assertion stops at concrete telescopes and
their one-fold translates: extension to arbitrary K-flat representatives uses a
separate resolution and right-fraction argument. Zero towers, zero transition
maps, and empty schemes satisfy the same cone and unit identities. The joint
normalization in the middle paragraph is the remaining supplied-tensorator
calculation inherited from the parent plan, not a statement that an arbitrary
previously chosen K-flat counit already has this normalization.
(blueprint: lem-sc-normalized-flat-telescope-comparison). -/
theorem exists_normalized_flat_telescope_comparison
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive] :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∃ α : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        flatTelescopeShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ≅
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).obj X),
        (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : flatTelescopeShiftRepresentative Y X) (hX' : flatTelescopeShiftRepresentative Y X')
          (s : X ⟶ X'),
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (α X' hX').hom =
            (α X hX).hom ≫
              ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                (DerivedCategory.Qh : HomotopyCategory
                  (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                  schemeDerivedCategory Z)).map s) ∧
        ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (htel : isFlatTelescope Y P),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        (α (X⟦(1 : ℤ)⟧) ⟨P, htel, Or.inr rfl⟩).hom ≫
            (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (α X ⟨P, htel, Or.inl rfl⟩).hom⟦(1 : ℤ)⟧' := by sorry

end AlgebraicGeometry
