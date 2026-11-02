/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.SupportCohomology
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# Supported cohomology as morphisms

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/lem-pur-supported-hom.md`
(blueprint: `lem-pur-supported-hom`).

The postponed identification is the composite of the three comparisons in the source.
First, supported sections are computed by the derived closed-support functor.  Second,
the coefficient unit and the derived tensor--Hom comparison identify global sections
with maps from the unit.  Third, the closed-immersion exceptional adjunction transports
those maps from `Z` to maps on `X`.  The cocycle characterization below records the
resulting comparison on supported cocycles; it deliberately quantifies over a packaged
representative rather than asserting a false uniqueness statement for cocycle maps.

The coefficients are the finite `ModuleCat A` model `ModuleDerivedCategory`; it is compared
with the recorded `CondensedRing` model by
`AlgebraicGeometry.ProEtale.finiteCoefficientDerivedEquivalence`.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.HomComplex
open CochainComplex.HomComplex.Cocycle

namespace AlgebraicGeometry.ProEtale

/-- The type of natural identifications `H^a_Z(X, F) ≅ Hom_{D(X,Λ)}(i_*Λ_Z, F[a])` for
bounded-below `F` (blueprint: lem-pur-supported-hom, statement). -/
abbrev SupportedCohomologyHomGeneralType
    {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom]
    {Z : Scheme.{u}} (i : Z ⟶ X.left) [IsClosedImmersion i]
    (A : Type (u + 1)) [CommRing A] [Finite A] (a : ℤ) :=
  ((DerivedCategory.Plus.ι ⋙
      derivedSupportCohomology (ModuleCat.{u + 1} A) i a ⋙
      forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) ≅
    (DerivedCategory.Plus.ι ⋙
      shiftFunctor (ModuleDerivedCategory X.left A) a ⋙
      preadditiveCoyoneda.obj (op
        ((DerivedCategory.singleFunctor
          (Sheaf (Scheme.ProEt.topology X.left) (ModuleCat.{u + 1} A)) 0).obj
          ((lowerStar (ModuleCat.{u + 1} A) i).obj
            ((constantSheaf (Scheme.ProEt.topology Z)
              (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)))))))

/-- The pro-étale sections with support in `Z`, `Γ_Z(X, -)` (blueprint: lem-pur-supported-hom,
proof step 1). -/
abbrev supportedCohomologyHomGeneralSections
    {k : Type u} [Field k]
    {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom]
    {Z : Scheme.{u}} (i : Z ⟶ X.left) [IsClosedImmersion i]
    (A : Type (u + 1)) [CommRing A] [Finite A] :=
  Sheaf.ΓSupport (Scheme.ProEt.topology X.left) (ModuleCat.{u + 1} A)
    (op (Scheme.ProEt.mk i.openComplement.ι))

/-- Degree-`a` supported cocycles of a complex `I` (blueprint: lem-pur-supported-hom,
proof step 1). -/
abbrev SupportedCohomologyHomGeneralCocycle
    {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom]
    {Z : Scheme.{u}} (i : Z ⟶ X.left) [IsClosedImmersion i]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (I : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X.left) (ModuleCat.{u + 1} A))) (a : ℤ) :=
  (((supportedCohomologyHomGeneralSections i A).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I.obj).cycles a

/-- The derived unit of `Γ_Z(X, -)` on a complex `I` (blueprint: lem-pur-supported-hom,
proof step 1). -/
noncomputable def supportedCohomologyHomGeneralDerivedUnit
    {k : Type u} [Field k]
    {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom]
    {Z : Scheme.{u}} {i : Z ⟶ X.left} [IsClosedImmersion i]
    {A : Type (u + 1)} [CommRing A] [Finite A] (I : CochainComplex
      (Sheaf (Scheme.ProEt.topology X.left) (ModuleCat.{u + 1} A)) ℤ) :
    DerivedCategory.Q.obj
        (((globalSectionsWithSupport (ModuleCat.{u + 1} A) i).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ⟶
      (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} A) i).obj
        (DerivedCategory.Q.obj I) :=
  (DerivedCategory.quotientCompQhIso (ModuleCat.{u + 1} A)).inv.app _ ≫
    (globalSectionsWithSupport (ModuleCat.{u + 1} A) i).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj I)

/-- The class in `H^a_Z(X, I)` of a supported cocycle (blueprint: lem-pur-supported-hom,
proof step 1). -/
noncomputable def supportedCohomologyHomGeneralCycleClass
    {k : Type u} [Field k]
    {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom]
    {Z : Scheme.{u}} {i : Z ⟶ X.left} [IsClosedImmersion i]
    {A : Type (u + 1)} [CommRing A] [Finite A]
    (I : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X.left) (ModuleCat.{u + 1} A))) (a : ℤ)
    (s : SupportedCohomologyHomGeneralCocycle X i A I a) :
    ((DerivedCategory.Plus.ι ⋙
      derivedSupportCohomology (ModuleCat.{u + 1} A) i a ⋙
      forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).obj
        (DerivedCategory.Plus.Q.obj I)) :=
  ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) a).map
      (supportedCohomologyHomGeneralDerivedUnit (X := X) (i := i) (I := I.obj))
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} A) a).inv.app _
        ((((supportedCohomologyHomGeneralSections i A).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I.obj).homologyπ a s)))

/-- `f : i_*Λ_Z ⟶ I^a` sends the global unit section `1` to the supported cocycle `s`
(blueprint: lem-pur-supported-hom, proof steps 2--3). -/
def SupportedCohomologyHomGeneralEvaluation
    {k : Type u} [Field k]
    {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom]
    {Z : Scheme.{u}} {i : Z ⟶ X.left} [IsClosedImmersion i]
    {A : Type (u + 1)} [CommRing A] [Finite A]
    (I : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X.left) (ModuleCat.{u + 1} A))) (a : ℤ)
    (s : SupportedCohomologyHomGeneralCocycle X i A I a)
    (f : (lowerStar (ModuleCat.{u + 1} A) i).obj
      ((constantSheaf (Scheme.ProEt.topology Z)
        (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)) ⟶ I.obj.X a) : Prop :=
  ((Sheaf.ΓSupportι (Scheme.ProEt.topology X.left) (ModuleCat.{u + 1} A)
      (op (Scheme.ProEt.mk i.openComplement.ι))).app (I.obj.X a) ≫
      (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X.left)
        (ModuleCat.{u + 1} A) (Scheme.ProEt.isTerminalMkId X.left)).hom.app
        (I.obj.X a)).hom
    ((((supportedCohomologyHomGeneralSections i A).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I.obj).iCycles a s) =
    f.hom.app (op (Scheme.ProEt.mk (𝟙 X.left)))
      ((Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A)
        (ModuleCat.of A A)).hom.app (op (Scheme.ProEt.mk (𝟙 X.left)))
        ((toSheafify (Scheme.ProEt.topology X.left)
          ((Functor.const X.left.ProEtᵒᵖ).obj (ModuleCat.of A A))).app
            (op (Scheme.ProEt.mk (𝟙 X.left))) (1 : A)))

/-- The characterization by the canonical injective-cocycle roof.

The class of a supported cocycle is transported by the actual derived unit of the
recorded pro-etale support functor.  The evaluation premise ties a cocycle map to that
supported cocycle, so the formula quantifies over all such maps and does not assert a
false uniqueness statement for maps whose roof is a boundary. -/
def SupportedCohomologyHomGeneralCharacterization
    {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom]
    {Z : Scheme.{u}} (i : Z ⟶ X.left) [IsClosedImmersion i]
    (A : Type (u + 1)) [CommRing A] [Finite A] (a : ℤ)
    (χ : SupportedCohomologyHomGeneralType X i A a) : Prop :=
  ∀ (I : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X.left) (ModuleCat.{u + 1} A)))
    (_hi : ∀ r : ℤ, Injective (I.obj.X r))
    (s : SupportedCohomologyHomGeneralCocycle X i A I a)
    (f : (lowerStar (ModuleCat.{u + 1} A) i).obj
      ((constantSheaf (Scheme.ProEt.topology Z)
        (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)) ⟶ I.obj.X a)
    (hf : f ≫ I.obj.d a (a + 1) = 0)
    (_heval : SupportedCohomologyHomGeneralEvaluation I a s f),
    (χ.hom.app (DerivedCategory.Plus.Q.obj I)).hom
        (supportedCohomologyHomGeneralCycleClass I a s) =
      (DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app _ ≫
        (ShiftedHom.map (Cocycle.equivHomShift.symm
          (CochainComplex.HomComplex.Cocycle.fromSingleMk f
            (zero_add a) (a + 1) rfl hf)) DerivedCategory.Q) ≫
        ((DerivedCategory.quotientCompQhIso _).inv.app I.obj)⟦a⟧'


/-- The specified supported-Hom identification, characterized by the three comparisons
in the proof of the blueprint lemma.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/lem-pur-supported-hom.md`, proof:
(1) supported sections and the derived closed-support functor; (2) coefficient-unit
tensor--Hom and the degree-`a` derived Hom comparison; (3) the closed-immersion
exceptional adjunction and its shift comparison. -/
theorem existsUnique_supportedCohomologyHomGeneral
    {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom]
    {Z : Scheme.{u}} (i : Z ⟶ X.left) [IsClosedImmersion i]
    (A : Type (u + 1)) [CommRing A] [Finite A] (a : ℤ) :
    ∃! χ : SupportedCohomologyHomGeneralType X i A a,
      SupportedCohomologyHomGeneralCharacterization X i A a χ := by
  sorry

/-- The natural identification used by the smooth-purity statement.

It is obtained from the uniquely characterized composite above, so its data are the
specified comparison and not an arbitrary inhabitant of `Nonempty`.  Source: the
nested blueprint path recorded in `lem-pur-supported-hom.md` (proof steps 1--3)
(blueprint: lem-pur-supported-hom). -/
noncomputable def supportedCohomologyHomGeneral
    {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom]
    {Z : Scheme.{u}} (i : Z ⟶ X.left) [IsClosedImmersion i]
    (A : Type (u + 1)) [CommRing A] [Finite A] (a : ℤ) :
    SupportedCohomologyHomGeneralType X i A a :=
  (existsUnique_supportedCohomologyHomGeneral X i A a).choose

end AlgebraicGeometry.ProEtale
