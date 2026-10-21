/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AcyclicFlatProperCoefficientModel
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization
public import Sheaf.SixFunctors.EtaleOpenTensor
public import Sheaf.Paper.ProperOpenCoefficientRefinement
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat

/-! # Sheetwise computation of the compactified etale coefficient arrow

Source: Stacks Project, more-etale.tex, Tag 0GL6; etale-cohomology.tex,
Tags 03S5 and 0F4L; blueprint Charts paragraph of det-sp-reduction-exceptional
(blueprint: lem-sp-etale-sum-coefficient-computation).

The graph map and derived units fix the model identifications. The coefficient
arrow is the actual proper counit mate followed by the normalized open comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Degreewise open extension of the supplied complex.
Source: Stacks 0GL6 (blueprint: lem-sp-etale-sum-coefficient-computation). -/
abbrev compactifiedEtaleOpenComplex
    (A : Type (u + 1)) [CommRing A] {U V : Scheme.{u}} {e : U ⟶ V}
    (c : Compactification e)
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapHomologicalComplex (.up ℤ)).obj P

/-- Degreewise proper direct image of open extension.
Source: Stacks 0GL6 (blueprint: lem-sp-etale-sum-coefficient-computation). -/
abbrev compactifiedEtaleDirectComplex
    (A : Type (u + 1)) [CommRing A] {U V : Scheme.{u}} {e : U ⟶ V}
    (c : Compactification e)
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  ((lowerStar (ModuleCat.{u + 1} A) c.g).mapHomologicalComplex (.up ℤ)).obj
    (compactifiedEtaleOpenComplex A c P)

/-- Degreewise extension along the canonical clopen graphs of the sheets.
Source: Stacks 0F4L, 03S5 (blueprint: lem-sp-etale-sum-coefficient-computation). -/
def etaleSumCompactifiedComplexMap
    (A : Type (u + 1)) [CommRing A] {U V : Scheme.{u}}
    (e : U ⟶ V) [Etale e] [IsSeparated e] (c : Compactification e)
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapHomologicalComplex
      (.up ℤ)).obj P ⟶ compactifiedEtaleDirectComplex A c P :=
  (NatTrans.mapHomologicalComplex (etaleCompactificationGraphMap A e c) (.up ℤ)).app P ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)) (.up ℤ)).inv.app P

/-- The specified acyclic-model boundary, from the sum complex to compact supports:
localize the graph map, apply the proper derived unit, and insert the exact open
localization factor. No isomorphism or representative is chosen.
Source: Stacks 0GL6, 015E (blueprint: lem-sp-etale-sum-coefficient-computation). -/
def etaleSumCompactifiedModelBoundary
    (A : Type (u + 1)) [CommRing A] {U V : Scheme.{u}}
    (e : U ⟶ V) [Etale e] [IsSeparated e] (c : Compactification e)
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    DerivedCategory.Q.obj
        (((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapHomologicalComplex
          (.up ℤ)).obj P) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
        (DerivedCategory.Q.obj P) :=
  DerivedCategory.Q.map (etaleSumCompactifiedComplexMap A e c P) ≫
    properAcyclicComparison A c.g (compactifiedEtaleOpenComplex A c P) ≫
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) c.g).map
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryFactors.inv.app P)

/-- The ordinary sum/scalar isomorphism fixed by the sum/evaluation and scalar
adjunctions and the actual restriction/scalar comparison. It extends scalars on
each sheet, rather than permuting sheets or choosing an endpoint isomorphism.
Source: Stacks 03S5, 0GL6 (blueprint: lem-sp-etale-sum-coefficient-computation). -/
def etaleSumScalarSheafIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] :
    etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⋙
        ProEtale.etaleSheafExtendScalars φ V ≅
      ProEtale.etaleSheafExtendScalars φ U ⋙
        etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance :=
  ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance).comp
    (ProEtale.etaleSheafExtendScalarsAdjunction φ V)).leftAdjointUniq
    (((ProEtale.etaleSheafExtendScalarsAdjunction φ U).comp
      (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) e inferInstance)).ofNatIsoRight
        (upperStarRestrictScalarsIsoSheaf φ e).symm)

/-- The sheetwise scalar chain map; mapping a natural transformation degreewise
makes it commute with the differentials, including the zero and empty-sheet cases.
Source: Stacks 03S5, 0GL6 (blueprint: lem-sp-etale-sum-coefficient-computation). -/
def etaleSumScalarComplexMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    coefficientExtendedComplex φ V
        (((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapHomologicalComplex
          (.up ℤ)).obj P) ⟶
      ((etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapHomologicalComplex
        (.up ℤ)).obj (coefficientExtendedComplex φ U P) :=
  (Functor.mapHomologicalComplexCompIso
    (Iso.refl (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⋙
      ProEtale.etaleSheafExtendScalars φ V)) (.up ℤ)).hom.app P ≫
    (NatTrans.mapHomologicalComplex (etaleSumScalarSheafIso φ e).hom (.up ℤ)).app P ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ProEtale.etaleSheafExtendScalars φ U ⋙
        etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance)) (.up ℤ)).inv.app P

/-- A sheet generator, using the sum-adjunction unit and the identification of etale
inverse image with literal restriction. An object S over U is precisely a test object
with a specified lift to U, so this includes every sheet over every etale test object.
Source: Stacks 03S5, 0F4L (blueprint: lem-sp-etale-sum-coefficient-computation). -/
def etaleSumSheetMap
    (A : Type (u + 1)) [CommRing A] {U V : Scheme.{u}}
    (e : U ⟶ V) [Etale e]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (S : U.Etale) :
    M.obj.obj (Opposite.op S) ⟶
      ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M).obj.obj
        (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj S)) :=
  (((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance).unit.app M) ≫
    (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e inferInstance).hom.app
      ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M)).hom.app (Opposite.op S)

/-- The local pure tensor x tensor b, via the actual scalar-adjunction unit. The
explicit identity reads its value in the B-module, before restricting coefficients.
Source: Stacks 0GL6 (blueprint: lem-sp-etale-sum-coefficient-computation). -/
def etaleScalarPureTensor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (T : Scheme.{u}) (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (S : T.Etaleᵒᵖ) (x : M.obj.obj S) (b : B) :
    ((ProEtale.etaleSheafExtendScalars φ T).obj M).obj.obj S :=
  b • @id (((ProEtale.etaleSheafExtendScalars φ T).obj M).obj.obj S)
    ((((ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit.app M).hom.app S).hom x)

/-- A bounded flat complex computes the actual compactified etale coefficient arrow
by the sheetwise tensor chain map, under the specified graph and acyclic boundaries.
The last equation on generators says x_s tensor b maps to x_s tensor b in the same
sheet; additivity gives the finite-support formula, even when the sheet set is empty.
No flatness or Tor-dimension assumption is made on B over A.

Source: Stacks 0GL6, 03S5, 0F4L; blueprint Charts paragraph
(blueprint: lem-sp-etale-sum-coefficient-computation).

Proof:
1. Properness makes c.Z Noetherian (lem-weil-pbc-finite-type-over-noetherian).
Apply lem-asd-etale-compact-support-normalization to each P.X n in degree zero,
over A and then to its ordinary B-extension. Higher proper direct images vanish;
the degree-zero comparison is extension along the clopen graphs of the sheets.
2. Open extension preserves flatness (lem-coef-etale-open-tensor). Sum extension
preserves flatness (lem-pur-etale-sum-flat-kflat); transport across the preceding
graph comparison to obtain flatness of the direct-image terms. Both functors
preserve the finite support interval. By lem-pc-bounded-above-flat-kflat-site the
open complex and its direct image are K-flat, as are P and its sum extension.
3. Apply lem-sp-acyclic-flat-proper-coefficient-model to j_!P. Its B-acyclicity
hypothesis follows through the ordinary open tensor isomorphism. The theorem
identifies the named proper B-adjoint counit transpose with the degreewise
ordinary projection morphism under the canonical derived units and scalar models.
Compose with the open tensor comparison, normalized to the identity on U.
4. On an etale test object, direct image evaluates on the fibre product. The
ordinary counit sends z tensor b to z tensor the restriction of b. Taking a sheet
component commutes with this restriction, giving x_s tensor b on the same sheet.
Both sum extension and tensor are locally generated by these generators; balancing
and additivity give equality without a globally split test scheme or flatness of B.
5. The formula commutes with differentials, giving (d x_s tensor b)_s on either
side. Naturality of the canonical model comparisons then gives the displayed
localized equality for the actual proper/open coefficient map. Finite support is
preserved; the empty sheet case is the unique map from zero to zero. This also
covers P=0, the identity coefficient map and the zero coefficient ring. -/
theorem etaleSumCoefficientComputation
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [IsNoetherian U] [IsNoetherian V] (c : Compactification e)
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hflat : ∀ n : ℤ, exactFunctor _ _ (MonoidalCategory.tensorRight (P.X n))) :
    (∀ n : ℤ, exactFunctor _ _
      (MonoidalCategory.tensorRight ((compactifiedEtaleOpenComplex A c P).X n))) ∧
      (∀ n : ℤ, exactFunctor _ _
        (MonoidalCategory.tensorRight ((compactifiedEtaleDirectComplex A c P).X n))) ∧
      etaleKFlat c.Z A (compactifiedEtaleOpenComplex A c P) ∧
      etaleKFlat V A (compactifiedEtaleDirectComplex A c P) ∧
      (∀ (n : ℤ) (q : ℕ), 0 < q → IsZero
        ((DerivedCategory.homologyFunctor
          (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ)).obj
          ((rightDerivedLowerStar (ModuleCat.{u + 1} A) c.g).obj
            ((DerivedCategory.singleFunctor
              (Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj
              ((compactifiedEtaleOpenComplex A c P).X n))))) ∧
      (∀ (n : ℤ) (q : ℕ), 0 < q → IsZero
        ((DerivedCategory.homologyFunctor
          (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)) (q : ℤ)).obj
          ((rightDerivedLowerStar (ModuleCat.{u + 1} B) c.g).obj
            ((DerivedCategory.singleFunctor
              (Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} B)) 0).obj
              ((compactifiedEtaleOpenComplex B c (coefficientExtendedComplex φ U P)).X n))))) ∧
      IsIso (properAcyclicComparison A c.g (compactifiedEtaleOpenComplex A c P)) ∧
      IsIso (properAcyclicComparison B c.g
        (compactifiedEtaleOpenComplex B c (coefficientExtendedComplex φ U P))) ∧
      IsIso (etaleSumCompactifiedComplexMap A e c P) ∧
      IsIso (etaleSumCompactifiedComplexMap B e c (coefficientExtendedComplex φ U P)) ∧
      IsIso (scalarExtensionRepresentative φ U P) ∧
      IsIso (scalarExtensionRepresentative φ V
        (((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapHomologicalComplex
          (.up ℤ)).obj P)) ∧
      ((scalarExtension φ V).map (etaleSumCompactifiedModelBoundary A e c P) ≫
          (properCoefficientMap φ c.g).app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj
              (DerivedCategory.Q.obj P)) ≫
          (rightDerivedLowerStar (ModuleCat.{u + 1} B) c.g).map
            (properOpenCoefficientOpenIso φ c.i (DerivedCategory.Q.obj P)).hom ≫
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
            (scalarExtensionRepresentative φ U P) =
        scalarExtensionRepresentative φ V
            (((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapHomologicalComplex
              (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (etaleSumScalarComplexMap φ e P) ≫
          etaleSumCompactifiedModelBoundary B e c (coefficientExtendedComplex φ U P)) ∧
      (∀ (n : ℤ) (S : U.Etale) (x : (P.X n).obj.obj (Opposite.op S)) (b : B),
        (((etaleSumScalarSheafIso φ e).hom.app (P.X n)).hom.app
            (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj S))).hom
            (etaleScalarPureTensor φ V
              ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj (P.X n))
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj S))
              ((etaleSumSheetMap A e (P.X n) S).hom x) b) =
          (etaleSumSheetMap B e ((ProEtale.etaleSheafExtendScalars φ U).obj (P.X n)) S).hom
            (etaleScalarPureTensor φ U (P.X n) (Opposite.op S) x b)) := by
  sorry

end AlgebraicGeometry.Etale
