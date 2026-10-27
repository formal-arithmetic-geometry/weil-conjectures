/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q149
-/
module

public import Sheaf.Algebra.Homology.RingedSiteScalarGlobalSections
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Sheaf.Paper.ProjectionMateExact
import Sheaf.CategoryTheory.KInjectiveDerivedMapComputation
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.SixFunctors.ResolvingDerivedAdjunction
import Sheaf.CategoryTheory.RingedToposKFlatPullback

/-! # Shifted-unit representation of ringed hypercohomology

Source: Stacks Project, Cohomology on Sites, Tags 08JA and 0BKV.
(blueprint: lem-sfb-ringed-hypercohomology-shifted-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RingedHypercohomologyShiftedUnit
open RingedSiteScalarGlobalSections

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u}) (A : Type u) [CommRing A]
  (s : A →+* Scalars R)
  [HasDerivedCategory.{w} (Modules R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- The structure sheaf, using the recorded module category.
Source: Stacks 08JA (blueprint: lem-sfb-ringed-hypercohomology-shifted-unit). -/
abbrev unitModule := SheafOfModules.unit
  ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

/-- The literal single complex with the structure sheaf in degree `n`.
Source: Stacks 08JA (blueprint: lem-sfb-ringed-hypercohomology-shifted-unit). -/
abbrev unitComplex (n : ℤ) := (HomologicalComplex.single (Modules R) (.up ℤ) n).obj
  (unitModule R)

/-- The literal single complex with `A` in degree `n`.
Source: Stacks 08JA (blueprint: lem-sfb-ringed-hypercohomology-shifted-unit). -/
abbrev scalarComplex (n : ℤ) := (HomologicalComplex.single (ModuleCat A) (.up ℤ) n).obj
  (ModuleCat.of A A)

/-- Hypercohomology with its specified scalar action, in every integer degree.
Source: Stacks 08JA (blueprint: lem-sfb-ringed-hypercohomology-shifted-unit). -/
abbrev hyper (n : ℤ) := derivedSections R A s ⋙ DerivedCategory.homologyFunctor (ModuleCat A) n

/-- The canonical identification of the cohomology of the localized single complex.
Source: Stacks 08JA (blueprint: lem-sfb-ringed-hypercohomology-shifted-unit). -/
def unitHomologyIso (n : ℤ) :
    (DerivedCategory.homologyFunctor (Modules R) n).obj
      (DerivedCategory.Q.obj (unitComplex R n)) ≅ unitModule R :=
  (DerivedCategory.homologyFunctorFactors (Modules R) n).app _ ≪≫
    HomologicalComplex.singleObjHomologySelfIso (.up ℤ) n (unitModule R)

/-- The class of one in the cohomology of the scalar single complex.
Source: Stacks 08JA (blueprint: lem-sfb-ringed-hypercohomology-shifted-unit). -/
def scalarOne (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat A) n).obj
      (DerivedCategory.Q.obj (scalarComplex A n)) :=
  ((DerivedCategory.homologyFunctorFactors (ModuleCat A) n).inv.app _)
    ((HomologicalComplex.singleObjHomologySelfIso (.up ℤ) n (ModuleCat.of A A)).inv 1)

/-- Evaluation of a derived morphism at the cohomology class of one.
Source: Stacks 08JA (blueprint: lem-sfb-ringed-hypercohomology-shifted-unit). -/
def evaluate (n : ℤ) (E : DerivedCategory (ModuleCat A))
    (f : DerivedCategory.Q.obj (scalarComplex A n) ⟶ E) :
    (DerivedCategory.homologyFunctor (ModuleCat A) n).obj E :=
  ((DerivedCategory.homologyFunctor (ModuleCat A) n).map f) (scalarOne A n)

/-- Transport of a global cocycle class through any specified representative.
Source: Stacks 08JA (blueprint: lem-sfb-ringed-hypercohomology-shifted-unit). -/
def cocycleClass (n : ℤ) (K : DerivedCategory (Modules R))
    (I : CochainComplex (Modules R) ℤ) (i : DerivedCategory.Q.obj I ≅ K)
    (z : (((sections R A s).mapHomologicalComplex (.up ℤ)).obj I).cycles n) :
    (hyper R A s n).obj K :=
  ((hyper R A s n).map i.hom)
    (((DerivedCategory.homologyFunctor (ModuleCat A) n).map
        ((sections R A s).rightDerivedFunctorUnitQ I))
      (((DerivedCategory.homologyFunctorFactors (ModuleCat A) n).inv.app _)
        (((((sections R A s).mapHomologicalComplex (.up ℤ)).obj I).homologyπ n) z)))

/-- The component of a single-complex map as a map from the structure sheaf.
Source: Stacks 08JA (blueprint: lem-sfb-ringed-hypercohomology-shifted-unit). -/
def component (n : ℤ) (I : CochainComplex (Modules R) ℤ)
    (f : unitComplex R n ⟶ I) : unitModule R ⟶ I.X n :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) n (unitModule R)).inv ≫ f.f n

/-- A compatible family with the already specified external scalar action.
Source: Stacks 08JA (blueprint: lem-sfb-ringed-hypercohomology-shifted-unit). -/
def scalarSection (M : Modules R) (x : M.sections) : (sections R A s).obj M :=
  ⟨x.val, fun _ _ i ↦ x.property i⟩

/-- The canonical unit and derived-adjunction comparisons, the additive representation,
and its edge map, including their normalization on every K-injective representative.
The ordinary adjunction is to the actual scalar sections functor; thus its left adjoint
is extension of scalars from the point, unique with its adjunction. The comparison on
single complexes is pinned by the left-derived comparison and the ordinary unit map,
so it is the unit/shift comparison rather than an arbitrary isomorphism.

Source: Stacks Project, Tags 08JA and 0BKV, with Tags 07A4 and 07A6.
(blueprint: lem-sfb-ringed-hypercohomology-shifted-unit).

Proof:
1. Apply the ringed projection adjunction (lem-weil-pbc-ringed-projection-mate-exact)
to the point morphism determined by s. On the rank-one scalar module its ordinary
adjunction evaluates a map at one, giving the structural unit isomorphism. Derive by
K-flat resolutions (lem-pc-kflat-resolution) and use the canonical shift comparisons.
2. A map O_n to a complex I is exactly a compatible global cocycle z, by a ↦ az.
Homotopies are exactly boundaries. This gives the additive Hom/cohomology bijection.
3. Choose a K-injective representative (prop-pur-kinjective-resolutions-exist).
K-injective localization (lem-weil-pbc-kinjective-hom-derived) transfers this bijection
to D(O). The derived-map computation (lem-sf-kinjective-derived-map-computation)
gives naturality for every derived morphism and independence of the representative.
4. The identical calculation for A_n, which is K-projective, gives evaluation at one
in D(A) (lem-coef-kprojective-derived-hom-bijection).
5. The resolving adjunction normalization (lem-sfb-resolving-derived-adjunction-normalization)
identifies the derived adjunct of f_z with the termwise adjunct sending 1 to z.
Thus gamma is the inverse of the stated adjunction/evaluation composite, with the
canonical unit comparison. K-flat pullback is supplied by
lem-weil-pbc-supplied-ringed-topos-kflat-pullback.
6. Applying cohomology to f_z sends a to the sheaf class of az. Evaluation on the unit
therefore is the cocycle quotient of Tag 0BKV. Boundaries vanish in this quotient.
Naturality of gamma and cohomology proves naturality and resolution independence of
this edge map. All computations use compatible families, without a final site object. -/
theorem shiftedUnitRepresentation :
    ∃ (P : ModuleCat.{u} A ⥤ Modules R) (_ : P.Additive)
      (adj : P ⊣ sections R A s) (unit : P.obj (ModuleCat.of A A) ≅ unitModule R)
      (L : DerivedCategory (ModuleCat A) ⥤ DerivedCategory (Modules R))
      (ε : DerivedCategory.Q ⋙ L ⟶ P.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
      L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ)) ∧
      (∀ (M : Modules R) (f : P.obj (ModuleCat.of A A) ⟶ M) (U : Cᵒᵖ),
        (adj.homEquiv _ _ f 1).val U =
          (unit.inv ≫ f).val.app U (1 : R.obj.obj U)) ∧
      ∃ (d : L ⊣ derivedSections R A s)
        (unitL : ∀ n : ℤ, L.obj (DerivedCategory.Q.obj (scalarComplex A n)) ≅
          DerivedCategory.Q.obj (unitComplex R n)),
        (∀ n : ℤ, (unitL n).hom = ε.app (scalarComplex A n) ≫
          DerivedCategory.Q.map
            (((HomologicalComplex.singleMapHomologicalComplex P (.up ℤ) n).app
              (ModuleCat.of A A)).hom ≫
              (HomologicalComplex.single (Modules R) (.up ℤ) n).map unit.hom)) ∧
        (∀ (M : CochainComplex (ModuleCat A) ℤ) (I : CochainComplex (Modules R) ℤ)
          (f : (P.mapHomologicalComplex (.up ℤ)).obj M ⟶ I),
          d.homEquiv _ _ (ε.app M ≫ DerivedCategory.Q.map f) =
            DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv M I f) ≫
              (sections R A s).rightDerivedFunctorUnitQ I) ∧
        ∃ (γ : ∀ (n : ℤ) (K : DerivedCategory (Modules R)),
            (hyper R A s n).obj K ≃+
              (DerivedCategory.Q.obj (unitComplex R n) ⟶ K))
          (edge : ∀ (n : ℤ) (K : DerivedCategory (Modules R)),
            (hyper R A s n).obj K →+
              (sections R A s).obj ((DerivedCategory.homologyFunctor (Modules R) n).obj K)),
          (∀ (n : ℤ) (K : DerivedCategory (Modules R)) (x : (hyper R A s n).obj K),
            evaluate A n _ (d.homEquiv _ _ ((unitL n).hom ≫ γ n K x)) = x) ∧
          (∀ (n : ℤ) (E : DerivedCategory (ModuleCat A)),
            Function.Bijective (evaluate A n E)) ∧
          (∀ (n : ℤ) (K K' : DerivedCategory (Modules R)) (h : K ⟶ K')
            (x : (hyper R A s n).obj K),
            γ n K' (((hyper R A s n).map h) x) = γ n K x ≫ h) ∧
          (∀ (n : ℤ) (K : DerivedCategory (Modules R))
            (I : CochainComplex (Modules R) ℤ) (_ : I.IsKInjective)
            (i : DerivedCategory.Q.obj I ≅ K)
            (z : (((sections R A s).mapHomologicalComplex (.up ℤ)).obj I).cycles n),
            ∃ f : unitComplex R n ⟶ I,
              (∀ (U : Cᵒᵖ) (a : R.obj.obj U),
                (component R n I f).val.app U a = a •
                  (((((sections R A s).mapHomologicalComplex (.up ℤ)).obj I).iCycles n)
                    z).val U) ∧
              γ n K (cocycleClass R A s n K I i z) = DerivedCategory.Q.map f ≫ i.hom) ∧
          (∀ (n : ℤ) (K : DerivedCategory (Modules R)) (x : (hyper R A s n).obj K),
            edge n K x = scalarSection R A s _ (SheafOfModules.unitHomEquiv _
              ((unitHomologyIso R n).inv ≫
                (DerivedCategory.homologyFunctor (Modules R) n).map (γ n K x)))) ∧
          (∀ (n : ℤ) (K K' : DerivedCategory (Modules R)) (h : K ⟶ K')
            (x : (hyper R A s n).obj K),
            ((sections R A s).map
              ((DerivedCategory.homologyFunctor (Modules R) n).map h)) (edge n K x) =
                edge n K' (((hyper R A s n).map h) x)) ∧
          (∀ (n : ℤ) (K : DerivedCategory (Modules R))
            (I : CochainComplex (Modules R) ℤ) (_ : I.IsKInjective)
            (i : DerivedCategory.Q.obj I ≅ K)
            (z : (((sections R A s).mapHomologicalComplex (.up ℤ)).obj I).cycles n),
            ∃ y : (I.cycles n).sections,
              (∀ U : Cᵒᵖ, (SheafOfModules.sectionsMap (I.iCycles n) y).val U =
                (((((sections R A s).mapHomologicalComplex (.up ℤ)).obj I).iCycles n)
                  z).val U) ∧
              edge n K (cocycleClass R A s n K I i z) =
                scalarSection R A s _ (SheafOfModules.sectionsMap
                  (I.homologyπ n ≫ (DerivedCategory.homologyFunctorFactors
                    (Modules R) n).inv.app I ≫
                      (DerivedCategory.homologyFunctor (Modules R) n).map i.hom) y)) := by
  sorry

end CategoryTheory.RingedHypercohomologyShiftedUnit
