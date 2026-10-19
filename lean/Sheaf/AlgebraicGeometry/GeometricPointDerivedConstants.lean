/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.CategoryTheory.Sites.Point.Flat
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import Sheaf.AlgebraicGeometry.AbelianSheavesGModules
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.PointedEtaleStalk

/-!
# Normalized constant and stalk equivalence at a geometric point

Source: Stacks Project, Tags 04JQ and 0F0F
(blueprint: lem-kun-geometric-point-derived-constants).

We encode abelian groups as modules over `ULift ℤ`. Restriction along `ULift.ringEquiv`
and `ModuleCat.forget₂AddCommGroupIsEquivalence` identify these with `AddCommGrpCat`.
The lift only places the fixed ring of integers in the coefficient universe. This retains the
ordinary integer tensor product, including its unbounded derived tensor and Koszul symmetry.
All functors below are specializations of the recorded stalk and constant-sheaf constructions.
The data structure packages the clauses of the theorem, with their canonical normalizations.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- The constant-sheaf functor at `Spec Ω`, in the integer-module encoding of abelian groups.
Source: Stacks Tags 04JQ, 0F0F (blueprint: lem-kun-geometric-point-derived-constants). -/
noncomputable abbrev geometricPointConstants (Ω : Type u) [Field Ω] :=
  constantSheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))

/-- The actual stalk at the identity geometric point, not an arbitrary equivalent functor.
Source: Stacks Tag 04JQ (blueprint: lem-kun-geometric-point-derived-constants). -/
noncomputable abbrev geometricPointStalk (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :=
  ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{u + 1}).sheafFiber
    (A := ModuleCat.{u + 1} (ULift.{u + 1} ℤ))

/-- The canonical constant-germ unit. It is inverse to the existing constant-stalk isomorphism,
whose construction is the sheafification unit followed by the germ map.
Source: Stacks Tags 04JQ, 03PT, 040R
(blueprint: lem-kun-geometric-point-derived-constants). -/
noncomputable abbrev geometricPointConstantGerm (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    𝟭 (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) ≅ geometricPointConstants Ω ⋙ geometricPointStalk Ω :=
  (((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{u + 1}).constantSheafCompSheafFiberIso
    (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).symm

/-- The canonical derived Koszul symmetry for ordinary integer complexes.
Source: Stacks Tags 03EK, 0F0F (blueprint: lem-kun-geometric-point-derived-constants).
This specializes the existing derived braiding; it chooses no additional structure. -/
noncomputable def geometricPointIntegerDerivedSymmetry
    (K L : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) : K ⊗ L ≅ L ⊗ K :=
  DerivedMonoidal.braiding'
    (DerivedCategory.Qh (C := ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    (HomotopyCategory.quasiIso (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) (.up ℤ)) K L


/-- All clauses of the normalized point equivalence. The underlying functors are fixed;
monoidality of the localization factorizations fixes the derived tensorators on K-flat
representatives. The derived adjunction is the termwise descent of the displayed adjunction.
Source: Stacks Tags 04JQ, 03EK, 010N, 05RU, 06YS, 0DEN, 0F0F
(blueprint: lem-kun-geometric-point-derived-constants). -/
structure GeometricPointDerivedConstantsData (Ω : Type u) [Field Ω] [IsAlgClosed Ω] where
  /-- The stalk is additive. -/
  [stalkAdditive : (geometricPointStalk Ω).Additive]
  /-- Equivalence of the actual stalk functor. -/
  [stalkEquivalence : (geometricPointStalk Ω).IsEquivalence]
  /-- Equivalence of the actual constant-sheaf functor. -/
  [constantEquivalence : (geometricPointConstants Ω).IsEquivalence]
  /-- The adjunction has the specified constant and stalk functors. -/
  adjunction : geometricPointConstants Ω ⊣ geometricPointStalk Ω
  /-- Its unit is the canonical constant-germ map. -/
  unit_eq : adjunction.unit = (geometricPointConstantGerm Ω).hom
  /-- The counit is invertible. -/
  [counitIsIso : IsIso adjunction.counit]
  /-- The counit is the unique map with the prescribed stalk. -/
  counit_unique (G : Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
      (f : (geometricPointConstants Ω).obj ((geometricPointStalk Ω).obj G) ⟶ G) :
    (geometricPointStalk Ω).map f =
      (geometricPointConstantGerm Ω).inv.app ((geometricPointStalk Ω).obj G) ↔
        f = adjunction.counit.app G
  /-- The constant tensor comparison is strong and respects symmetry. -/
  [constantMonoidal : (geometricPointConstants Ω).Braided]
  /-- The unit is monoidal for the canonical stalk tensor comparison. -/
  unit_monoidal : NatTrans.IsMonoidal adjunction.unit
  /-- The specified counit is monoidal. -/
  counit_monoidal : NatTrans.IsMonoidal adjunction.counit
  /-- The derived integer symmetry is fixed by `integer_symmetry_eq`. -/
  [integerDerivedSymmetric :
    SymmetricCategory (DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))]
  /-- The sheaf symmetry is uniquely fixed by `constant_symmetry`, since the derived
  constant functor is an equivalence with invertible tensorators. -/
  [sheafDerivedSymmetric : SymmetricCategory (DerivedCategory
    (Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))))]
  /-- The coefficient symmetry is the existing canonical derived Koszul symmetry. -/
  integer_symmetry_eq
      (K L : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    (β_ K L) = geometricPointIntegerDerivedSymmetry K L
  /-- The descended constant functor is strong monoidal for ordinary derived tensor. -/
  [derivedConstantMonoidal : (geometricPointConstants Ω).mapDerivedCategory.Monoidal]
  /-- The descended stalk functor is strong monoidal for ordinary derived tensor. -/
  [derivedStalkMonoidal : (geometricPointStalk Ω).mapDerivedCategory.Monoidal]
  /-- The derived constant tensor comparison is the termwise canonical comparison. -/
  constant_factors_monoidal :
    NatTrans.IsMonoidal (geometricPointConstants Ω).mapDerivedCategoryFactors.hom
  /-- The derived germ tensor comparison is the termwise canonical comparison. -/
  stalk_factors_monoidal :
    NatTrans.IsMonoidal (geometricPointStalk Ω).mapDerivedCategoryFactors.hom
  /-- The constant comparison respects the canonical derived Koszul symmetry. -/
  constant_symmetry
      (K L : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    Functor.LaxMonoidal.μ (geometricPointConstants Ω).mapDerivedCategory K L ≫
        (geometricPointConstants Ω).mapDerivedCategory.map
          (β_ K L).hom =
      (β_ ((geometricPointConstants Ω).mapDerivedCategory.obj K)
        ((geometricPointConstants Ω).mapDerivedCategory.obj L)).hom ≫
          Functor.LaxMonoidal.μ (geometricPointConstants Ω).mapDerivedCategory L K
  /-- The germ comparison respects the canonical derived Koszul symmetry. -/
  stalk_symmetry
      (K L : DerivedCategory
        (Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))) :
    Functor.LaxMonoidal.μ (geometricPointStalk Ω).mapDerivedCategory K L ≫
        (geometricPointStalk Ω).mapDerivedCategory.map
          (β_ K L).hom =
      (β_ ((geometricPointStalk Ω).mapDerivedCategory.obj K)
        ((geometricPointStalk Ω).mapDerivedCategory.obj L)).hom ≫
          Functor.LaxMonoidal.μ (geometricPointStalk Ω).mapDerivedCategory L K
  /-- The descended unit is monoidal. -/
  derived_unit_monoidal : NatTrans.IsMonoidal adjunction.mapDerivedCategoryAdjunction.unit
  /-- The descended counit is monoidal. -/
  derived_counit_monoidal : NatTrans.IsMonoidal adjunction.mapDerivedCategoryAdjunction.counit
  /-- The derived adjunction unit is invertible. -/
  [derivedUnitIsIso : IsIso adjunction.mapDerivedCategoryAdjunction.unit]
  /-- The derived adjunction counit is invertible. -/
  [derivedCounitIsIso : IsIso adjunction.mapDerivedCategoryAdjunction.counit]
  /-- Every cohomological lower bound is preserved by the constant functor. -/
  constant_isGE (K : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) (a : ℤ) :
    DerivedCategory.IsGE K a →
      DerivedCategory.IsGE ((geometricPointConstants Ω).mapDerivedCategory.obj K) a
  /-- Every cohomological lower bound is preserved by the stalk functor. -/
  stalk_isGE
      (K : DerivedCategory
        (Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))))
      (a : ℤ) :
    DerivedCategory.IsGE K a →
      DerivedCategory.IsGE ((geometricPointStalk Ω).mapDerivedCategory.obj K) a

/-- The normalized exact constant/stalk equivalence and its ordinary derived tensor extension.
Source: Stacks Tags 04JQ and 0F0F
(blueprint: lem-kun-geometric-point-derived-constants).

Proof: specialize `lem-exc-abelian-sheaves-gmodules` to the trivial Galois group of Ω.
The canonical constant-germ isomorphism gives the unit; full faithfulness of the stalk
constructs the unique counit with inverse germ as stalk. Naturality gives both triangle
identities. Additive equivalences preserve kernels and cokernels, hence are exact.
The exact-functor cohomology comparison and localization universal property descend the
functors, unit, counit and triangle identities termwise to unbounded derived categories;
the cohomology comparison preserves every lower bound. On local pure tensors the constant
and germ comparisons send m tensor n to m tensor n. They give the monoidal unit and counit
identities and symmetry. Equivalences preserve arbitrary coproducts, so these comparisons
extend to total tensor complexes with the same differential signs. They preserve K-flatness:
for acyclic A and inverse G, F(P) tensor A is F(P tensor G(A)), which is acyclic.
Use `lem-pc-kflat-resolution`, then localize these comparisons in each variable.
The resulting tensorators satisfy the displayed localization-factorization normalization,
and associativity, unit, symmetry and the unit/counit equations descend unchanged.
The coefficient symmetry is the existing derived Koszul symmetry. Compatibility of the
derived constant functor uniquely determines the sheaf symmetry: this functor is essentially
surjective and has invertible tensorators. Its canonical tensor comparison preserves the
Koszul signs on K-flat representatives, so this is exactly the ordinary derived sheaf
symmetry, and is symmetric. -/
theorem nonempty_geometricPointDerivedConstantsData (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    Nonempty (GeometricPointDerivedConstantsData Ω) := by
  sorry

end AlgebraicGeometry.Etale
