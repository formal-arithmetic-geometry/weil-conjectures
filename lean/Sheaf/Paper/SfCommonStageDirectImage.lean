/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.Paper.SfCommonStageWeilCohomology
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.Paper.WeilIndSheafCategory
import Sheaf.Paper.CompletedCoefficientPushforwardComparison
import Sheaf.Paper.SfIntegralDirectImageConstructible
import Sheaf.Paper.SfIntegralConstructible
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Sheaf.Paper.PbcDescentFunctors

/-! # Common-stage direct image and its induced Weil structure

Source: Bhatt--Scholze 6.8.14(2), 6.8.15; blueprint derived-direct-image convention
(blueprint: def-weil-derived-direct-image).
The existing integral tower construction is reexported. Its rational/common-stage
extension is characterized by the derived inverse-image adjunction. Taking fixed pairs
uses the mate of the normalized Frobenius pullback square, not a derived category of pairs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- Composition of geometric pullbacks, descended from finite integral reductions.
Source: Stacks 099N(5), BS 6.8.15 (blueprint: def-weil-derived-direct-image). -/
def sfModelPullComposition {Z₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] (f : X₀ ⟶ Y₀) (g : Y₀ ⟶ Z₀) :
    zlPull D l hl Ω (f ≫ g) ≅ zlPull D l hl Ω g ⋙ zlPull D l hl Ω f :=
  letI := sfWeilPrimeInvertible D l hl X₀
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := sfWeilPrimeInvertible D l hl Z₀
  eqToIso (congrArg (fun h ↦ commonStageDerivedPullback l Ω h)
    (congrArg (fun h ↦ h.left)
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map_comp f g))) ≪≫
    zlPullComp l Ω (zlFiberMap D f) (zlFiberMap D g)

/-- The normalized inverse-image square, built from the composition comparisons.
Source: Stacks 0D6G, BS 6.8.15 (blueprint: def-weil-derived-direct-image). -/
def sfModelPullSquare {V₀ W₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType V₀.hom] [QuasiCompact V₀.hom]
    [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom]
    (j : X₀ ⟶ Y₀) (a : W₀ ⟶ Y₀) (b : V₀ ⟶ X₀) (jW : V₀ ⟶ W₀)
    (h : b ≫ j = jW ≫ a) :
    zlPull D l hl Ω a ⋙ zlPull D l hl Ω jW ≅
      zlPull D l hl Ω j ⋙ zlPull D l hl Ω b :=
  (sfModelPullComposition D l hl Ω jW a).symm ≪≫
    eqToIso (congrArg (fun f ↦ zlPull D l hl Ω f) h.symm) ≪≫
      sfModelPullComposition D l hl Ω b j

/-- The actual geometric inverse image has its constructible derived right adjoint.
Source: BS 6.8.14(2), 6.8.15 (blueprint: def-weil-derived-direct-image).
Proof: ordinary completed-ring derived direct image is right adjoint to completed
inverse image. CompletedCoefficientPushforwardComparison identifies it with the
specified finite-reduction tower and derived limit. SfIntegralDirectImageConstructible
restricts it to bounded constructible objects for finite-type schemes over the field.
Rational transport preserves the adjunction; scalar-extension comparisons preserve
its unit and counit. PbcDescentFunctors descends those functors and maps to common stages.
The descended unit and counit satisfy the triangle identities at each finite stage. -/
theorem sfModelPull_isLeftAdjoint (f : X₀ ⟶ Y₀) :
    (zlPull D l hl Ω f).IsLeftAdjoint := by
  sorry

/-- Derived direct image on the actual geometric common-stage category, determined
up to its unique adjunction-compatible isomorphism. The universal property specifies
its data; this is not a choice of an arbitrary functor.
Source: BS 6.8.14(2), 6.8.15 (blueprint: def-weil-derived-direct-image). -/
@[irreducible]
def sfModelDerivedPush (f : X₀ ⟶ Y₀) :
    generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left :=
  @Functor.rightAdjoint _ _ _ _ (zlPull D l hl Ω f)
    (sfModelPull_isLeftAdjoint D l hl Ω f)

/-- The unit and counit specifying the geometric derived direct image.
Source: BS 6.8.14(2), 6.8.15 (blueprint: def-weil-derived-direct-image). -/
@[irreducible]
def sfModelDerivedAdjunction (f : X₀ ⟶ Y₀) :
    zlPull D l hl Ω f ⊣ sfModelDerivedPush D l hl Ω f := by
  unfold sfModelDerivedPush
  exact @Adjunction.ofIsLeftAdjoint _ _ _ _ (zlPull D l hl Ω f)
    (sfModelPull_isLeftAdjoint D l hl Ω f)

/-- The geometric open-exchange arrow is the mate of the normalized pullback square.
Source: Stacks 0D6G (blueprint: def-weil-derived-direct-image). -/
def sfModelDerivedExchange {V₀ W₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType V₀.hom] [QuasiCompact V₀.hom]
    [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom]
    (j : X₀ ⟶ Y₀) (a : W₀ ⟶ Y₀) (b : V₀ ⟶ X₀) (jW : V₀ ⟶ W₀)
    (h : b ≫ j = jW ≫ a)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left) :
    (zlPull D l hl Ω a).obj ((sfModelDerivedPush D l hl Ω j).obj K) ⟶
      (sfModelDerivedPush D l hl Ω jW).obj ((zlPull D l hl Ω b).obj K) :=
  (sfModelDerivedAdjunction D l hl Ω jW).homEquiv _ _
    ((sfModelPullSquare D l hl Ω j a b jW h).hom.app
        ((sfModelDerivedPush D l hl Ω j).obj K) ≫
      (zlPull D l hl Ω b).map ((sfModelDerivedAdjunction D l hl Ω j).counit.app K))

/-- The normalized shift structure on geometric inverse image.
Source: BS 6.8.15, cohomological pullback convention
(blueprint: def-weil-derived-direct-image). -/
@[instance_reducible]
def sfModelPullCommShift (f : X₀ ⟶ Y₀) : (zlPull D l hl Ω f).CommShift ℤ :=
  cast (congrArg (fun F ↦ F.CommShift ℤ)
    (congrArg₂ (fun hX hY ↦ @commonStageDerivedPullback l _ Ω _ _ _ _ _
      (zlFiberMap D f) hX hY)
      (Subsingleton.elim (constructiblePullbackResidueUnits D l hl
        (D.geometricFiber X₀).left) (sfWeilPrimeInvertible D l hl X₀))
      (Subsingleton.elim (constructiblePullbackResidueUnits D l hl
        (D.geometricFiber Y₀).left) (sfWeilPrimeInvertible D l hl Y₀))))
    ((constructible_pullback_t_exact D l hl Ω (Padic.finiteCoefficientBase l Ω)
      (zlFiberMap D f)).2.some).commShift

/-- The uniquely adjunction-compatible shift structure on derived direct image.
Source: Stacks 05TE, derived adjunction
(blueprint: def-weil-derived-direct-image). -/
@[instance_reducible]
def sfModelPushCommShift (f : X₀ ⟶ Y₀) : (sfModelDerivedPush D l hl Ω f).CommShift ℤ :=
  letI := sfModelPullCommShift D l hl Ω f
  (sfModelDerivedAdjunction D l hl Ω f).rightAdjointCommShift ℤ

/-- The prescribed image of a connecting map, including the derived shift comparison.
Source: Stacks 05TE (blueprint: def-weil-derived-direct-image). -/
def sfModelPushConnecting (f : X₀ ⟶ Y₀)
    {K L : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left}
    (w : K ⟶ L⟦(1 : ℤ)⟧) :
    (sfModelDerivedPush D l hl Ω f).obj K ⟶
      ((sfModelDerivedPush D l hl Ω f).obj L)⟦(1 : ℤ)⟧ :=
  letI := sfModelPushCommShift D l hl Ω f
  (sfModelDerivedPush D l hl Ω f).map w ≫
    ((sfModelDerivedPush D l hl Ω f).commShiftIso (1 : ℤ)).hom.app L

/-- The induced inverse image of fixed pairs admits the induced derived direct image.
Source: blueprint Weil-equivariant derived operations
(blueprint: def-weil-derived-direct-image).
Proof: take the right-adjoint mate of zlFrobeniusSquare using the derived adjunction.
Frobenius is an automorphism on both schemes; the inverse square supplies the inverse
mate. Its unit/counit equations equip the geometric direct image with its induced
invertible Weil structure and restrict the adjunction to equivariant arrows. -/
theorem sfModelWeilPull_isLeftAdjoint (f : X₀ ⟶ Y₀) :
    (IsoAlgebra.mapOfNatIso (zlFrobeniusSquare D l hl Ω f)).IsLeftAdjoint := by
  sorry

/-- Derived direct image of Weil fixed pairs; its underlying functor is geometric Rf_*.
Source: blueprint Weil-equivariant derived operations
(blueprint: def-weil-derived-direct-image). -/
@[irreducible]
def sfModelWeilDerivedPush (f : X₀ ⟶ Y₀) :
    sfCommonStageWeilComplex D l hl X₀ Ω ⥤ sfCommonStageWeilComplex D l hl Y₀ Ω :=
  @Functor.rightAdjoint _ _ _ _ (IsoAlgebra.mapOfNatIso (zlFrobeniusSquare D l hl Ω f))
    (sfModelWeilPull_isLeftAdjoint D l hl Ω f)

/-- The canonical derived inverse-image/direct-image adjunction on Weil pairs.
Source: BS 6.8.15 (blueprint: def-weil-derived-direct-image). -/
@[irreducible]
def sfModelWeilDerivedAdjunction (f : X₀ ⟶ Y₀) :
    IsoAlgebra.mapOfNatIso (zlFrobeniusSquare D l hl Ω f) ⊣
      sfModelWeilDerivedPush D l hl Ω f := by
  unfold sfModelWeilDerivedPush
  exact @Adjunction.ofIsLeftAdjoint _ _ _ _ (IsoAlgebra.mapOfNatIso (zlFrobeniusSquare D l hl Ω f))
    (sfModelWeilPull_isLeftAdjoint D l hl Ω f)

/-- Forgetting the induced Weil structure gives the actual geometric derived image.
Source: BS 6.8.14(2), blueprint Weil comparison
(blueprint: def-weil-derived-direct-image).
Proof: the mate construction in sfModelWeilPull_isLeftAdjoint has exactly the
geometric derived-image carrier. Uniqueness of right adjoints identifies that
construction with sfModelWeilDerivedPush, compatibly with its unit and counit.
Forgetting gives the displayed natural isomorphism. The counit equation
characterizes it by the geometric adjunction, proving uniqueness. -/
theorem sfModelWeilDerivedPush_forget (f : X₀ ⟶ Y₀) :
    ∃! e : sfModelWeilDerivedPush D l hl Ω f ⋙ sfCommonStageWeilForget D l hl Y₀ Ω ≅
        sfCommonStageWeilForget D l hl X₀ Ω ⋙ sfModelDerivedPush D l hl Ω f,
      ∀ K : sfCommonStageWeilComplex D l hl X₀ Ω,
        (zlPull D l hl Ω f).map (e.hom.app K) ≫
            (sfModelDerivedAdjunction D l hl Ω f).counit.app K.carrier =
          ((sfModelWeilDerivedAdjunction D l hl Ω f).counit.app K).hom.f := by
  sorry

/-- The forgetful comparison specified by the adjunction counit equation above.
Source: BS 6.8.14(2), blueprint Weil comparison
(blueprint: def-weil-derived-direct-image). -/
def sfModelWeilDerivedPushForget (f : X₀ ⟶ Y₀) :=
  (sfModelWeilDerivedPush_forget D l hl Ω f).exists.choose

end WeilConjectures
