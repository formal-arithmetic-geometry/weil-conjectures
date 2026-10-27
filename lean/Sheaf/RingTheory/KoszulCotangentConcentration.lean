/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J5
-/
module

public import Sheaf.RingTheory.CotangentResolutionCoherence
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.RingTheory.KoszulPolynomialSquare
import Sheaf.RingTheory.CotangentFlatBaseChange
import Sheaf.RingTheory.PolynomialAugmentationCotangent
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat

/-!
# Concentration of the cotangent complex of a Koszul quotient

Source: Stacks Project, Cotangent Complex, Tag 08SJ, proof using Tag 08SI.
(blueprint: lem-trf-koszul-cotangent-concentration).
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace Algebra.CotangentResolution

private def extensionSingleIso
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    {A B : CommRingCat.{u}} (f : A ⟶ B)
    (M : ModuleCat.{u} A) (n : ℤ) (hM : Module.Flat A M) :
    (baseChangeExtension f).obj ((DerivedCategory.singleFunctor _ n).obj M) ≅
      (DerivedCategory.singleFunctor _ n).obj ((ModuleCat.extendScalars f.hom).obj M) := by
  let : HasExactColimitsOfShape ℤ (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (AsSmall.equiv (C := ℤ)).symm
  let (N : ModuleCat.{u} A) : PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} A)).flip.obj N) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (MonoidalCategory.tensorRight N))
  let F := ModuleCat.extendScalars f.hom
  let : F.Additive := (ModuleCat.extendRestrictScalarsAdj f.hom).left_adjoint_additive
  let := ModuleCat.extendScalars_preservesKFlatQuasiIso f.hom
  let K := (CochainComplex.singleFunctor (ModuleCat.{u} A) n).obj M
  have hK : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat K :=
    (CochainComplex.kFlat_single_obj_iff_flat M n).2 ((ModuleCat.flat_iff_flat M).2 hM)
  have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat K hK
  let E := (F.mapHomologicalComplex (.up ℤ)).obj K
  let e : (baseChangeExtension f).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj E :=
    (F.leftDerivedFunctor.mapIso
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app K)).symm ≪≫
    asIso (F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj K)) ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (.up ℤ)).app K) ≪≫
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} B)).app E
  exact (baseChangeExtension f).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ n).app M) ≪≫ e ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) n).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ n).app (F.obj M)).symm

/-- The polynomial base-change argument concentrates the cotangent complex in
 degree minus one, before any identification of that cohomology module.
Source: Stacks Project, Cotangent Complex, Tag 08SJ, proof, and Tag 08SI
(blueprint: lem-trf-koszul-cotangent-concentration).

Proof: Let P = Z[x_i] and send x_i to f_i. The Koszul resolution of Z over P
becomes the Koszul complex on f after tensoring with R. Koszul regularity says
its augmentation to R/I is a quasi-isomorphism, by isIso_comparison of the
Koszul derived quotient theorem. This is the canonical derived multiplication
for the square (P, Z, R, R/I). Cotangent flat base change therefore identifies
the quotient cotangent complex with the derived scalar extension of L[Z/P].
The polynomial augmentation theorem identifies the latter with (J/J²)[1].
Its displayed variable basis makes J/J² free over Z, so this single complex is
K-flat. The scalar-extension counit computes its derived extension as the single
ordinary tensor in degree minus one. Such a single object is both at least and
at most minus one for the standard t-structure. Transport these bounds through
the base-change isomorphism. No identification of this tensor with I/I² is
needed. The empty basis, zero ring, and unit ideal cases use the same argument. -/
theorem koszul_cotangent_concentrated
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (C : Coherence.{u}) (R : Type u) [CommRing R] (r : ℕ) (f : Fin r → R)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) :
    let L := cotangentComplex C
      (Arrow.mk (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range f)))))
    L.IsGE (-1) ∧ L.IsLE (-1) := by
  dsimp only
  let q := koszulPolynomialSquare R f
  have hmu : IsIso (derivedSquareMultiplication q) :=
    isIso_koszulPolynomialSquare R f hreg
  have := isIso_cotangentBaseChange C q hmu
  obtain ⟨⟨e, _⟩, ⟨b, _⟩, _⟩ :=
    PolynomialAugmentationCotangent.exists_canonical_iso_and_basis C r
  have : Module.Free (ULift.{u} ℤ)
      (PolynomialAugmentationCotangent.augmentationIdeal r).Cotangent := Module.Free.of_basis b
  let M := ModuleCat.of (ULift.{u} ℤ)
    (PolynomialAugmentationCotangent.augmentationIdeal r).Cotangent
  have hflat : Module.Flat (ULift.{u} ℤ) M := inferInstance
  let t := extensionSingleIso (A := CommRingCat.of (ULift.{u} ℤ)) q.right M (-1) hflat
  let k := (asIso (cotangentBaseChange C q)).symm ≪≫
    (baseChangeExtension q.right).mapIso e ≪≫ t
  exact ⟨DerivedCategory.TStructure.t.isGE_of_iso k.symm (-1),
    DerivedCategory.TStructure.t.isLE_of_iso k.symm (-1)⟩

end Algebra.CotangentResolution
