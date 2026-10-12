/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedQCohDirectSums
public import Sheaf.CategoryTheory.CompactObject
public import Sheaf.CategoryTheory.WeakTriangulatedGenerator
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.AlgebraicGeometry.DerivedAmbientDirectSums
import Sheaf.AlgebraicGeometry.DerivedQCohDirectSumsAux
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import Sheaf.CategoryTheory.TriangulatedEquivalenceTransfer
import Sheaf.Topology.StalkDirectSums

/-! # A small-Hom model for a supported compact detector

Source: Stacks Project, duality.tex, lemma-when-sheafy, proof of (3), Section Tag 0E4G;
derived.tex, lemma-write-as-colimit (Tag 09SN).
(blueprint: lem-sc-supported-compact-detector-model).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry

/-- Prepare the supported subcategory for the compact-generator theorem, without
constructing any tower or telescope.
Source: Stacks Project, duality.tex, lemma-when-sheafy, proof of (3), Section Tag 0E4G;
derived.tex, lemma-write-as-colimit (Tag 09SN).
(blueprint: lem-sc-supported-compact-detector-model).

Proof: Form the full subcategory of ambient complexes with quasi-coherent cohomology
and zero cohomology stalks on V. The hypothesis htri supplies its triangulated structure.
Ambient sums have sum cohomology; stalks commute with sums, so this property is closed
under sums, including the empty sum. The inclusion therefore creates these coproducts.
K-injective resolutions identify derived Hom with a quotient of the small set of chain
maps into a K-injective representative. Thus this full subcategory is locally u-small.
Take its ShrinkHoms model, with exactly the same objects and shrunk Hom sets. Transport
zero, addition, shifts, triangles and coproducts along the canonical equivalence.
Compose its inverse with the full-subcategory inclusion to obtain F. The supported
objects E and Q give e and q. Full faithfulness and agreement of coproducts identify
the compactness comparison for e with that for E in D_QCoh(Y), so e is compact.
The singleton coproduct is e. For a nonzero object, hgen gives a nonzero map from some
shift of E; the shift equivalence rewrites this as a map from E into a shift of the
object. Full faithfulness transports it to the model, proving singleton generation.
These constructions work also for E = 0: hgen then makes the supported category zero.
No choice of an arbitrary derived object is made; the model is ShrinkHoms of the stated
full subcategory and F is its canonical inverse followed by the inclusion. -/
theorem supported_compact_detector_model (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (V : Y.Opens) (E Q : schemeDerivedQCohCategory Y)
    (htri : ObjectProperty.IsTriangulated (fun K : schemeDerivedCategory Y ↦
      schemeDerivedQCohProperty Y K ∧
        ∀ (k : ℤ) (y : Y), y ∉ (V : Set Y)ᶜ →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj K).val.presheaf y))))
    (hcompact :
      letI : HasCoproducts.{u} (schemeDerivedQCohCategory Y) := derivedQCohDirectSums Y
      IsCompactObject E)
    (hsupport : ∀ (k : ℤ) (y : Y), y ∉ (V : Set Y)ᶜ →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj E.obj).val.presheaf y)))
    (hgen : ∀ K : schemeDerivedQCohCategory Y,
      (∀ (k : ℤ) (y : Y), y ∉ (V : Set Y)ᶜ →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj K.obj).val.presheaf y))) →
      (IsZero K.obj ↔ ∀ n : ℤ, Subsingleton (E.obj⟦n⟧ ⟶ K.obj)))
    (hQ : ∀ (k : ℤ) (y : Y), y ∉ (V : Set Y)ᶜ →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj Q.obj).val.presheaf y))) :
    ∃ (C : Type (u + 1)) (_ : Category.{u} C)
      (_ : HasZeroObject C) (_ : HasShift C ℤ) (_ : Preadditive C)
      (_ : ∀ n : ℤ, (shiftFunctor C n).Additive) (_ : Pretriangulated C)
      (_ : IsTriangulated C) (_ : HasCoproducts.{u} C)
      (F : C ⥤ schemeDerivedCategory Y) (_ : F.CommShift ℤ),
      F.IsTriangulated ∧ F.Additive ∧
      (∀ I : Type u, PreservesColimitsOfShape (Discrete I) F) ∧
      (∀ K : C, schemeDerivedQCohProperty Y (F.obj K)) ∧
      ∃ e q : C, Nonempty (F.obj e ≅ E.obj) ∧ Nonempty (F.obj q ≅ Q.obj) ∧
        IsCompactObject e ∧
        IsTriangulatedGeneratingFamily (fun _ : ULift.{u} Unit ↦ e) := by sorry

end AlgebraicGeometry
