/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.Paper.OrgogozoInductionData
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.CategoryTheory.ProperFaceMatchingObject
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.AlgebraicGeometry.ProperHypercoverEtaleDescent
import Sheaf.Paper.GeneralNearbySliceTest
import Sheaf.Paper.OrientedNearbyCycles
import Sheaf.TraceFormula.SimplicialDerivedImageSpectralSequence

/-!
# Truncated nearby-cycle descent along a proper hypercover

Source: Orgogozo, Modifications et cycles proches sur une base générale,
Lemmas 3.1.1--3.1.2, pp. 6--7
(blueprint: lem-trf-nearby-proper-hyperdescent).

An augmented simplicial scheme over `X` is a simplicial object in `Over X`.
The matching cones are limits of the finite proper-face diagrams in that slice.
No choice of a matching scheme or of a representative complex is fixed here.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialObject
open AlgebraicGeometry.OrientedNearbyCycles

namespace AlgebraicGeometry.Orgogozo

/-- Proper hyperdescent transfers the degreewise truncated ordinary nearby comparison
properties to the augmentation. The coefficient sheaves are compared linearly after
restriction along the constant-ring sheafification unit and the `AsSmall` equivalence.
Source: Orgogozo, Lemmas 3.1.1--3.1.2, including the nonconstant coefficient variant
(blueprint: lem-trf-nearby-proper-hyperdescent).

Proof plan:
1. Fix arbitrary preliminary `T → S` and further `T' → T`. Apply proper-hypercover
   etale descent [lem-trf-proper-hypercover-etale-descent] after these base changes.
   Use [lem-trf-general-nearby-slice-test] to test the ordinary comparison on every
   compatible geometric specialization, with the generic strict localization retained.
2. Descent over the generic strict localization, derived composition, and simplicial
   proper exchange [lem-trf-simplicial-proper-exchange] identify the sliced nearby
   complex with the total derived augmentation image of its levelwise sliced complexes.
   Component restriction is that of [lem-trf-simplicial-derived-image-spectral-sequence].
3. Proper exchange after `T' → T` identifies the sliced comparison with the derived
   augmentation image of the levelwise comparisons. The descent units and counit-defined
   exchanges agree on ordinary coefficient sections; their canonical derived maps agree.
4. Take the cone in the total simplicial derived category. Exact component restriction
   gives the levelwise cones. The two nearby complexes are nonnegative, so their cone
   vanishes strictly below -1. Enough injectives follows from
   [prop-pur-kinjective-resolutions-exist], also on the small total site, and
   [lem-weil-pbc-dplus-injective-representative] gives representatives with this bound.
5. For `p ≤ r+1`, the two quantifiers of `P_(r-p)` kill the degree-p comparison cone
   through degree `r-p`. Derived direct image preserves this lower bound, by the same
   injective-representative theorem. For all p the uniform bound is strictly below -1.
6. Apply [lem-trf-simplicial-derived-image-spectral-sequence] to the cone, with lower
   bound -1. On a diagonal `n ≤ r`, every possible term has `0 ≤ p ≤ n+1 ≤ r+1` and
   `q = n-p ≤ r-p`, so it vanishes. The finite filtration then kills the abutment.
   For `r = -1` the single boundary term `(p,q) = (0,-1)` is killed by `P_(-1)`.
7. The slice test gives vanishing through degree r on the whole vanishing topos.
   Both base changes were arbitrary, so this is `UniversalTruncatedComparison f Λ K r`.
-/
theorem universalTruncatedComparison_of_proper_hypercover
    {X S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : X ⟶ S) [IsProper f]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (m : ℕ) (hm : 1 ≤ m) (hmΛ : ∀ x : Λ, m • x = 0)
    (hmS : IsUnit (m : Γ(S, ⊤)))
    (K : {L : EtaleDerived.{u, u + 1} X Λ //
      IsBounded (etaleDatum.{u, u + 1} X) (Coeff.{u, u + 1} Λ) L})
    (hKge : DerivedCategory.TStructure.t.IsGE K.val 0)
    (hKc : ∀ q : ℤ,
      ∃ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u, u + 1} Λ)),
        Scheme.IsConstructibleEtaleModuleSheaf F ∧
        Nonempty (
          (PresheafOfModules.forgetToPresheafModuleCat
            (op (⊤_ (EtaleSite.{u, u + 1} X))) terminalIsTerminal.op).obj
            ((PresheafOfModules.restrictScalars
              (Functor.whiskerRight
                (toSheafify (etaleTopology.{u, u + 1} X)
                  ((Functor.const (EtaleSite.{u, u + 1} X)ᵒᵖ).obj
                    (CommRingCat.of (Coeff.{u, u + 1} Λ))))
                (forget₂ CommRingCat RingCat))).obj
              ((DerivedCategory.homologyFunctor
                ((etaleDatum.{u, u + 1} X).modules (Coeff.{u, u + 1} Λ)) q).obj K.val).val) ≅
          (AsSmall.down : EtaleSite.{u, u + 1} X ⥤ X.Etale).op ⋙ F.obj))
    (U : SimplicialObject (Over X))
    (M : ∀ n : ℕ, Cone (properFaceDiagram U n))
    (hM : ∀ n : ℕ, IsLimit (M n))
    (μ : ∀ n : ℕ, U.obj (op (SimplexCategory.mk n)) ⟶ (M n).pt)
    (hμ : ∀ (n : ℕ) (a : ProperFaceCategory n),
      μ n ≫ (M n).π.app (op a) = U.map a.obj.hom.op)
    (hproper : ∀ n : ℕ, IsProper (μ n).left)
    (hsurj : ∀ n : ℕ, Surjective (μ n).left)
    (hft : ∀ n : ℕ,
      LocallyOfFiniteType ((U.obj (op (SimplexCategory.mk n))).hom ≫ f) ∧
      QuasiCompact ((U.obj (op (SimplexCategory.mk n))).hom ≫ f))
    (r : ℤ) (hr : -1 ≤ r)
    (hlevels : ∀ i : ℕ, (i : ℤ) ≤ r + 1 →
      UniversalTruncatedComparison
        ((U.obj (op (SimplexCategory.mk i))).hom ≫ f) Λ
        ⟨((etaleModules (U.obj (op (SimplexCategory.mk i))).hom).pull
            (Coeff.{u, u + 1} Λ)).obj K.val,
          ((etaleModules (U.obj (op (SimplexCategory.mk i))).hom).modulePull
            (Coeff.{u, u + 1} Λ)).bounded_mapDerivedCategory_obj K.property⟩
        (r - (i : ℤ))) :
    UniversalTruncatedComparison f Λ K r := by
  sorry

end AlgebraicGeometry.Orgogozo
