/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.Paper.LocalizingClosure
public import Sheaf.Paper.FiniteDiscreteCondensedRing
public import Sheaf.Paper.FiniteDiscreteSchemeRing
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import Sheaf.AlgebraicGeometry.UnboundedSiteComparison
import Sheaf.Paper.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Finite coefficient comparison on localizing closures

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ctf-finite-comparison/
sk-prop-ctf-finite-comparison-localizing.md
(blueprint: det-ctf-finite-comparison-localizing).

## Main definitions

* `finiteComparisonRealization`: the specified finite-discrete coefficient transport.
* `finiteComparisonEtaleClosure`, `finiteComparisonProEtaleClosure`: the two closures.
* `finiteComparisonOpenIso`, `finiteComparisonCompactSupportMap`: the canonical arrows.

## Main statements

* `finiteComparisonRealization_exact`: exactness of the specified coefficient transport.
* `finiteComparisonLocalizing`: the equivalence and its compatibility with operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale

/-- View fixed-scalar module presheaves as internal modules before sheafification.
Source: blueprint finite comparison, coefficient identification in proof step 1
(blueprint: det-ctf-finite-comparison-localizing). -/
def finiteComparisonPresheaf (X : Scheme.{u}) (B : Type) [CommRing B] :
    (X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} B)) ⥤
      Mod (X.ProEtᵒᵖ ⥤ Ab.{u + 1})
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B))) where
  obj F := by
    let act :
        (Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B)) ⊗
            (F ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}) ⟶
          (F ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}) :=
      { app U := InternalAbelianSheafModule.ordinaryAction
          (S := ULift.{u + 1} B) (N := F.obj U)
        naturality U V f := by
          apply AddCommGrpCat.hom_ext_toIntLinearMap
          apply TensorProduct.ext'
          intro r m
          exact ((F.map f).hom.map_smul r m).symm }
    letI : ModObj
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B)))
        (F ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}) :=
      ModObj.mk' _ act (by
        apply NatTrans.ext
        funext U
        apply AddCommGrpCat.hom_ext_toIntLinearMap
        apply TensorProduct.ext'
        intro z m
        exact Int.cast_smul_eq_zsmul (M := F.obj U) (ULift.{u + 1} B) z.down m) (by
        apply NatTrans.ext
        funext U
        apply AddCommGrpCat.hom_ext_toIntLinearMap
        apply TensorProduct.ext_threefold
        intro r s m
        exact mul_smul (α := ULift.{u + 1} B) (β := F.obj U) r s m)
    exact ⟨F ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}⟩
  map f := Mod.homMk (Functor.whiskerRight f (forget₂ _ Ab.{u + 1})) (by
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro r m
    exact (f.app U).hom.map_smul r m)
  map_id F := by apply Mod.hom_ext; rfl
  map_comp f g := by apply Mod.hom_ext; rfl


/-- Sheafify the ordinary fixed-scalar action as an internal constant-ring action.
Source: blueprint finite comparison, proof step 1
(blueprint: det-ctf-finite-comparison-localizing). -/
def finiteComparisonConstantRealization (X : Scheme.{u}) (B : Type) [CommRing B] :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B)) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} B)))) :=
  sheafToPresheaf _ _ ⋙ finiteComparisonPresheaf X B ⋙
    (presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mapMod _

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [DiscreteTopology B] [Finite B]

/-- Transport the sheafified scalar action along the specified coefficient ring isomorphism.
The isomorphism is exactly the pullback of the finite-discrete point identification.
Source: blueprint finite comparison, proof step 1
(blueprint: det-ctf-finite-comparison-localizing). -/
def finiteComparisonRealization (X : Scheme.{u})
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom] :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B)) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X) :=
  finiteComparisonConstantRealization X B ⋙
    Mod.comap (finiteDiscreteSchemeRingIso B X eR).inv

/-- The specified coefficient transport is an exact equivalence.
Source: blueprint finite comparison, coefficient paragraph and proof step 1
(blueprint: det-ctf-finite-comparison-localizing).

Proof: an internal presheaf action is precisely the sectionwise scalar action.
Monoidal sheafification extends it uniquely to the associated constant ring sheaf.
Restriction along constant sections is inverse: local scalar representatives and
sheaf uniqueness recover both the action and every linear map. The unit and counit
are the sheafification identifications on underlying abelian sheaves. Transport along
`finiteDiscreteSchemeRingIso` has inverse transport along its inverse ring map.
The two composite functors are inverse and retain the underlying additive sheaves,
so preserve finite limits, finite colimits, and addition. This includes the zero ring
and empty scheme. -/
theorem finiteComparisonRealization_exact (X : Scheme.{u})
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom] :
    (finiteComparisonRealization B X eR).IsEquivalence ∧
    (finiteComparisonRealization B X eR).Additive ∧
    PreservesFiniteLimits (finiteComparisonRealization B X eR) ∧
    PreservesFiniteColimits (finiteComparisonRealization B X eR) := by
  sorry

variable (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
  ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
    Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom]

/-- Additivity of the specified coefficient transport, from the coefficient paragraph.
Source: blueprint finite comparison (blueprint: det-ctf-finite-comparison-localizing). -/
instance finiteComparisonRealization_additive (X : Scheme.{u}) :
    (finiteComparisonRealization B X eR).Additive :=
  (finiteComparisonRealization_exact B X eR).2.1

/-- Left exactness of the coefficient transport, from the coefficient paragraph.
Source: blueprint finite comparison (blueprint: det-ctf-finite-comparison-localizing). -/
instance finiteComparisonRealization_limits (X : Scheme.{u}) :
    PreservesFiniteLimits (finiteComparisonRealization B X eR) :=
  (finiteComparisonRealization_exact B X eR).2.2.1

/-- Right exactness of the coefficient transport, from the coefficient paragraph.
Source: blueprint finite comparison (blueprint: det-ctf-finite-comparison-localizing). -/
instance finiteComparisonRealization_colimits (X : Scheme.{u}) :
    PreservesFiniteColimits (finiteComparisonRealization B X eR) :=
  (finiteComparisonRealization_exact B X eR).2.2.2

/-- The etale generators: the recorded bounded constructible property and finite Tor
amplitude tested against every module sheaf in degree zero.
Source: blueprint finite comparison, statement
(blueprint: det-ctf-finite-comparison-localizing). -/
def finiteComparisonEtaleGenerators (X : Scheme.{u}) :
    ObjectProperty (Etale.DerivedCategoryModule (ULift.{u + 1} B) X) :=
  Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} B) X ⊓
    _root_.DerivedCategory.finiteTorAmplitude _

/-- The pro-etale generators transported from the recorded constant-model definition.
Source: blueprint finite comparison, coefficient paragraph and definition of Dctf
(blueprint: det-ctf-finite-comparison-localizing). -/
def finiteComparisonProEtaleGenerators (X : Scheme.{u}) :
    ObjectProperty (_root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B)))) :=
  fun K ↦ (constantModelBoundedConstructible (Profinite.continuousMapRingObj.{u} B) X ⊓
    _root_.DerivedCategory.finiteTorAmplitude _)
      ((finiteComparisonRealization B X eR).mapDerivedCategory.obj K)

/-- The etale localizing closure uses the recorded intersection convention.
Source: blueprint finite comparison (blueprint: det-ctf-finite-comparison-localizing). -/
def finiteComparisonEtaleClosure (X : Scheme.{u}) :=
  CategoryTheory.localizingClosure (finiteComparisonEtaleGenerators B X)

/-- The ordinary pro-etale localizing closure, with the transported Dctf generators.
Source: blueprint finite comparison (blueprint: det-ctf-finite-comparison-localizing). -/
def finiteComparisonProEtaleClosure (X : Scheme.{u}) :=
  CategoryTheory.localizingClosure (finiteComparisonProEtaleGenerators B eR X)

/-- The canonical open-extension comparison, applied termwise and localized.
Source: blueprint finite comparison, Operations; Stacks Tag 09AF
(blueprint: det-ctf-finite-comparison-localizing). -/
def finiteComparisonOpenIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} B)) j).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) X).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) U).mapDerivedCategory ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} B)) j).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- For the chosen open/proper factorization, the compact-support comparison is exactly
alpha at j_! K followed by Rp_* of the open comparison. All values are ambient.
Source: blueprint finite comparison, final paragraph of proof
(blueprint: det-ctf-finite-comparison-localizing). -/
def finiteComparisonCompactSupportMap {X P Y : Scheme.{u}} (j : X ⟶ P) (p : P ⟶ Y)
    [IsOpenImmersion j]
    (K : Etale.DerivedCategoryModule (ULift.{u + 1} B) X) :=
  unboundedDirectImageComparisonMap (ULift.{u + 1} B) p
      ((Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) j).mapDerivedCategory.obj K) ≫
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) p).rightDerivedFunctor.map
      ((finiteComparisonOpenIso B j).hom.app K)

/-- Comparison identifies the two localizing closures, exactly and with ambient sums,
and the canonical pullback, direct-image, open-extension and compact-support comparisons
are invertible on the indicated inputs. No stability assertion for direct images occurs.

Source: blueprint main-20261015, sk-prop-ctf-finite-comparison-localizing.md and its proof
(blueprint: det-ctf-finite-comparison-localizing).

Proof, following the node's five steps:
1. The finite-discrete condensed-ring and scheme-ring identifications transport module
   actions exactly, preserving sums, tensor and the finite constant models. The unbounded
   site comparison is exact, fully faithful and sum-preserving
   (lem-sfb-unbounded-site-comparison). The finite Noetherian coefficient comparison
   det-pe-finite-tor-comparison-noetherian identifies the Dctf generators.
2. The inverse image of the pro-etale closure is replete, triangulated and sum-closed.
   It contains the etale generators, so the defining intersection of
   sk-def-localizing-closure gives preservation of the etale closure.
3. The replete essential image of that closure is sum-closed and shift-closed.
   Fullness lifts any arrow between image objects, and exactness sends its cone to
   a cone of the given arrow. Thus the essential image is triangulated, including zero
   from the empty sum. It contains all pro-etale generators by step 1. Minimality gives
   the reverse inclusion. Full faithfulness restricts, giving the equivalence; triangles
   and sums are the ambient ones.
4. The pullback square is sk-thm-pe-direct-image-comparison. For open extension use
   lem-cbc-proetale-extension-zero-comparison and the two extension-exactness nodes:
   applying the sheaf isomorphism degreewise gives a natural complex isomorphism and
   exactness descends it through quasi-isomorphisms. For finite-type direct image use
   lem-sfb-unbounded-direct-image-comparison. Restrict these ambient maps to closure inputs.
5. For a chosen compactification compose alpha on j_! K with Rp_* of the open
   comparison. Both factors are isomorphisms in the ambient category, naturally in K.
   Their composite is exactly the stipulated comparison for Rf_! = Rp_* j_!; no closure
   stability of direct image is used. -/
theorem finiteComparisonLocalizing
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k]
    [Algebra (ZMod p) k] [IsAlgClosure (ZMod p) k]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p)
    (hB : ∃ n : ℕ, (ℓ : B) ^ n = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] :
    ∃ hpres : ∀ K : Etale.DerivedCategoryModule (ULift.{u + 1} B) X,
        finiteComparisonEtaleClosure B X K →
          finiteComparisonProEtaleClosure B eR X
            ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
              X).mapDerivedCategory.obj K),
      ((finiteComparisonProEtaleClosure B eR X).lift
        ((finiteComparisonEtaleClosure B X).ι ⋙
          (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) X).mapDerivedCategory)
        (fun K ↦ hpres K.obj K.property)).IsEquivalence ∧
      (∀ T : Triangle (Etale.DerivedCategoryModule (ULift.{u + 1} B) X),
        finiteComparisonEtaleClosure B X T.obj₁ →
        finiteComparisonEtaleClosure B X T.obj₂ →
        finiteComparisonEtaleClosure B X T.obj₃ →
        T ∈ distTriang _ →
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
          X).mapDerivedCategory.mapTriangle.obj T) ∈ distTriang _) ∧
      (∀ (I : Type (u + 2)) (K : I → Etale.DerivedCategoryModule (ULift.{u + 1} B) X),
        (∀ i : I, finiteComparisonEtaleClosure B X (K i)) →
        ∀ c : Cofan K, IsColimit c → finiteComparisonEtaleClosure B X c.pt ∧
          Nonempty (IsColimit
            ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
              X).mapDerivedCategory.mapCocone c))) ∧
      (∀ (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
        [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
        (g : X ⟶ Y) [g.IsOver (Spec (.of k))] [LocallyOfFiniteType g] [QuasiCompact g],
        (∀ K : Etale.DerivedCategoryModule (ULift.{u + 1} B) Y,
          finiteComparisonEtaleClosure B Y K →
          IsIso ((unboundedDirectImagePullbackIso (ULift.{u + 1} B) g).hom.app K)) ∧
        (∀ K : Etale.DerivedCategoryModule (ULift.{u + 1} B) X,
          finiteComparisonEtaleClosure B X K →
          IsIso (unboundedDirectImageComparisonMap (ULift.{u + 1} B) g K))) ∧
      (∀ (U : Scheme.{u}) [U.Over (Spec (.of k))]
        [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
        (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j]
        (K : Etale.DerivedCategoryModule (ULift.{u + 1} B) U),
        finiteComparisonEtaleClosure B U K → IsIso ((finiteComparisonOpenIso B j).hom.app K)) ∧
      (∀ (P Y : Scheme.{u}) [P.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
        [LocallyOfFiniteType (P ↘ Spec (.of k))] [QuasiCompact (P ↘ Spec (.of k))]
        [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
        (j : X ⟶ P) (r : P ⟶ Y) [j.IsOver (Spec (.of k))] [r.IsOver (Spec (.of k))]
        [IsOpenImmersion j] [IsProper r]
        (K : Etale.DerivedCategoryModule (ULift.{u + 1} B) X),
        finiteComparisonEtaleClosure B X K →
          IsIso (finiteComparisonCompactSupportMap B j r K)) := by
  sorry

end AlgebraicGeometry.ProEtale
