/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.CompletedExtensionZeroComparison
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Sheaf.SixFunctors.OpenTensorNormalization
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Augmented strict reduction and ringed open extension

Source: Stacks Project, Tags 0GL1 and 0E8I; blueprint
sec-six-functors-basics/sk-prop-sf-cbc/lem-cbc-completed-extension-zero-comparison.proof.md,
opening tensor/reduction argument (blueprint: lem-cbc-ringed-open-strict-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Reindex a ring sheaf from the open site's concrete category to the ambient slice.
Source: Stacks 00XZ (blueprint: lem-cbc-ringed-open-strict-reduction). -/
def cbcSliceRing {T : Scheme.{u}} (W : T.ProEt)
    (S : Sheaf (ProEt.topology W.left) CommRingCat.{u + 1}) :=
  ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{u + 1}
    ((ProEt.topology T).over W) (ProEt.topology W.left)).obj S

/-- The existing normalized finite slice map is invertible.
Source: Stacks 00XZ, the datum's finite coefficient presheaf
(blueprint: lem-cbc-ringed-open-strict-reduction).
Proof: cbcFiniteSliceMap is induced by the identical continuous-function presheaves
on the same schemes. The localization equivalence and sheafification compatibility
give its inverse; their two composites fix the presheaf units, hence are identities. -/
@[instance]
theorem cbcFiniteSliceMap_isIso {T : Scheme.{u}} (W : T.ProEt)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    IsIso (cbcFiniteSliceMap d T W n) := by
  sorry

/-- The existing finite restriction map, viewed as its canonical isomorphism.
Source: Stacks 00XZ (blueprint: lem-cbc-ringed-open-strict-reduction). -/
def cbcFiniteRestriction {T : Scheme.{u}} (W : T.ProEt)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (reductionCoefficient T d n).over W ≅ cbcSliceRing W (reductionCoefficient W.left d n) :=
  asIso (cbcFiniteSliceMap d T W n)

/-- The existing completed slice map is invertible.
Source: sectionwise coefficient limits (blueprint: lem-cbc-ringed-open-strict-reduction).
Proof: each finite slice map is invertible and natural in the quotient maps. Taking
inverse limits yields an inverse on compatible section families. The two composites
are identities because every finite projection is; projections jointly detect equality. -/
@[instance]
theorem cbcCompletedSliceMap_isIso {T : Scheme.{u}} (W : T.ProEt)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    IsIso (cbcCompletedSliceMap d T W) := by
  sorry

/-- The existing completed restriction map, with its uniquely determined inverse.
Source: sectionwise limits (blueprint: lem-cbc-ringed-open-strict-reduction). -/
def cbcCompletedRestriction {T : Scheme.{u}} (W : T.ProEt)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (completedReductionCoefficient T d).over W ≅
      cbcSliceRing W (completedReductionCoefficient W.left d) :=
  asIso (cbcCompletedSliceMap d T W)

/-- Actual extension: transport along the concrete ringed slice equivalence, take the
extension presheaf, and sheafify as modules.
Source: Stacks 03DI, 03DJ (blueprint: lem-cbc-ringed-open-strict-reduction). -/
def cbcRingedOpenExtension {T : Scheme.{u}} (W : T.ProEt)
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology W.left) CommRingCat.{u + 1}}
    (c : R.over W ≅ cbcSliceRing W S) : reductionModules W.left S ⥤ reductionModules T R :=
  SheafOfModules.pushforward.{u + 1} (F := cbcSliceFunctor T W)
    ((sheafCompose ((ProEt.topology T).over W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom) ⋙
    SheafOfModules.localizedSystemExtension.{u + 1, u, u + 1} R W

open Classical in
/-- A section in the extension summand, followed by the module-sheafification unit.
Source: Stacks 03DI (blueprint: lem-cbc-ringed-open-strict-reduction). -/
def cbcOpenSection {T : Scheme.{u}} (W : T.ProEt)
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology W.left) CommRingCat.{u + 1}}
    (c : R.over W ≅ cbcSliceRing W S) (M : reductionModules W.left S)
    (V : T.ProEt) (a : V ⟶ W)
    (x : M.val.obj (op ((cbcSliceFunctor T W).obj (Over.mk a)))) :
    ((cbcRingedOpenExtension W c).obj M).val.obj (op V) :=
  ((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
    (𝟙 (reductionModuleRing T R).obj)).unit.app
      ((SheafOfModules.extensionByZeroPresheaf (reductionModuleRing T R) W).obj
        ((SheafOfModules.pushforward.{u + 1} (F := cbcSliceFunctor T W)
          ((sheafCompose ((ProEt.topology T).over W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)).obj M))).app (op V)
      (DirectSum.of _ a x)

/-- The actual open extension is additive and exact for all coefficient ring sheaves.
Source: Stacks 03DI, 03DJ (blueprint: lem-cbc-ringed-open-strict-reduction).
Proof: the ringed slice transport is an equivalence, hence exact. Extension on the
slice is the recorded exact localizedSystemExtension, so the composite is exact. -/
theorem cbcRingedOpenExtension_exact {T : Scheme.{u}} (W : T.ProEt)
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology W.left) CommRingCat.{u + 1}}
    (c : R.over W ≅ cbcSliceRing W S) :
    (cbcRingedOpenExtension W c).Additive ∧ PreservesFiniteLimits (cbcRingedOpenExtension W c) ∧
      PreservesFiniteColimits (cbcRingedOpenExtension W c) := by
  sorry

/-- Additivity of the concrete extension.
Source: Stacks 03DI (blueprint: lem-cbc-ringed-open-strict-reduction). -/
instance cbcRingedOpenExtension_additive {T : Scheme.{u}} (W : T.ProEt)
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology W.left) CommRingCat.{u + 1}}
    (c : R.over W ≅ cbcSliceRing W S) : (cbcRingedOpenExtension W c).Additive :=
  (cbcRingedOpenExtension_exact W c).1

/-- Preservation of finite limits by the concrete extension.
Source: Stacks 03DI (blueprint: lem-cbc-ringed-open-strict-reduction). -/
instance cbcRingedOpenExtension_limits {T : Scheme.{u}} (W : T.ProEt)
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology W.left) CommRingCat.{u + 1}}
    (c : R.over W ≅ cbcSliceRing W S) : PreservesFiniteLimits (cbcRingedOpenExtension W c) :=
  (cbcRingedOpenExtension_exact W c).2.1

/-- Preservation of finite colimits by the concrete extension.
Source: Stacks 03DI (blueprint: lem-cbc-ringed-open-strict-reduction). -/
instance cbcRingedOpenExtension_colimits {T : Scheme.{u}} (W : T.ProEt)
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology W.left) CommRingCat.{u + 1}}
    (c : R.over W ≅ cbcSliceRing W S) : PreservesFiniteColimits (cbcRingedOpenExtension W c) :=
  (cbcRingedOpenExtension_exact W c).2.2



section ScalarComparison
variable {T : Scheme.{u}} (W : T.ProEt)
  {R B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
  {S C : Sheaf (ProEt.topology W.left) CommRingCat.{u + 1}}
  (cR : R.over W ≅ cbcSliceRing W S) (cB : B.over W ≅ cbcSliceRing W C)
  (φ : R ⟶ B) (ψ : S ⟶ C)

/-- Compatibility of the two ringed restriction identifications with a coefficient map.
Source: the quotient maps of the datum (blueprint: lem-cbc-ringed-open-strict-reduction). -/
def CbcOpenRingSquare : Prop :=
  ((ProEt.topology T).overPullback CommRingCat.{u + 1} W).map φ ≫ cB.hom =
    cR.hom ≫ ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{u + 1}
      ((ProEt.topology T).over W) (ProEt.topology W.left)).map ψ

/-- The scalar-extension comparison is uniquely fixed before restricting coefficients.
Source: Stacks 0E8I, 0GL1 (blueprint: lem-cbc-ringed-open-strict-reduction).
Proof: on the summand indexed by a map V to W, send [x] tensor b to
[x tensor b|W]. Balancing and restriction commute with this rule. Tensor and
module-sheafification universal properties give the map and its uniqueness.
The inverse sends [x tensor b] to [x] tensor b; balancing makes the two
composites identities. Naturality in the module follows on the same generators.
This is the inverse of the open-unit adjunct in lem-sf-open-tensor-normalization. -/
theorem cbcOpenScalarIso_existsUnique
    (_h : CbcOpenRingSquare W cR cB φ ψ) :
    ∃! β : cbcRingedOpenExtension W cR ⋙ reductionChange T φ ≅
        reductionChange W.left ψ ⋙ cbcRingedOpenExtension W cB,
      ∀ (M : reductionModules W.left S) (V : T.ProEt) (a : V ⟶ W)
        (b : B.obj.obj (op V))
        (x : M.val.obj (op ((cbcSliceFunctor T W).obj (Over.mk a)))),
        (β.hom.app M).val.app (op V)
          (reductionTensorSection T φ ((cbcRingedOpenExtension W cR).obj M) (op V) b
            (cbcOpenSection W cR M V a x)) =
        cbcOpenSection W cB ((reductionChange W.left ψ).obj M) V a
          (reductionTensorSection W.left ψ M
            (op ((cbcSliceFunctor T W).obj (Over.mk a)))
            (cB.hom.hom.app (op (Over.mk a)) b) x) := by
  sorry

/-- The canonical coefficient-linear comparison, with its pure tensor normalization.
Source: Stacks 0E8I, 0GL1 (blueprint: lem-cbc-ringed-open-strict-reduction). -/
def cbcOpenScalarIso (h : CbcOpenRingSquare W cR cB φ ψ) :=
  (cbcOpenScalarIso_existsUnique W cR cB φ ψ h).exists.choose

/-- Extension commutes with scalar restriction by the identity on extension summands.
Source: Stacks 03DA, 03DI (blueprint: lem-cbc-ringed-open-strict-reduction).
Proof: both underlying abelian sheaves are sheafifications of the same direct-sum
presheaf, with the same R-action because the ring square commutes. The identity on
every summand extends uniquely by sheafification, and its inverse is identical. -/
theorem cbcOpenRestrictIso_existsUnique (_h : CbcOpenRingSquare W cR cB φ ψ) :
    ∃! θ : reductionRestrict W.left ψ ⋙ cbcRingedOpenExtension W cR ≅
        cbcRingedOpenExtension W cB ⋙ reductionRestrict T φ,
      ∀ (M : reductionModules W.left C) (V : T.ProEt) (a : V ⟶ W)
        (x : M.val.obj (op ((cbcSliceFunctor T W).obj (Over.mk a)))),
        (θ.hom.app M).val.app (op V)
          (cbcOpenSection W cR ((reductionRestrict W.left ψ).obj M) V a x) =
        cbcOpenSection W cB M V a x := by
  sorry

/-- Scalar restriction comparison with the prescribed underlying summand maps.
Source: Stacks 03DA, 03DI (blueprint: lem-cbc-ringed-open-strict-reduction). -/
def cbcOpenRestrictIso (h : CbcOpenRingSquare W cR cB φ ψ) :=
  (cbcOpenRestrictIso_existsUnique W cR cB φ ψ h).exists.choose
end ScalarComparison

variable {T : Scheme.{u}} (W : T.ProEt) [IsOpenImmersion W.hom]
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The canonical finite identifications preserve every quotient map.
Source: sheafification naturality (blueprint: lem-cbc-ringed-open-strict-reduction).
Proof: both composites are induced by postcomposition by A/I^(b+1) to A/I^(a+1)
on continuous functions. Sheafification uniqueness identifies them. -/
theorem cbcQuotientSquare (b a : ℕ) (hab : a ≤ b) :
    CbcOpenRingSquare W (cbcFiniteRestriction W d b) (cbcFiniteRestriction W d a)
      (reductionCoefficientMap T d b a hab) (reductionCoefficientMap W.left d b a hab) := by
  sorry

/-- Completed restriction preserves every finite projection.
Source: the completed limit sheaf (blueprint: lem-cbc-ringed-open-strict-reduction).
Proof: this is precisely the defining equality of cbcCompletedRestriction, read in
the ring-square direction. -/
theorem cbcProjectionSquare (n : ℕ) :
    CbcOpenRingSquare W (cbcCompletedRestriction W d) (cbcFiniteRestriction W d n)
      (completedReductionProjection T d n) (completedReductionProjection W.left d n) := by
  sorry

/-- Ordinary open extension with the completed coefficient ring.
Source: Stacks 03DI (blueprint: lem-cbc-ringed-open-strict-reduction). -/
abbrev cbcCompletedExtension := cbcOpenShriek d W.hom (inferInstance : IsOpenImmersion W.hom)

/-- Additivity inherited from the existing completed open extension.
Source: Stacks 03DI (blueprint: lem-cbc-ringed-open-strict-reduction). -/
instance cbcCompletedExtension_additive : (cbcCompletedExtension W d).Additive :=
  cbcOpenShriek_additive d W.hom inferInstance

/-- Exactness inherited from the existing completed open extension.
Source: Stacks 03DJ (blueprint: lem-cbc-ringed-open-strict-reduction). -/
instance cbcCompletedExtension_limits : PreservesFiniteLimits (cbcCompletedExtension W d) :=
  cbcOpenShriek_finiteLimits d W.hom inferInstance

/-- Colimit preservation inherited from the existing completed open extension.
Source: Stacks 03DI (blueprint: lem-cbc-ringed-open-strict-reduction). -/
instance cbcCompletedExtension_colimits : PreservesFiniteColimits (cbcCompletedExtension W d) :=
  cbcOpenShriek_finiteColimits d W.hom inferInstance

/-- Apply the same completed-coefficient extension at every strict tower level.
Source: strict towers in the datum (blueprint: lem-cbc-ringed-open-strict-reduction). -/
def cbcCompletedTowerExtension :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (cbcCompletedExtension W d)

/-- Exactness on towers is levelwise, including the zero tower.
Source: levelwise abelian tower category
(blueprint: lem-cbc-ringed-open-strict-reduction).
Proof: kernels and cokernels of diagrams are computed objectwise, and the extension
is additive and exact on modules. Consequently its diagram functor is additive and exact. -/
theorem cbcCompletedTowerExtension_exact :
    (cbcCompletedTowerExtension W d).Additive ∧
      PreservesFiniteLimits (cbcCompletedTowerExtension W d) ∧
      PreservesFiniteColimits (cbcCompletedTowerExtension W d) := by
  sorry

/-- Additivity on strict towers.
Source: the datum's towers (blueprint: lem-cbc-ringed-open-strict-reduction). -/
instance cbcCompletedTowerExtension_additive : (cbcCompletedTowerExtension W d).Additive :=
  (cbcCompletedTowerExtension_exact W d).1

/-- Preservation of finite limits on strict towers.
Source: the datum's towers (blueprint: lem-cbc-ringed-open-strict-reduction). -/
instance cbcCompletedTowerExtension_limits :
    PreservesFiniteLimits (cbcCompletedTowerExtension W d) :=
  (cbcCompletedTowerExtension_exact W d).2.1

/-- Preservation of finite colimits on strict towers.
Source: the datum's towers (blueprint: lem-cbc-ringed-open-strict-reduction). -/
instance cbcCompletedTowerExtension_colimits :
    PreservesFiniteColimits (cbcCompletedTowerExtension W d) :=
  (cbcCompletedTowerExtension_exact W d).2.2

/-- The ordinary strict tower comparison is the coefficient-linear comparison followed
by the inverse scalar-restriction comparison at every level. Its naturality is actual
compatibility with all transitions, rather than merely equality in a derived category.
Source: Stacks 0GL1, strict refinement in the node
(blueprint: lem-cbc-ringed-open-strict-reduction).
Proof: the n-th map is [x] tensor b to [x tensor b|W]. Each quotient-transition square
sends this generator to [x tensor q(b)|W] along both paths. Thus the level maps and
inverses give maps of actual strict towers. Their naturality in M follows on the same
generators. The tensor and sheafification universal properties give uniqueness. -/
theorem cbcStrictReductionIso_existsUnique :
    ∃! δ : cbcCompletedExtension W d ⋙ completedReductionModuleTowerFunctor T d ≅
        completedReductionModuleTowerFunctor W.left d ⋙ cbcCompletedTowerExtension W d,
      ∀ (M : reductionModules W.left (completedReductionCoefficient W.left d)) (n : ℕ),
        (δ.hom.app M).app (op n) =
          (reductionRestrict T (completedReductionProjection T d n)).map
            ((cbcOpenScalarIso W (cbcCompletedRestriction W d) (cbcFiniteRestriction W d n)
              (completedReductionProjection T d n) (completedReductionProjection W.left d n)
              (cbcProjectionSquare W d n)).hom.app M) ≫
          (cbcOpenRestrictIso W (cbcCompletedRestriction W d) (cbcFiniteRestriction W d n)
            (completedReductionProjection T d n) (completedReductionProjection W.left d n)
            (cbcProjectionSquare W d n)).inv.app
              ((reductionChange W.left (completedReductionProjection W.left d n)).obj M) := by
  sorry

/-- The strict comparison with its uniquely prescribed finite-level maps.
Source: Stacks 0GL1 (blueprint: lem-cbc-ringed-open-strict-reduction). -/
def cbcStrictReductionIso := (cbcStrictReductionIso_existsUnique W d).exists.choose



/-- The comparison on actual strict complexes, obtained by applying its module map
in every degree. Source: Stacks 0GL1
(blueprint: lem-cbc-ringed-open-strict-reduction). -/
def cbcStrictReductionComplexIso :=
  letI := cbcCompletedExtension_additive W d
  letI := cbcCompletedTowerExtension_additive W d
  letI := completedReductionModuleTowerFunctor_additive T d
  letI := completedReductionModuleTowerFunctor_additive W.left d
  NatIso.mapHomologicalComplex (cbcStrictReductionIso W d) (.up ℤ)

/-- Both strict quotient augmentations agree under the comparison, level by level.
Applying this in every degree is equality of augmented strict complex diagrams.
Source: the node's quotient-augmentation refinement of Stacks 0GL1
(blueprint: lem-cbc-ringed-open-strict-reduction).
Proof: on every extension summand the two paths send [x] to [x tensor 1].
Module sheafification extends that equality uniquely. The quotient maps preserve 1,
so these are strict augmentation maps and equality holds before localization. -/
theorem cbcStrictReduction_augmentation
    (M : reductionModules W.left (completedReductionCoefficient W.left d)) (n : ℕ) :
    (((completedReductionModuleUnit d T).app ((cbcCompletedExtension W d).obj M)).app
      (op n)) ≫ ((cbcStrictReductionIso W d).hom.app M).app (op n) =
    (cbcCompletedExtension W d).map (((completedReductionModuleUnit d W.left).app M).app
      (op n)) := by
  sorry

/-- The coefficient-linear finite comparison, before scalar restriction.
Source: Stacks 0GL1 (blueprint: lem-cbc-ringed-open-strict-reduction). -/
def cbcFiniteReductionIso (n : ℕ) :=
  cbcOpenScalarIso W (cbcCompletedRestriction W d) (cbcFiniteRestriction W d n)
    (completedReductionProjection T d n) (completedReductionProjection W.left d n)
    (cbcProjectionSquare W d n)

/-- The comparison between the b-th and a-th quotient coefficient rings.
Source: Stacks 0GL1 (blueprint: lem-cbc-ringed-open-strict-reduction). -/
def cbcQuotientReductionIso (b a : ℕ) (hab : a ≤ b) :=
  cbcOpenScalarIso W (cbcFiniteRestriction W d b) (cbcFiniteRestriction W d a)
    (reductionCoefficientMap T d b a hab) (reductionCoefficientMap W.left d b a hab)
    (cbcQuotientSquare W d b a hab)

/-- Compatibility with quotient normalization in every degree, including equal indices.
The maps are over the smaller quotient ring, before restricting coefficients.
Source: balancing normalization of the datum, Stacks 0GL1
(blueprint: lem-cbc-ringed-open-strict-reduction).
Proof: on (([x] tensor r) tensor s) both paths give [x tensor q(r)|W*s|W].
Balancing and module sheafification extend this identity to the degreewise maps.
Since it holds in every degree, it is equality of the chain maps. For b=a the
quotient map is the identity and this is the ordinary tensor unit normalization. -/
theorem cbcStrictReduction_normalization (b a : ℕ) (hab : a ≤ b)
    (P : CochainComplex (reductionModules W.left
      (completedReductionCoefficient W.left d)) ℤ) (p : ℤ) :
    (reductionChange T (reductionCoefficientMap T d b a hab)).map
        ((cbcFiniteReductionIso W d b).hom.app (P.X p)) ≫
      (cbcQuotientReductionIso W d b a hab).hom.app
        ((reductionChange W.left (completedReductionProjection W.left d b)).obj (P.X p)) ≫
      (cbcRingedOpenExtension W (cbcFiniteRestriction W d a)).map
        ((reductionBalance W.left (completedReductionProjection W.left d b)
          (reductionCoefficientMap W.left d b a hab) (completedReductionProjection W.left d a)
          (completedReductionProjection_comp W.left d b a hab) P).f p) =
    (reductionBalance T (completedReductionProjection T d b)
        (reductionCoefficientMap T d b a hab) (completedReductionProjection T d a)
        (completedReductionProjection_comp T d b a hab)
        (((cbcCompletedExtension W d).mapHomologicalComplex (.up ℤ)).obj P)).f p ≫
      (cbcFiniteReductionIso W d a).hom.app (P.X p) := by
  sorry

/-- The left endpoint's canonical computation on a representative, using exact open
extension and then the reduction tower's universal counit.
Source: Stacks 0GL1 (blueprint: lem-cbc-ringed-open-strict-reduction). -/
def cbcLeftReductionComputation
    (P : CochainComplex (reductionModules W.left
      (completedReductionCoefficient W.left d)) ℤ) :
    ((cbcCompletedExtension W d).mapDerivedCategory ⋙ completedReductionTower T d).obj
        (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((completedReductionComplexTowerFunctor T d).obj
        (((cbcCompletedExtension W d).mapHomologicalComplex (.up ℤ)).obj P)) :=
  (completedReductionTower T d).map
      ((cbcCompletedExtension W d).mapDerivedCategoryFactors.hom.app P) ≫
    completedReductionTowerComplexCounit T d
      (((cbcCompletedExtension W d).mapHomologicalComplex (.up ℤ)).obj P)

/-- The right endpoint's canonical computation, reducing on the open and extending
its entire strict tower by the exact functor.
Source: Stacks 0GL1 (blueprint: lem-cbc-ringed-open-strict-reduction). -/
def cbcRightReductionComputation
    (P : CochainComplex (reductionModules W.left
      (completedReductionCoefficient W.left d)) ℤ) :
    (completedReductionTower W.left d ⋙ (cbcCompletedTowerExtension W d).mapDerivedCategory).obj
        (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((cbcCompletedTowerExtension W d).mapHomologicalComplex (.up ℤ)).obj
        ((completedReductionComplexTowerFunctor W.left d).obj P)) :=
  (cbcCompletedTowerExtension W d).mapDerivedCategory.map
      (completedReductionTowerComplexCounit W.left d P) ≫
    (cbcCompletedTowerExtension W d).mapDerivedCategoryFactors.hom.app
      ((completedReductionComplexTowerFunctor W.left d).obj P)

attribute [local irreducible] cbcLeftReductionComputation cbcRightReductionComputation
attribute [local irreducible] completedReductionTower Functor.mapDerivedCategory
attribute [local irreducible] Functor.mapDerivedCategoryFactors

/-- Canonical natural strict reduction under ringed open extension. Its components
are the desired rho_(e,K). The unique characterization ties them to actual strict
chain maps, not just arbitrary isomorphisms of derived objects. No completeness or
quasi-compactness assumption occurs.

Source: blueprint lem-cbc-completed-extension-zero-comparison.proof.md, opening
reduction argument; Stacks 0GL1, with the node's strict refinement
(blueprint: lem-cbc-ringed-open-strict-reduction).

Proof:
1. Identify finite coefficients by sheafification localization; their maps agree by
naturality. Sectionwise limits give the completed coefficient identification. The
ringed slice extension is exact (lem-pur-site-restriction-module-adjunction-exact).
Choose a flat-term K-flat resolution (lem-pc-kflat-resolution). Its open extension
is again flat-term K-flat (lem-cbc-ringed-open-flat-resolution). Thus both endpoints
are computed from that same representative, using levelwise exactness of towers.
2. The slice tensor formula (lem-weil-pbc-ringed-slice-extension-tensor), with inverse
fixed by the open-unit adjunct (lem-sf-open-tensor-normalization), gives exactly
[x] tensor b to [x tensor b|W]. This is cbcOpenScalarIso before scalar restriction.
It commutes with differentials, hence gives the displayed strict complex map.
3. Quotient transitions agree on those generators, so the maps assemble as an actual
strict tower isomorphism cbcStrictReductionIso. The identity on abelian sheafifications
compares restriction of scalars, retaining linearity over each quotient ring.
4. The two quotient augmentations send [x] to [x tensor 1], giving the strict equality
cbcStrictReduction_augmentation before localization.
5. Successive scalar extension of a flat-term K-flat complex remains K-flat over the
quotient (lem-pur-kflat-change-of-rings). Both normalization paths agree on tensors,
as stated in cbcStrictReduction_normalization. Equal indices give the tensor unit.
For three indices both paths give [x tensor q(r)|W*q(s)|W*t|W]; this is the datum's
three-index balancing cocycle, preserved by the same generator formula.
6. The maps are natural for all chain maps between those representatives. Exact
extension preserves quasi-isomorphisms; coefficient change preserves them on K-flat
complexes (lem-pur-derived-change-of-rings), levelwise on towers. The resolving-class
localization equivalence (lem-weil-pbc-site-derived-tensor-descent, first assertion)
and localization universal property descend the strict map and its inverse uniquely.
The displayed counit equation proves independence of the representative, and naturality
in the whole derived category includes all inverted quasi-isomorphisms. -/
theorem cbcRingedOpenStrictReduction :
    ∃! ρ : (cbcCompletedExtension W d).mapDerivedCategory ⋙ completedReductionTower T d ≅
        completedReductionTower W.left d ⋙ (cbcCompletedTowerExtension W d).mapDerivedCategory,
      ∀ (P : CochainComplex (reductionModules W.left
          (completedReductionCoefficient W.left d)) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients
            (R := completedReductionCoefficient W.left d) P →
        (∀ p : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology W.left)
          (R := completedReductionCoefficient W.left d) (P.X p)) →
        IsIso (cbcLeftReductionComputation W d P) ∧
        IsIso (cbcRightReductionComputation W d P) ∧
        ρ.hom.app (DerivedCategory.Q.obj P) ≫ cbcRightReductionComputation W d P =
          cbcLeftReductionComputation W d P ≫
            DerivedCategory.Q.map ((cbcStrictReductionComplexIso W d).hom.app P) := by
  sorry




/-- The first parenthesization of the three-index normalization in a fixed degree.
Source: datum's balancing cocycle (blueprint: lem-cbc-ringed-open-strict-reduction). -/
def cbcNormalizeLeftAt (X : Scheme.{u}) {A' : Type (u + 1)} [CommRing A']
    (d' : AdicCoefficientDatum A') (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c)
    (P : CochainComplex (reductionModules X (completedReductionCoefficient X d')) ℤ) (p : ℤ) :=
  (reductionChange X (reductionCoefficientMap X d' b a hab)).map
      ((reductionBalance X (completedReductionProjection X d' c)
        (reductionCoefficientMap X d' c b hbc) (completedReductionProjection X d' b)
        (completedReductionProjection_comp X d' c b hbc) P).f p) ≫
    (reductionBalance X (completedReductionProjection X d' b)
      (reductionCoefficientMap X d' b a hab) (completedReductionProjection X d' a)
      (completedReductionProjection_comp X d' b a hab) P).f p

/-- The second parenthesization, first composing the two quotient extensions.
Source: datum's balancing cocycle (blueprint: lem-cbc-ringed-open-strict-reduction). -/
def cbcNormalizeRightAt (X : Scheme.{u}) {A' : Type (u + 1)} [CommRing A']
    (d' : AdicCoefficientDatum A') (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c)
    (P : CochainComplex (reductionModules X (completedReductionCoefficient X d')) ℤ) (p : ℤ) :=
  (reductionBalance X (reductionCoefficientMap X d' c b hbc)
      (reductionCoefficientMap X d' b a hab)
      (reductionCoefficientMap X d' c a (hab.trans hbc))
      (reductionCoefficientMap_comp X d' c b a hab hbc)
      ((reductionChangeComplex X (completedReductionProjection X d' c)).obj P)).f p ≫
    (reductionBalance X (completedReductionProjection X d' c)
      (reductionCoefficientMap X d' c a (hab.trans hbc)) (completedReductionProjection X d' a)
      (completedReductionProjection_comp X d' c a (hab.trans hbc)) P).f p

/-- Successively commute all three scalar extensions with open extension in degree p.
Source: Stacks 0GL1 (blueprint: lem-cbc-ringed-open-strict-reduction). -/
def cbcTripleScalarComparisonAt (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c)
    (P : CochainComplex (reductionModules W.left
      (completedReductionCoefficient W.left d)) ℤ) (p : ℤ) :=
  (reductionChange T (reductionCoefficientMap T d b a hab)).map
      ((reductionChange T (reductionCoefficientMap T d c b hbc)).map
        ((cbcFiniteReductionIso W d c).hom.app (P.X p))) ≫
    (reductionChange T (reductionCoefficientMap T d b a hab)).map
      ((cbcQuotientReductionIso W d c b hbc).hom.app
        ((reductionChange W.left (completedReductionProjection W.left d c)).obj (P.X p))) ≫
    (cbcQuotientReductionIso W d b a hab).hom.app
      ((reductionChange W.left (reductionCoefficientMap W.left d c b hbc)).obj
        ((reductionChange W.left (completedReductionProjection W.left d c)).obj (P.X p)))

/-- Both three-index normalization paths are preserved, and agree before localization.
All equal-index cases are included. Quantification over every degree expresses the
actual chain-map equations over the smallest quotient coefficient ring.
Source: strict refinement of Stacks 0GL1 and the datum's normalization cocycle
(blueprint: lem-cbc-ringed-open-strict-reduction).
Proof: on (([x] tensor r) tensor s) tensor t, every path gives
[x tensor q_(c,a)(r)|W*q_(b,a)(s)|W*t|W]. Multiplicativity of the quotient maps
and associativity identify the two normalizations on T and W. The tensor and
module-sheafification universal properties extend this equality from the generators
to the degreewise maps; equality in every degree is equality of chain maps. -/
theorem cbcStrictReduction_cocycle (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c)
    (P : CochainComplex (reductionModules W.left
      (completedReductionCoefficient W.left d)) ℤ) (p : ℤ) :
    cbcNormalizeLeftAt T d c b a hab hbc
        (((cbcCompletedExtension W d).mapHomologicalComplex (.up ℤ)).obj P) p ≫
        (cbcFiniteReductionIso W d a).hom.app (P.X p) =
      cbcTripleScalarComparisonAt W d c b a hab hbc P p ≫
        (cbcRingedOpenExtension W (cbcFiniteRestriction W d a)).map
          (cbcNormalizeLeftAt W.left d c b a hab hbc P p) ∧
    cbcNormalizeRightAt T d c b a hab hbc
        (((cbcCompletedExtension W d).mapHomologicalComplex (.up ℤ)).obj P) p ≫
        (cbcFiniteReductionIso W d a).hom.app (P.X p) =
      cbcTripleScalarComparisonAt W d c b a hab hbc P p ≫
        (cbcRingedOpenExtension W (cbcFiniteRestriction W d a)).map
          (cbcNormalizeRightAt W.left d c b a hab hbc P p) ∧
    cbcNormalizeLeftAt T d c b a hab hbc
        (((cbcCompletedExtension W d).mapHomologicalComplex (.up ℤ)).obj P) p =
      cbcNormalizeRightAt T d c b a hab hbc
        (((cbcCompletedExtension W d).mapHomologicalComplex (.up ℤ)).obj P) p ∧
    cbcNormalizeLeftAt W.left d c b a hab hbc P p =
      cbcNormalizeRightAt W.left d c b a hab hbc P p := by
  sorry

end AlgebraicGeometry.Scheme
