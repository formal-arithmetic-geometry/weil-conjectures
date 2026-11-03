/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.CondensedL2Growth
public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.Compactification.Affine
public import WeilConjectures.AlgebraicGeometry.AffineSpaceCharts
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.PoincareDuality.CondensedModule.CondensedModuleDerivedLocalFrobenius
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportGeometry
import all WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Rank-r Plancherel statement for the condensed Fourier transform

This is the statement layer for `sk-cor-plancherel`.  The Fourier and inverse
outputs below are canonical functions of the input strict pair; their trace
functions use the canonical `CondensedModule.derivedAlternatingTrace` operation
on their own Weil datum.  The affine Fourier functor used by the construction is the
published `condensedAffineFourierTransform`.
Source: latest blueprint, part-weights-riemann-hypothesis/sec-fourier-transform/
sec-trace-functions-and-plancherel/sk-cor-plancherel/_section.md
(blueprint: sk-cor-plancherel).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry AlgebraicGeometry.ProEtale
open Opposite
open scoped CategoryTheory.Obj
  AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilConjectures.NativeL2

/-- The squared finite-extension trace energy used by the rank-r Plancherel statement.
The trace function is the condensed alternating local Frobenius trace of
`def-weil-local-frobenius-trace`.
Source: sk-cor-plancherel, display (18.3) (blueprint: sk-cor-plancherel). -/
def affineExtensionTraceEnergy
    (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (ι : PadicAlgCl l →+* ℂ)
    (t : ∀ (n : ℕ) (hn : 1 ≤ n),
      D.extensionPoints X₀ n hn → PadicAlgCl l)
    (n : ℕ) (hn : 1 ≤ n) : ℝ :=
  ∑ᶠ x : D.extensionPoints X₀ n hn, ‖ι (t n hn x)‖ ^ 2

/-- The ambient constant-model object underlying a strict condensed Weil pair.
Source: strict-pair setting (blueprint: sk-cor-plancherel). -/
def condensedStrictUnderlying
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (K : CondensedRing.StrictWeilCondensed.Complex
      (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀)) :
    (constantModelBoundedConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left).FullSubcategory :=
  let U := (CondensedRing.StrictWeilCondensed.forget
    (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀)).obj K
  ⟨U.obj, U.property.1⟩

/-- The canonical cohomology-transport form of the strict pair's own Weil action.
Source: local trace of the given strict pair (blueprint: sk-cor-plancherel). -/
def condensedStrict_cohomologyIso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (K : CondensedRing.StrictWeilCondensed.Complex
      (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀)) :
    (CondensedRing.CohomologyTransport.L
      (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀).hom).obj
      (condensedStrictUnderlying D l X₀ K).obj ≅
      (condensedStrictUnderlying D l X₀ K).obj := by
  let U := (CondensedRing.StrictWeilCondensed.forget
    (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀)).obj K
  exact (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
    (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀).hom).app U.obj ≪≫
    (ObjectProperty.ι _).mapIso K.str

/-- The terminal profinite set has its canonical point.
Source: terminal-section scalar coordinates (blueprint: sk-cor-plancherel). -/
instance traceTerminalInhabited : Inhabited (⊤_ Profinite.{u}) :=
  ⟨(terminalIsTerminal.from (Profinite.of PUnit.{u + 1})) PUnit.unit⟩

/-- Terminality makes evaluation independent of the point.
Source: terminal-section scalar coordinates (blueprint: sk-cor-plancherel). -/
instance traceTerminalSubsingleton : Subsingleton (⊤_ Profinite.{u}) := by
  constructor
  intro x y
  let c : (⊤_ Profinite.{u}) ⟶ (⊤_ Profinite.{u}) :=
    ConcreteCategory.ofHom ⟨fun _ ↦ x, continuous_const⟩
  exact ConcreteCategory.congr_hom (terminalIsTerminal.hom_ext c (𝟙 _)) y

/-- The section ring coordinates of the forgetful additive sheaf are the original
ring sections, with the same operations.
Source: condensed coefficient scalar convention (blueprint: sk-cor-plancherel). -/
def traceSectionCoordinates
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R)] (S : Profinite.{u}) :
    (condensedSectionRing ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R)).obj.obj (op S) ≃+*
      R.obj.obj (op S) := by
  let T := coherentTopology Profinite.{u}
  let A := (sheafCompose T (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  have hm : (sheafToPresheaf T Ab.{u + 1}).monObjObj A =
      R.obj.monObjCompForget₂ := by
    apply MonObj.ext
    let : MonObj A.obj := R.obj.monObjCompForget₂
    exact Sheaf.μ_comp_map_mul A
  refine { toEquiv := Equiv.refl _
           map_add' := fun _ _ ↦ rfl
           map_mul' := ?_ }
  intro a b
  change (((sheafToPresheaf T Ab.{u + 1}).monObjObj A).mul.app (op S)).hom
    (a ⊗ₜ[ℤ] b) = (show R.obj.obj (op S) from a) * (show R.obj.obj (op S) from b)
  have h := congrArg (fun m : MonObj A.obj ↦ m.mul) hm
  rw [h]
  rfl

/-- The canonical terminal-section coordinates of the algebraic-closure coefficient ring.
Source: the Qbar_l scalar convention (blueprint: sk-cor-plancherel). -/
noncomputable def condensedScalarRing_equiv (l : ℕ) [Fact l.Prime] :
    ↑(condensedScalarRing (Profinite.padicAlgClRingObj l)) ≃+* PadicAlgCl l :=
  (traceSectionCoordinates (Profinite.padicAlgClCondensedRing l) (⊤_ Profinite.{u})).trans
    { toFun := fun f ↦ f.down.val
          ((terminalIsTerminal.from (Profinite.of PUnit.{u + 1})) PUnit.unit)
      invFun := Profinite.PadicAlgCl.constSectionRingHom l (op (⊤_ Profinite.{u}))
      left_inv := fun f ↦ by
        apply ULift.ext
        apply Subtype.ext
        apply ContinuousMap.ext
        intro x
        exact congrArg f.down.val (Subsingleton.elim _ _)
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }

/-- The condensed trace attached to a strict pair, using its own IsoAlgebra structure.
Source: def-weil-local-frobenius-trace in the setting (blueprint: sk-cor-plancherel). -/
def condensedStrictTrace
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (K : CondensedRing.StrictWeilCondensed.Complex
      (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀))
    (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints X₀ n hn) : PadicAlgCl l :=
  (condensedScalarRing_equiv l)
    (CondensedModule.derivedAlternatingTrace (Profinite.padicAlgClRingObj l) D
      (D.geometricFrobenius X₀).hom (condensedStrictUnderlying D l X₀ K).obj
      (condensedStrict_cohomologyIso D l X₀ K)
      (localExtensionPoint D X₀ n hn x) (n - 1)
      (localExtensionPoint_return D X₀ n hn x))

/-- The carrier satisfies the constructibility predicate used by the growth definition.
Source: strict-pair and growth conventions (blueprint: sk-cor-plancherel).
Proof: the strict carrier has bounded finite-constant-model constructible cohomology.
Forgetting the specified scalar local models gives ordinary constructible cohomology;
boundedness is unchanged. This is precisely the weaker boundedConstructible predicate. -/
theorem condensedStrictGrowth_mem
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (K : CondensedRing.StrictWeilCondensed.Complex
      (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀)) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left)
      ((CondensedRing.StrictWeilCondensed.forget
        (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀)).obj K).obj := by
  rw [(adicConstructibilityPredicateComparison l (D.geometricFiber X₀).left
    (Profinite.padicAlgClRingObj l) .algebraicClosure).2]
  exact K.obj.a.property.1

/-- The canonical view required by the published growth parameter, retaining the carrier
and the ambient image of the given Weil datum.
Source: growth convention (blueprint: sk-cor-plancherel). -/
def condensedStrictGrowthComplex
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (K : CondensedRing.StrictWeilCondensed.Complex
      (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀)) :
    condensedStrictWeilComplex (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom :=
  let U := (CondensedRing.StrictWeilCondensed.forget
    (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀)).obj K
  ⟨CategoryTheory.Endofunctor.IsoAlgebra.mk U.obj
      ((ObjectProperty.ι _).mapIso K.str), condensedStrictGrowth_mem D l X₀ K⟩

/-- The growth parameter evaluated on the canonical forgetful view of a strict pair.
Source: sk-def-wrp-l2-definition in the growth clause (blueprint: sk-cor-plancherel). -/
def condensedGrowthParameter
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (hl : l ≠ D.p)
    [IsAffine X₀.left] [IsSeparated X₀.hom]
    [SmoothOfRelativeDimension 1 X₀.hom] [GeometricallyConnected X₀.hom]
    (ι : PadicAlgCl l →+* ℂ)
    (K : CondensedRing.StrictWeilCondensed.Complex
      (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀)) : EReal :=
  growthParameter D l X₀ hl ι (condensedStrictGrowthComplex D l X₀ K)

/-- Descent of a pulled-back module along a specified invariant morphism. The equality
fixes the comparison; no isomorphism is chosen.
Source: arithmetic descent of the Fourier kernel (blueprint: sk-cor-plancherel). -/
@[irreducible] def invariantSheafDatum
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (g : X ≅ X) (f : X ⟶ Y) (hf : g.hom ≫ f = f)
    (A : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (CondensedRing.upperStar Λ g.hom).obj ((CondensedRing.upperStar Λ f).obj A) ≅
      (CondensedRing.upperStar Λ f).obj A :=
  ((CondensedRing.upperStarComp Λ g.hom f).app A).symm ≪≫
    eqToIso (congrArg (fun t ↦ (CondensedRing.upperStar Λ t).obj A) hf)

/-- Exact inverse image takes the given sheaf descent to its degree-zero complex.
Source: arithmetic descent of the Fourier kernel (blueprint: sk-cor-plancherel). -/
@[irreducible] def invariantSingleDatum
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme.{u}} (g : X ≅ X)
    (A : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (φ : (CondensedRing.upperStar Λ g.hom).obj A ≅ A) :
    (CondensedRing.StrictWeilCondensed.action Λ g).obj
      ((DerivedCategory.singleFunctor _ 0).obj A) ≅
        (DerivedCategory.singleFunctor _ 0).obj A :=
  ((CondensedRing.upperStar Λ g.hom).mapDerivedCategorySingleFunctor 0).app A ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso φ

set_option maxHeartbeats 1600000 in
-- The derived-category tensor/exchange comparison needs additional elaboration heartbeats.
/-- The induced Frobenius comparison for a specified Fourier correspondence. All
factors are the prescribed six-operation comparisons, on the ambient categories.
Source: induced Weil structure in the Fourier definition (blueprint: sk-cor-plancherel). -/
@[irreducible] def fourierExchangeComponent
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {V W : Scheme.{u}} (g : V ≅ V) (h : W ≅ W) (p₁ p₂ : W ⟶ V)
    (c : Compactification p₂)
    (sq₁ : CommSq h.hom p₁ p₁ g.hom) (sq₂ : CommSq h.hom p₂ p₂ g.hom)
    (s : CondensedRing.CompactificationReindexing.Square c c h.hom g.hom)
    [IsIso s.middle]
    (L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)))
    (φL : (CondensedRing.StrictWeilCondensed.action Λ h).obj L ≅ L)
    (d : ℤ)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V))) :
    (CondensedRing.StrictWeilCondensed.action Λ g).obj
      (((CondensedRing.upperStar Λ p₁).leftDerivedFunctor ⋙ tensorRight L ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification Λ c ⋙
          shiftFunctor _ d).obj K) ≅
    ((CondensedRing.upperStar Λ p₁).leftDerivedFunctor ⋙ tensorRight L ⋙
      CondensedRing.rightDerivedLowerShriekOfCompactification Λ c ⋙
        shiftFunctor _ d).obj ((CondensedRing.StrictWeilCondensed.action Λ g).obj K) := by
  let P := (CondensedRing.upperStar Λ p₁).leftDerivedFunctor
  let R := CondensedRing.rightDerivedLowerShriekOfCompactification Λ c
  letI := (CondensedRing.CompactificationReindexing.square_isIso Λ s sq₂).2
  exact ((CondensedRing.StrictWeilCondensed.action Λ g).commShiftIso d).app _ ≪≫
    (shiftFunctor _ d).mapIso
      ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ g.hom).symm.app _ ≪≫
        (asIso (CondensedRing.CompactificationReindexing.squareExchange Λ s)).app _ ≪≫
        R.mapIso
          (((CondensedRing.leftDerivedUpperStarTensorIso Λ h.hom).app (P.obj K)).app L ≪≫
            tensorIso
              ((CondensedRing.pullbackSquareComparison Λ sq₁).symm.app K ≪≫
                P.mapIso ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
                  Λ g.hom).app K))
              ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ h.hom).app L ≪≫ φL)))

namespace RankRAffine

variable (D : FiniteFieldDatum.{u}) (r : ℕ)

/-- The standard arithmetic affine space V₀ = Aʳ, with its actual structure map.
Source: sk-cor-plancherel, setting (blueprint: sk-cor-plancherel). -/
abbrev model : Over (Spec (.of D.k₀)) :=
  Over.mk (AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))

/-- Standard affine geometry for the recorded bundled model.
Source: affine Fourier setting (blueprint: sk-cor-plancherel). -/
instance model_locallyOfFiniteType : LocallyOfFiniteType (model D r).hom := by
  dsimp [model]
  infer_instance

/-- Standard affine geometry for the recorded bundled model.
Source: affine Fourier setting (blueprint: sk-cor-plancherel). -/
instance model_quasiCompact : QuasiCompact (model D r).hom := by
  dsimp [model]
  infer_instance

/-- Standard affine geometry for the recorded bundled model.
Source: affine Fourier setting (blueprint: sk-cor-plancherel). -/
instance model_isAffine : IsAffine (model D r).left := by
  dsimp [model]
  infer_instance

/-- Standard affine geometry for the recorded bundled model.
Source: affine Fourier setting (blueprint: sk-cor-plancherel). -/
instance model_isSeparated : IsSeparated (model D r).hom := by
  dsimp [model]
  infer_instance

/-- The arithmetic Fourier product with its first-projection base map.
Source: sk-cor-plancherel, Fourier square (blueprint: sk-cor-plancherel). -/
abbrev productModel : Over (Spec (.of D.k₀)) :=
  Over.mk (pullback.fst (model D r).hom (model D r).hom ≫ (model D r).hom)

/-- Standard affine geometry for the recorded bundled model.
Source: affine Fourier setting (blueprint: sk-cor-plancherel). -/
instance productModel_locallyOfFiniteType : LocallyOfFiniteType (productModel D r).hom := by
  change LocallyOfFiniteType
    (pullback.fst (model D r).hom (model D r).hom ≫ (model D r).hom)
  exact locallyOfFiniteType_comp _ _

/-- Standard affine geometry for the recorded bundled model.
Source: affine Fourier setting (blueprint: sk-cor-plancherel). -/
instance productModel_quasiCompact : QuasiCompact (productModel D r).hom := by
  dsimp [productModel]
  infer_instance

/-- Standard affine geometry for the recorded bundled model.
Source: affine Fourier setting (blueprint: sk-cor-plancherel). -/
instance productModel_isAffine : IsAffine (productModel D r).left := by
  dsimp [productModel]
  infer_instance

/-- Standard affine geometry for the recorded bundled model.
Source: affine Fourier setting (blueprint: sk-cor-plancherel). -/
instance productModel_isSeparated : IsSeparated (productModel D r).hom := by
  dsimp [productModel]
  infer_instance

/-- The first arithmetic projection. Source: the Fourier square
(blueprint: sk-cor-plancherel). -/
def firstModel : productModel D r ⟶ model D r :=
  Over.homMk (pullback.fst _ _) rfl

/-- The second arithmetic projection. Source: the Fourier square
(blueprint: sk-cor-plancherel). -/
def secondModel : productModel D r ⟶ model D r :=
  Over.homMk (pullback.snd _ _) pullback.condition.symm

/-- Scalar extension to the fixed algebraic closure.
Source: the geometric reduction (blueprint: sk-cor-plancherel). -/
abbrev geometric := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- The canonical affine-space base-change isomorphism.
Source: V = V₀ × k in the setting (blueprint: sk-cor-plancherel). -/
def coordinates : (D.geometricFiber (model D r)).left ≅
    AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)) :=
  AffineSpace.pullbackIso (ULift.{u} (Fin r))
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- The geometric structure projection of the literal affine space.
Source: the Fourier square (blueprint: sk-cor-plancherel). -/
abbrev projection := AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)) ↘ Spec (.of D.k)

/-- Scalar extension preserves the Fourier product, including both affine coordinates.
Source: the geometric Fourier square (blueprint: sk-cor-plancherel).
Proof: base change preserves the arithmetic pullback cone. Compose its two legs with
AffineSpace.pullbackIso; its projection identities identify the two base maps with
projection. The universal property then supplies this Cartesian cone. -/
theorem productCartesian : IsPullback
    (((geometric D).map (firstModel D r)).left ≫ (coordinates D r).hom)
    (((geometric D).map (secondModel D r)).left ≫ (coordinates D r).hom)
    (projection D r) (projection D r) := by
  have h : IsLimit (BinaryFan.mk (firstModel D r) (secondModel D r)) :=
    IsLimit.pullbackConeEquivBinaryFanFunctor
      (limit.isLimit (cospan (model D r).hom (model D r).hom))
  have hb := Over.isPullback_of_binaryFan_isLimit _
    (mapIsLimitOfPreservesOfIsLimit (geometric D) _ _ h)
  apply hb.of_iso (Iso.refl _) (coordinates D r) (coordinates D r) (Iso.refl _)
  · simp
  · simp
  · simp [coordinates, projection]
  · simp [coordinates, projection]

/-- The unique product isomorphism with the specified projection maps.
Source: the geometric Fourier square (blueprint: sk-cor-plancherel). -/
def productCoordinates : (D.geometricFiber (productModel D r)).left ≅
    pullback (projection D r) (projection D r) :=
  (productCartesian D r).isoPullback

/-- Frobenius on the literal affine space, transported by the canonical coordinates.
Source: the induced Weil structure (blueprint: sk-cor-plancherel). -/
def frobenius := (coordinates D r).symm ≪≫
  D.geometricFrobenius (model D r) ≪≫ coordinates D r

/-- Frobenius on the literal Fourier product, with the same coordinate transport.
Source: the induced Weil structure (blueprint: sk-cor-plancherel). -/
def productFrobenius := (productCoordinates D r).symm ≪≫
  D.geometricFrobenius (productModel D r) ≪≫ productCoordinates D r

/-- An arithmetic compactification of the second projection. The geometric
compactification will be its scalar extension, so the middle has specified Frobenius.
Source: the definition of Rp₂! (blueprint: sk-cor-plancherel). -/
@[irreducible] def arithmeticCompactification : Compactification (secondModel D r).left :=
  letI : LocallyOfFiniteType (secondModel D r).left := by
    change LocallyOfFiniteType (pullback.snd (model D r).hom (model D r).hom)
    infer_instance
  letI : QuasiCompact (secondModel D r).left := by
    change QuasiCompact (pullback.snd (model D r).hom (model D r).hom)
    infer_instance
  letI : HasCompactification (secondModel D r).left :=
    HasCompactification.of_isQuasiAffine (secondModel D r).left
  HasCompactification.compactification (secondModel D r).left

/-- The arithmetic middle model, with its map to the finite field.
Source: the definition of Rp₂! (blueprint: sk-cor-plancherel). -/
abbrev middle : Over (Spec (.of D.k₀)) :=
  Over.mk ((arithmeticCompactification D r).g ≫ (model D r).hom)

/-- Standard affine geometry for the recorded bundled model.
Source: affine Fourier setting (blueprint: sk-cor-plancherel). -/
instance middle_locallyOfFiniteType : LocallyOfFiniteType (middle D r).hom := by
  dsimp [middle]
  infer_instance

/-- Standard affine geometry for the recorded bundled model.
Source: affine Fourier setting (blueprint: sk-cor-plancherel). -/
instance middle_quasiCompact : QuasiCompact (middle D r).hom := by
  dsimp [middle]
  infer_instance

/-- The arithmetic open map of the chosen compactification.
Source: the definition of Rp₂! (blueprint: sk-cor-plancherel). -/
def openModel : productModel D r ⟶ middle D r :=
  Over.homMk (arithmeticCompactification D r).i (by
    change (arithmeticCompactification D r).i ≫
      ((arithmeticCompactification D r).g ≫ (model D r).hom) = _
    rw [← Category.assoc, ← (arithmeticCompactification D r).comm]
    exact (secondModel D r).w)

/-- The arithmetic proper map of the chosen compactification.
Source: the definition of Rp₂! (blueprint: sk-cor-plancherel). -/
def properModel : middle D r ⟶ model D r :=
  Over.homMk (arithmeticCompactification D r).g rfl

/-- The two geometric compactification maps have the required factorization and
proper/open properties after coordinate transport.
Source: the Fourier definition (blueprint: sk-cor-plancherel).
Proof: pull back the arithmetic open/proper factorization to k. Properness and open
immersions are stable under base change; composing with the coordinate isomorphisms
preserves them. The product-coordinate second-projection identity gives factorization. -/
theorem compactification_properties :
    pullback.snd (projection D r) (projection D r) =
      ((productCoordinates D r).inv ≫ ((geometric D).map (openModel D r)).left) ≫
        (((geometric D).map (properModel D r)).left ≫ (coordinates D r).hom) ∧
    IsProper (((geometric D).map (properModel D r)).left ≫ (coordinates D r).hom) ∧
    IsOpenImmersion ((productCoordinates D r).inv ≫
      ((geometric D).map (openModel D r)).left) := by
  have hbase {X Y : Over (Spec (.of D.k₀))} (f : X ⟶ Y) :
      IsPullback
        (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
        (((geometric D).map f).left) f.left
        (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) := by
    refine IsPullback.of_bot ?_ (by simp [geometric]) (IsPullback.of_hasPullback _ _)
    simpa [Over.w f] using IsPullback.of_hasPullback X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  have hi : IsOpenImmersion (((geometric D).map (openModel D r)).left) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsOpenImmersion) (hbase (openModel D r))
      (show IsOpenImmersion (arithmeticCompactification D r).i from inferInstance)
  have hg : IsProper (((geometric D).map (properModel D r)).left) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsProper) (hbase (properModel D r))
      (show IsProper (arithmeticCompactification D r).g from inferInstance)
  refine ⟨?_, inferInstance, inferInstance⟩
  have hf : openModel D r ≫ properModel D r = secondModel D r := by
    ext
    exact (arithmeticCompactification D r).comm.symm
  have hf' := congrArg (fun f ↦ ((geometric D).map f).left) hf
  simp only [Functor.map_comp, Over.comp_left] at hf'
  rw [Category.assoc, ← Category.assoc (((geometric D).map (openModel D r)).left), hf']
  exact ((productCartesian D r).isoPullback_inv_snd).symm

/-- The actual compactification passed to the published affine Fourier transform.
Source: the definition of Rp₂! (blueprint: sk-cor-plancherel). -/
def compactification : Compactification (pullback.snd (projection D r) (projection D r)) where
  Z := ((geometric D).obj (middle D r)).left
  i := (productCoordinates D r).inv ≫ ((geometric D).map (openModel D r)).left
  g := ((geometric D).map (properModel D r)).left ≫ (coordinates D r).hom
  comm := (compactification_properties D r).1
  isProper := (compactification_properties D r).2.1
  isOpenImmersion := (compactification_properties D r).2.2

/-- Frobenius commutes with the two projections and with the compactification maps.
The open square is Cartesian.
Source: the induced Weil structure (blueprint: sk-cor-plancherel).
Proof: the arithmetic projection and compactification maps commute with geometric
Frobenius by frobenius_square_cartesian. Conjugate by coordinates/productCoordinates.
For the open square both horizontal Frobenius maps are isomorphisms, so the
commutative square is Cartesian. -/
theorem frobeniusSquares :
    CommSq (productFrobenius D r).hom
      (pullback.fst (projection D r) (projection D r))
      (pullback.fst (projection D r) (projection D r)) (frobenius D r).hom ∧
    CommSq (productFrobenius D r).hom
      (pullback.snd (projection D r) (projection D r))
      (pullback.snd (projection D r) (projection D r)) (frobenius D r).hom ∧
    IsPullback (productFrobenius D r).hom (compactification D r).i
      (compactification D r).i (D.geometricFrobenius (middle D r)).hom ∧
    CommSq (D.geometricFrobenius (middle D r)).hom (compactification D r).g
      (compactification D r).g (frobenius D r).hom := by
  have hn {X Y : Over (Spec (.of D.k₀))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y) :
      (D.geometricFrobenius X).hom ≫ ((geometric D).map f).left =
        ((geometric D).map f).left ≫ (D.geometricFrobenius Y).hom :=
    (D.frobenius_square_cartesian X Y f).2.2.2.2.1
  have hp₁ : (productCoordinates D r).hom ≫
      pullback.fst (projection D r) (projection D r) =
      ((geometric D).map (firstModel D r)).left ≫ (coordinates D r).hom :=
    (productCartesian D r).isoPullback_hom_fst
  have hp₂ : (productCoordinates D r).hom ≫
      pullback.snd (projection D r) (projection D r) =
      ((geometric D).map (secondModel D r)).left ≫ (coordinates D r).hom :=
    (productCartesian D r).isoPullback_hom_snd
  have transport {A B A' B' : Scheme.{u}} (eA : A ≅ A') (eB : B ≅ B')
      (a : A ⟶ A) (b : B ⟶ B) (f : A ⟶ B) (f' : A' ⟶ B')
      (hf : eA.hom ≫ f' = f ≫ eB.hom) (h : a ≫ f = f ≫ b) :
      ((eA.inv ≫ a) ≫ eA.hom) ≫ f' = f' ≫ ((eB.inv ≫ b) ≫ eB.hom) := by
    calc
      ((eA.inv ≫ a) ≫ eA.hom) ≫ f' = eA.inv ≫ a ≫ f ≫ eB.hom := by
        simp only [Category.assoc, hf]
      _ = eA.inv ≫ f ≫ b ≫ eB.hom := by
        rw [← Category.assoc a, h]
        simp only [Category.assoc]
      _ = f' ≫ ((eB.inv ≫ b) ≫ eB.hom) := by
        have he : eA.inv ≫ f = f' ≫ eB.inv := by
          apply (cancel_mono eB.hom).mp
          simp only [Category.assoc]
          rw [← hf]
          simp
        rw [← Category.assoc eA.inv f, he]
        simp only [Category.assoc]
  have h₁ := transport (productCoordinates D r) (coordinates D r)
    (D.geometricFrobenius (productModel D r)).hom (D.geometricFrobenius (model D r)).hom
    ((geometric D).map (firstModel D r)).left
    (pullback.fst (projection D r) (projection D r)) hp₁ (hn (firstModel D r))
  have h₂ := transport (productCoordinates D r) (coordinates D r)
    (D.geometricFrobenius (productModel D r)).hom (D.geometricFrobenius (model D r)).hom
    ((geometric D).map (secondModel D r)).left
    (pullback.snd (projection D r) (projection D r)) hp₂ (hn (secondModel D r))
  have hi : (productFrobenius D r).hom ≫ (compactification D r).i =
      (compactification D r).i ≫ (D.geometricFrobenius (middle D r)).hom := by
    simp only [compactification, productFrobenius, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.hom_inv_id_assoc]
    exact congrArg ((productCoordinates D r).inv ≫ ·) (hn (openModel D r))
  have hg : (D.geometricFrobenius (middle D r)).hom ≫ (compactification D r).g =
      (compactification D r).g ≫ (frobenius D r).hom := by
    simp only [compactification, frobenius, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [← Category.assoc (D.geometricFrobenius _).hom, hn (properModel D r)]
    simp
  exact ⟨⟨h₁⟩, ⟨h₂⟩, IsPullback.of_horiz_isIso ⟨hi⟩, ⟨hg⟩⟩

/-- The compactification Frobenius square uses the arithmetic middle's own Frobenius.
Source: compact-support exchange in the defining transform (blueprint: sk-cor-plancherel). -/
def compactificationSquare : CondensedRing.CompactificationReindexing.Square
    (compactification D r) (compactification D r)
    (productFrobenius D r).hom (frobenius D r).hom where
  middle := (D.geometricFrobenius (middle D r)).hom
  openSquare := (frobeniusSquares D r).2.2.1
  properSquare := (frobeniusSquares D r).2.2.2

/-- The literal product's finite-field structure is the first projection followed by
scalar extension. Source: the affine Fourier definition (blueprint: sk-cor-plancherel). -/
instance productOver : (pullback (projection D r) (projection D r)).Over (Spec (.of D.k₀)) :=
  ⟨pullback.fst _ _ ≫ projection D r ≫
    Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))⟩

/-- The pairing morphism into the arithmetic affine line.
Source: Kψ = pairing* Lψ (blueprint: sk-cor-plancherel). -/
def pairingMap : pullback (projection D r) (projection D r) ⟶
    AffineSpace PUnit (Spec (.of D.k₀)) :=
  AffineSpace.homOfVector (_ ↘ Spec (.of D.k₀))
    (fun _ ↦ AffineSpace.stdPairing (ULift.{u} (Fin r)) (Spec (.of D.k)))

set_option maxHeartbeats 800000 in
-- The affine-coordinate calculation requires additional elaboration heartbeats.
/-- The standard pairing is defined over the finite field and is Frobenius invariant.
Source: arithmetic descent of Kψ (blueprint: sk-cor-plancherel).
Proof: each coordinate is arithmetic and the pairing is their sum of products.
Geometric Frobenius fixes that arithmetic morphism; check on the coordinate and
base projections using the two product-coordinate identities. -/
theorem pairingMap_invariant :
    (productFrobenius D r).hom ≫ pairingMap D r = pairingMap D r := by
  letI := Fintype.ofFinite D.k₀
  let b := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  let f := AffineSpace.map (ULift.{u} (Fin r)) b
  have hf : (frobenius D r).hom ≫ f = f := by
    have h := (D.galoisMap_projections (model D r).hom
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)).1
    change (D.geometricFrobenius (model D r)).hom ≫ _ = _ at h
    apply (cancel_epi (coordinates D r).hom).mp
    simpa only [frobenius, coordinates, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.hom_inv_id_assoc, f, b, AffineSpace.pullbackIso_hom_map,
      model, Over.mk_hom, Over.mk_left] using h
  have hc (i : ULift.{u} (Fin r)) :
      (frobenius D r).hom.appTop (AffineSpace.coord (Spec (.of D.k)) i) =
        AffineSpace.coord (Spec (.of D.k)) i := by
    have h := congrArg (fun g ↦ g.appTop (AffineSpace.coord (Spec (.of D.k₀)) i)) hf
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      f, AffineSpace.map_appTop_coord] using h
  have hb : (frobenius D r).hom ≫ projection D r ≫ b = projection D r ≫ b := by
    have h := congrArg (fun g ↦ g ≫
      (AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))) hf
    simpa only [Category.assoc, f, AffineSpace.map_over, projection] using h
  have hprod : (productFrobenius D r).hom ≫
      (pullback (projection D r) (projection D r) ↘ Spec (.of D.k₀)) =
      (pullback (projection D r) (projection D r) ↘ Spec (.of D.k₀)) := by
    change (productFrobenius D r).hom ≫
      pullback.fst (projection D r) (projection D r) ≫ projection D r ≫ b =
      pullback.fst (projection D r) (projection D r) ≫ projection D r ≫ b
    rw [← Category.assoc (productFrobenius D r).hom,
      (frobeniusSquares D r).1.w, Category.assoc, hb]
  have hp : (productFrobenius D r).hom.appTop
      (AffineSpace.stdPairing (ULift.{u} (Fin r)) (Spec (.of D.k))) =
      AffineSpace.stdPairing (ULift.{u} (Fin r)) (Spec (.of D.k)) := by
    simp only [AffineSpace.stdPairing, map_sum, map_mul]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    · rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        (frobeniusSquares D r).1.w, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hc]
    · rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        (frobeniusSquares D r).2.1.w, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hc]
  apply AffineSpace.hom_ext
  · simpa only [pairingMap, Category.assoc, AffineSpace.homOfVector_over] using hprod
  · intro i
    simpa only [pairingMap, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.homOfVector_appTop_coord] using hp

variable (l : ℕ) [Fact l.Prime]

/-- The coefficient-derived category of the geometric affine space.
Source: D(V_proet,Λ) (blueprint: sk-cor-plancherel). -/
abbrev category := DerivedCategory
  (Mod (Sheaf (Scheme.ProEt.topology (AffineSpace (ULift.{u} (Fin r))
    (Spec (.of D.k)))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l)
        (AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k)))))

/-- This is the published affine transform itself, with its real compactification.
Source: def-fd-transform and the rank-r setting (blueprint: sk-cor-plancherel). -/
@[irreducible] def transform (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj l))) :
    category D r l ⥤ category D r l :=
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  letI : (Spec (.of D.k)).Over (Spec (.of D.k₀)) :=
    ⟨Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))⟩
  condensedAffineFourierTransform (Profinite.padicAlgClRingObj l) D.k₀ (Spec (.of D.k))
    (ULift.{u} (Fin r)) ψ (compactification D r)

/-- The actual degree-zero pairing kernel in the published transform.
Source: Kψ = pairing* Lψ (blueprint: sk-cor-plancherel). -/
def kernel (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj l))) :=
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (pairingMap D r)).obj
    (condensedArtinSchreierSheaf (Profinite.padicAlgClRingObj l) D.k₀ ψ)

/-- Arithmetic-kernel descent is the pullback compositor of its invariant pairing map.
No Frobenius isomorphism is chosen.
Source: the induced Weil structure (blueprint: sk-cor-plancherel). -/
@[irreducible] def kernelDatum (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj l))) :
    (CondensedRing.StrictWeilCondensed.action (Profinite.padicAlgClRingObj l)
      (productFrobenius D r)).obj
      ((DerivedCategory.singleFunctor _ 0).obj (kernel D r l ψ)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (kernel D r l ψ) :=
  invariantSingleDatum (Profinite.padicAlgClRingObj l) (productFrobenius D r)
    (kernel D r l ψ)
    (invariantSheafDatum (Profinite.padicAlgClRingObj l) (productFrobenius D r)
      (pairingMap D r) (pairingMap_invariant D r)
      (letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
       condensedArtinSchreierSheaf (Profinite.padicAlgClRingObj l) D.k₀ ψ))

/-- The published affine transform has exactly the displayed six-operation composite.
This equality supplies the canonical comparison without unfolding large derived functors
while elaborating the Weil datum.
Source: def-fd-transform, defining formula (blueprint: sk-cor-plancherel).
Proof: unfold transform, condensedAffineFourierTransform and condensedFourierTransform.
Unfold condensedFourierKernel, condensedArtinSchreierSheafOf, kernel and pairingMap.
The finite-field instance and the product's arithmetic structure are the same on both
sides; the shift is the cardinality of the specified coordinate type. The two functors
are then definitionally identical, including all six-operation comparison data. -/
theorem transform_factorization
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj l))) :
    transform D r l ψ =
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (pullback.fst (projection D r) (projection D r))).leftDerivedFunctor ⋙
        tensorRight ((DerivedCategory.singleFunctor _ 0).obj (kernel D r l ψ)) ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification
          (Profinite.padicAlgClRingObj l) (compactification D r) ⋙
        shiftFunctor _ (Fintype.card (ULift.{u} (Fin r)) : ℤ) := by
  sorry

set_option maxHeartbeats 1600000 in
-- The derived-category tensor/exchange comparison needs additional elaboration heartbeats.
/-- Canonical Frobenius exchange for the published affine Fourier transform.
Every map is prescribed: shift, proper/open exchange, monoidal pullback, the first
projection's commuting square, and the arithmetic-kernel descent.
Source: the induced Weil structure (blueprint: sk-cor-plancherel). -/
@[irreducible] def frobeniusComponent
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj l)))
    (K : category D r l) :
    (CondensedRing.StrictWeilCondensed.action (Profinite.padicAlgClRingObj l)
      (frobenius D r)).obj ((transform D r l ψ).obj K) ≅
    (transform D r l ψ).obj ((CondensedRing.StrictWeilCondensed.action
      (Profinite.padicAlgClRingObj l) (frobenius D r)).obj K) := by
  let e := eqToIso (transform_factorization D r l ψ)
  let s := compactificationSquare D r
  letI : IsIso s.middle := inferInstanceAs
    (IsIso (D.geometricFrobenius (middle D r)).hom)
  exact (CondensedRing.StrictWeilCondensed.action
      (Profinite.padicAlgClRingObj l) (frobenius D r)).mapIso (e.app K) ≪≫
    fourierExchangeComponent (Profinite.padicAlgClRingObj l)
    (frobenius D r) (productFrobenius D r)
    (pullback.fst (projection D r) (projection D r))
    (pullback.snd (projection D r) (projection D r)) (compactification D r)
    (frobeniusSquares D r).1 (frobeniusSquares D r).2.1 s
    ((DerivedCategory.singleFunctor _ 0).obj (kernel D r l ψ)) (kernelDatum D r l ψ)
    (Fintype.card (ULift.{u} (Fin r)) : ℤ) K ≪≫
    (e.app ((CondensedRing.StrictWeilCondensed.action
      (Profinite.padicAlgClRingObj l) (frobenius D r)).obj K)).symm

/-- Rank-one affine space supplies the curve instances; these are not assumptions
in any rank. Source: the line-growth clause (blueprint: sk-cor-plancherel).
Proof: affine space in one coordinate is smooth of relative dimension one and
geometrically connected. Substitute r = 1 and apply the standard affine-space
smoothness and geometric-connectedness instances. -/
theorem curveInstances (hr : r = 1) :
    SmoothOfRelativeDimension 1 (model D r).hom ∧
      GeometricallyConnected (model D r).hom := by
  subst r
  constructor
  · simpa [model] using
      AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin 1)) (Spec (.of D.k₀))
  · change GeometricallyConnected
      (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
    infer_instance

end RankRAffine

/-- Pull the specified Weil datum through a commuting square, using only the canonical
exact/derived pullback and composition comparisons.
Source: induced Weil structures in sk-cor-plancherel (blueprint: sk-cor-plancherel). -/
def pullWeilDatum
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (gX : X ≅ X) (gY : Y ≅ Y) (f : X ⟶ Y)
    (sq : CommSq gX.hom f f gY.hom)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (φ : (CondensedRing.StrictWeilCondensed.action Λ gY).obj K ≅ K) :
    (CondensedRing.StrictWeilCondensed.action Λ gX).obj
      ((CondensedRing.upperStar Λ f).leftDerivedFunctor.obj K) ≅
        (CondensedRing.upperStar Λ f).leftDerivedFunctor.obj K :=
  (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ gX.hom).symm.app _ ≪≫
    (CondensedRing.pullbackSquareComparison Λ sq).symm.app K ≪≫
    (CondensedRing.upperStar Λ f).leftDerivedFunctor.mapIso
      ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ gY.hom).app K ≪≫ φ)

/-- The actual affine transform applied between the two canonical coordinate pullbacks.
Source: FTψ K on V = V₀ × k (blueprint: sk-cor-plancherel). -/
@[irreducible] def condensedAffineFourierCarrier
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (r : ℕ)
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj l)))
    (K : CondensedRing.StrictWeilCondensed.Complex
      (Profinite.padicAlgClRingObj l) (D.geometricFrobenius (RankRAffine.model D r))) :=
  (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
    (RankRAffine.coordinates D r).hom).leftDerivedFunctor.obj
      ((RankRAffine.transform D r l ψ).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (RankRAffine.coordinates D r).inv).leftDerivedFunctor.obj K.obj.a.obj))

/-- Fourier preserves the recorded bounded-constructible finite-Tor subcategory.
Source: def-fd-transform and sk-cor-plancherel's bounded constructible setting
(blueprint: sk-cor-plancherel).
Proof: the first projection preserves constructibility and finite Tor amplitude under
pullback. The character kernel is a lisse line, so tensoring preserves both properties.
The separated finite-type compact-support functor preserves constructibility. Over
Qbar_l bounded constructible complexes have finite Tor amplitude. The rank shift and
coordinate equivalences preserve these properties. -/
theorem condensedAffineFourier_mem
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p) (r : ℕ)
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj l)))
    (K : CondensedRing.StrictWeilCondensed.Complex
      (Profinite.padicAlgClRingObj l) (D.geometricFrobenius (RankRAffine.model D r))) :
    (constantModelBoundedConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber (RankRAffine.model D r)).left ⊓ fun L ↦
        DerivedCategory.finiteTorAmplitude _ L) (condensedAffineFourierCarrier D l r ψ K) := by
  sorry

/-- The induced Weil structure on the actual Fourier carrier: transport K.str to
literal coordinates, apply the prescribed Fourier Frobenius exchange, then transport
back. Source: induced Weil structures (blueprint: sk-cor-plancherel). -/
@[irreducible] def condensedAffineFourierDatum
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (r : ℕ)
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj l)))
    (K : CondensedRing.StrictWeilCondensed.Complex
      (Profinite.padicAlgClRingObj l) (D.geometricFrobenius (RankRAffine.model D r))) :
    (CondensedRing.StrictWeilCondensed.action (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius (RankRAffine.model D r))).obj
        (condensedAffineFourierCarrier D l r ψ K) ≅ condensedAffineFourierCarrier D l r ψ K := by
  unfold condensedAffineFourierCarrier
  let e := RankRAffine.coordinates D r
  let g := D.geometricFrobenius (RankRAffine.model D r)
  let g' := RankRAffine.frobenius D r
  let Λ := Profinite.padicAlgClRingObj l
  let J := (CondensedRing.upperStar Λ e.inv).leftDerivedFunctor.obj K.obj.a.obj
  let φ := pullWeilDatum Λ g' g e.inv (⟨by simp [g', RankRAffine.frobenius, e, g]⟩)
    K.obj.a.obj ((ObjectProperty.ι _).mapIso K.str)
  exact pullWeilDatum Λ g g' e.hom (⟨by simp [g', RankRAffine.frobenius, e, g]⟩)
    ((RankRAffine.transform D r l ψ).obj J)
    (RankRAffine.frobeniusComponent D r l ψ J ≪≫
      (RankRAffine.transform D r l ψ).mapIso φ)

/-- Tensoring with the actual negative Tate line remains in the recorded Dctf.
Source: Complement and the signed Tate convention (blueprint: sk-cor-plancherel).
Proof: the negative Tate sheaf is a lisse rank-one module, including exponent zero.
Tensoring a finite scalar local model with this line preserves constructibility,
and its Tor amplitude is zero. The finite Tor interval of K is therefore preserved. -/
theorem condensedTateTwist_mem
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (r : ℕ) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (K : CondensedRing.StrictWeilCondensed.Complex
      (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀)) :
    (constantModelBoundedConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left ⊓ fun L ↦ DerivedCategory.finiteTorAmplitude _ L)
      (K.obj.a.obj ⊗
        (CondensedRing.StrictWeilCondensed.derivedTateLine l
          (AlgebraicGeometry.ProEtale.PurityTransport.Coefficient.closure)
          (D.geometricFiber X₀).left (-(r : ℤ)))) := by
  let X := (D.geometricFiber X₀).left
  let Λ := Profinite.padicAlgClRingObj l
  letI : LocallyOfFiniteType (D.geometricFiber X₀).hom := by
    dsimp [FiniteFieldDatum.geometricFiber]
    infer_instance
  letI : QuasiCompact (D.geometricFiber X₀).hom := by
    dsimp [FiniteFieldDatum.geometricFiber]
    infer_instance
  letI : Fact (ringChar D.k ≠ l) := ⟨by
    intro h
    apply (PurityTransport.primeUnit D l hl).ne_zero
    simpa only [h] using (CharP.cast_eq_zero D.k (ringChar D.k))⟩
  letI : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦ by
    simpa [X] using ((PurityTransport.primeUnit D l hl).map
      (((D.geometricFiber X₀).left ↘ Spec (.of D.k)).residueFieldAlgebraMap x)).invertible
  have hc := (adicConstructibilityPredicateComparison l X Λ .algebraicClosure).2
  have hL := (CondensedRing.StrictWeilCondensed.tate_mem l
    PurityTransport.Coefficient.closure X (-(r : ℤ))).1
  have hK := K.obj.a.property.1
  letI hm : (boundedConstructible (condensedRingObj Λ X)).IsMonoidal :=
    CondensedRing.isMonoidal_boundedConstructible l (D.geometricFiber X₀)
  have hb : constantModelBoundedConstructible Λ X
      (K.obj.a.obj ⊗ CondensedRing.StrictWeilCondensed.derivedTateLine l
        PurityTransport.Coefficient.closure X (-(r : ℤ))) := by
    apply (congrFun hc _).mp
    exact ObjectProperty.prop_tensor ((congrFun hc _).mpr hK) ((congrFun hc _).mpr hL)
  exact (congrFun (integral_ctf_equals_bc l X (Mon.mk Λ)
    (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩)))).2.2.2 _).mpr hb

/-- The actual K(-r), with tensor datum from K.str and the normalized negative Tate line.
Source: Complement (blueprint: sk-cor-plancherel). -/
noncomputable def condensedTateTwist
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (r : ℕ) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (K : CondensedRing.StrictWeilCondensed.Complex
      (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀)) :
    CondensedRing.StrictWeilCondensed.Complex
      (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀) := by
  let g := D.geometricFrobenius X₀
  letI : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) := fun x ↦ by
    simpa using ((AlgebraicGeometry.ProEtale.PurityTransport.primeUnit D l hl).map
      (((D.geometricFiber X₀).left ↘ Spec (.of D.k)).residueFieldAlgebraMap x)).invertible
  let U := K.obj.a.obj ⊗
    (CondensedRing.StrictWeilCondensed.derivedTateLine l
      (AlgebraicGeometry.ProEtale.PurityTransport.Coefficient.closure)
      (D.geometricFiber X₀).left (-(r : ℤ)))
  let φ := CondensedRing.StrictWeilCondensed.tensorDatum
    (Profinite.padicAlgClRingObj l) g ((ObjectProperty.ι _).mapIso K.str)
    (CondensedRing.StrictWeilCondensed.tateDatum l
      (AlgebraicGeometry.ProEtale.PurityTransport.Coefficient.closure)
      g (r := -(r : ℤ)))
  exact CategoryTheory.Endofunctor.IsoAlgebra.mk ⟨U,
    condensedTateTwist_mem D l hl r X₀ K⟩ (ObjectProperty.isoMk _ φ)

/-- The Fourier output has the published transform as carrier and its canonical
induced Weil structure as datum. No functor or isomorphism is chosen.
Source: FTψ K (blueprint: sk-cor-plancherel). -/
def condensedAffineFourierOutput
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p) (r : ℕ)
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj l)))
    (K : CondensedRing.StrictWeilCondensed.Complex
      (Profinite.padicAlgClRingObj l) (D.geometricFrobenius (RankRAffine.model D r))) :
    CondensedRing.StrictWeilCondensed.Complex
      (Profinite.padicAlgClRingObj l) (D.geometricFrobenius (RankRAffine.model D r)) :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk
    ⟨condensedAffineFourierCarrier D l r ψ K, condensedAffineFourier_mem D l hl r ψ K⟩
    (ObjectProperty.isoMk _ (condensedAffineFourierDatum D l r ψ K))

/-- The line-growth clause, including its finite-value qualification. The curve
instances follow from the standard affine model only when r = 1.
Source: growth consequence (blueprint: sk-cor-plancherel). -/
def condensedRankRGrowthClause
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p) (r : ℕ)
    (ι : PadicAlgCl l →+* ℂ)
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj l)))
    (K : CondensedRing.StrictWeilCondensed.Complex
      (Profinite.padicAlgClRingObj l) (D.geometricFrobenius (RankRAffine.model D r))) : Prop :=
  ∀ hr : r = 1,
    let hc := RankRAffine.curveInstances D r hr
    letI : SmoothOfRelativeDimension 1 (RankRAffine.model D r).hom := hc.1
    letI : GeometricallyConnected (RankRAffine.model D r).hom := hc.2
    ((condensedGrowthParameter D l (RankRAffine.model D r) hl ι
        (condensedAffineFourierOutput D l hl r ψ K) ≠ ⊤ ∧
      condensedGrowthParameter D l (RankRAffine.model D r) hl ι
        (condensedAffineFourierOutput D l hl r ψ K) ≠ ⊥) ∧
     (condensedGrowthParameter D l (RankRAffine.model D r) hl ι K ≠ ⊤ ∧
      condensedGrowthParameter D l (RankRAffine.model D r) hl ι K ≠ ⊥)) →
    condensedGrowthParameter D l (RankRAffine.model D r) hl ι
        (condensedAffineFourierOutput D l hl r ψ K) =
      condensedGrowthParameter D l (RankRAffine.model D r) hl ι K + 1

/-- Apply the actual Fourier output twice, first with ψ and then with ψ⁻¹.
Source: Complement (blueprint: sk-cor-plancherel). -/
def condensedInverseAffineFourierOutput
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p) (r : ℕ)
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj l)))
    (K : CondensedRing.StrictWeilCondensed.Complex
      (Profinite.padicAlgClRingObj l) (D.geometricFrobenius (RankRAffine.model D r))) :
    CondensedRing.StrictWeilCondensed.Complex
      (Profinite.padicAlgClRingObj l) (D.geometricFrobenius (RankRAffine.model D r)) :=
  condensedAffineFourierOutput D l hl r ψ⁻¹ (condensedAffineFourierOutput D l hl r ψ K)

/-- Trace of the actual rank-r Tate-twisted strict pair, with geometric-Frobenius
normalization supplied by `condensedTateTwist`.
Source: Complement (blueprint: sk-cor-plancherel). -/
def condensedTateTwistTrace
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (r : ℕ)
    (K : CondensedRing.StrictWeilCondensed.Complex
      (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀))
    (n : ℕ) (hn : 1 ≤ n) (z : D.extensionPoints X₀ n hn) : PadicAlgCl l :=
  condensedStrictTrace D l X₀ (condensedTateTwist D l hl r X₀ K) n hn z

/-- Rank-r condensed Plancherel, its finite line-growth consequence, and the
inverse-character trace normalization, with actual Fourier outputs and actual K(-r).
Source: latest blueprint, part-weights-riemann-hypothesis/sec-fourier-transform/
sec-trace-functions-and-plancherel/sk-cor-plancherel/_section.md and the accepted
rank-r Complement correction (blueprint: sk-cor-plancherel).

Proof, following the node's eight steps.
1. Put M = p₁*K tensor Kψ and B = Rp₂!M. Restricted pullback, tensor and compact
support preserve the constructible domains. The character kernel is a lisse line.
For a rational y with closed image y₀ of degree d dividing n, use
lem-zl-iterate-local-trace-choice-independence and
lem-fd-condensed-weil-fibre-equivariance: the stalk of B is the compact cohomology
of the y₀-fibre and the isomorphism intertwines the closed-point operator and its
n/d power. Thus its alternating trace is t_B,n(y).
2. Apply lem-fd-condensed-model-frobenius-operators to the fibre and its restricted
strict pair. It constructs the model Frobenius before cohomology and identifies
its global and local iterates. thm-trf-frobenius-fixed-points identifies its finite
fixed-point scheme, indexed by the pairs (x,y) over F_(q^n). The constructible
point-supertrace bridge lem-fd-condensed-point-supertrace supplies right duals,
finite-dimensional cohomology and categorical-to-alternating traces.
3. Apply nt-assume-trace-formula over the residue field of y₀ with exponent n/d.
The separated finite-type fibre, finite fixed points and right duals have just
been checked independently. The two operator bridges identify its left side with
t_B,n(y), and its summands with t_M,n(x,y). No trace formula is inferred from the
stalk comparison: the assumption is applied here.
4. sk-lem-as-properties gives the kernel scalar ψ(Tr <x,y>). Trace linearity
sk-p-trace and the finite alternating-degree sum give the integrand trace. Shift
by r contributes (-1)^r. This yields exactly the setting's finite Fourier
formula (18.3), with the induced Weil structure used in the definitions above.
5. Character values are p-th roots of unity, so their complex absolute values are
one, and conjugation equals inversion. The character law identifies inversion
with negation of the argument.
6. For x=z the orthogonality sum is q^(nr). Otherwise choose a nonzero coordinate
of x-z. sk-lem-orthogonality gives zero for the scalar trace-character sum, hence
a translation with character value different from one. Translating the rank-r
sum forces it to vanish. For r=0 only the diagonal case exists. Expand the square
in (18.3), interchange finite sums and use this orthogonality. The two rank-shift
signs cancel, leaving the asserted energy identity.
7. At r=1, sk-def-wrp-l2-definition gives the extended-real logarithmic limsup.
Our q>1 and ell different from p supply its conventions. Positive energies obey
log_q(q^n S_n)=n+log_q S_n; zero energies give minus infinity on both sides.
Division by n and then the limsup therefore translate by one; translation
commutes with tail suprema and their infimum. Subtract one as in the definition,
yielding the growth equality whenever both parameters are finite.
8. The inverse character is nontrivial. Apply (18.3) twice with ψ and ψ⁻¹. The
signs cancel and the same orthogonality leaves q^(nr) times the original trace.
The specified negative Tate line has geometric Frobenius scalar q^r, hence
q^(nr) after n returns. Trace linearity and the alternating-degree formula give
the trace of the actual tensor pair K(-r), proving both Complement equalities. -/
theorem condensedRankRPlancherel
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p) (r : ℕ)
    (ι : PadicAlgCl l →+* ℂ)
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj l))) (hψ : ψ ≠ 1)
    (K : CondensedRing.StrictWeilCondensed.Complex
      (Profinite.padicAlgClRingObj l) (D.geometricFrobenius (RankRAffine.model D r))) :
    (∀ (n : ℕ) (hn : 1 ≤ n),
      affineExtensionTraceEnergy D l (RankRAffine.model D r) ι
          (condensedStrictTrace D l (RankRAffine.model D r)
            (condensedAffineFourierOutput D l hl r ψ K)) n hn =
        (D.q : ℝ) ^ (n * r) * affineExtensionTraceEnergy D l (RankRAffine.model D r) ι
          (condensedStrictTrace D l (RankRAffine.model D r) K) n hn) ∧
    condensedRankRGrowthClause D l hl r ι ψ K ∧
    (∀ (n : ℕ) (hn : 1 ≤ n) (z : D.extensionPoints (RankRAffine.model D r) n hn),
      condensedStrictTrace D l (RankRAffine.model D r)
          (condensedInverseAffineFourierOutput D l hl r ψ K) n hn z =
        (D.q : PadicAlgCl l) ^ (n * r) *
          condensedStrictTrace D l (RankRAffine.model D r) K n hn z ∧
      condensedStrictTrace D l (RankRAffine.model D r)
          (condensedInverseAffineFourierOutput D l hl r ψ K) n hn z =
        condensedTateTwistTrace D l hl (RankRAffine.model D r) r K n hn z) := by
  sorry

end WeilConjectures.NativeL2
