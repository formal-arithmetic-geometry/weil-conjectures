/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.AlgebraicGeometry.GaloisLisseRepresentations
public import WeilConjectures.AlgebraicGeometry.StratifiedLattice
public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.RepresentationTheory.LAdic
public import WeilConjectures.AlgebraicGeometry.RegularNormalDecomposition
public import WeilConjectures.AlgebraicGeometry.ProEtaleLisseOrigin
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyConstantSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
public import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModels
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Point.Over
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import WeilConjectures.AlgebraicGeometry.ProEtaleOriginFromFiniteModels
public import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonLocalization
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.AlgebraicGeometry.ProEtaleEtaleFiniteModels
public import WeilConjectures.AlgebraicGeometry.ProEtaleModelTypePartition
public import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
public import WeilConjectures.AlgebraicGeometry.ProEtaleUniformModelEtaleCover
public import Mathlib.CategoryTheory.Sites.SheafHom
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalContinuity
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.Precoverage.Generates
public import Mathlib.CategoryTheory.Sites.Finite
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Data.Finite.Prod
public import WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.SiteConstantModuleIsomSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantSheafStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FLCFiber
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.CategoryTheory.RingObjects.GlobalSections

/-! # Lisse sheaves and continuous representations

Source: latest blueprint, sec-six-functors/sk-lem-finite,
thm-lisse-qlbar-representations, clauses (1)--(5)
(blueprint: thm-lisse-qlbar-representations).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct CategoryTheory.Obj
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale
namespace LisseQlbar

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The actual fibre: pull back to the geometric point, then evaluate sections.
Source: blueprint, Fibres (blueprint: thm-lisse-qlbar-representations). -/
abbrev fibre {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ X) :=
  CondensedRing.upperStar Λ x ⋙
    CondensedRing.Evaluation.sections (Scheme.ProEt.topology (Spec (.of Ω)))
      (condensedRingObj Λ (Spec (.of Ω))) (Scheme.ProEt.mk (𝟙 _))

/-- Sections of the ordinary inverse image of an abelian sheaf.
Source: blueprint, Fibres (blueprint: thm-lisse-qlbar-representations). -/
abbrev abFibre {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ X) :=
  ProEtale.upperStar Ab.{u + 1} x ⋙
    (sheafSections (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1}).obj
      (op (Scheme.ProEt.mk (𝟙 _)))

/-- The canonical underlying-sheaf identification for the module fibre. Scalar
extension along the invertible coefficient pullback map is restriction along its inverse.
Source: blueprint, Fibres (blueprint: thm-lisse-qlbar-representations). -/
@[irreducible] def fibreUnderlyingIso {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ X)
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    AddCommGrpCat.of ((fibre Λ x).obj L) ≅ (abFibre x).obj L.X :=
  ((sheafSections (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1}).obj
    (op (Scheme.ProEt.mk (𝟙 _)))).mapIso
      ((Mod.forget _).mapIso ((Mod.extendScalarsIsoComapInv
        (condensedPullbackHom Λ x)).app
          (((ProEtale.upperStar Ab.{u + 1} x).mapMod (condensedRingObj Λ X)).obj L)))

/-- Canonical comparison from the pro-etale fibre of an etale abelian sheaf to
its usual geometric stalk: commute inverse images, invert the comparison unit,
and take the germ of a section on the geometric point.
Source: blueprint, Fibres (blueprint: thm-lisse-qlbar-representations). -/
@[irreducible] def finiteFibreMap {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) :
    (abFibre x).obj ((comparisonUpperStar Ab.{u + 1} X).obj F) ⟶
      (Scheme.pointSmallEtale x).sheafFiber.obj F :=
  ((sheafSections (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1}).obj
    (op (Scheme.ProEt.mk (𝟙 _)))).map
      ((comparisonCoefficientPullbackIso Ab.{u + 1} x).inv.app F) ≫
  (inv ((comparisonAdjunction Ab.{u + 1} (Spec (.of Ω))).unit.app
    ((Etale.upperStar Ab.{u + 1} x).obj F))).hom.app
      (op (Scheme.Etale.mk (𝟙 _))) ≫
  (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
    (Scheme.Etale.mk (𝟙 _)) (Over.homMk (𝟙 _) (by simp))
    ((Etale.upperStar Ab.{u + 1} x).obj F).obj ≫
  (Etale.upperStarCompSheafFiberIso Ab.{u + 1} x (𝟙 _)).hom.app F ≫
  eqToHom (congrArg (fun z ↦ (Scheme.pointSmallEtale z).sheafFiber.obj F)
    (Category.id_comp x))

/-- The lattice condition uses the given inclusion and its scalar-extension adjoint.
Source: blueprint, introductory lattice definition
(blueprint: thm-lisse-qlbar-representations). -/
def hasLattice
    (B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj B] [IsCommMonObj B]
    (a : Λ ⟶ B) [IsMonHom a] (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X)) : Prop :=
  ∃ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
    CondensedRing.LocallyFree (condensedRingObj Λ X) M ∧
    ∃ i : M ⟶ (Mod.comap (coefficientMap a X)).obj L,
      Mono i ∧ IsIso (((Mod.extendRestrictAdjunction (coefficientMap a X)).homEquiv M L).symm i)

/-- Constant scalars in a continuous condensed coefficient ring, at the point.
Source: blueprint, coefficient convention
(blueprint: thm-lisse-qlbar-representations). -/
def continuousScalar (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (a : R) : condensedScalarRing (Profinite.continuousMapRingObj.{u} R) :=
  ULift.up (ContinuousMap.const (⊤_ Profinite.{u}) a)

set_option maxHeartbeats 0 in
-- Large clause records contain canonical sheaf, fibre and coefficient comparison types.
set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- An equivalence onto precisely the prescribed representations, with its actual
linear geometric fibre. Fullness and faithfulness and the essential-image equality
are the usual equivalence with that full subcategory.
Source: blueprint, clauses (1)--(3)
(blueprint: thm-lisse-qlbar-representations). -/
structure FibreEquivalence (R : Type) [CommRing R]
    (scalar : R → condensedScalarRing Λ) {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ X) (G : Type v) [Group G]
    (P : ObjectProperty
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (Q : ObjectProperty (Rep.{u + 1} R G)) where
  functor : P.FullSubcategory ⥤ Rep.{u + 1} R G
  full : functor.Full
  faithful : functor.Faithful
  image : ∀ V : Rep.{u + 1} R G,
    (∃ L : P.FullSubcategory, Nonempty (functor.obj L ≅ V)) ↔ Q V
  comparison : functor ⋙ forget₂ (Rep.{u + 1} R G) (ModuleCat.{u + 1} R) ⋙
      forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1} ≅
    P.ι ⋙ fibre Λ x ⋙ forget₂ _ Ab.{u + 1}
  linear : ∀ (L : P.FullSubcategory) (a : R) (v : (functor.obj L).V),
    comparison.hom.app L (a • v) =
      @id ((fibre Λ x).obj L.obj)
        (CondensedRing.affineScalarSection Λ (Spec (.of Ω)) (scalar a) •
          @id ((fibre Λ x).obj L.obj) (comparison.hom.app L v))

/-- The map on actual fibres induced by any morphism of underlying sheaves,
including an inclusion across two coefficient rings.
Source: blueprint, clauses (1)--(3) (blueprint: thm-lisse-qlbar-representations). -/
@[irreducible] def fibreMap
    (B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj B] [IsCommMonObj B]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ X)
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X))
    (f : L.X ⟶ M.X) :
    AddCommGrpCat.of ((fibre Λ x).obj L) ⟶ AddCommGrpCat.of ((fibre B x).obj M) :=
  (fibreUnderlyingIso Λ x L).hom ≫ (abFibre x).map f ≫
    (fibreUnderlyingIso B x M).inv

/-- Constant scalars as morphisms from the tensor unit, using the constant-sheaf
adjunction. Source: blueprint, Fibres (blueprint: thm-lisse-qlbar-representations). -/
@[irreducible] def constantSection (r : condensedScalarRing Λ) :
    𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ :=
  ((constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    terminalIsTerminal).homEquiv (𝟙_ Ab.{u + 1}) Λ).symm
      (AddCommGrpCat.ofHom
        (((AddMonoidHom.mulRight r).comp (Int.castAddHom (condensedScalarRing Λ))).comp
          AddEquiv.ulift.toAddMonoidHom))

/-- Multiplication by the specified ordinary scalar on an internal module.
Source: blueprint, reductions in (1) (blueprint: thm-lisse-qlbar-representations). -/
@[irreducible] def scalarEnd (X : Scheme.{u}) (r : condensedScalarRing Λ)
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    L.X ⟶ L.X :=
  (λ_ L.X).inv ≫
    ((Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫
      (upperStarFromPoint X).map (constantSection Λ r)) ▷ L.X) ≫
    ModObj.smul (M := condensedRingObj Λ X) (X := L.X)

/-- Canonical tensor pairing on geometric fibres, before passing from the
integer tensor product to the balanced coefficient tensor product.
Source: blueprint, tensor compatibility (blueprint: thm-lisse-qlbar-representations). -/
@[irreducible] def tensorPair {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ X)
    (L M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (v : (fibre Λ x).obj L) (w : (fibre Λ x).obj M) :
    (fibre Λ x).obj (L ⊗ M) :=
  let U := op (Scheme.ProEt.mk (𝟙 (Spec (.of Ω))))
  let ev₀ := (evaluation (Spec (.of Ω)).ProEtᵒᵖ Ab.{u + 1}).obj U
  letI : ev₀.Monoidal := Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _, μIso _ _ := Iso.refl _ }
  let ev := sheafToPresheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1} ⋙ ev₀
  let pb := ProEtale.upperStar Ab.{u + 1} x
  (fibreUnderlyingIso Λ x (L ⊗ M)).inv
    (ev.map (pb.map (Mod.tensorObjπ L M))
      (ev.map (Functor.LaxMonoidal.μ pb L.X M.X)
        (Functor.LaxMonoidal.μ ev (pb.obj L.X) (pb.obj M.X)
          ((fibreUnderlyingIso Λ x L).hom v ⊗ₜ[ℤ]
            (fibreUnderlyingIso Λ x M).hom w))))

set_option maxHeartbeats 0 in
-- Large clause records contain canonical sheaf, fibre and coefficient comparison types.
set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- Tensor and unit compatibility on the actual fibre. The pure-tensor formula
fixes the comparison, hence its associativity, symmetry and unit coherence.
Source: blueprint, tensor compatibility (blueprint: thm-lisse-qlbar-representations). -/
structure TensorCompatibility (R : Type) [CommRing R]
    (scalar : R → condensedScalarRing Λ) {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ X) (G : Type v) [Group G]
    (P : ObjectProperty
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (Q : ObjectProperty (Rep.{u + 1} R G))
    (e : FibreEquivalence Λ R scalar x G P Q) where
  closed : ∀ L M : P.FullSubcategory, P (L.obj ⊗ M.obj)
  unit : P (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
  unitTrivial : Nonempty (e.functor.obj ⟨_, unit⟩ ≅ Rep.trivial R G (ULift.{u + 1} R))
  tensor : ∀ L M : P.FullSubcategory,
    ∃ t : ((e.functor.obj L).V ⊗[R] (e.functor.obj M).V) ≃ₗ[R]
        (e.functor.obj ⟨L.obj ⊗ M.obj, closed L M⟩).V,
      (∀ v w, e.comparison.hom.app ⟨_, closed L M⟩ (t (v ⊗ₜ[R] w)) =
        tensorPair Λ x L.obj M.obj (e.comparison.hom.app L v)
          (e.comparison.hom.app M w)) ∧
      ∀ g v w, t ((e.functor.obj L).ρ g v ⊗ₜ[R] (e.functor.obj M).ρ g w) =
        (e.functor.obj ⟨_, closed L M⟩).ρ g (t (v ⊗ₜ[R] w))

set_option maxHeartbeats 0 in
-- Large clause records contain canonical sheaf, fibre and coefficient comparison types.
set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- Scalar extension is characterized by the actual inclusion on geometric fibres.
The requirement applies to every scalar-extension presentation, so in particular
it asserts independence of the chosen lattice and of the finite-field model.
Source: blueprint, (2), (3) and scalar compatibility
(blueprint: thm-lisse-qlbar-representations). -/
structure ScalarCompatibility
    (B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj B] [IsCommMonObj B]
    (a : Λ ⟶ B) [IsMonHom a]
    (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    (sR : R → condensedScalarRing Λ) (sS : S → condensedScalarRing B)
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ X)
    (G : Type v) [Group G]
    (P : ObjectProperty
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (Q : ObjectProperty (Rep.{u + 1} R G))
    (P' : ObjectProperty
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X)))
    (Q' : ObjectProperty (Rep.{u + 1} S G))
    (e : FibreEquivalence Λ R sR x G P Q)
    (e' : FibreEquivalence B S sS x G P' Q') where
  closed : ∀ L : P.FullSubcategory, P' ((Mod.extendScalars (coefficientMap a X)).obj L.obj)
  comparison : ∀ (L : P.FullSubcategory) (M : P'.FullSubcategory)
    (i : L.obj ⟶ (Mod.comap (coefficientMap a X)).obj M.obj),
    IsIso (((Mod.extendRestrictAdjunction (coefficientMap a X)).homEquiv L.obj M.obj).symm i) →
    ∃ t : (S ⊗[R] (e.functor.obj L).V) ≃ₗ[S] (e'.functor.obj M).V,
      (∀ b v, e'.comparison.hom.app M (t (b ⊗ₜ[R] v)) =
        @id ((fibre B x).obj M.obj)
          (CondensedRing.affineScalarSection B (Spec (.of Ω)) (sS b) •
            @id ((fibre B x).obj M.obj)
              (fibreMap Λ B x L.obj M.obj i.hom (e.comparison.hom.app L v)))) ∧
      ∀ g b v, t (b ⊗ₜ[R] (e.functor.obj L).ρ g v) =
        (e'.functor.obj M).ρ g (t (b ⊗ₜ[R] v))

variable (l : ℕ) [Fact l.Prime]

/-- The condensed finite-extension coefficient, with the inherited absolute-value
 topology. Source: blueprint, coefficient convention
(blueprint: thm-lisse-qlbar-representations). -/
abbrev fieldRing (E : PadicAlgCl.FiniteIntermediateField l) :=
  letI := PadicAlgCl.normedFieldOfAlgebra l E
  Profinite.continuousMapRingObj.{u} E

/-- The recorded integer ring with its induced topology, condensed by continuous
functions. Source: blueprint, coefficient convention
(blueprint: thm-lisse-qlbar-representations). -/
abbrev integerRing (E : PadicAlgCl.FiniteIntermediateField l) :=
  letI := PadicAlgCl.normedFieldOfAlgebra l E
  Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers l E)

/-- Canonical integral-to-rational coefficient inclusion.
Source: blueprint, lattices (blueprint: thm-lisse-qlbar-representations). -/
abbrev integerInclusion (E : PadicAlgCl.FiniteIntermediateField l) :
    integerRing.{u} l E ⟶ fieldRing l E :=
  letI := PadicAlgCl.normedFieldOfAlgebra l E
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMap
        (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val)

/-- Integral lisse finite-extension modules, with a monic lattice and its actual
localization isomorphism. Source: blueprint, (2)
(blueprint: thm-lisse-qlbar-representations). -/
def integralField (E : PadicAlgCl.FiniteIntermediateField l) (X : Scheme.{u}) :
    ObjectProperty
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj (fieldRing l E) X)) :=
  fun L ↦ CondensedRing.LocallyFree (condensedRingObj (fieldRing l E) X) L ∧
    hasLattice (integerRing l E) (fieldRing l E) (integerInclusion l E) X L

/-- Integral algebraic-closure modules are precisely the scalar extensions of
integral lisse finite-extension models. Source: blueprint, (3)
(blueprint: thm-lisse-qlbar-representations). -/
def integralClosure (X : Scheme.{u}) : ObjectProperty
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X)) :=
  fun L ↦ CondensedRing.LocallyFree (condensedRingObj (Profinite.padicAlgClRingObj l) X) L ∧
    ∃ (E : PadicAlgCl.FiniteIntermediateField l)
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (fieldRing l E) X)),
      integralField l E X M ∧
      Nonempty ((Mod.extendScalars (coefficientMap
        (Profinite.padicSubfieldRingObjToPadicAlgCl l E) X)).obj M ≅ L)

/-- Constant finite-extension scalars in the coefficient sheaf.
Source: blueprint, Fibres (blueprint: thm-lisse-qlbar-representations). -/
def fieldScalar (E : PadicAlgCl.FiniteIntermediateField l) (a : E) :
    condensedScalarRing (fieldRing.{u} l E) :=
  letI := PadicAlgCl.normedFieldOfAlgebra l E
  continuousScalar E a

/-- Constant integral scalars in the coefficient sheaf.
Source: blueprint, Fibres (blueprint: thm-lisse-qlbar-representations). -/
def integerScalar (E : PadicAlgCl.FiniteIntermediateField l)
    (a : Padic.coefficientExtensionIntegers l E) :
    condensedScalarRing (integerRing.{u} l E) :=
  letI := PadicAlgCl.normedFieldOfAlgebra l E
  continuousScalar _ a

/-- The full subcategory of continuous finite free integral representations.
Source: blueprint, (1) (blueprint: thm-lisse-qlbar-representations). -/
def integralRep (E : PadicAlgCl.FiniteIntermediateField l) (G : ProfiniteGrp.{u}) :
    ObjectProperty (Rep.{u + 1} (Padic.coefficientExtensionIntegers l E) G) :=
  fun V ↦ Module.Free (Padic.coefficientExtensionIntegers l E) V.V ∧
    Representation.IsContinuousIntegral l E G V.V
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv _ V.V).toMonoidHom.comp
        (Representation.asGroupHom V.ρ))

/-- Continuous finite-dimensional finite-extension representations.
Source: blueprint, (2) (blueprint: thm-lisse-qlbar-representations). -/
def fieldRep (E : PadicAlgCl.FiniteIntermediateField l) (G : ProfiniteGrp.{u}) :
    ObjectProperty (Rep.{u + 1} E G) :=
  fun V ↦ Representation.IsContinuousCoefficient l E G V.V
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv _ V.V).toMonoidHom.comp
      (Representation.asGroupHom V.ρ))

/-- Continuous finite-dimensional algebraic-closure representations with a
finite field of definition, using the recorded stable-subspace definition.
Source: blueprint, (3), (5) (blueprint: thm-lisse-qlbar-representations). -/
def definedRep (G : ProfiniteGrp.{u}) : ObjectProperty (Rep.{u + 1} (PadicAlgCl l) G) :=
  fun V ↦ Representation.IsLAdic l (PadicAlgCl l) G V.V
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv _ V.V).toMonoidHom.comp
      (Representation.asGroupHom V.ρ))

/-- Continuity over the absolute-value topology of the algebraic closure, with
finite dimension. This does not use the finite-subextension condition defining
its condensed coefficient sheaf.
Source: blueprint, (5) (blueprint: thm-lisse-qlbar-representations). -/
def continuousClosureRep (G : ProfiniteGrp.{u}) :
    ObjectProperty (Rep.{u + 1} (PadicAlgCl l) G) :=
  fun V ↦ FiniteDimensional (PadicAlgCl l) V.V ∧
    letI : TopologicalSpace V.V := moduleTopology (PadicAlgCl l) V.V
    Continuous (fun p : G × V.V ↦ V.ρ p.1 p.2)

/-- Forget a fixed-ring etale module sheaf to its abelian sheaf.
Source: blueprint, finite reductions (blueprint: thm-lisse-qlbar-representations). -/
abbrev underlyingAb {X : Scheme.{u}} (R : Type (u + 1)) [Ring R]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1})).obj F

/-- The canonical forgetful comparison for the usual geometric stalk.
Source: blueprint, Fibres (blueprint: thm-lisse-qlbar-representations). -/
@[irreducible] def moduleStalkUnderlyingIso {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (R : Type (u + 1)) [Ring R]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (Scheme.pointSmallEtale x).sheafFiber.obj (underlyingAb R F) ≅
      AddCommGrpCat.of (((Scheme.pointSmallEtale x).sheafFiber
        (A := ModuleCat.{u + 1} R)).obj F) :=
  letI : PreservesFilteredColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  ((Scheme.pointSmallEtale x).sheafFiberCompIso
    (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1})).app F

/-- The reduction map on fibres, ending in exactly the finite Galois representation
of the descended etale sheaf. Every comparison in this definition is canonical.
Source: blueprint, (1) (blueprint: thm-lisse-qlbar-representations). -/
@[irreducible] def reductionOnFibre
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (G : ProfiniteGrp.{u})
    [∀ P, MulAction G ((FiniteEtale.fiber x).obj P)]
    (d : GaloisLisseFiniteCorrespondence x G)
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))
    (R : Type (u + 1)) [Ring R] [Finite R]
    (F : LisseModuleSheafCategory X R)
    (q : L.X ⟶ (comparisonUpperStar Ab.{u + 1} X).obj (underlyingAb R F.obj)) :
    AddCommGrpCat.of ((fibre Λ x).obj L) ⟶
      AddCommGrpCat.of (((d.e R).functor.obj F).obj.V) :=
  (fibreUnderlyingIso Λ x L).hom ≫ (abFibre x).map q ≫
    finiteFibreMap x (underlyingAb R F.obj) ≫
    (moduleStalkUnderlyingIso x R F.obj).hom ≫
    (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1}).map ((d.τ R).inv.app F)

set_option maxHeartbeats 0 in
-- Large clause records contain canonical sheaf, fibre and coefficient comparison types.
set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- A finite reduction is the actual cokernel of multiplication by the chosen
uniformizer power. Its action is normalized by the finite-coefficient equivalence,
using the canonical map from point sections to the etale stalk.
Source: blueprint, (1) (blueprint: thm-lisse-qlbar-representations). -/
structure FiniteReduction
    (A : Type) [CommRing A] (scalar : A → condensedScalarRing Λ)
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (G : ProfiniteGrp.{u})
    [∀ P, MulAction G ((FiniteEtale.fiber x).obj P)]
    (d : GaloisLisseFiniteCorrespondence x G)
    (P : ObjectProperty
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (Q : ObjectProperty (Rep.{u + 1} A G))
    (e : FibreEquivalence Λ A scalar x G P Q) (L : P.FullSubcategory)
    (R : Type (u + 1)) [CommRing R] [Finite R] (qA : A →+* R) (π : A) where
  etale : LisseModuleSheafCategory X R
  quotient : L.obj.X ⟶ (comparisonUpperStar Ab.{u + 1} X).obj (underlyingAb R etale.obj)
  linear : ∀ a : A,
    scalarEnd Λ X (scalar a) L.obj ≫ quotient =
      quotient ≫ (comparisonUpperStar Ab.{u + 1} X).map
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1})).map ((qA a) • (𝟙 etale.obj)))
  zero : scalarEnd Λ X (scalar π) L.obj ≫ quotient = 0
  cokernel : IsColimit (CokernelCofork.ofπ quotient zero)
  equivariant : ∀ g v,
    reductionOnFibre Λ x G d L.obj R etale quotient
        (e.comparison.hom.app L ((e.functor.obj L).ρ g v)) =
      (((d.e R).functor.obj etale).obj.ρ g)
        (reductionOnFibre Λ x G d L.obj R etale quotient (e.comparison.hom.app L v))
  surjective : Function.Surjective (reductionOnFibre Λ x G d L.obj R etale quotient)
  kernel : ∀ v,
    reductionOnFibre Λ x G d L.obj R etale quotient (e.comparison.hom.app L v) = 0 ↔
      ∃ w : (e.functor.obj L).V, v = π • w

/-- Specialize the finite-reduction template to the recorded uniformizer power
and its recorded finite quotient ring, with the canonical quotient homomorphism.
Source: blueprint, (1) (blueprint: thm-lisse-qlbar-representations). -/
abbrev integralFiniteReduction
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (G : ProfiniteGrp.{u})
    [∀ P, MulAction G ((FiniteEtale.fiber x).obj P)]
    (d : GaloisLisseFiniteCorrespondence x G)
    (E : PadicAlgCl.FiniteIntermediateField l)
    (e : FibreEquivalence (integerRing l E) (Padic.coefficientExtensionIntegers l E)
      (integerScalar l E) x G
      (CondensedRing.LocallyFree (condensedRingObj (integerRing l E) X)) (integralRep l E G))
    (L : ObjectProperty.FullSubcategory (CondensedRing.LocallyFree
      (condensedRingObj (integerRing l E) X))) (n : ℕ) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  FiniteReduction (integerRing l E) (Padic.coefficientExtensionIntegers l E)
    (integerScalar l E) x G d
    (CondensedRing.LocallyFree (condensedRingObj (integerRing l E) X)) (integralRep l E G) e L
    (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
    (ULift.ringEquiv.symm.toRingHom.comp
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))))
    ((Padic.coefficientExtensionUniformizer l E) ^ (n + 1))

/-- The finite reductions recover the fibre by their inverse limit. Compatibility
is expressed by common lifts at two successive quotient levels; since these are
surjective normalized quotients, this is precisely the usual transition equation.
Source: blueprint, (1) (blueprint: thm-lisse-qlbar-representations). -/
def ReductionComplete
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (G : ProfiniteGrp.{u})
    [∀ P, MulAction G ((FiniteEtale.fiber x).obj P)]
    (d : GaloisLisseFiniteCorrespondence x G)
    (E : PadicAlgCl.FiniteIntermediateField l)
    (e : FibreEquivalence (integerRing l E) (Padic.coefficientExtensionIntegers l E)
      (integerScalar l E) x G
      (CondensedRing.LocallyFree (condensedRingObj (integerRing l E) X)) (integralRep l E G))
    (L : ObjectProperty.FullSubcategory (CondensedRing.LocallyFree
      (condensedRingObj (integerRing l E) X)))
    (r : ∀ n : ℕ, integralFiniteReduction l x G d E e L n) : Prop :=
  letI (n : ℕ) : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  ∀ t : ∀ n : ℕ, (((d.e _).functor.obj (r n).etale).obj.V),
    (∀ n : ℕ, ∃ v : (fibre (integerRing l E) x).obj L.obj,
      reductionOnFibre (integerRing l E) x G d L.obj _ (r n).etale (r n).quotient v = t n ∧
      reductionOnFibre (integerRing l E) x G d L.obj _
        (r (n + 1)).etale (r (n + 1)).quotient v = t (n + 1)) →
    ∃! v : (fibre (integerRing l E) x).obj L.obj,
      ∀ n : ℕ, reductionOnFibre (integerRing l E) x G d L.obj _ (r n).etale (r n).quotient v = t n

set_option maxHeartbeats 0 in
-- Large clause records contain canonical sheaf, fibre and coefficient comparison types.
set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- The five clauses of the lisse-representation theorem, with a single coherent
choice of all monodromy functors and canonical geometric-fibre comparisons.
Source: blueprint, clauses (1)--(5)
(blueprint: thm-lisse-qlbar-representations). -/
structure Correspondence
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (G : ProfiniteGrp.{u})
    [∀ P, MulAction G ((FiniteEtale.fiber x).obj P)] where
  finite : GaloisLisseFiniteCorrespondence x G
  integral : ∀ E : PadicAlgCl.FiniteIntermediateField l,
    FibreEquivalence (integerRing l E) (Padic.coefficientExtensionIntegers l E)
      (integerScalar l E) x G
      (CondensedRing.LocallyFree (condensedRingObj (integerRing l E) X)) (integralRep l E G)
  rational : ∀ E : PadicAlgCl.FiniteIntermediateField l,
    FibreEquivalence (fieldRing l E) E (fieldScalar l E) x G (integralField l E X) (fieldRep l E G)
  algebraic : FibreEquivalence (Profinite.padicAlgClRingObj l) (PadicAlgCl l)
    (Profinite.PadicAlgCl.constSectionRingHom l (op (⊤_ Profinite.{u}))) x G
    (integralClosure l X) (definedRep l G)
  reductions : ∀ (E : PadicAlgCl.FiniteIntermediateField l)
      (L : ObjectProperty.FullSubcategory (CondensedRing.LocallyFree
        (condensedRingObj (integerRing l E) X))),
    ∃ r : ∀ n : ℕ, integralFiniteReduction l x G finite E (integral E) L n,
      ReductionComplete l x G finite E (integral E) L r
  integralTensor : ∀ E : PadicAlgCl.FiniteIntermediateField l,
    TensorCompatibility (integerRing l E) (Padic.coefficientExtensionIntegers l E)
      (integerScalar l E) x G
      (CondensedRing.LocallyFree (condensedRingObj (integerRing l E) X))
      (integralRep l E G) (integral E)
  rationalTensor : ∀ E : PadicAlgCl.FiniteIntermediateField l,
    TensorCompatibility (fieldRing l E) E (fieldScalar l E) x G
      (integralField l E X) (fieldRep l E G) (rational E)
  algebraicTensor : TensorCompatibility (Profinite.padicAlgClRingObj l) (PadicAlgCl l)
    (Profinite.PadicAlgCl.constSectionRingHom l (op (⊤_ Profinite.{u}))) x G
    (integralClosure l X) (definedRep l G) algebraic
  localization : ∀ E : PadicAlgCl.FiniteIntermediateField l,
    ScalarCompatibility (integerRing l E) (fieldRing l E) (integerInclusion l E)
      (Padic.coefficientExtensionIntegers l E) E (integerScalar l E) (fieldScalar l E) x G
      (CondensedRing.LocallyFree (condensedRingObj (integerRing l E) X))
      (integralRep l E G) (integralField l E X) (fieldRep l E G) (integral E) (rational E)
  algebraicExtension : ∀ E : PadicAlgCl.FiniteIntermediateField l,
    ScalarCompatibility (fieldRing l E) (Profinite.padicAlgClRingObj l)
      (Profinite.padicSubfieldRingObjToPadicAlgCl l E) E (PadicAlgCl l) (fieldScalar l E)
      (Profinite.PadicAlgCl.constSectionRingHom l (op (⊤_ Profinite.{u}))) x G
      (integralField l E X) (fieldRep l E G) (integralClosure l X) (definedRep l G)
      (rational E) algebraic
  fieldExtension : ∀ (E F : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ F),
    letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
    ScalarCompatibility (fieldRing l E) (fieldRing l F) (Profinite.padicSubfieldRingObjMap l h)
      E F (fieldScalar l E) (fieldScalar l F) x G
      (integralField l E X) (fieldRep l E G) (integralField l F X) (fieldRep l F G)
      (rational E) (rational F)
  normalField : (∀ p : X, IsDomain (X.presheaf.stalk p) ∧
      IsIntegrallyClosed (X.presheaf.stalk p)) →
    ∀ (E : PadicAlgCl.FiniteIntermediateField l)
      (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (fieldRing l E) X)),
      CondensedRing.LocallyFree (condensedRingObj (fieldRing l E) X) L → integralField l E X L
  normalAlgebraic : (∀ p : X, IsDomain (X.presheaf.stalk p) ∧
      IsIntegrallyClosed (X.presheaf.stalk p)) →
    ∀ L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X),
      CondensedRing.LocallyFree (condensedRingObj (Profinite.padicAlgClRingObj l) X) L →
        integralClosure l X L
  regularNormal : (∀ p : X, ∃ U : X.affineOpens,
      p ∈ (U : X.Opens) ∧ IsRegularRing Γ(X, U)) → ∀ p : X,
    IsDomain (X.presheaf.stalk p) ∧ IsIntegrallyClosed (X.presheaf.stalk p)
  fieldsOfDefinition : ∀ V : Rep.{u + 1} (PadicAlgCl l) G,
    continuousClosureRep l G V ↔ definedRep l G V

/-- Lisse sheaves with integral, rational and algebraic-closure coefficients have
the geometric-fibre equivalences and compatibilities specified above. In particular,
normality (hence regularity) removes the integrality restriction, and every continuous
finite-dimensional algebraic-closure representation has a finite field of definition.

Source: latest blueprint, sec-six-functors/sk-lem-finite,
thm-lisse-qlbar-representations (blueprint: thm-lisse-qlbar-representations).

Proof (following the blueprint proof, in its order):

1. At a geometric point $s=\operatorname{Spec}\kappa$, the module pullback equivalence identifies
$\Lambda_s$-modules with condensed $\Lambda$-modules through $p_s^*$, the pro-étale site of $s$
being equivalent to profinite sets through $S\mapsto\operatorname{Spec}LC(S,\kappa)$, the final
object $s$ corresponding to the point $*$. Since $p_s^*$ is an equivalence, the unit of
$p_s^*\dashv p_*\pi_{s*}$ is an isomorphism, so $\Gamma(s,p_s^*N)=N(*)$; in particular
$\Lambda_s(s)=\Lambda(*)$, which is the ordinary ring $\mathcal O_E$, $E$ or $\Qlb$. A cover of
$*$ in the condensed site is a finite jointly surjective family of profinite sets, so one member
is nonempty and a point of it is a section. Pulling a lisse trivialization back along such a
section makes it globally free on $s$. Evaluation of this free module is therefore $\Lambda^r$;
maps evaluate as matrices over $\Lambda$. Consequently the fibre of a lisse module is finite free
and respects tensor products and coefficient extension. For a finite (discrete) coefficient ring
the pulled condensed ring is the constant ring and the comparison inverse image of the constant
étale ring, and a discrete continuous-function sheaf is $\nu^*$ of the constant étale sheaf; so
for a finite constant coefficient sheaf pulled from the étale site the fibre is its usual
geometric stalk. These assertions follow on each free chart from the coefficient identifications,
rather than from an assertion that geometric stalks detect arbitrary pro-étale sheaves.

2. Put $A=\mathcal O_E$, $A_n=A/\varpi^n$. The cited integral reduction equivalence is stated for
the continuous-function ring sheaves $U\mapsto C(|U|,A)$ and $U\mapsto C(|U|,E)$; since $A$ and
$E$ are totally disconnected topological rings, the canonical comparison $p_X^*\underline T\to
C(|-|,T)$ is an isomorphism of ring sheaves for $T=A,E$, and it is compatible with the inclusion
$A\subset E$ because it is defined by $f\mapsto f\circ\pi_S$ on test objects. Transporting module
categories along these ring isomorphisms, the equivalence and its isomorphisms $A_X[1/\ell]\cong
E_X$, $A_X/\varpi^n\cong A_{n,X}$ hold for the pulled coefficients $p_X^*\underline A$,
$p_X^*\underline E$ of the statement; all later uses of the integral reduction equivalence are
through this transport. The integral reduction equivalence identifies lisse $A_X$-modules with
normalized towers of finite locally free $(A_n)_X$-modules, with inverse the sheaf limit and its
actual quotient projections. Each finite level is a finite local system. Etale origin, and the
invertible unit of the comparison, identify these levels and all their arrows with classical
finite locally constant module sheaves. Only clause (1) of the finite-coefficient Galois
equivalence is used: the extra hypotheses and different definition of the adic objects in its
clause (2) play no role. It supplies finite free fibres $M_n$, with equivariant quotient
identifications $M_{n+1}/\varpi^nM_{n+1}\simeq M_n$.

3. Choose a basis of $M_1$ and lift it successively through the surjective transitions. At level
$n+1$ these lifts form a basis: modulo the maximal ideal they are a basis, so the resulting square
matrix has unit determinant over the finite local ring. The rank is fixed by $M_1$. Thus
$M=\varprojlim M_n\simeq A^r$, including $r=0$. The coefficient limit and the free-chart
calculation at the geometric point identify $M$ with $L_{0,\bar x}$, with its quotient
projections. Its action is continuous because each projection to the finite discrete $M_n$ is
continuous and their kernels define the adic topology. For two towers, an $A$-linear map of their
limits is exactly a compatible family of quotient maps, and equivariance is detected on all
quotients. Hence finite-level full faithfulness and the reduction equivalence give full
faithfulness at $A$.

4. Conversely, given a continuous action on $M\simeq A^r$, its quotients $M/\varpi^nM$ are finite
continuous representations. The finite equivalence produces classical sheaves with these fibres.
Its full faithfulness uniquely lifts the quotient arrows, so their composites and their normalized
scalar quotient identifications satisfy the same equations as the module quotients. Pull them to
the pro-etale site and apply the inverse of the integral reduction equivalence. This produces a
lisse $L_0$ with the specified reductions and fibre $M$, giving essential surjectivity and the
asserted compatibility with reduction. This entire integral construction works on any connected
scheme; Noetherianity has not been used.

5. Put $A=\mathcal O_E$. For lisse lattices $L_0,L'_0$, the sheaf $\mathcal Hom_A(L_0,-)$ commutes
with filtered colimits: on each finite free chart it is a finite direct sum, which commutes with
these colimits. By integral coefficient localization, transported to the pulled coefficients as in
step 2, $L'_0[1/\ell]=\varinjlim_c\ell^{-c}L'_0$. Apply the cited sections theorem to the
resulting Hom sheaves at the qcqs object $X$, and tensor-Hom adjunction, to get
$$\operatorname{Hom}_{E_X}(L_0[1/\ell],L'_0[1/\ell])=\operatorname{Hom}_{A_X}(L_0,L'_0)[1/\ell].$$
The integral equivalence identifies the right side with
$\operatorname{Hom}_{\pi_1,A}(M,M')[1/\ell]$, where $M=L_{0,\bar x}$ and $M'=L'_{0,\bar x}$. This
is $\operatorname{Hom}_{\pi_1,E}(M[1/\ell],M'[1/\ell])$: finitely many basis images have a common
denominator, and torsion freeness detects equality. The point calculation identifies the localized
fibres with those of the rational sheaves. For two lattices in the same $L$, the displayed sheaf
Hom equality applied to $\mathrm{id}_L$ gives an integral map inducing $\ell^c\mathrm{id}_L$ for
some $c$. Its fibre is equivariant by the integral equivalence; cancel the nonzero scalar after
localization to see the two actions on $L_{\bar x}$ agree. This proves (2)'s full faithfulness and
independence of lattice.

6. Every continuous representation on a finite-dimensional $E$-space has a stable finite free
$A$-lattice, with its adic topology and continuous restricted action. The integral construction
applied to it, then localization, produces the given representation as fibre. Together with the
preceding Hom bijection this proves (2). Tensor compatibility at $A$ is checked modulo every
$\varpi^n$, where the finite equivalence is a tensor equivalence; the reduction equivalence and
completeness identify these comparisons on the integral modules. For $E\subset F$, extension of a
free $A$-chart to $\mathcal O_F$ and reduction modulo $\varpi_F^n$ uses a finite quotient of $A$,
since a power of $\varpi_E$ vanishes in this quotient. The finite scalar-extension compatibility
therefore gives precisely the extended action. Localization gives the tensor and finite-field
scalar compatibilities at $E$. The unit, associativity and composition equations hold modulo every
finite level, hence on the limits and their localizations.

7. For integral $E$-models $L',L''$, their scalar extensions to finite $F\supset E$ remain
integral: extend a lattice by $\mathcal O_F\otimes_{\mathcal O_E}-$, which is finite free on every
lattice chart. Their fibres and actions extend by the preceding scalar compatibility. Finite
descent of Hom gives $$\operatorname{Hom}_{\QbarX}(L'_{\Qlb},L''_{\Qlb})=\varinjlim_{F\supset
E}\operatorname{Hom}_{F_X}(L'_F,L''_F).$$ Use (2) at every $F$. Each equivariant matrix over
$\Qlb$ has finitely many entries, so they lie in one finite $F$; its equivariance equations are
equations over $F$ and hold there because $F\hookrightarrow\Qlb$ is injective. Equality of
matrices is also detected at that stage. Thus the last colimit is exactly the equivariant
$\Qlb$-linear Hom of the two fibres. This avoids invoking an uncited general theorem that
invariants commute with infinite intersections and scalar extension.

8. If two integral finite-field models give the same $\QbarX$-module, lift the chosen comparison
isomorphism and its inverse using the finite-descent Hom bijections. The two identities hold at a
further common finite stage by the equality relation in the filtered colimit. By (2) these lifted
maps are equivariant on fibres; hence the action on the specified fibre of $L$ is independent of
the finite-field model. A representation defined over $E$ is obtained by (2) and then extension to
$\Qlb$, proving essential surjectivity in (3). Tensor products and extension comparisons descend
to a common finite stage; all their equations hold there by the preceding tensor/scalar
construction, so persist after extension. This proves (3) with all stated compatibilities.

9. Assume now that $X$ is normal, and let $L$ be lisse over $E_X$. Its rank is constant on the
connected $X$ by the rank-locus lemma. Its lattice sheaf is represented by a separated surjective
etale $q:T=\mathrm{Lat}(L)\to X$, with universal lattice. For a geometric $\bar y$, a point of $T$
over the closed point of the strict localization $S=X_{(\bar y)}$ gives a section of $T_S\to S$,
by the strictly henselian etale-section lemma. The pulled-back universal lattice is a lattice $N$
of $L|_S$. No global extension of this section to $X$ is asserted.

10. Every finite etale cover of the strictly henselian local $S$ splits into copies of $S$: each
point of its closed fibre gives a section by the etale-section lemma, and these sections are
clopen by the separated etale-section lemma; their complement is finite and has empty closed
fibre, hence is empty. The finite-cover equivalence therefore makes $\pi_1(S)$ trivial. Apply the
integral construction (valid on any connected base, as observed above) to $N$; it is constant,
hence $L|_S\simeq E_S^r$. The lattice-scheme description for this trivial module identifies $T_S$
with the disjoint union of copies of $S$ indexed by the discrete set of lattices in $E^r$. Here
$S$ is affine, so the qcqs hypothesis of the lattice-scheme description is satisfied.

11. The strict-local splitting just proved is exactly the hypothesis of the normal-component lemma
for $T\to X$. Choose a nonempty component (surjectivity of $q$ and the chosen geometric point
ensure one exists). It is finite etale surjective over $X$, and the universal lattice restricts to
it. Apply finite-etale trace descent of lattices to this cover and this lattice. Its trace-image
lattice is lisse over $\mathcal O_{E,X}$ and localizes to $L$, proving the first assertion of (4).
This use of trace descent has a genuinely finite etale cover, rather than an arbitrary etale
atlas. It replaces the imported application of the stratified-lattice node, whose
finite-type-over-a-field hypothesis is unavailable for the present general Noetherian $X$.

12. Finite descent of lisse $\QbarX$-modules supplies $L\simeq\QbarX\otimes_{E_X}L_E$ with finite
$E$ and lisse $L_E$. On normal $X$ the preceding argument supplies a lattice of $L_E$, so $L$ is
integral. A regular scheme is normal by the regular-normal result. This proves the remaining
assertions of (4), including the regular case, without requiring that $X$ be separated or of
finite type over a field.

13. For a continuous finite-dimensional $\Qlb$-representation of the profinite group $\pi_1$,
choose a finite basis indexed by $I$ and let $\phi(g)$ be its matrix. The group $\pi_1$ is
compact. Matrix multiplication gives the monoid homomorphism required by the compact matrix
coefficient descent lemma, and each entry is continuous because coordinate projections in the
absolute-value matrix topology are continuous. That lemma gives a single finite $E/\mathbf Q_\ell$
containing every entry of every $\phi(g)$. Its statement allows empty $I$, so also covers
dimension zero. No assertion about the colimit topology on the coefficient sheaf is used here:
both statements use the absolute-value topology on $\Qlb$.

14. For the field $E$ just obtained, the matrices $\phi(g)$ lie in $\operatorname{GL}_I(E)$: their
determinants lie in $E$ and are nonzero, hence have inverses in $E$. Therefore $E^I$ is stable.
The action is continuous since $E$ has the subspace absolute-value topology in $\Qlb$, as do
finite matrix spaces and their subspaces of invertible matrices: the factorization of the original
continuous map through $\operatorname{GL}_I(E)$ is continuous by the definition of subspace
topology. Extending scalars identifies $\Qlb\otimes_E E^I$ with the original space using the
chosen basis and gives its original action. This proves (5), including dimension zero.

15. For connected normal Noetherian $X$, (4) makes every lisse $\QbarX$-module integral and (5)
makes every continuous finite-dimensional representation defined over a finite $E$. Apply (3) and
its tensor/scalar compatibilities. Regular $X$ is included by normality. Finally, on the nodal
example of the cited stratified-lattice statement, a lattice pulled to its connected $\mathbf
Z$-torsor would be a constant rank-one lattice preserved by multiplication by $\ell$, which is
impossible: multiplication changes its valuation by the positive valuation of $\ell$. Its action
cannot extend to the profinite completion, since such a continuous action would have a stable
lattice by the compact-group lattice theorem. This verifies the final contrast and the role of the
normality hypothesis. -/
theorem lisse_qlbar_representations
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X] [ConnectedSpace X]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (G : ProfiniteGrp.{u}) [∀ P, MulAction G ((FiniteEtale.fiber x).obj P)]
    [PreGaloisCategory.IsFundamentalGroup (FiniteEtale.fiber x) G] :
    Nonempty (Correspondence l x G) := by
  sorry

end LisseQlbar
end AlgebraicGeometry.ProEtale
