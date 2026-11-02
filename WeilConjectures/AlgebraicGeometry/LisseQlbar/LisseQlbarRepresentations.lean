/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseRepresentations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.StratifiedLattice
public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
public import WeilConjectures.AlgebraicGeometry.RegularNormalDecomposition
public import WeilConjectures.AlgebraicGeometry.ProEtaleLisseOrigin
public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.CategoryTheory.SetFunctorAut.AutProfinite
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.CategoryTheory.RingObjects.GlobalSections
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LocalRing.Basic
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.Topology.Defs.Filter
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.AlgebraicGeometry.ContinuousRingUniverseRealization
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.CategoryTheory.Preadditive.HomOrthogonal
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Analysis.Normed.Algebra.Ultra
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Connected.Clopen
import Mathlib.LinearAlgebra.InvariantBasisNumber
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.AlgebraicGeometry.StratifiedLatticeScheme
import WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficientNormalization
import WeilConjectures.AlgebraicGeometry.IntegralLatticeCoefficientTransport
import WeilConjectures.AlgebraicGeometry.LisseLatticeSliceTransport
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingLattices
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingRestriction
import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStrictlyHenselian
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.Strict.StrictBaseClosedPointLocalizations
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantSplit
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFiniteDescentLisse
public import WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.LimitBaseChange
public import WeilConjectures.AlgebraicGeometry.NormalEtale
public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.ProperBaseChange.CondensedFieldLfpLocalTriviality
public import WeilConjectures.RepresentationTheory.LAdicContinuous
public import WeilConjectures.RingTheory.StrictHenselizationTriples
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.SpectralFiniteEtaleTraceLattice

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

/-- An embedded lisse integral module whose given inclusion rationalizes to an isomorphism.
Source: latest blueprint, thm-lisse-qlbar-representations.md, introductory lattice definition,
and sk-lem-uniform-constructible-ext/_section.md, lattice antecedent
(blueprint: def-sfb-lisse-integral-lattice). -/
def hasLattice
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj B] [IsCommMonObj B]
    (a : Λ ⟶ B) [IsMonHom a] (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X)) : Prop :=
  ∃ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
    CondensedRing.LocallyFree (condensedRingObj Λ X) M ∧
    ∃ i : M ⟶ (Mod.comap (coefficientMap a X)).obj L,
      Mono i ∧ IsIso (((Mod.extendRestrictAdjunction (coefficientMap a X)).homEquiv M L).symm i)

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

/-- The finite-extension condensed coefficient ring with its inherited absolute-value topology.
Source: latest blueprint, thm-lisse-qlbar-representations.md, coefficient convention
(blueprint: def-sfb-lisse-integral-lattice). -/
abbrev fieldRing (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  Profinite.continuousMapRingObj.{u} E

/-- The condensed ring of integers with its induced topology.
Source: latest blueprint, thm-lisse-qlbar-representations.md, coefficient convention
(blueprint: def-sfb-lisse-integral-lattice). -/
abbrev integerRing (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers ℓ E)

/-- The canonical inclusion of integral into rational condensed coefficients.
Source: latest blueprint, thm-lisse-qlbar-representations.md, lattice definition
(blueprint: def-sfb-lisse-integral-lattice). -/
abbrev integerInclusion (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    integerRing.{u} ℓ E ⟶ fieldRing ℓ E :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMap
        (Padic.coefficientExtensionIntegers ℓ E).subtype continuous_subtype_val)

set_option maxHeartbeats 0 in
-- Large clause records contain canonical sheaf, fibre and coefficient comparison types.
set_option genSizeOfSpec false in
set_option genInjectivity false in
set_option maxHeartbeats 0 in
-- Large clause records contain canonical sheaf, fibre and coefficient comparison types.
set_option genSizeOfSpec false in
set_option genInjectivity false in
set_option maxHeartbeats 0 in
-- Large clause records contain canonical sheaf, fibre and coefficient comparison types.
set_option genSizeOfSpec false in
set_option genInjectivity false in
variable (l : ℕ) [Fact l.Prime]

set_option maxHeartbeats 0 in
-- Large clause records contain canonical sheaf, fibre and coefficient comparison types.
set_option genSizeOfSpec false in
set_option genInjectivity false in
set_option maxHeartbeats 0 in
-- Large clause records contain canonical sheaf, fibre and coefficient comparison types.
set_option genSizeOfSpec false in
set_option genInjectivity false in
end LisseQlbar
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.LisseQlbar

/-- Lisse sheaves with integral, rational and algebraic-closure coefficients have
exactly the normalized geometric-fibre correspondences of clauses (1)--(5).

Source: latest blueprint, sec-six-functors/sk-lem-finite,
thm-lisse-qlbar-representations (blueprint: thm-lisse-qlbar-representations).

Proof: the simultaneous monodromy construction supplies clauses (1)--(3), including
all quotient, tensor and scalar normalizations for the same choice of functors.
The normal finite-field lattice theorem and finite coefficient descent give the
two normality implications. The regular-normal theorem gives regularNormal.
The compact-matrix finite-model theorem, with its continuity converse, gives
fieldsOfDefinition. Assemble these independent clauses with Correspondence.mk. -/
theorem lisse_qlbar_representations
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X] [ConnectedSpace X]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (G : ProfiniteGrp.{u}) [∀ P, MulAction G ((FiniteEtale.fiber x).obj P)]
    [PreGaloisCategory.IsFundamentalGroup (FiniteEtale.fiber x) G] :
    Nonempty (Correspondence l x G) := by
  obtain ⟨c⟩ := exists_core_correspondence l X Ω x G
  have h := normal_integrality l X
  refine ⟨Correspondence.mk c.finite c.integral c.rational c.algebraic c.reductions
    c.integralTensor c.rationalTensor c.algebraicTensor c.localization c.algebraicExtension
    c.fieldExtension h.normalField h.normalAlgebraic
    (regular_normal_and_normal_decomposition X).1 ?_⟩
  intro V
  exact (Representation.isLAdic_iff_continuous l G V.V
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv _ V.V).toMonoidHom.comp
      (Representation.asGroupHom V.ρ))).symm

end AlgebraicGeometry.ProEtale.LisseQlbar
