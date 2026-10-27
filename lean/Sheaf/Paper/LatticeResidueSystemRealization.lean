/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q104
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Connected.Basic
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Paper.GaloisLisseRepresentations
public import Sheaf.Paper.LisseCompletedSystemData
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import Mathlib.CategoryTheory.Limits.HasLimits
import Sheaf.Paper.LisseCompletedSystemComparison
import Sheaf.Paper.IntegralCoefficientPresentationComparison

/-! # Integral lattices, coherent residue systems and completed realization

Source: Bhatt--Scholze, Proposition 6.8.4(1), pp. 59--60, and Lemma 7.4.7, p. 70;
Stanford Weil II seminar, L19, Proposition 1.1.9, third bullet
(blueprint: lem-a1-lattice-residue-system-realization).

Levels are indexed by n with exponent n+1. Finite coefficient modules are stored as
A-modules annihilated by the coefficient ideal, as in the existing normalized-system
category. Quotient comparisons are specified by their cokernel universal properties;
thus the maps are the adjoints of the displayed transitions, rather than arbitrary
isomorphisms. Natural transformations retain every transition and limit projection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CompletedLisse AlgebraicGeometry.ProEtale WeilConjectures

namespace AlgebraicGeometry.Scheme.LatticeResidue

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (G : ProfiniteGrp.{u})

/-- Finite free continuous integral representations, including the zero module.
Source: BS 7.4.7; L19 1.1.9 (blueprint: lem-a1-lattice-residue-system-realization). -/
abbrev Lattices := ObjectProperty.FullSubcategory
  (fun V : Rep.{u + 1} (Padic.coefficientExtensionIntegers l E) G ↦
    Module.Free (Padic.coefficientExtensionIntegers l E) V.V ∧
      Representation.IsContinuousIntegral l E G V.V (galoisRepLinearAction _ V))

variable (X : Scheme.{u})

/-- The actual constant residue section, via constant sheafification.
Source: BS 6.8.2(1) (blueprint: lem-a1-lattice-residue-system-realization). -/
def residueConstant (n : ℕ) (U : X.ProEtᵒᵖ)
    (a : Padic.coefficientExtensionIntegers l E) :
    (integralCoefficientSheaf l E X n).obj.obj U :=
  (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app U
    ⟨algebraMap _ _ a⟩

/-- The actual constant integral section in the completed coefficient sheaf.
Source: BS 6.8.2(1) (blueprint: lem-a1-lattice-residue-system-realization). -/
def integralConstant (U : X.ProEtᵒᵖ) (a : Padic.coefficientExtensionIntegers l E) :
    (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U :=
  (integralConstantToCompletionOfUniverses l E X).hom.app U
    ((toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))))).app U ⟨a⟩)

variable [IsNoetherian X] [X.IsSeparated]
  [∀ x : X, Invertible (l : X.residueField x)]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
  [∀ P, MulAction G ((FiniteEtale.fiber x).obj P)]

/-- Simultaneous realization data, with quotient-normalized fibres and projections.
These fields package the conclusions of BS 6.8.4(1), BS 7.4.7 and L19 1.1.9.
All data are quantified over by the existence theorem; this structure chooses nothing.
Source: BS 6.8.4(1), 7.4.7 (blueprint: lem-a1-lattice-residue-system-realization). -/
structure Realization (c : GaloisLisseFiniteCorrespondence x G) where
  tower : Lattices l E G ⥤ LisseIntegralSheaf l E X
  completed : Lattices l E G ⥤
    ringedSiteModules.{u + 1} (completedIntegralCoefficientSheafUnrestricted l E X)
  rank (V : Lattices l E G) : (completed.obj V).IsFiniteLocallyFreeOfRank
    (Module.finrank (Padic.coefficientExtensionIntegers l E) V.obj.V)
  finite_free (V : Lattices l E G) (n : ℕ) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i : 𝒰.I₀, Nonempty
      (((tower.obj V).obj.obj (op n)).over (𝒰.etalePrecoverageToEtale i) ≅
        (constantSheaf (X.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
          (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).obj
          (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
            (Fin (Module.finrank (Padic.coefficientExtensionIntegers l E) V.obj.V) →
              Padic.coefficientExtensionRing l E (n + 1))))
  fibre (V : Lattices l E G) (n : ℕ) :
    ModuleCat.of (Padic.coefficientExtensionIntegers l E) V.obj.V ⟶
      ((pointSmallEtale x).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).obj
          ((tower.obj V).obj.obj (op n))
  fibre_quotient (V : Lattices l E G) (n : ℕ) :
    ∃ h : (Padic.coefficientExtensionUniformizer l E ^ (n + 1) • 𝟙
        (ModuleCat.of (Padic.coefficientExtensionIntegers l E) V.obj.V)) ≫ fibre V n = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ (fibre V n) h))
  fibre_transition (V : Lattices l E G) (n j : ℕ) (hjn : j ≤ n) :
    fibre V n ≫ ((pointSmallEtale x).ulift.{u + 1}.sheafFiber
      (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).map
        ((tower.obj V).obj.map (homOfLE hjn).op) = fibre V j
  fibre_natural {V W : Lattices l E G} (f : V ⟶ W) (n : ℕ) :
    ModuleCat.ofHom f.hom.hom.toLinearMap ≫ fibre W n = fibre V n ≫
      ((pointSmallEtale x).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).map
          ((tower.map f).hom.app (op n))
  discrete_continuous (V : Lattices l E G) (n : ℕ) (v : V.obj.V) :
    IsOpen {g : G | fibre V n (V.obj.ρ g v) = fibre V n v}
  monodromy (V : Lattices l E G) (n : ℕ) :
    ∃ h : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf
      (Padic.coefficientExtensionIntegers l E) ((tower.obj V).obj.obj (op n))),
    ∃ κ : (((pointSmallEtale x).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).obj
          ((tower.obj V).obj.obj (op n))) ≃
        (((pointSmallEtale x).sheafFiber (A := Type (u + 1))).obj
          (galoisUnderlyingSetSheaf (Padic.coefficientExtensionIntegers l E)
            ((tower.obj V).obj.obj (op n)))),
      (∀ (U : X.Etale) (z : (pointSmallEtale x).fiber.obj U)
          (s : ((tower.obj V).obj.obj (op n)).obj.obj (op U)),
        κ ((pointSmallEtale x).ulift.{u + 1}.toPresheafFiber U ⟨z⟩
          ((tower.obj V).obj.obj (op n)).obj s) =
        (pointSmallEtale x).toPresheafFiber U z
          (galoisUnderlyingSetSheaf (Padic.coefficientExtensionIntegers l E)
            ((tower.obj V).obj.obj (op n))).obj s) ∧
      ∀ (g : G) (v : V.obj.V), κ (fibre V n (V.obj.ρ g v)) =
        (c.γ g).hom.app (galoisUnderlyingFLC (Padic.coefficientExtensionIntegers l E)
          ((tower.obj V).obj.obj (op n)) h) (κ (fibre V n v))
  transition_quotient (V : Lattices l E G) (n j : ℕ) (hjn : j ≤ n) :
    ∃ h : (Padic.coefficientExtensionUniformizer l E ^ (j + 1) •
        𝟙 ((tower.obj V).obj.obj (op n))) ≫
          (tower.obj V).obj.map (homOfLE hjn).op = 0,
      Nonempty (IsColimit
        (CokernelCofork.ofπ ((tower.obj V).obj.map (homOfLE hjn).op) h))
  projection (V : Lattices l E G) :
    (Functor.const ℕᵒᵖ).obj
        ((SheafOfModules.toSheaf _).obj (completed.obj V)) ⟶
      ((tower.obj V).obj ⋙
        sheafCompose _ (forget₂ (ModuleCat.{u + 1}
          (Padic.coefficientExtensionIntegers l E)) AddCommGrpCat)) ⋙
        supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} X
  limit_property (V : Lattices l E G) : IsLimit (Cone.mk _ (projection V))
  projection_natural {V W : Lattices l E G} (f : V ⟶ W) (n : ℕ) :
    (SheafOfModules.toSheaf _).map (completed.map f) ≫ (projection W).app (op n) =
      (projection V).app (op n) ≫
        (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} X).map
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1}
            (Padic.coefficientExtensionIntegers l E)) AddCommGrpCat)).map
              ((tower.map f).hom.app (op n)))
  scalar (V : Lattices l E G) (a : Padic.coefficientExtensionIntegers l E) :
    (SheafOfModules.toSheaf _).obj (completed.obj V) ⟶
      (SheafOfModules.toSheaf _).obj (completed.obj V)
  scalar_sections (V : Lattices l E G) (a : Padic.coefficientExtensionIntegers l E)
      (U : X.ProEtᵒᵖ) (s : (completed.obj V).val.obj U) :
    (scalar V a).hom.app U s = integralConstant l E X U a • s
  projection_quotient (V : Lattices l E G) (n : ℕ) :
    ∃ h : scalar V (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) ≫
        (projection V).app (op n) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ ((projection V).app (op n)) h))
  coordinate_action (V : Lattices l E G) (n : ℕ) (U : X.ProEtᵒᵖ)
      (b : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U)
      (a : Padic.coefficientExtensionIntegers l E)
      (hb : ((limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app U) b =
        residueConstant l E X n U a) (s : (completed.obj V).val.obj U) :
    ((projection V).app (op n)).hom.app U (b • s) =
      ((supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} X).map
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1}
          (Padic.coefficientExtensionIntegers l E)) AddCommGrpCat)).map
            (a • 𝟙 ((tower.obj V).obj.obj (op n))))).hom.app U
              (((projection V).app (op n)).hom.app U s)

/-- A finite free integral representation admits its coherent finite residue sheaves
and its rank-preserving completed pro-etale realization, simultaneously functorially.
Source: BS Proposition 6.8.4(1), pp. 59--60, Lemma 7.4.7, p. 70, and L19 1.1.9
(blueprint: lem-a1-lattice-residue-system-realization).

Proof: (1) Choose an A-basis. The DVR theorem and its finite residue field imply
finiteness of A/(uniformizer^(n+1)) and of each module quotient. Joint continuity
implies open stabilizers on each discrete quotient, and quotient maps are equivariant.
(2) Apply cor-galois-lisse-representations at each finite ring. The finite action has
open normal kernel; thm-galois-fundamental trivializes it on a finite etale cover.
This proves the asserted free rank, including zero. (3) Full faithfulness lifts all
quotient maps uniquely. Faithfulness gives identities and composition. The adjoint
scalar-change maps are isomorphisms: in a basis they identify the same free modules.
For three levels both tensor composites send c tensor b tensor [v] to cb[v], proving
associativity coherence. This is equivalently the displayed cokernel universal property.
(4) Apply lem-per-lisse-completed-system-comparison. Its inverse is the actual sheaf
limit. Use lem-weil-pbc-integral-coefficient-presentation-comparison to identify its
coefficient presentation with the recorded completed constant ring, keeping all residue
projections. This transports the coordinate action, local freeness and quotient maps.
The rank equals the finite-level rank after reduction to the residue field at geometric
points. (5) Equivariant linear maps descend to all quotients. Full faithfulness lifts
them, preserving identities, composition and scalar adjoints. The sheaf-limit maps
act coordinatewise (def-pur-sheaf-inverse-limit), so their projection and quotient
comparisons are natural. -/
theorem realization_exists [ConnectedSpace X]
    [IsFundamentalGroup (FiniteEtale.fiber x) G] :
    ∃ c : GaloisLisseFiniteCorrespondence x G, Nonempty (Realization l E G X x c) := by
  sorry

end AlgebraicGeometry.Scheme.LatticeResidue
