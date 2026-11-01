/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalPerfectOrdinaryReductions
public import WeilConjectures.NumberTheory.Padics.IntegralScalarTowers
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import WeilConjectures.AlgebraicGeometry.InternalPerfectMatrix.InternalPerfectBasisSuccessor
public import WeilConjectures.AlgebraicGeometry.InternalPerfectMatrix.InternalPerfectCoefficientTransitions
public import WeilConjectures.AlgebraicGeometry.InternalPerfectMatrix.InternalPerfectDifferentialCompatibility
public import WeilConjectures.AlgebraicGeometry.InternalPerfectMatrix.InternalPerfectFiniteCochainCoordinates
public import WeilConjectures.AlgebraicGeometry.InternalPerfectMatrix.InternalPerfectSuccessorCompatibility

/-! # Ordinary quotient endomorphisms and scalar Hom cohomology -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem cohomology_of_cochainComparison
    (X : Scheme.{u}) (W : X.ProEt) (_hAffine : IsAffine W.left)
    (_hweak : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W)
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (a b : ℤ) (_ha : P.IsStrictlyGE a) (_hb : P.IsStrictlyLE b)
    (_hfree : ∀ i : ℤ, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i))
    (comparison : ∀ n : ℕ, InternalPerfectMatrix.quotientCochains l E W.left P n ≅
      CochainComplex.HomComplex (internalPerfectOrdinaryReduction l E W.left P n)
        (internalPerfectOrdinaryReduction l E W.left P n))
    (square : ∀ n : ℕ,
      (comparison (n + 1)).hom ≫ InternalPerfectMatrix.successorMap l E W.left P n =
        InternalPerfectMatrix.quotientStep l E W.left P n ≫ (comparison n).hom) :
    ∃ e : ∀ n : ℕ, internalPerfectOrdinaryHom l E W.left P n ≃
      LocallyConstant (ConnectedComponents W.left)
        ((Padic.scalarQuotient (Padic.coefficientExtensionUniformizer l E)
          (CochainComplex.moduleHomComplex P P) (n + 1)).homology 0),
      ∀ (n : ℕ) (x : internalPerfectOrdinaryHom l E W.left P (n + 1)),
        e n (internalPerfectOrdinaryHomStep l E W.left P n x) =
        LocallyConstant.map
          (HomologicalComplex.homologyMap
            (Padic.scalarQuotientTransition (Padic.coefficientExtensionUniformizer l E)
              (CochainComplex.moduleHomComplex P P) (n + 2) (n + 1)
              (Nat.succ_le_succ (Nat.le_succ n))) 0) (e (n + 1) x) := by
  let G := InternalPerfectMatrix.sections l E W.left
  let Q := fun n : ℕ ↦ Padic.scalarQuotient (Padic.coefficientExtensionUniformizer l E)
    (CochainComplex.moduleHomComplex P P) (n + 1)
  let r : ∀ n : ℕ,
      (CochainComplex.HomComplex (internalPerfectOrdinaryReduction l E W.left P n)
        (internalPerfectOrdinaryReduction l E W.left P n)).homology 0 ≅
          G.obj ((Q n).homology 0) := fun n ↦
    (HomologicalComplex.homologyFunctor _ _ 0).mapIso (comparison n).symm ≪≫
      ((Q n).sc 0).mapHomologyIso G
  refine ⟨fun n ↦ (homologyHomEquiv _ _).trans
    ((r n).addCommGroupIsoToAddEquiv.toEquiv.trans Equiv.ulift), ?_⟩
  intro n x
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ (.up ℤ)).map_surjective x
  rw [internalPerfectOrdinaryHomStep_map]
  let Φ := Mod.extendScalars (AdicCompletion.transition l E W.left n)
  let α := internalPerfectOrdinaryReductionStep l E W.left P n
  let γ := InternalPerfectMatrix.successorMap l E W.left P n
  let ψ := InternalPerfectMatrix.quotientStep l E W.left P n
  have hs : γ ≫ (comparison n).inv = (comparison (n + 1)).inv ≫ ψ := by
    apply (cancel_epi (comparison (n + 1)).hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [square n, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hH := congrArg (fun k ↦ HomologicalComplex.homologyMap k 0) hs
  simp only [HomologicalComplex.homologyMap_comp] at hH
  let τ := Padic.scalarQuotientTransition (Padic.coefficientExtensionUniformizer l E)
    (CochainComplex.moduleHomComplex P P) (n + 2) (n + 1)
    (Nat.succ_le_succ (Nat.le_succ n))
  have hnat : HomologicalComplex.homologyMap γ 0 ≫ (r n).hom =
      (r (n + 1)).hom ≫ G.map (HomologicalComplex.homologyMap τ 0) := by
    dsimp only [r, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      HomologicalComplex.homologyFunctor]
    rw [← Category.assoc, hH, Category.assoc]
    exact congrArg (fun k ↦ HomologicalComplex.homologyMap (comparison (n + 1)).inv 0 ≫ k)
      (ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor _ _ 0).map τ) G)
  have hh := homologyHomEquiv_scalar Φ α α f
  change ((r n).hom (homologyHomEquiv _ _
      ((HomotopyCategory.quotient _ (.up ℤ)).map
        (α.inv ≫ (Φ.mapHomologicalComplex (.up ℤ)).map f ≫ α.hom)))).down = _
  rw [hh]
  change ((r n).hom (HomologicalComplex.homologyMap γ 0
    (homologyHomEquiv _ _ ((HomotopyCategory.quotient _ (.up ℤ)).map f)))).down = _
  rw [← AddCommGrpCat.comp_apply, hnat, AddCommGrpCat.comp_apply]
  rfl

/-- Homotopy endomorphisms of the ordinary quotient model are locally constant quotient
Hom cohomology, with the formula for ordinary successor reduction. This statement
concerns ordinary complexes only and makes no assertion about derived reductions.

Source: Stacks Tags 09C5, 09C6 and 0A8H; blueprint Compatible isomorphisms.
(blueprint: lem-pe-internal-perfect-ordinary-hom-cohomology).

Proof: identify maps modulo homotopy with degree-zero cohomology of the signed Hom
complex. Fix a finite basis in each nonzero integral term. After finite quotient scalar
extension the terms are finite constant free modules. On the weakly contractible slice,
exact sections identify the internal Hom entries with locally constant finite matrices.
Only finitely many source degrees occur, so finite products commute with scalar quotient.
The resulting cochain identification sends the differential to d f minus the signed f d,
and identifies the Hom cochain complex with sections of the constant scalar quotient of
moduleHomComplex P P. Exact constant realization and exact sections commute with homology.
Sections of the finite constant cohomology module are locally constant functions on the
connected components of W. Passing to degree-zero homology gives the asserted equivalence.
Use the same integral bases at both levels: scalar extension reduces every matrix entry,
and the ordinary balancing map multiplies the adjacent scalars. This proves compatibility
on chain maps and on homotopies, hence on all homotopy classes. The finite zero module,
the empty scheme, and the zero complex yield singleton sets on both sides. -/
theorem internalPerfectOrdinary_homCohomology
    (X : Scheme.{u}) (W : X.ProEt) (_hAffine : IsAffine W.left)
    (_hweak : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W)
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (a b : ℤ) (_ha : P.IsStrictlyGE a) (_hb : P.IsStrictlyLE b)
    (_hfree : ∀ i : ℤ, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i)) :
    ∃ e : ∀ n : ℕ, internalPerfectOrdinaryHom l E W.left P n ≃
      LocallyConstant (ConnectedComponents W.left)
        ((Padic.scalarQuotient (Padic.coefficientExtensionUniformizer l E)
          (CochainComplex.moduleHomComplex P P) (n + 1)).homology 0),
      ∀ (n : ℕ) (x : internalPerfectOrdinaryHom l E W.left P (n + 1)),
        e n (internalPerfectOrdinaryHomStep l E W.left P n x) =
        LocallyConstant.map
          (HomologicalComplex.homologyMap
            (Padic.scalarQuotientTransition (Padic.coefficientExtensionUniformizer l E)
              (CochainComplex.moduleHomComplex P P) (n + 2) (n + 1)
              (Nat.succ_le_succ (Nat.le_succ n))) 0) (e (n + 1) x) := by
  sorry

end AlgebraicGeometry.ProEtale
