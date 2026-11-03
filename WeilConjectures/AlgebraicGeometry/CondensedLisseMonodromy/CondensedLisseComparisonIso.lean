/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseRepresentations
public import WeilConjectures.AlgebraicGeometry.EtaleAdicPathData
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCoverLift
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.StalkTransport
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import WeilConjectures.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PathTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReduction
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.Fibre.FibreFunctorBasepointTransportData
public import WeilConjectures.AlgebraicGeometry.Curve.FLCFiber
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Germ
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import WeilConjectures.AlgebraicGeometry.CondensedLisseMonodromy.ClassicalAdicPathNormalization
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteColimits
import WeilConjectures.AlgebraicGeometry.CondensedLisseMonodromy.ClassicalAdicPathFullness
/-! # Uniqueness of the fibre-normalized lisse comparison

Source: the latest blueprint's lisse representation theorem, clauses (1)--(3).
(blueprint: lem-a1-normalized-comparison-isomorphism).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CondensedLisseMonodromy
variable (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
  [ConnectedSpace X] [IsNoetherian X] [X.IsSeparated]
  [∀ z : X, Invertible (l : X.residueField z)]
attribute [local irreducible] fibre rawFibre geometricEvaluation

private theorem faithful_fibre {X : Scheme.{u}} [ConnectedSpace X]
    [IsNoetherian X] [X.IsSeparated] [∀ z : X, Invertible (l : X.residueField z)]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    (lisseAlgebraicFiberFunctor l X x (Coeff.{u} l)).Faithful := by
  obtain ⟨G, hact, hG⟩ := FiniteEtale.exists_isFundamentalGroup x
  let := hact
  let := hG
  obtain ⟨c, hd⟩ := galois_lisse_representations x G
  obtain ⟨d⟩ := hd l (Coeff.{u} l)
  exact Functor.Faithful.of_iso d.τA

private def bridge (C C' : Comparison l X) (L : Lisse l X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    (lisseAlgebraicFiberFunctor l X x (Coeff.{u} l)).obj (C.equivalence.functor.obj L) ≅
      (lisseAlgebraicFiberFunctor l X x (Coeff.{u} l)).obj (C'.equivalence.functor.obj L) :=
  (C.fibreIso Ω x).app L ≪≫ ((C'.fibreIso Ω x).app L).symm

omit [ConnectedSpace X] in
private theorem bridge_path (C C' : Comparison l X) (L : Lisse l X)
    {Ω Ω' : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ X)
    (τ : FiniteEtale.fiber x ≅ FiniteEtale.fiber y)
    (h : C.path l τ L = C'.path l τ L) :
    (C.classicalPaths.algebraic.map x y (flcPath τ)).hom.app
        (C.equivalence.functor.obj L) ≫ (bridge l C C' L y).hom =
      (bridge l C C' L x).hom ≫
        (C'.classicalPaths.algebraic.map x y (flcPath τ)).hom.app
          (C'.equivalence.functor.obj L) := by
  apply ConcreteCategory.hom_ext
  intro v
  have hp := DFunLike.congr_fun h ((C.fibreIso Ω x).hom.app L v)
  have he := congrArg ((C'.fibreIso Ω' y).inv.app L) hp
  simp only [Comparison.path, Iso.toLinearEquiv_apply,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, ← ModuleCat.comp_apply, Category.assoc,
    Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc] at he
  simpa [bridge, Category.assoc] using he

/-- Normalized condensed paths determine a unique fibre-compatible comparison.
Source: `thm-lisse-qlbar-representations`, proof, full faithfulness in clauses (1)--(3).
(blueprint: lem-a1-normalized-comparison-isomorphism).
Proof: at each lisse object, compare the two classical fibres through their
specified isomorphisms to the same condensed fibre. Equality of condensed paths
makes these comparison maps commute with paths. Classical normalized paths are
unique, so classical path fullness lifts the map and its inverse. A classical
fibre functor is faithful by the Galois correspondence; it proves the inverse
identities, naturality on lisse morphisms, and uniqueness of the resulting
natural isomorphism. The lifted maps have exactly the prescribed fibre values. -/
theorem normalized_comparison_iso
    (C C' : Comparison l X)
    (hpaths : ∀ (Ω Ω' : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
      (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ X)
      (τ : FiniteEtale.fiber x ≅ FiniteEtale.fiber y) (L : Lisse l X),
      C.path l τ L = C'.path l τ L) :
    ∃! e : C.equivalence.functor ≅ C'.equivalence.functor,
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
        (L : Lisse l X),
        (lisseAlgebraicFiberFunctor l X x (Coeff.{u} l)).map (e.hom.app L) ≫
          (C'.fibreIso Ω x).hom.app L = (C.fibreIso Ω x).hom.app L := by
  classical
  let z : X := Classical.choice inferInstance
  let x := FiniteEtale.geometricPoint z
  let := faithful_fibre l x
  have hobj (L : Lisse l X) :
      ∃ e : C.equivalence.functor.obj L ≅ C'.equivalence.functor.obj L,
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ X),
          (lisseAlgebraicFiberFunctor l X y (Coeff.{u} l)).map e.hom =
            (bridge l C C' L y).hom := by
    obtain ⟨f, hf⟩ := classical_adic_path_full l C.classicalPaths
      (C.equivalence.functor.obj L) (C'.equivalence.functor.obj L)
      (fun Ω _ _ y ↦ (bridge l C C' L y).hom)
      (fun Ω Ω' _ _ _ _ y y' τ ↦ by
        have hb := bridge_path l C C' L y y' τ (hpaths Ω Ω' y y' τ L)
        rw [classical_adic_paths_equal l C'.classicalPaths C.classicalPaths y y'
          (flcPath τ) (C'.equivalence.functor.obj L)] at hb
        exact hb)
    obtain ⟨g, hg⟩ := classical_adic_path_full l C'.classicalPaths
      (C'.equivalence.functor.obj L) (C.equivalence.functor.obj L)
      (fun Ω _ _ y ↦ (bridge l C' C L y).hom)
      (fun Ω Ω' _ _ _ _ y y' τ ↦ by
        have hb := bridge_path l C' C L y y' τ (hpaths Ω Ω' y y' τ L).symm
        rw [classical_adic_paths_equal l C.classicalPaths C'.classicalPaths y y'
          (flcPath τ) (C.equivalence.functor.obj L)] at hb
        exact hb)
    refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
    · apply (lisseAlgebraicFiberFunctor l X x (Coeff.{u} l)).map_injective
      rw [Functor.map_comp, CategoryTheory.Functor.map_id, hf _ x, hg _ x]
      simp [bridge]
    · apply (lisseAlgebraicFiberFunctor l X x (Coeff.{u} l)).map_injective
      rw [Functor.map_comp, CategoryTheory.Functor.map_id, hf _ x, hg _ x]
      simp [bridge]
  choose e he using hobj
  have hn {L M : Lisse l X} (f : L ⟶ M) :
      C.equivalence.functor.map f ≫ (e M).hom =
        (e L).hom ≫ C'.equivalence.functor.map f := by
    apply (lisseAlgebraicFiberFunctor l X x (Coeff.{u} l)).map_injective
    rw [Functor.map_comp, Functor.map_comp, he _ _ x, he _ _ x]
    exact (((C.fibreIso _ x) ≪≫ (C'.fibreIso _ x).symm).hom.naturality f)
  refine ⟨NatIso.ofComponents e (fun f ↦ hn f), ?_, ?_⟩
  · intro Ω _ _ y L
    change (lisseAlgebraicFiberFunctor l X y (Coeff.{u} l)).map (e L).hom ≫
      (C'.fibreIso Ω y).hom.app L = (C.fibreIso Ω y).hom.app L
    rw [he L Ω y]
    simp [bridge]
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext L
    apply (lisseAlgebraicFiberFunctor l X x (Coeff.{u} l)).map_injective
    change (lisseAlgebraicFiberFunctor l X x (Coeff.{u} l)).map (e'.hom.app L) =
      (lisseAlgebraicFiberFunctor l X x (Coeff.{u} l)).map (e L).hom
    have hm := congrArg (fun f ↦ f ≫ (C'.fibreIso _ x).inv.app L) (he' _ x L)
    have hm' : (lisseAlgebraicFiberFunctor l X x (Coeff.{u} l)).map (e'.hom.app L) =
        (bridge l C C' L x).hom := by
      simpa [bridge, Category.assoc] using hm
    exact hm'.trans (he L _ x).symm

end AlgebraicGeometry.ProEtale.CondensedLisseMonodromy
