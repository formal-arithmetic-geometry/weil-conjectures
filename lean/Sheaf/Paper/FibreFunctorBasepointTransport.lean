/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.Paper.FibreFunctorBasepointTransportData
import Sheaf.Paper.FibreFunctorLinearTransport
import Sheaf.Paper.AdicFibrePathExtension
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
import Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence
import WeilConjectures.Mathlib.CategoryTheory.Galois.Prorepresentability

/-! # Etale paths and transport of finite and adic stalks

Source: Stacks Project, 0BND (2), 0BN5; Deligne, Weil II (1.1.1) b)-d), pp.146-147
(blueprint: lem-wf-fibre-functor-basepoint-transport).

## Main definitions

* `LinearFibrePathFamily`: natural linear path maps and their functoriality laws.
* `FiniteFibrePathTransport`: evaluation on underlying FLC sheaves and scalar compatibility.
* `AdicFibrePathTransport`: integral, rational and algebraic path maps, characterized at
  finite levels and on pure tensors, with canonical scalar comparisons.

## Main statements

* `fibre_functor_basepoint_transport`: existence of paths, topological conjugation and
  transport at all finite and adic coefficient levels.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}}

private theorem flcPath_exists [ConnectedSpace Y]
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y) :
    Nonempty (flcFiber y ≅ flcFiber z) := by
  obtain ⟨Φ, _, hΦ, _⟩ := exists_finiteEtale_flc_equivalence_sheaf Y
  obtain ⟨ηy⟩ := hΦ Ωy y
  obtain ⟨ηz⟩ := hΦ Ωz z
  obtain ⟨t⟩ := PreGaloisCategory.nonempty_iso_of_fiberFunctor
    (FiniteEtale.fiber y) (FiniteEtale.fiber z)
  let U := CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u}
  exact ⟨((Functor.whiskeringLeft _ _ (Type (u + 1))).obj Φ.functor).preimageIso
    (ηy ≪≫ Functor.isoWhiskerRight t U ≪≫ ηz.symm)⟩

private theorem setPath_conj_continuous {C : Type v} [Category.{w} C]
    {F H : C ⥤ Type (u + 1)} (t : F ≅ H) : Continuous t.conjAut := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro X
  let : TopologicalSpace (F.obj X) := ⊥
  let : DiscreteTopology (F.obj X) := ⟨rfl⟩
  let : TopologicalSpace (H.obj X) := ⊥
  let : DiscreteTopology (H.obj X) := ⟨rfl⟩
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro x
  have h₁ : Continuous (SetFunctorAut.evaluation F) := continuous_induced_dom
  have h₂ : Continuous (fun g : Aut F ↦ SetFunctorAut.evaluation F g X) :=
    (continuous_apply X).comp h₁
  have h₃ : Continuous (fun a : Aut (F.obj X) ↦ (a.hom : F.obj X → F.obj X)) :=
    continuous_induced_dom
  change Continuous (fun g : Aut F ↦ t.hom.app X (g.hom.app X (t.inv.app X x)))
  exact continuous_of_discreteTopology.comp
    ((continuous_apply (t.inv.app X x)).comp (h₃.comp h₂))


private theorem setPath_topologicalConjugation
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) :
    ∃ c : Aut (flcFiber y) ≃ₜ* Aut (flcFiber z),
      c.toMulEquiv = t.conjAut ∧
      ∀ (s : flcFiber y ≅ flcFiber z) (g : Aut (flcFiber y)),
        s.conjAut g = (t.symm ≪≫ s).symm ≪≫ c g ≪≫ (t.symm ≪≫ s) := by
  let c : Aut (flcFiber y) ≃ₜ* Aut (flcFiber z) :=
    { t.conjAut with
      continuous_toFun := setPath_conj_continuous t
      continuous_invFun := setPath_conj_continuous t.symm }
  refine ⟨c, rfl, ?_⟩
  intro s g
  change s.conjAut g = (t.symm ≪≫ s).symm ≪≫ t.conjAut g ≪≫ (t.symm ≪≫ s)
  simp [Iso.conjAut_apply, Iso.trans_assoc]

/-- Any two geometric fibre functors have a path; every path conjugates their topological
automorphism groups, and these paths transport finite and all three adic coefficient levels.
Source: Stacks 0BND (2), 0BN5 and Deligne, Weil II (1.1.1) b)-d), pp.146-147
(blueprint: lem-wf-fibre-functor-basepoint-transport).

Proof: the existing Galois-category fibre isomorphism theorem on finite etale covers,
transported through their equivalence with finite locally constant sheaves, gives a path.
Conjugation by any path is continuous in the evaluation topology, as is its inverse;
cancellation of natural isomorphisms gives the change-of-path formula.

Naturality of a set path with projections, addition and scalar multiplication gives
linear maps on lisse module stalks. Naturality with the scalar unit gives finite scalar
compatibility. Apply this construction at the finite levels of each integral lisse
system and take the inverse limit. Rationalize these paths; clearing denominators proves
naturality for all rational arrows. The scalar comparisons have their prescribed germ
and nested pure-tensor formulas, and their squares follow by adjunction and tensor
extensionality from the integral scalar unit square. Extend each rational model path to
the algebraic closure. The scalar square respects the uniquely normalized coefficient
comparisons, so these maps form a natural isomorphism on coefficient pairs and descend
through localization. Their model components give exactly the algebraic evaluation
formula. All four path laws hold levelwise and on pure tensors, hence at every coefficient
level. Assemble these constructions into the finite and adic transport records.
-/
theorem fibre_functor_basepoint_transport {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy]
    (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz]
    (z : Spec (.of Ωz) ⟶ Y) :
    Nonempty (flcFiber y ≅ flcFiber z) ∧
    (∀ t : flcFiber y ≅ flcFiber z,
      ∃ c : Aut (flcFiber y) ≃ₜ* Aut (flcFiber z),
        c.toMulEquiv = t.conjAut ∧
        ∀ (s : flcFiber y ≅ flcFiber z) (g : Aut (flcFiber y)),
          s.conjAut g = (t.symm ≪≫ s).symm ≪≫ c g ≪≫ (t.symm ≪≫ s)) ∧
    Nonempty (FiniteFibrePathTransport Y) ∧
    ∀ (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
      [∀ x : Y, Invertible (l : Y.residueField x)]
      (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q],
      Nonempty (AdicFibrePathTransport l Y Q) := by
  obtain ⟨c⟩ := finite_fibre_path_transport_exists Y
  refine ⟨flcPath_exists y z, setPath_topologicalConjugation y z, ⟨c⟩, ?_⟩
  intro l _ _ _ _ Q _ _ _
  obtain ⟨i⟩ := integral_fibre_path_transport_exists l Y Q
  obtain ⟨a, _⟩ := adic_fibre_path_transport_of_integral l Q i
  exact ⟨a⟩

end AlgebraicGeometry.Scheme
