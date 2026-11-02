/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedQcqsComposition.CondensedQcqsCompositionDefs

/-! Coherent compactification system for one qcqs morphism.
(blueprint: new-p3-qcqs-refinement-system)
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
open CompactSupportComposition
variable (ℓ : ℕ) [Fact ℓ.Prime]
def RefinementSystemData {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  Nonempty (System ℓ f)

/-- Extract the coherent system already contained in the bounded qcqs theorem.
Source: `condensedShriekBoundedQcqs`, its preservation and coherent-comparison clauses. -/
private theorem systemOfBoundedQcqs
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [QuasiSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left]
    [QuasiCompact f.left] : RefinementSystemData ℓ f.left := by
  have h := condensedShriekBoundedQcqs ℓ k f
  obtain ⟨hcomp, htriX, htriY, hpres, htri, hopen, ⟨τ, hτr, hτid, hτcoc⟩,
    hvan, hneg⟩ := h
  change Nonempty (System ℓ f.left)
  exact ⟨System.mk hpres τ hτr hτid hτcoc⟩

/-- The geometric-fibre map of a separated finite-type map has a coherent compactification
system.
Source: Stacks Tag 0F7J, lemma-shriek-composition (independence of the compactification);
latest blueprint lem-zl-shriek-composition.proof (blueprint: new-p3-qcqs-refinement-system).

Proof: compactifications exist by Nagata, and `Rc_!` preserves bounded constructible objects by
the bounded qcqs theorem (`preserves`). Any two compactifications `c, d` are refined by a third,
the closure of `X` in `c.Z ×_Y d.Z`. Put `comparison c d` = the inverse of the refinement map
to `c` followed by the refinement map to `d`. It is independent of the common refinement,
because refinement maps compose and two refinements have a common refinement. This gives
`refinement`, `comparison_id` and `comparison_cocycle`. -/
theorem qcqsRefinementSystemExists
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hℓ : ℓ ≠ D.p)
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [QuasiSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [QuasiSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left]
    [QuasiCompact f₀.left] : RefinementSystemData ℓ (modelMap D f₀) := by
  classical
  let t := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  let f := (Over.pullback t).map f₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let := Fintype.ofFinite D.k₀
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let : Fact (ringChar D.k).Prime := ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
  let : Fact (ringChar D.k ≠ ℓ) :=
    ⟨(ringChar.eq D.k D.p).symm ▸ hℓ.symm⟩
  let : LocallyOfFiniteType ((Over.pullback t).obj X₀).hom :=
    MorphismProperty.baseChange_obj (P := @LocallyOfFiniteType) t X₀ inferInstance
  let : QuasiCompact ((Over.pullback t).obj X₀).hom :=
    MorphismProperty.baseChange_obj (P := @QuasiCompact) t X₀ inferInstance
  let : QuasiSeparated ((Over.pullback t).obj X₀).hom :=
    MorphismProperty.baseChange_obj (P := @QuasiSeparated) t X₀ inferInstance
  let : LocallyOfFiniteType ((Over.pullback t).obj Y₀).hom :=
    MorphismProperty.baseChange_obj (P := @LocallyOfFiniteType) t Y₀ inferInstance
  let : QuasiCompact ((Over.pullback t).obj Y₀).hom :=
    MorphismProperty.baseChange_obj (P := @QuasiCompact) t Y₀ inferInstance
  let : QuasiSeparated ((Over.pullback t).obj Y₀).hom :=
    MorphismProperty.baseChange_obj (P := @QuasiSeparated) t Y₀ inferInstance
  let : IsSeparated f.left :=
    MorphismProperty.overPullbackMap (P := @IsSeparated) t f₀ inferInstance
  let : LocallyOfFiniteType f.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType) t f₀ inferInstance
  let : QuasiCompact f.left :=
    MorphismProperty.overPullbackMap (P := @QuasiCompact) t f₀ inferInstance
  exact systemOfBoundedQcqs ℓ D.k f

/-- The composite of the geometric-fibre maps has a coherent compactification system.
Source: Stacks Tag 0F7J, lemma-shriek-composition; latest blueprint
lem-zl-shriek-composition.proof (blueprint: new-p3-qcqs-composite-refinement-system).

Proof: `modelMap D h₀ ≫ modelMap D g₀` is the geometric-fibre map of `h₀ ≫ g₀`, which is
separated and of finite type. Apply the construction of `qcqsRefinementSystemExists` to it. -/
theorem qcqsCompositeRefinementSystemExists
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hℓ : ℓ ≠ D.p)
    {X₀ Z₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [QuasiSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [QuasiSeparated Z₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [QuasiSeparated Y₀.hom]
    (h₀ : X₀ ⟶ Z₀) (g₀ : Z₀ ⟶ Y₀)
    [IsSeparated h₀.left] [LocallyOfFiniteType h₀.left] [QuasiCompact h₀.left]
    [IsSeparated g₀.left] [LocallyOfFiniteType g₀.left] [QuasiCompact g₀.left] :
    RefinementSystemData ℓ (modelMap D h₀ ≫ modelMap D g₀) := by
  let : IsSeparated (h₀ ≫ g₀).left :=
    inferInstanceAs (IsSeparated (h₀.left ≫ g₀.left))
  let : LocallyOfFiniteType (h₀ ≫ g₀).left :=
    inferInstanceAs (LocallyOfFiniteType (h₀.left ≫ g₀.left))
  let : QuasiCompact (h₀ ≫ g₀).left :=
    inferInstanceAs (QuasiCompact (h₀.left ≫ g₀.left))
  simpa only [modelMap, Functor.map_comp, Over.comp_left] using
    qcqsRefinementSystemExists ℓ D hℓ (h₀ ≫ g₀)

end AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
