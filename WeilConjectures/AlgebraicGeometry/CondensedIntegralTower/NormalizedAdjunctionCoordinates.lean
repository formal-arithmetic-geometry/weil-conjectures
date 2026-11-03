/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.CondensedNormalizedTowers

/-! # Coordinates of the normalized reduction adjunction

Source: latest blueprint, `sk-lem-sp-tower/sk-lem-sp-tower-equivalence.md` and
`sk-prop-sp-integral-adjunction-bijection.md` (blueprint: def-sp-normalized-adjunction-coordinates).
The statement uses the current condensed coefficient ring pulled back from the point.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedIntegralTower

namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The projection is the scalar transpose of precisely the evaluated counit.
Source: sk-lem-sp-tower-equivalence.proof.md, Counit paragraph
(blueprint: def-sp-normalized-adjunction-coordinates).
Proof: expand the extension/restriction Hom correspondence and the three whiskered
transformations defining the projection. Functoriality and associativity identify
both expressions, without choosing or changing an adjunction. -/
theorem derivedLimitProjection_transpose (D : Model l E T) (adj : D.red ⊣ D.rlim)
    (n : ℕ) (C : DerivedTowers l E T) :
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      ((upperStarFromPoint T).map (quotient l E n))).homEquiv _ _
        ((D.levels n).inv.app (D.rlim.obj C) ≫ (evaluation l E T n).map
          (adj.counit.app C)) =
      (derivedLimitProjection l E T D adj n).app C := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, derivedLimitProjection,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]

/-- Localization carries the ordinary Hom correspondence to the derived one on chain maps.
Source: sk-lem-sp-tower-equivalence, Adjunction paragraph
(blueprint: def-sp-normalized-adjunction-coordinates). -/
def DerivedHomNormalized (D : Model l E T) (adjunction : D.red ⊣ D.rlim) : Prop :=
  ∀ (P : CochainComplex (AdicCompletion.Modules l E T) ℤ)
    (I : CochainComplex (Towers l E T) ℤ)
    (f : (D.ordinaryRed.mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
    adjunction.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)
        (D.redCounit.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
        ((D.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P I f) ≫
        D.limitUnit.app I

/-- The unit on representatives is the derived ordinary unit.
Source: sk-lem-sp-tower-equivalence, Unit paragraph
(blueprint: def-sp-normalized-adjunction-coordinates). -/
def DerivedUnitNormalized (D : Model l E T) (adjunction : D.red ⊣ D.rlim) : Prop :=
  ∀ P : CochainComplex (AdicCompletion.Modules l E T) ℤ,
    DerivedCategory.Q.map
        ((D.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      D.limitUnit.app ((D.ordinaryRed.mapHomologicalComplex (.up ℤ)).obj P) =
    adjunction.unit.app (DerivedCategory.Q.obj P) ≫ D.rlim.map (D.redCounit.app P)

/-- Unit normalization and the full chain-map Hom normalization are equivalent.
Source: sk-lem-sp-tower-equivalence.proof.md, Adjunction paragraph
(blueprint: def-sp-normalized-adjunction-coordinates).
Proof: specialize the Hom formula to the identity for the forward implication.
For the converse, expand the two Hom transposes, insert the unit identity, and
use naturality of the total right-derived comparison on the given chain map. -/
theorem derivedHomNormalized_iff_unit (D : Model l E T) (adj : D.red ⊣ D.rlim) :
    DerivedHomNormalized l E T D adj ↔ DerivedUnitNormalized l E T D adj := by
  constructor
  · intro h P
    have hh := h P ((D.ordinaryRed.mapHomologicalComplex (.up ℤ)).obj P) (𝟙 _)
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit] at hh
    erw [DerivedCategory.Q.map_id, Category.comp_id,
      (D.ordinaryLimit.mapHomologicalComplex (.up ℤ)).map_id, Category.comp_id] at hh
    exact hh.symm
  · intro h P I f
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    rw [Functor.map_comp, ← Category.assoc, ← h P, Category.assoc]
    have hn := D.limitUnit.naturality f
    change DerivedCategory.Q.map
        ((D.ordinaryLimit.mapHomologicalComplex (.up ℤ)).map f) ≫ D.limitUnit.app I =
      D.limitUnit.app ((D.ordinaryRed.mapHomologicalComplex (.up ℤ)).obj P) ≫
        D.rlim.map (DerivedCategory.Q.map f) at hn
    rw [← hn, DerivedCategory.Q.map_comp, Category.assoc]

/-- The normalized Hom correspondence fixes the derived counit on representatives.
Source: sk-lem-sp-tower-equivalence.proof.md, Adjunction paragraph
(blueprint: def-sp-normalized-adjunction-coordinates).
Proof: evaluate the correspondence on the ordinary counit. Its ordinary transpose
is the identity. Apply the inverse derived Hom correspondence; its formula is the
derived reduction of the limit comparison followed by the actual derived counit. -/
theorem derivedCounit_of_transpose (D : Model l E T) (adj : D.red ⊣ D.rlim)
    (h : DerivedHomNormalized l E T D adj) (I : CochainComplex (Towers l E T) ℤ) :
    D.red.map (D.limitUnit.app I) ≫ adj.counit.app (DerivedCategory.Q.obj I) =
      D.redCounit.app ((D.ordinaryLimit.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((D.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).counit.app I) := by
  have hh := h ((D.ordinaryLimit.mapHomologicalComplex (.up ℤ)).obj I) I
    ((D.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).counit.app I)
  have hid : (D.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv _ _
      ((D.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).counit.app I) = 𝟙 _ := by
    rw [Adjunction.homEquiv_unit, Adjunction.right_triangle_components]
  erw [hid, DerivedCategory.Q.map_id, Category.id_comp] at hh
  have hi := congrArg (adj.homEquiv _ _).symm hh
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit] at hi
  exact hi.symm

/-- The derived projections agree with the ordinary limit projections.
Source: sk-lem-sp-tower-equivalence, Counit paragraph
(blueprint: def-sp-normalized-adjunction-coordinates). -/
def LimitProjectionsNormalized (D : Model l E T) (adjunction : D.red ⊣ D.rlim) : Prop :=
  ∀ (n : ℕ) (I : CochainComplex (Towers l E T) ℤ),
    D.limitUnit.app I ≫
      (derivedLimitProjection l E T D adjunction n).app (DerivedCategory.Q.obj I) ≫
      (Mod.comap ((upperStarFromPoint T).map (quotient l E n))).mapDerivedCategory.map
        (internalEvaluationFactor l E T n I).hom ≫
      (Mod.comap ((upperStarFromPoint T).map (quotient l E n))).mapDerivedCategoryFactors.hom.app
        (((ordinaryInternalEvaluation l E T n).mapHomologicalComplex (.up ℤ)).obj I) =
    DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (ordinaryLimitProjection l E T D n) (.up ℤ)).app I)

/-- The unit is the canonical Roos completion augmentation.
Source: sk-lem-sp-tower-equivalence, Unit paragraph
(blueprint: def-sp-normalized-adjunction-coordinates). -/
def CompletionUnitNormalized (D : Model l E T) (adjunction : D.red ⊣ D.rlim) : Prop :=
  ∀ (K : Integral l E T)
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ)
    (e : DerivedCategory.Q.obj P ≅ K),
    (HomologicalComplex.quasiIso (AdicCompletion.Modules l E T) (.up ℤ)).kFlat P →
      ∃ c : D.rlim.obj (D.red.obj K) ≅ DerivedCategory.Q.obj (AdicCompletion.roos l E T P),
        adjunction.unit.app K ≫ c.hom = AdicCompletion.completionMap l E T K P e

end AlgebraicGeometry.ProEtale.CondensedIntegralTower
