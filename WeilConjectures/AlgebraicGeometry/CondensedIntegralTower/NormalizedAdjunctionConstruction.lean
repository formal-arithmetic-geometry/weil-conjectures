/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.NormalizedAdjunctionCoordinates

/-! # Canonical reduction/limit adjunction and completion unit
Source: sk-lem-sp-tower-equivalence, Adjunction and Unit paragraphs.
(blueprint: lem-sp-normalized-adjunction-construction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- Consecutive coefficient quotient maps agree sectionwise.
Source: the quotient diagram in the Adjunction paragraph
(blueprint: lem-sp-normalized-adjunction-construction).
Proof: evaluate on a section and then at a point; both maps are the same quotient map. -/
theorem normalized_quotient_step (n : ℕ) :
    quotient l E (n + 1) ≫ step l E n = quotient l E n := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  ext U x
  apply ULift.ext
  apply ContinuousMap.ext
  intro z
  rfl

/-- The section scalar map preserves composition.
Source: the internal/section comparison in the Adjunction paragraph
(blueprint: lem-sp-normalized-adjunction-construction).
Proof: both sides act by composition on every section and element. -/
theorem normalized_sectionScalarMap_comp
    {R S V : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}}
    [MonObj R] [MonObj S] [MonObj V]
    [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj V]
    (a : R ⟶ S) [IsMonHom a] (b : S ⟶ V) [IsMonHom b] :
    CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T)
        (a ≫ b) =
      CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) a ≫
        CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) b := by
  ext U x
  rfl

/-- The actual compatible structural maps into the ell-power quotient diagram.
Source: sk-lem-sp-tower-equivalence.proof.md, Adjunction paragraph
(blueprint: lem-sp-normalized-adjunction-construction). -/
def coefficientQuotients :
    (Functor.const ℕᵒᵖ).obj
        (CategoryTheory.InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology T) (AdicCompletion.ring l E T)) ⟶ rings l E T :=
  NatTrans.ofOpSequence
    (fun n ↦ CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T) ((upperStarFromPoint T).map (quotient l E n))) (by
        intro n
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
          rings, Functor.ofOpSequence_map_homOfLE_succ]
        simp only [← normalized_sectionScalarMap_comp, ← Functor.map_comp,
          normalized_quotient_step])

/-- The unbounded tensor/limit adjunction, with normalized Hom and completion unit.
Source: sk-lem-sp-tower-equivalence.proof.md, Adjunction and Unit paragraphs
(blueprint: lem-sp-normalized-adjunction-construction).

Proof: form the section-ring diagram of the quotient maps, and apply the ringed
sequence projection derived adjunction. Conjugate its base module category by the
internal/section equivalence. The tensor-generator comparison identifies ordinary
levels and their quotient transitions. Uniqueness of universal left derived functors
identifies evaluated reduction with internal derived scalar extension, preserving
its counit. The normalized derived Hom correspondence gives the displayed unit
identity. The separate proved projection compatibility theorem then determines
the actual derived projections. Repleteness gives
exact countable products, so these right-derived limits are computed by the Roos
fiber. Write ell = u pi^e. Quotient ideals agree at indices en; the quotient and
transition maps agree under these identifications. Cofinal restriction of the
uniformizer tower to these indices is a quasi-isomorphism of Roos fibers carrying
the augmentation to the ell-power augmentation. Its inverse, followed by the
right-derived limit comparison, identifies the actual unit with the specified
uniformizer completionMap. Naturality transports this equality from Q(P) to K
along the supplied representative isomorphism. -/
theorem normalized_adjunction_construction :
    ∃ D : Model l E T, ∃ adj : D.red ⊣ D.rlim,
      DerivedHomNormalized l E T D adj ∧
      CompletionUnitNormalized l E T D adj := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedIntegralTower
