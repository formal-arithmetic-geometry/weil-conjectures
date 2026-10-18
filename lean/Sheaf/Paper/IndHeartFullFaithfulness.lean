/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.Limits.Indization.Category
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.ObjectProperty.Ind
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.SheafTensorStructure
import Sheaf.Paper.CoefficientHeartSmall
import Sheaf.Paper.ConstructibleExtContinuity
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian

/-!
# Constructible sheaves are finitely presented and realize the ind-heart fully faithfully

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ind-heart/
`det-ind-heart-full-faithfulness` (blueprint: det-ind-heart-full-faithfulness).

The coefficient ring objects carry their canonical ring-object structures: the one of
`Profinite.continuousMapRingObj E` resp. `Profinite.padicAlgClRingObj ℓ`, and on
`Λ_X = condensedRingObj Λ X` the one transported along `upperStarFromPoint X` (the scoped
instance `Functor.monObjObj` of `CategoryTheory.Obj`). Small diagrams are indexed by categories
in `Type (u + 1)`, the hom universe of the module category, as in `CategoryTheory.Ind`
(size convention def-weil-size-convention).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The two assertions of det-ind-heart-full-faithfulness for a condensed coefficient ring
object `Λ` and a scheme `X`, in `Mod_{Λ_X}` (internal modules over `Λ_X = p_X^* Λ`):
1. every constructible module (sk-def-sfb-constructible) is finitely presentable, i.e.
`Hom(C, -)` preserves all small filtered colimits;
2. there is a functor `Φ : Ind(Cons(X, Λ)) ⥤ Mod_{Λ_X}` which is the realization: its
restriction along `Ind.yoneda` is isomorphic to the inclusion of the constructible modules,
and it sends the canonical colimit of the presentation diagram of every ind-object to an actual
colimit; this `Φ` is full and faithful, and its essential image is `ObjectProperty.ind.{u + 1}`
of the constructible modules, i.e. `IndCons(X, Λ)`.
Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ind-heart/
`det-ind-heart-full-faithfulness`, clauses 1 and 2 (blueprint: det-ind-heart-full-faithfulness). -/
def IndHeartFullFaithfulnessAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) : Prop :=
  (∀ C : ObjectProperty.FullSubcategory (IsConstantModelConstructible Λ X),
    IsFinitelyPresentable.{u + 1}
      (C.1 : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))) ∧
  ∃ Φ : CategoryTheory.Ind (ObjectProperty.FullSubcategory
      (IsConstantModelConstructible Λ X)) ⥤
    CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
    Nonempty (CategoryTheory.Ind.yoneda ⋙ Φ ≅
      ObjectProperty.ι (IsConstantModelConstructible Λ X)) ∧
    (∀ Z : CategoryTheory.Ind (ObjectProperty.FullSubcategory
        (IsConstantModelConstructible Λ X)),
      Nonempty (IsColimit
        (Φ.mapCocone (colimit.cocone
          ((CategoryTheory.Ind.presentation Z).F ⋙ CategoryTheory.Ind.yoneda))))) ∧
    Φ.Full ∧ Φ.Faithful ∧
    (∀ M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X),
      Φ.essImage M ↔ ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) M)

/-- Constructible coefficient modules are finitely presented, and their ordinary ind-category
realizes fully faithfully as the filtered-colimit closure in the ambient module category, for
both coefficient choices `Λ = E` (a finite extension of `ℚ_ℓ` inside `\bar ℚ_ℓ`) and
`Λ = \bar ℚ_ℓ`, on a Noetherian scheme `X` (locally Noetherian and quasi-compact).
Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ind-heart/
`det-ind-heart-full-faithfulness` (blueprint: det-ind-heart-full-faithfulness).

Proof (the node's five steps):
1. The size convention makes the pro-etale site small; strong monoidal sheafification
(det-def-sfb-sheaf-tensor-structure) gives the hypotheses of
def-weil-pbc-internal-abelian-sheaf-module-equivalence, so internal modules over `Λ_X` are
equivalent to sectionwise modules, which form an abelian category with all small colimits
(lem-pur-ringed-site-grothendieck-abelian, Stacks 03DA, 03DB). By
det-lem-coefficient-heart-small the constructible modules have a small skeleton.
2. For constructible `C` and a small filtered diagram `M_j`, regard all as complexes in degree
zero; the constructible clause of sk-lem-constructible-ext-continuity with `q = 0` and
lem-weil-pbc-derived-single-fully-faithful (Stacks 06XS) identify
`colim Hom(C, M_j) → Hom(C, colim M_j)` with a bijection: `C` is finitely presented.
3. For filtered diagrams `C_i`, `D_j` with colimits `A`, `B`, send the class of `f : C_i → D_j`
to `d_j f`; filteredness gives the representative description of the colimit of Hom groups, it
is bijective onto `Hom(C_i, B)` by step 2, and the colimit universal property
(def-weil-pbc-category-colimit, Stacks 002F, 05PW) identifies the limit over `i` with
`Hom(A, B)`.
4. The representative map preserves identities and composition by the cocone identities and
uniqueness of factorizations, so it is a functor, fully faithful by step 3.
5. Its essential image is by construction the replete closure of small filtered colimits of
constructible objects, namely `ObjectProperty.ind` of the constructible property. -/
theorem indHeart_fullFaithfulness
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X] :
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      IndHeartFullFaithfulnessAssertions (Profinite.continuousMapRingObj.{u} E) X) ∧
    IndHeartFullFaithfulnessAssertions (Profinite.padicAlgClRingObj.{u} ℓ) X := by
  sorry

end AlgebraicGeometry.ProEtale
