/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence
public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.Paper.ProEtaleFiniteModelStalks
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.AlgebraicGeometry.ProEtaleInverseImageStalk
import Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk
import Mathlib.Algebra.Module.FinitePresentation
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.Paper.CondensedConstantConstructibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.AlgebraicGeometry.Sites.Proetale

/-! # Finite constant models and finite-stalk constructibility

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-integral-criterion-reductions.proof.md, second paragraph; Stacks Tags 099Y and 09AJ
(blueprint: lem-pe-finite-coefficient-model-comparison).

The coefficient encoding is the normalized section-action equivalence already supplied by
FiniteDiscreteOrdinary. The witness clauses retain each stratum and each cover. Arbitrary
constant values on empty covering objects are discarded before asserting their finiteness.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The finite geometric-stalk clause of the existing ordinary constructibility definition,
without its separate local-constancy clause. No field characteristic is excluded.
Source: Stacks Tag 09AJ, definition-constructible
(blueprint: lem-pe-finite-coefficient-model-comparison). -/
def ordinaryFiniteStalks (T : Scheme.{u}) (F : Ordinary A T) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T),
    Finite (Scheme.proEtaleGeometricModuleStalk x (Scheme.proEtaleConstantRing T A) F)

/-- The ordinary local condition on one stratum, using the recorded localized-site
local constancy and actual geometric stalks, rather than etale origin or finite Tor amplitude.
Source: Stacks Tag 09AJ, definition-constructible
(blueprint: lem-pe-finite-coefficient-model-comparison). -/
def ordinaryFiniteLocalCondition (T : Scheme.{u}) (F : Ordinary A T) : Prop :=
  Scheme.IsLocallyConstantProEtaleModuleSheaf T A F ∧ ordinaryFiniteStalks A T F

/-- Finite constant ordinary models on a specified cover. Module pullback uses the canonical
constant-coefficient comparison, and the constant model is simultaneous ring/module
sheafification. This spells out the ordinary side of the same-cover comparison.
Source: Stacks Tag 099Y, lemma-compare-locally-constant
(blueprint: lem-pe-finite-coefficient-model-comparison). -/
def ordinaryFiniteCoverModels (T : Scheme.{u}) (F : Ordinary A T)
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage T) : Prop :=
  ∀ i : C.I₀, ∃ P : ModuleCat.{u + 1} (ULift.{u + 1} A), Finite P ∧
    Nonempty (Scheme.proEtaleConstantModulePullback (C.f i) A F ≅
      Scheme.proEtaleConstantModuleSheaf (C.X i) A P)

/-- Bounded constructibility in the intrinsic ordinary constant-ring module category:
standard bounded cohomology and the existing finite-stalk constructibility predicate in
every degree. This is the ordinary target of the comparison, with no Tor restriction.
Source: blueprint sk-def-sfb-constructible, final paragraph; Stacks Tag 09AL
(blueprint: lem-pe-finite-coefficient-model-comparison). -/
def ordinaryIntrinsicBoundedConstructible [Finite A] (T : Scheme.{u}) :
    ObjectProperty (Scheme.proEtaleDerivedCategory T A) :=
  DerivedCategory.TStructure.t.bounded ⊓ fun K ↦ ∀ q : ℤ,
    Scheme.IsConstructibleProEtaleModuleSheaf T A
      ((DerivedCategory.homologyFunctor (Ordinary A T) q).obj K)

/-- All clauses of the finite-coefficient comparison for the specified normalized encoding.
The stratum clauses are pointwise, so zero strata and empty strata are included. The global
ordinary predicate retains its recorded convention of a positive number of strata.
Source: blueprint sk-prop-integral-criterion-reductions.proof.md, second paragraph;
Stacks Tags 099Y and 09AJ (blueprint: lem-pe-finite-coefficient-model-comparison). -/
structure FiniteCoefficientModelComparison [Finite A] (X : Scheme.{u}) (e : Encoding A X) :
    Prop where
  /-- Constructibility agrees for the original sheaf and its section-action image. -/
  constructible : ∀ M : Internal A X,
    IsConstantModelConstructible (coefficient A) X M ↔
      Scheme.IsConstructibleProEtaleModuleSheaf X A (e.ordinary.functor.obj M)
  /-- On every fixed stratification, exactly the same strata satisfy the local conditions. -/
  strata : ∀ (M : Internal A X) (S : Scheme.Stratification X),
    (∀ i : Fin S.n, HasFiniteConstantLocalModel (coefficient A) (S.domain i)
      ((CondensedRing.upperStar (coefficient A) (S.immersion i)).obj M)) ↔
    ∀ i : Fin S.n, ordinaryFiniteLocalCondition A (S.domain i)
      (Scheme.proEtaleConstantModulePullback (S.immersion i) A (e.ordinary.functor.obj M))
  /-- A finite model cover remains the very same finite model cover in ordinary coordinates. -/
  covers : ∀ (M : Internal A X) (S : Scheme.Stratification X) (i : Fin S.n)
      (C : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain i)),
    HasFiniteConstantLocalModelOnCover (coefficient A)
      ((CondensedRing.upperStar (coefficient A) (S.immersion i)).obj M) C ↔
    ordinaryFiniteCoverModels A (S.domain i)
      (Scheme.proEtaleConstantModulePullback (S.immersion i) A (e.ordinary.functor.obj M)) C
  /-- Every localized-site trivialization is retained on its nonempty members. This uses
  the full index universe of the recorded ordinary local-constancy definition. -/
  discardEmpty : ∀ (M : Internal A X) (S : Scheme.Stratification X) (i : Fin S.n)
      (I : Type (u + 1)) (W : I → (S.domain i).ProEt)
      (f : ∀ j : I, W j ⟶ Scheme.ProEt.mk (𝟙 (S.domain i)))
      (P : I → ModuleCat.{u + 1} (ULift.{u + 1} A)),
    Presieve.ofArrows W f ∈ (Scheme.ProEt.precoverage (S.domain i)).coverings _ →
    (∀ j : I,
      Nonempty ((Scheme.proEtaleConstantModulePullback (S.immersion i) A
        (e.ordinary.functor.obj M)).over (W j) ≅
          Scheme.proEtaleConstantModuleSheafOver (S.domain i) A (W j) (P j))) →
    ordinaryFiniteStalks A (S.domain i)
      (Scheme.proEtaleConstantModulePullback (S.immersion i) A (e.ordinary.functor.obj M)) →
    (Presieve.ofArrows (fun j : {j : I // Nonempty (W j).left} ↦ W j.val)
      (fun j ↦ f j.val) ∈ (Scheme.ProEt.precoverage (S.domain i)).coverings _) ∧
    ∀ j : I, Nonempty (W j).left → Finite (P j) ∧
      ∃ Q : Mod Ab.{u + 1} (scalarRingObj (coefficient A)),
        Mod.IsFinitelyPresented (scalarRingObj (coefficient A)) Q ∧
        Nonempty ((CondensedRing.upperStar (coefficient A) (W j).hom).obj
          ((CondensedRing.upperStar (coefficient A) (S.immersion i)).obj M) ≅
            (finiteConstantScalarExtension (coefficient A) (W j).left).obj Q)
  /-- The actual termwise derived equivalence preserves and reflects each vanishing interval. -/
  intervals : ∀ (K : DerivedCategory (Internal A X)) (a b : ℤ), a ≤ b →
    (∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor (Internal A X) q).obj K)) ↔
    (∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor (Ordinary A X) q).obj
        (e.ordinaryDerived.functor.obj K)))
  /-- Both bounded-constructible membership tests agree, without a finite-Tor condition. -/
  boundedConstructible : ∀ K : DerivedCategory (Internal A X),
    constantModelBoundedConstructible (coefficient A) X K ↔
      ordinaryIntrinsicBoundedConstructible A X (e.ordinaryDerived.functor.obj K)
  /-- The equivalence on the full subcategories is induced by the specified ambient functor. -/
  boundedEquivalence : ∃ d : ConstantModelBoundedConstructible (coefficient A) X ≌
      (ordinaryIntrinsicBoundedConstructible A X).FullSubcategory,
    Nonempty (d.functor ⋙ (ordinaryIntrinsicBoundedConstructible A X).ι ≅
      (constantModelBoundedConstructible (coefficient A) X).ι ⋙ e.ordinaryDerived.functor)

/-- Finite discrete coefficients identify finite constant local models with locally constant
finite-stalk constructibility, retaining strata, covers after deletion of empty objects, and
all cohomological vanishing intervals under the induced bounded-constructible equivalence.

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-integral-criterion-reductions.proof.md, second paragraph
(blueprint: lem-pe-finite-coefficient-model-comparison).

Proof following the seven DAG steps:
1. Use lem-sf-module-object-ordinary-coefficient-equivalence for the normalized Encoding.
Its ringIso is the canonical constant-coefficient identification. The section-action
construction retains the abelian sheaf. By lem-sfb-internal-module-operations-transport,
restriction along each stratum immersion and covering arrow agrees under this encoding.
2. Over a finite ring A, a finitely presented module is a quotient of finite A^n and hence
finite. Conversely the finite free module A^P surjects onto a finite module P. Its kernel R
is finite, so A^R maps onto that kernel, giving a finite presentation. Finite generation
likewise agrees with finiteness of the underlying set. This includes zero rings.
3. With discrete finite coefficients, the scalar local model is A_U tensor_{A_U} P_U,
isomorphic to P_U by a tensor m mapping to am and inverse m mapping to 1 tensor m. These
restriction-compatible maps respect the balancing relations, retaining the same cover.
4. Finite constant values on a cover give local constancy and finite geometric stalks by
lem-weil-pbc-proetale-finite-model-stalks, on each original stratum.
5. Conversely discard the empty objects of any ordinary trivializing cover. They contribute
no points or affine opens to its covering condition, so the remaining family still covers.
Choose a geometric point on each remaining object. By
lem-sfb-proetale-object-inverse-image-restriction the localized restriction is inverse image.
Then lem-pur-proetale-inverse-image-stalk and lem-weil-proetale-constant-sheaf-stalk identify
the constant value with a finite stalk. Step 2 makes this value finitely presented, and
step 3 supplies the internal finite scalar model on precisely that cover member.
6. Apply steps 4 and 5 on each stratum of any finite constructible locally closed
stratification. On a Noetherian scheme the global and affine-local conventions agree.
The empty scheme is allowed: an empty stratum imposes no condition, and a single empty
stratum also meets the ordinary definition's positive-number convention. Zero sheaves and
empty covering families on the empty scheme are included.
7. The termwise extension of the exact equivalence commutes with cohomology: it preserves
kernels, images and cokernels, and the inverse gives reflection of zero cohomology. Thus
every vanishing interval is unchanged. Step 6 identifies every cohomology sheaf's
constructibility. Restrict the equivalence and its inverse to the full bounded
constructible subcategories; their unit and counit give the asserted equivalence and its
commuting comparison with the ambient functor. No completeness or Tor bound is used.
-/
theorem finiteCoefficientModelComparison [Finite A] [DiscreteTopology A]
    (X : Scheme.{u}) [IsNoetherian X] :
    ∃ e : Encoding A X, FiniteCoefficientModelComparison A X e := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
