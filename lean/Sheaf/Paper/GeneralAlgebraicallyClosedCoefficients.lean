/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
Authors: SHEAF group Q44
-/
module

public import Sheaf.Paper.SfAlgebraicallyClosedCoefficients
public import Mathlib.CategoryTheory.Pi.Basic

/-! # Common-stage coefficients over arbitrary schemes

Source: blueprint sec-smooth-purity/sk-def-sf-operations, order 1462;
main-20261015 sec-proetale-coefficients/sk-def-sf-operations, order 1821
(blueprint: def-weil-algebraically-closed-coefficients).

The datum-free intrinsic construction reuses the finite-field interface and its
legacy coefficient transports. Only preservation proofs mention p; choosing zero
there imposes no characteristic on Y. Tensor normalization identifies the resulting
transitions and comparisons with every finite-field specialization. Objects remain
literal pairs, with directed-colimit Hom groups and no Karoubi completion.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace WeilConjectures
namespace GeneralAlgebraicallyClosedCoefficients

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion
  coefficientInclusion_laws)

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

/-- The specified raw rational stage, using its equivalent small coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def Stage (E : Index l Ω) :=
  sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageCategory (E : Index l Ω) :
    Category (Stage l Ω Y E) :=
  inferInstanceAs (Category (sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y))

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stagePreadditive (E : Index l Ω) :
    Preadditive (Stage l Ω Y E) :=
  inferInstanceAs (Preadditive
    (sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y))

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageZero (E : Index l Ω) :
    HasZeroObject (Stage l Ω Y E) :=
  sfRationalConstructibleZero l (Coefficient.{u} l Ω E) Y

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageShift (E : Index l Ω) :
    HasShift (Stage l Ω Y E) ℤ :=
  sfRationalConstructibleShift l (Coefficient.{u} l Ω E) Y

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageShiftAdditive (E : Index l Ω) (n : ℤ) :
    (shiftFunctor (Stage l Ω Y E) n).Additive :=
  sfRationalConstructibleShiftAdditive l (Coefficient.{u} l Ω E) Y n

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stagePretriangulated (E : Index l Ω) :
    Pretriangulated (Stage l Ω Y E) :=
  sfRationalConstructiblePretriangulated l (Coefficient.{u} l Ω E) Y

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageTriangulated (E : Index l Ω) :
    IsTriangulated (Stage l Ω Y E) :=
  sfRationalConstructibleTriangulated l (Coefficient.{u} l Ω E) Y

/-- The characteristic parameter affects only preservation proofs, not scalar extension.
This identifies the datum-free transition with every allowed specialization before
forming the common-stage system, without choosing a finite-field datum.
Source: blueprint order 1821, scalar-transition clause
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: unfold sfConstructibleIntegralScalarExtension. For either parameter its object
is the same ambient completed extension with a proof of the same intrinsic predicate.
Proof irrelevance identifies these subtype objects; the full-subcategory morphism maps
are the same ambient maps. Functor extensionality gives the first equality. Substitute
that equality in sfRationalScalarExtension_existsUnique: the two specifications have
the same object formula and the same image of every pure tensor. Uniqueness gives the
second equality. The argument includes identity coefficient maps and zero objects and
uses no geometric hypothesis on Y. -/
theorem scalarExtension_parameter_independent
    (l : ℕ) [Fact l.Prime] (p q : ℕ) (hp : l ≠ p) (hq : l ≠ q)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u}) :
    sfConstructibleIntegralScalarExtension p l hp E L ι Y =
        sfConstructibleIntegralScalarExtension q l hq E L ι Y ∧
      sfRationalScalarExtension l E Y p hp L ι =
        sfRationalScalarExtension l E Y q hq L ι := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      exact ⟨rfl, rfl⟩

/-- The actual completed rational scalar transition, with both coefficient identifications.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def transition (E L : Index l Ω) (h : E ≤ L) :
    Stage l Ω Y E ⥤ Stage l Ω Y L :=
  sfRationalScalarExtension l (Coefficient.{u} l Ω E) Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h)

/-- The datum-free restricted completed integral tensor transition.
Only its preservation proof uses the zero instance of the redundant parameter.
Source: blueprint order 1821 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev integralTransition (E L : Index l Ω) (h : E ≤ L) :=
  sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
    (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h) Y

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The integral transition inherits the ordinary tensor shift through its canonical
quotient-completion comparison, not through an arbitrary exact-functor witness.
Source: blueprint order 1462, exact transition clause
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: conjugate the ordinary derived tensor shift by sfIntegralOrdinaryComparison.
The full intrinsic subcategory inherits the ambient shift. The inclusion's shift
comparisons identify its shifted objects with ambient shifts on both sides. Full
faithfulness lifts each component and its inverse. Naturality, the zero equation and
the addition equation follow from the ordinary ones by cancellation of the comparisons.
The formula fixes all components,
so extensionality of natural isomorphisms and proof irrelevance prove uniqueness. -/
theorem integralScalarCommShift_existsUnique
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u}) :
    ∃! c : (sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).CommShift ℤ,
      (fun [commInst : (sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).CommShift ℤ] ↦
        ∀ (n : ℤ) (K : sfIntegralConstructibleCategory l E Y),
          HEq
            ((((sfConstructibleIntegralScalarExtension 0 l
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).commShiftIso n).hom.app K).hom ≫
              ((sfIntegralConstructible l L Y).ι.commShiftIso n).hom.app
                ((sfConstructibleIntegralScalarExtension 0 l
                  (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj K))
            ((sfIntegralOrdinaryComparison l E L ι Y).inv.app
                ((shiftFunctor (sfIntegralConstructibleCategory l E Y) n).obj K) ≫
              (Functor.commShiftIso
                ((sfIntegralConstructible l E Y).ι ⋙ integralOrdinaryDerivedScalar l E L ι Y)
                n).hom.app K ≫
              (shiftFunctor (DerivedCategory (scalarReductionSource.{u, u} l L Y)) n).map
                ((sfIntegralOrdinaryComparison l E L ι Y).hom.app K)))
        (commInst := c) := by
  sorry

/-- The fixed ordinary-to-completed normalization of the integral transition shift.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance integralTransitionCommShift (E L : Index l Ω) (h : E ≤ L) :
    (integralTransition l Ω Y E L h).CommShift ℤ :=
  (integralScalarCommShift_existsUnique l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y).exists.choose

/-- The rational transition shift is uniquely fixed by localizing the normalized integral
shift. Source: blueprint order 1462, exact transition clause
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: tensor the integral components and inverses with one. On pure tensors, integral
naturality gives rational naturality; generation gives it on every Hom. The recorded
rational shift and localization comparison are normalized to the integral shift and
identity at one. Thus the displayed HEq gives the shift-by-one comparison. Iteration and
inverse shifts give all integer comparisons and their coherence. A coherent integer-shift
comparison is determined at one, which also proves uniqueness. -/
theorem transitionCommShift_existsUnique (E L : Index l Ω) (h : E ≤ L) :
    ∃! c : (transition l Ω Y E L h).CommShift ℤ,
      (fun [commInst : (transition l Ω Y E L h).CommShift ℤ] ↦
        ∀ K : Stage l Ω Y E,
          HEq (((transition l Ω Y E L h).commShiftIso (1 : ℤ)).hom.app K)
            ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) Y).map
              (((integralTransition l Ω Y E L h).commShiftIso (1 : ℤ)).hom.app K.obj)))
        (commInst := c) := by
  sorry

/-- The canonical, integral-image-normalized shift comparison of the rational transition.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance transitionCommShift (E L : Index l Ω) (h : E ≤ L) :
    (transition l Ω Y E L h).CommShift ℤ :=
  (transitionCommShift_existsUnique l Ω Y E L h).exists.choose

/-- Exactness for the normalized shift comparison on the recorded intrinsic rational stages.
Source: blueprint order 1462, exact transition clause
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: use the exactness argument of sfScalarExtension_exact_triangulated: the Roos cone
shift is conjugate through the quotient-completion comparison to the ordinary tensor
shift. Full intrinsic subcategories inherit distinguished triangles, and rationalization
has precisely the isomorphic integral image triangles. The preceding normalization is
that same comparison, so the finite scalar transition preserves distinguished triangles
including their connecting arrows. -/
@[instance]
theorem transitionExact (E L : Index l Ω) (h : E ≤ L) :
    (transition l Ω Y E L h).IsTriangulated := by
  sorry

/-- Additivity of the published intrinsic rational scalar-extension functor.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: the transition is the published sfRationalScalarExtension. Its named
additivity instance gives precisely the two equations for the recorded stage Hom groups. -/
@[instance]
theorem transitionAdditive (E L : Index l Ω) (h : E ≤ L) :
    (transition l Ω Y E L h).Additive := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      have hΩ := Padic.finiteCoefficientFields_properties l Ω
      exact hΩ.rec (fun _ _ ↦ sfRationalScalarExtension_additive l (Coefficient.{u} l Ω E) Y 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h))

/-- Balanced tensor composition followed by the specified coefficient-map equality.
This helper keeps the ordinary field structures explicit during size transport.
Source: blueprint order 1821 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def scalarAssociator
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
    (ι : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] M) (k : E →ₐ[Padic l] M)
    (h : j.comp ι = k) (Y : AlgebraicGeometry.Scheme.{u}) :
    sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙
        sfRationalScalarExtension l L Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j ≅
      sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M k :=
  sfRationalScalarComp l E L ι Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j ≪≫
    eqToIso (congrArg
      (sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M) h)

/-- The scalar associator is fixed by the published balanced-tensor comparison.
Source: blueprint order 1462, canonical composition clause
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: use sfRationalScalarComp, followed by equality transport along the actual
coefficient-inclusion composition law, exactly scalarAssociator. The stage
structures are the published rational structures, so this has the asserted endpoints.
HEq specifies the entire natural isomorphism and hence proves uniqueness. -/
theorem associator_existsUnique (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    ∃! a : transition l Ω Y E L h ⋙ transition l Ω Y L M k ≅
        transition l Ω Y E M (h.trans k),
      HEq a (scalarAssociator l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (Coefficient.{u} l Ω M) (coefficientInclusion l Ω E L h)
        (coefficientInclusion l Ω L M k) (coefficientInclusion l Ω E M (h.trans k))
        ((coefficientInclusion_laws l Ω).2 E L M h k) Y) := by
  refine ⟨_, HEq.rfl, ?_⟩
  intro a ha
  exact eq_of_heq ha

/-- The canonical scalar associator, with its tensor-generator normalization.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def associator (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    transition l Ω Y E L h ⋙ transition l Ω Y L M k ≅
      transition l Ω Y E M (h.trans k) :=
  (associator_existsUnique l Ω Y E L M h k).exists.choose

/-- The normalized scalar unit, transported through the coefficient identifications.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def unitor (E : Index l Ω) : transition l Ω Y E E le_rfl ≅
    𝟭 (Stage l Ω Y E) :=
  eqToIso (congrArg (sfRationalScalarExtension l
    (Coefficient.{u} l Ω E) Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω E))
    ((coefficientInclusion_laws l Ω).1 E)) ≪≫
    sfRationalScalarUnit l (Coefficient.{u} l Ω E) Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))

/-- The normalized tensor associators satisfy the stage-system cocycle.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: sfRationalScalar_coherence proves the tensor pentagon. The small
coefficient inclusions compose by coefficientInclusion_laws. Substitution gives the
displayed cocycle, including repeated fields and identity inclusions. -/
theorem associator_cocycle
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u})
    (E L M N : Padic.FiniteCoefficientFields l Ω)
    (h : E ≤ L) (k : L ≤ M) (m : M ≤ N) (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E) :
    (GeneralAlgebraicallyClosedCoefficients.transition l Ω Y M N m).map
        ((GeneralAlgebraicallyClosedCoefficients.associator l Ω Y E L M h k).hom.app K) ≫
        (GeneralAlgebraicallyClosedCoefficients.associator l Ω Y E M N (h.trans k) m).hom.app K =
      (GeneralAlgebraicallyClosedCoefficients.associator l Ω Y L M N k m).hom.app
          ((GeneralAlgebraicallyClosedCoefficients.transition l Ω Y E L h).obj K) ≫
        (GeneralAlgebraicallyClosedCoefficients.associator l Ω Y E L N h (k.trans m)).hom.app K :=
            by
  sorry

/-- The tensor transitions and associators uniquely determine the stage system.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: take T to be transition and assoc to be associator; associator_cocycle is
precisely the required coherence equation. Conversely the displayed equalities fix
all data fields of StageSystem; the remaining cocycle proof is proof irrelevant. -/
theorem stageSystem_existsUnique
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u})
    :
    ∃! S : StageSystem (GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y),
      (∀ (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L), S.T h =
          GeneralAlgebraicallyClosedCoefficients.transition l Ω Y E L h) ∧
      (∀ (E L M : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) (k : L ≤ M),
        HEq (S.assoc h k) (GeneralAlgebraicallyClosedCoefficients.associator l Ω Y E L M h k)) := by
  let S : StageSystem (Stage l Ω Y) :=
    { T := fun {E L} h ↦ transition l Ω Y E L h
      assoc := fun {E L M} h k ↦ associator l Ω Y E L M h k
      cocycle := fun h k m K ↦ associator_cocycle l Ω Y _ _ _ _ h k m K }
  refine ⟨S, ⟨fun _ _ _ ↦ rfl, fun _ _ _ _ _ ↦ HEq.rfl⟩, ?_⟩
  rintro ⟨T, a, c⟩ ⟨hT, ha⟩
  have ht : @T = @S.T := by
    funext E L h
    exact hT E L h
  cases ht
  have he : @a = @S.assoc := by
    funext E L M h k
    exact eq_of_heq (ha E L M h k)
  cases he
  rfl

/-- The stage system with exactly the specified tensor functors and associators.
The uniqueness specification fixes every data field, retaining a small opaque interface
for later elaboration of dependent representative types.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev stageSystem : StageSystem (Stage l Ω Y) :=
  (stageSystem_existsUnique l Ω Y).exists.choose

/-- The existing tensor functor as a transition of the uniquely fixed stage system.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev stageTransition (E L : Index l Ω) (h : E ≤ L) :=
  (stageSystem l Ω Y).T h

/-- The specified shift comparison transported by equality of the transition functors.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageTransitionCommShift (E L : Index l Ω) (h : E ≤ L) :
    (stageTransition l Ω Y E L h).CommShift ℤ :=
  cast (congrArg (fun F : Stage l Ω Y E ⥤ Stage l Ω Y L ↦ F.CommShift ℤ)
    ((stageSystem_existsUnique l Ω Y).exists.choose_spec.1 E L h).symm)
    (transitionCommShift l Ω Y E L h)

/-- Exactness of the prescribed stage transition.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: stageSystem_existsUnique identifies this functor and its shift comparison
with the specified tensor extension. Apply transitionExact. -/
@[instance]
theorem stageTransition_exact
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u})
    (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) :
    (GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω Y E L h).IsTriangulated := by
  sorry

/-- Additivity of the prescribed stage transition.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: equality of functors with transition reduces the claim to transitionAdditive. -/
@[instance]
theorem stageTransition_additive
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u})
    (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) :
    (GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω Y E L h).Additive := by
  unfold stageTransition
  rw [(stageSystem_existsUnique l Ω Y).exists.choose_spec.1 E L h]
  exact transitionAdditive l Ω Y E L h


/-- The upstream common-stage pair category, specialized to the specified rational stages.
Its objects are literal pairs, and no idempotents are adjoined.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev Pair := (stageSystem l Ω Y).PairCategory

/-- Cache the existing upstream category on the named concrete pair type.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance pairCategory : Category (Pair l Ω Y) :=
  inferInstanceAs (Category (stageSystem l Ω Y).PairCategory)

variable {l Ω Y}

/-- The directed index of common finite coefficient overfields of two pairs.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
abbrev Common (A B : Pair l Ω Y) :=
  {L : Index l Ω // A.stage ≤ L ∧ B.stage ≤ L}

/-- The compositum of the source and target fields supplies a common coefficient stage.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance commonNonempty (A B : Pair l Ω Y) : Nonempty (Common A B) :=
  ⟨⟨Padic.finiteCoefficientCompositum l Ω A.stage B.stage,
    (Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage⟩⟩

/-- Composita make the common-overfield poset directed while retaining both lower bounds.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance commonDirected (A B : Pair l Ω Y) :
    IsDirectedOrder (Common A B) where
  directed L M :=
    ⟨⟨Padic.finiteCoefficientCompositum l Ω L.val M.val,
        L.property.1.trans ((Padic.finiteCoefficientFields_properties l Ω).1 L.val M.val).1,
        L.property.2.trans ((Padic.finiteCoefficientFields_properties l Ω).1 L.val M.val).1⟩,
      (Padic.finiteCoefficientFields_properties l Ω).1 L.val M.val⟩

/-- Hom at one common coefficient field.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def StageHom (A B : Pair l Ω Y) (L : Common A B) :=
  ((stageTransition l Ω Y A.stage L.val L.property.1).obj A.obj ⟶
    (stageTransition l Ω Y B.stage L.val L.property.2).obj B.obj)

/-- Cache the abelian group of a stage Hom before forming the dependent colimit family.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageHomAddCommGroup (A B : Pair l Ω Y) (L : Common A B) :
    AddCommGroup (StageHom A B L) :=
  inferInstanceAs (AddCommGroup
    ((stageTransition l Ω Y A.stage L.val L.property.1).obj A.obj ⟶
      (stageTransition l Ω Y B.stage L.val L.property.2).obj B.obj))

/-- Extend the representative and conjugate by the specified associators.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def transport (A B : Pair l Ω Y) (L M : Common A B) (h : L ≤ M)
    (f : StageHom A B L) : StageHom A B M :=
  ((stageSystem l Ω Y).assoc L.property.1 h).inv.app A.obj ≫
    (stageTransition l Ω Y L.val M.val h).map f ≫
    ((stageSystem l Ω Y).assoc L.property.2 h).hom.app B.obj

/-- Transport is additive and preserves zero.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: scalar extension is additive. Left and right composition by each fixed
associator component are additive by preadditivity of the rational target stage. -/
theorem transport_additive
    {l : ℕ} [Fact l.Prime]
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    (A B : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y) (L M :
        GeneralAlgebraicallyClosedCoefficients.Common A B) (h : L ≤ M) :
    GeneralAlgebraicallyClosedCoefficients.transport A B L M h 0 = 0 ∧
      ∀ f g, GeneralAlgebraicallyClosedCoefficients.transport A B L M h (f + g) =
        GeneralAlgebraicallyClosedCoefficients.transport A B L M h f +
            GeneralAlgebraicallyClosedCoefficients.transport A B L M h g := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      constructor
      · simp only [transport, Functor.map_zero, Limits.comp_zero, Limits.zero_comp]
      · intro f g
        dsimp only [transport, stageHomAddCommGroup]
        rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

/-- The transition homomorphism of the directed Hom system.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def transportHom (A B : Pair l Ω Y) (L M : Common A B) (h : L ≤ M) :
    StageHom A B L →+ StageHom A B M where
  toFun := transport A B L M h
  map_zero' := (transport_additive A B L M h).1
  map_add' := (transport_additive A B L M h).2

/-- The actual representative transports form a directed system of abelian groups.
Source: blueprint order 1462, displayed Hom colimit
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: for a reflexive extension, the normalized tensor unit and the two unit coherence
laws identify the conjugated map with the original map. For two successive extensions,
expand transport and use the associator cocycle and naturality; the inner inverse
associators cancel. This gives identity and composition on each representative. -/
@[instance]
theorem transportSystem (A B : Pair l Ω Y) :
    DirectedSystem (StageHom A B) (fun {L M} h ↦ transportHom A B L M h) := by
  sorry

/-- Decidable equality is used only to realize Mathlib's algebraic direct limit.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance commonDecidableEq (A B : Pair l Ω Y) :
    DecidableEq (Common A B) := Classical.decEq _

/-- The actual abelian-group colimit, with no completion of its objects.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def ColimitHom (A B : Pair l Ω Y) :=
  AddCommGroup.DirectLimit (StageHom A B) (transportHom A B)

/-- The direct limit's abelian group structure, on the fixed Hom type.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance colimitHomGroup (A B : Pair l Ω Y) : AddCommGroup (ColimitHom A B) :=
  inferInstanceAs (AddCommGroup
    (AddCommGroup.DirectLimit (StageHom A B) (transportHom A B)))

/-- The class of a map over a common finite coefficient field.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def colimitOf (A B : Pair l Ω Y) (L : Index l Ω)
    (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f : StageHom A B ⟨L, hA, hB⟩) : ColimitHom A B :=
  AddCommGroup.DirectLimit.of (StageHom A B) (transportHom A B) ⟨L, hA, hB⟩ f

/-- The upstream quotient Hom has exactly the stated abelian-colimit coordinates.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: send each common-stage representative to its direct-limit class. The tensor
cocycle and unit law make transport a directed system; the quotient relation is exactly
equality after extension. The direct-limit representative criterion therefore makes
this map well-defined and bijective. Every Hom is represented, proving uniqueness. -/
theorem homCoordinates_existsUnique
    {l : ℕ} [Fact l.Prime]
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    (A B : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y) :
    ∃! e : (A ⟶ B) ≃ GeneralAlgebraicallyClosedCoefficients.ColimitHom A B,
      ∀ (L : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
        (f : GeneralAlgebraicallyClosedCoefficients.StageHom A B ⟨L, hA, hB⟩),
        e (StageSystem.PairCategory.mkHom L hA hB f) =
          GeneralAlgebraicallyClosedCoefficients.colimitOf A
            B L hA hB f := by
  sorry

/-- The canonical Hom coordinates, fixed on every common-stage representative.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def homCoordinates (A B : Pair l Ω Y) :=
  (homCoordinates_existsUnique A B).exists.choose

/-- The abelian group transported from the specified directed colimit.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance homAddCommGroup (A B : Pair l Ω Y) : AddCommGroup (A ⟶ B) :=
  (homCoordinates A B).addCommGroup

/-- The map represented at L, using the existing upstream quotient constructor.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev ofHom (A B : Pair l Ω Y) (L : Index l Ω)
    (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f : StageHom A B ⟨L, hA, hB⟩) : A ⟶ B :=
  StageSystem.PairCategory.mkHom L hA hB f

/-- The fixed composition is additive in each variable.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: represent the three maps at a common compositum. Colimit structure maps are
additive and stage composition is bilinear, giving both asserted equations. -/
theorem composition_bilinear
    {l : ℕ} [Fact l.Prime]
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    :
    (∀ (A B C : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y) (f f' : A ⟶ B) (g : B ⟶ C),
      (f + f') ≫ g = f ≫ g + f' ≫ g) ∧
    (∀ (A B C : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y) (f : A ⟶ B) (g g' : B ⟶ C),
      f ≫ (g + g') = f ≫ g + f ≫ g') := by
  sorry

/-- Preadditivity uses the actual colimit abelian groups.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance preadditive : Preadditive (Pair l Ω Y) where
  homGroup A B := homAddCommGroup A B
  add_comp A B C f f' g := composition_bilinear.1 A B C f f' g
  comp_add A B C f g g' := composition_bilinear.2 A B C f g g'

/-- The existing upstream inclusion of the actual rational finite stage.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev inclusion (E : Index l Ω) : Stage l Ω Y E ⥤ Pair l Ω Y :=
  (stageSystem l Ω Y).ι E

/-- The inclusion preserves the abelian-colimit addition.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: inclusion sends f to its normalized representative, and homCoordinates sends
that representative to its direct-limit class. Both normalization by fixed unit
components and the direct-limit structure maps are additive. -/
@[instance]
theorem inclusion_additive
    {l : ℕ} [Fact l.Prime]
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    (E : Padic.FiniteCoefficientFields l Ω) : (GeneralAlgebraicallyClosedCoefficients.inclusion E :
        GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E ⥤ _).Additive := by
  sorry

/-- Every class has a finite representative, and equality is equality at a later stage.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: composita make each common-overfield index nonempty and directed. The normalized
tensor unit and associator pentagon make transport an actual directed system. Apply
Mathlib's directed-colimit representation and zero-exactness criteria to the difference
of two representatives. This gives precisely equality after one further extension. -/
theorem representatives
    {l : ℕ} [Fact l.Prime]
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    (A B : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y) :
    (∀ f : A ⟶ B, ∃ (L : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
      (u : GeneralAlgebraicallyClosedCoefficients.StageHom A B ⟨L, hA, hB⟩), f =
          GeneralAlgebraicallyClosedCoefficients.ofHom A B L hA hB u) ∧
    (∀ (L M : GeneralAlgebraicallyClosedCoefficients.Common A B) (f :
        GeneralAlgebraicallyClosedCoefficients.StageHom A B L) (g :
        GeneralAlgebraicallyClosedCoefficients.StageHom A B M),
      GeneralAlgebraicallyClosedCoefficients.ofHom A B L.val L.property.1 L.property.2 f =
          GeneralAlgebraicallyClosedCoefficients.ofHom A B M.val M.property.1 M.property.2 g ↔
        ∃ (N : GeneralAlgebraicallyClosedCoefficients.Common A B) (hL : L ≤ N) (hM : M ≤ N),
          GeneralAlgebraicallyClosedCoefficients.transport A B L N hL f =
              GeneralAlgebraicallyClosedCoefficients.transport A B M N hM g) := by
  constructor
  · intro f
    induction f using StageSystem.PairCategory.hom_induction with
    | h L hA hB f => exact ⟨L, hA, hB, f, rfl⟩
  · intro L M f g
    constructor
    · intro e
      obtain ⟨N, hL, hM, he⟩ :=
        (StageSystem.PairCategory.mkHom_eq_mkHom_iff' f g).mp e
      exact ⟨⟨N, L.property.1.trans hL, L.property.2.trans hL⟩, hL, hM, he⟩
    · rintro ⟨N, hL, hM, he⟩
      exact (StageSystem.PairCategory.mkHom_eq_mkHom_iff' f g).mpr
        ⟨N.val, hL, hM, he⟩

/-- Stagewise object shift, with the coefficient field unchanged.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def shiftPair (n : ℤ) (A : Pair l Ω Y) : Pair l Ω Y :=
  ⟨A.stage, (shiftFunctor (Stage l Ω Y A.stage) n).obj A.obj⟩

/-- The shifted representative uses the prescribed scalar-extension shift comparison.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def shiftRepresentative (n : ℤ) (A B : Pair l Ω Y)
    (L : Index l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f : StageHom A B ⟨L, hA, hB⟩) :
    StageHom (shiftPair n A) (shiftPair n B) ⟨L, hA, hB⟩ :=
  ((stageTransition l Ω Y A.stage L hA).commShiftIso n).hom.app A.obj ≫
    (shiftFunctor (Stage l Ω Y L) n).map f ≫
    ((stageTransition l Ω Y B.stage L hB).commShiftIso n).inv.app B.obj

/-- The induced shift is specified on every object, representative and stage inclusion.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: shift each finite representative using shiftRepresentative. Exact scalar
extension and associator compatibility with shifts make this independent of stage.
The finite-stage shift units and addition isomorphisms descend componentwise; equality
and coherence may be checked after moving the finite diagrams to a common field.
The inclusion comparisons are identities on the displayed shifted pairs. Thus these
formulas determine the functors and their coherent comparisons on the generators.
Every object is literally in its own stage. The identity inclusion comparisons and
their coherence equations fix the zero and addition comparisons there, hence everywhere.
This proves uniqueness of the full shift structure, not just its object and arrow maps. -/
theorem shift_existsUnique :
    ∃! s : HasShift (Pair l Ω Y) ℤ,
      (fun [shiftInst : HasShift (Pair l Ω Y) ℤ] ↦
        (∀ n : ℤ, (shiftFunctor (Pair l Ω Y) n).Additive) ∧
        (∀ (n : ℤ) (A : Pair l Ω Y),
          (shiftFunctor (Pair l Ω Y) n).obj A = shiftPair n A) ∧
        (∀ (n : ℤ) (A B : Pair l Ω Y) (L : Index l Ω)
          (hA : A.stage ≤ L) (hB : B.stage ≤ L) (f : StageHom A B ⟨L, hA, hB⟩),
          HEq ((shiftFunctor (Pair l Ω Y) n).map (ofHom A B L hA hB f))
            (ofHom (shiftPair n A) (shiftPair n B) L hA hB
              (shiftRepresentative n A B L hA hB f))) ∧
        ∃ c : ∀ E : Index l Ω, (inclusion E : Stage l Ω Y E ⥤ _).CommShift ℤ,
          (fun [commInst : ∀ E : Index l Ω,
              (inclusion E : Stage l Ω Y E ⥤ _).CommShift ℤ] ↦
            ∀ (n : ℤ) (E : Index l Ω) (K : Stage l Ω Y E),
              HEq (((inclusion E : Stage l Ω Y E ⥤ _).commShiftIso n).hom.app K)
                (𝟙 ((inclusion E : Stage l Ω Y E ⥤ _).obj
                  ((shiftFunctor (Stage l Ω Y E) n).obj K)))) (commInst := c))
        (shiftInst := s) := by
  sorry

/-- The stagewise shift with the representative formula of shift_existsUnique.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance hasShift : HasShift (Pair l Ω Y) ℤ := shift_existsUnique.exists.choose

/-- Each induced integer shift is additive.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance shiftAdditive (n : ℤ) :
    (shiftFunctor (Pair l Ω Y) n).Additive := shift_existsUnique.exists.choose_spec.1 n

/-- The normalized exact-stage shift comparison, fixed to identity on shifted pairs.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance inclusionCommShift (E : Index l Ω) :
    (inclusion E : Stage l Ω Y E ⥤ _).CommShift ℤ :=
  shift_existsUnique.exists.choose_spec.2.2.2.choose E

/-- A stage zero object remains zero after forming directed Hom colimits.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: take the zero object at the bottom coefficient field. Every transition is exact
and therefore preserves zero. At every common field its Hom groups to and from any
object vanish. Their directed colimits vanish, giving the zero-object universal property. -/
theorem zero_exists : HasZeroObject (Pair l Ω Y) := by
  sorry

attribute [instance] zero_exists

/-- The canonical coefficient-stage identifications commute with shifts.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: on finite representatives this is scalar-extension shift compatibility and
sfRationalScalar_coherence. The normalized inclusion comparisons are
identities on shifted pairs. The cocycle equation identifies both composites. -/
@[instance]
theorem transitionIso_commShift
    {l : ℕ} [Fact l.Prime]
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) :
    NatTrans.CommShift ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).transIso h).hom ℤ
        := by
  sorry

/-- The recorded common-stage distinguished-triangle criterion.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev Distinguished (T : Triangle (Pair l Ω Y)) : Prop :=
  (stageSystem l Ω Y).CommonStageDistinguished T

/-- The unique pretriangulation supplied by the common-stage Verdier theorem.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance pretriangulated : Pretriangulated (Pair l Ω Y) :=
  (StageSystem.commonStage_verdier_existsUnique (stageSystem l Ω Y)).exists.choose

/-- The Verdier axiom for the specified common-stage triangles.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance isTriangulated : IsTriangulated (Pair l Ω Y) :=
  (StageSystem.commonStage_verdier_existsUnique (stageSystem l Ω Y)).exists.choose_spec.2.1

/-- Each actual rational finite-stage inclusion is exact.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance inclusion_exact (E : Index l Ω) :
    (inclusion E : Stage l Ω Y E ⥤ _).IsTriangulated :=
  (StageSystem.commonStage_verdier_existsUnique (stageSystem l Ω Y)).exists.choose_spec.2.2 E

/-- The triangle criterion, exposing the finite-field-of-definition clause.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: this is the distinguished-set clause of commonStage_verdier_existsUnique
for the actual scalar-extension stage system. -/
theorem distinguished_iff
    {l : ℕ} [Fact l.Prime]
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    (T : Triangle (GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y)) :
    T ∈ distTriang (GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y) ↔
        GeneralAlgebraicallyClosedCoefficients.Distinguished T := by
  exact (StageSystem.commonStage_verdier_existsUnique
    (stageSystem l Ω Y)).exists.choose_spec.1 T

/-- A specified cone over L gives exactly the recorded common-stage cone, including
its second and connecting arrows and the literal cone pair (L,C).
Source: blueprint order 1462, common-stage cone clause
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: apply the exact stage inclusion at L to the displayed distinguished triangle.
The canonical isoToStage identifications identify its first two objects with A and B.
Conjugate the arrows by these identifications and the specified inclusion shift
comparison. This is precisely commonStageCone, whose first arrow is the represented u,
second arrow is the represented i with the normalized identity extension, and third
arrow is p followed by the inverse scalar shift comparison. Its third object is the
literal pair (L,C). Isomorphism closure preserves distinguishedness. -/
theorem commonStage_cone (A B : Pair l Ω Y) (L : Index l Ω)
    (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (C : Stage l Ω Y L) (u : A.toStage hA ⟶ B.toStage hB)
    (i : B.toStage hB ⟶ C) (p : C ⟶ (A.toStage hA)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk u i p ∈ distTriang (Stage l Ω Y L)) :
    (stageSystem l Ω Y).commonStageCone A B L hA hB C u i p ∈
      distTriang (Pair l Ω Y) := by
  sorry

end GeneralAlgebraicallyClosedCoefficients

/-- The algebraically closed coefficient category is the pair category itself.
No Karoubi envelope occurs: its objects are finite-field pairs and its Hom groups are
canonically the displayed directed colimits.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev generalAlgebraicallyClosedConstructibleCategory
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u}) :=
  GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y

namespace GeneralAlgebraicallyClosedCoefficients

universe d
variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

/-- The proof parameter in preservation cannot change the tensor functor.
Source: blueprint order 1821, scalar transitions
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: the integral restrictions have the same ambient object and arrow maps;
only their membership proofs differ, hence they agree by proof irrelevance.
The two rational functors therefore satisfy the identical exists-unique tensor
specification of sfRationalScalarExtension_existsUnique. Its uniqueness identifies
these functors on objects and all pure tensors, hence on every morphism. -/
theorem specialization_transition (E L : AlgebraicallyClosedCoefficients.Index l Ω)
    (h : E ≤ L) :
    transition l Ω Y E L h = SfAlgebraicallyClosedCoefficients.transition D l hl Ω Y E L h := by
  have hΩ := Padic.finiteCoefficientFields_properties l Ω
  exact hΩ.rec (fun _ _ ↦ rfl)

/-- The normalized associator and identity comparison specialize canonically.
Source: blueprint order 1821, canonical composition clause
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: the ordinary balanced tensor associator and multiplication unit contain
no p. The quotient-completion comparisons are the very same uniquely normalized
comparisons. Proof irrelevance identifies the integral restrictions. Their
exists-unique component specifications identify the integral comparisons and
then their rational images. Substitution through coefficientInclusion_laws
identifies the displayed stage associators and units, also for repeated fields. -/
theorem specialization_comparisons :
    (∀ (E L M : AlgebraicallyClosedCoefficients.Index l Ω) (h : E ≤ L) (k : L ≤ M),
      HEq (GeneralAlgebraicallyClosedCoefficients.associator l Ω Y E L M h k)
        (SfAlgebraicallyClosedCoefficients.associator D l hl Ω Y E L M h k)) ∧
    (∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
      HEq (unitor l Ω Y E) (SfAlgebraicallyClosedCoefficients.unitor D l hl Ω Y E)) := by
  sorry

/-- The normalized scalar shift comparisons agree under specialization.
Source: blueprint order 1821, exact transitions
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: the integral comparison is fixed by the same ordinary tensor shift and
quotient-completion normalization on every object, independently of the proof
parameter. Uniqueness identifies the two integral CommShift structures. The
rational shift comparison is uniquely their localized image at one, with its
coherent integer iterates, so its uniqueness gives the displayed identification. -/
theorem specialization_transitionShift
    (E L : AlgebraicallyClosedCoefficients.Index l Ω) (h : E ≤ L) :
    HEq (transitionCommShift l Ω Y E L h)
      (SfAlgebraicallyClosedCoefficients.transitionCommShift D l hl Ω Y E L h) := by
  sorry

/-- Equality of the complete normalized stage data, not merely its carriers.
Source: blueprint order 1821, finite-stage pair construction
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: both Stage families reduce to sfRationalConstructibleCategory on the
same small coefficient fields. specialization_transition and the associator
clause of specialization_comparisons identify every data field of StageSystem.
Its remaining cocycle field is a proof. Alternatively apply the uniqueness
clause of stageSystem_existsUnique to the old system. -/
theorem specialization_stageSystem :
    stageSystem l Ω Y = SfAlgebraicallyClosedCoefficients.stageSystem D l hl Ω Y := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      have hOld :=
        (SfAlgebraicallyClosedCoefficients.stageSystem_existsUnique D l hl Ω Y).exists.choose_spec
      apply (stageSystem_existsUnique l Ω Y).unique
      · exact (stageSystem_existsUnique l Ω Y).exists.choose_spec
      · constructor
        · intro E L h
          exact (hOld.1 E L h).trans (specialization_transition D l hl Ω Y E L h).symm
        · intro E L M h k
          exact (hOld.2 E L M h k).trans
            ((specialization_comparisons D l hl Ω Y).1 E L M h k).symm


/-- The canonical identification is equality transport of the normalized systems.
It preserves all pairs and representative maps; no arbitrary equivalence is chosen.
Source: blueprint order 1821 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def specialization :
    Pair l Ω Y ≌ SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y :=
  Pi.eqToEquivalence (fun S : StageSystem (Stage l Ω Y) ↦ S.PairCategory)
    (specialization_stageSystem D l hl Ω Y)

/-- Specialization fixes the literal coefficient pair and every representative.
Source: blueprint order 1821, pair and Hom clauses
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: eliminate specialization_stageSystem. Pi.eqToEquivalence then reduces
to the identity equivalence. The object formula is reflexivity, and the map
formula is reflexivity after the assumed HEq identifies the finite maps. -/
theorem specialization_pairs :
    (∀ (E : AlgebraicallyClosedCoefficients.Index l Ω) (K : Stage l Ω Y E),
      (specialization D l hl Ω Y).functor.obj ⟨E, K⟩ = ⟨E, K⟩) ∧
    (∀ (A B : Pair l Ω Y) (L : AlgebraicallyClosedCoefficients.Index l Ω)
      (hA : A.stage ≤ L) (hB : B.stage ≤ L)
      (f : StageHom A B ⟨L, hA, hB⟩)
      (g : SfAlgebraicallyClosedCoefficients.StageHom
        (⟨A.stage, A.obj⟩ : SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y)
        (⟨B.stage, B.obj⟩ : SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y) ⟨L, hA, hB⟩),
      HEq f g → HEq ((specialization D l hl Ω Y).functor.map (ofHom A B L hA hB f))
        (SfAlgebraicallyClosedCoefficients.ofHom
          (⟨A.stage, A.obj⟩ : SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y)
          (⟨B.stage, B.obj⟩ : SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y) L hA hB g)) := by
  sorry

/-- Equality transport intertwines the actual directed Hom transition maps.
Source: blueprint order 1821, displayed Hom colimit
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: expand transport as associator inverse, scalar image, associator.
The equality of stage systems identifies all three factors. The assumption
identifies the input representatives, proving the formula at every later stage.
It consequently induces the canonical map of the abelian direct limits. -/
theorem specialization_transport (A B : Pair l Ω Y) (L M : Common A B) (h : L ≤ M)
    (f : StageHom A B L)
    (g : SfAlgebraicallyClosedCoefficients.StageHom
      (⟨A.stage, A.obj⟩ : SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y)
      (⟨B.stage, B.obj⟩ : SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y)
      ⟨L.val, L.property⟩) (hfg : HEq f g) :
    HEq (transport A B L M h f)
      (SfAlgebraicallyClosedCoefficients.transport
        (⟨A.stage, A.obj⟩ : SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y)
        (⟨B.stage, B.obj⟩ : SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y)
        ⟨L.val, L.property⟩ ⟨M.val, M.property⟩ h g) := by
  sorry

/-- The canonical Hom coordinates agree under specialization, including every colimit class.
Source: blueprint order 1821, displayed Hom colimit
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: specialization_stageSystem identifies the coefficient systems. On a finite
representative, specialization_pairs gives the identical representative and
specialization_transport gives identical transition maps. The two homCoordinates
specifications therefore give the same direct-limit class. Every morphism has a finite
representative by representatives, which proves the displayed heterogeneous equality. -/
theorem specialization_homCoordinates (A B : Pair l Ω Y) (f : A ⟶ B) :
    HEq
      (SfAlgebraicallyClosedCoefficients.homCoordinates
        ((specialization D l hl Ω Y).functor.obj A)
        ((specialization D l hl Ω Y).functor.obj B)
        ((specialization D l hl Ω Y).functor.map f))
      (homCoordinates A B f) := by
  sorry

/-- Specialization is additive for the prescribed Hom colimit group laws.
Source: blueprint order 1821, abelian Hom colimit
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: represent two morphisms over a common field. specialization_pairs
identifies their images with the same finite maps. Addition is stage addition
on both sides and specialization_transport respects the same directed system.
Every morphism has a representative, giving the additive-functor equations. -/
@[instance]
theorem specialization_additive : (specialization D l hl Ω Y).functor.Additive := by
  sorry

/-- The shift identification is uniquely normalized to identity on shifted pairs.
Source: blueprint order 1821, stagewise shift
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: both integral shift comparisons are conjugates of the same ordinary
tensor comparison, and both rational comparisons are their uniquely specified
localizations. Thus specialization carries shiftRepresentative to the old
shiftRepresentative. The identity components on shifted pairs are natural by
that formula. The stagewise zero and addition constraints coincide by their
identity inclusion normalizations. These give a coherent CommShift structure;
its components are all specified, proving uniqueness. -/
theorem specialization_commShift_existsUnique :
    ∃! c : (specialization D l hl Ω Y).functor.CommShift ℤ,
      (fun [commInst : (specialization D l hl Ω Y).functor.CommShift ℤ] ↦
        ∀ (n : ℤ) (A : Pair l Ω Y),
          HEq (((specialization D l hl Ω Y).functor.commShiftIso n).hom.app A)
            (𝟙 ((shiftFunctor (SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y) n).obj
              ((specialization D l hl Ω Y).functor.obj A)))) (commInst := c) := by
  sorry

/-- The identity-normalized coherent shift comparison for specialization.
Source: blueprint order 1821 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance specialization_commShift :
    (specialization D l hl Ω Y).functor.CommShift ℤ :=
  (specialization_commShift_existsUnique D l hl Ω Y).exists.choose

/-- Specialization preserves and reflects the specified distinguished triangles.
Source: blueprint order 1821, common-stage triangles
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: each distinguished triangle is isomorphic to a distinguished finite-stage
image. specialization_pairs identifies the finite image arrows, and the
identity-normalized shift comparison identifies its connecting arrow. The same
argument with inverse equality transport gives reflection. The old and new
Verdier pretriangulations have precisely these common-stage distinguished sets. -/
theorem specialization_distinguished (T : Triangle (Pair l Ω Y)) :
    T ∈ distTriang (Pair l Ω Y) ↔
      (specialization D l hl Ω Y).functor.mapTriangle.obj T ∈
        distTriang (SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y) := by
  sorry

/-- The canonical specialization is exact for the normalized shift comparison.
Source: blueprint order 1821, triangulated category
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: apply the forward implication of specialization_distinguished to each
triangle. This is the IsTriangulated condition for specialization_commShift. -/
@[instance]
theorem specialization_exact : (specialization D l hl Ω Y).functor.IsTriangulated := by
  constructor
  intro T hT
  exact (specialization_distinguished D l hl Ω Y T).mp hT

end GeneralAlgebraicallyClosedCoefficients
end WeilConjectures

