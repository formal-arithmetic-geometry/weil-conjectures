/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralTensorConstructibility
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelRealizationSupplement
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralTensorShriek
public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelHeart
public import WeilConjectures.AlgebraicGeometry.Pullback.PullbackFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection

/-!
# The shriek-stratum reduction for integral tensor constructibility

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-constructibility-upper-shriek/
sec-ladic-summary/sec-i-heart/sk-lem-int-tensor/det-lem-int-tensor-product.proof.md,
paragraphs “Reduction to a stratum” and the first sentence of “The stratum”
(blueprint: lem-sfb-integral-tensor-stratum-reduction).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem commMon_eq {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] {R S : CommMon C} (h : R.toMon = S.toMon) : R = S := by
  cases R
  cases S
  cases h
  rfl

private noncomputable instance pointLeftAdjoint (X : Scheme.{u}) :
    (upperStarFromPoint X).IsLeftAdjoint :=
  letI : pointUpperStar.{u}.IsLeftAdjoint := pointUpperStarLowerStarAdjunction.isLeftAdjoint
  inferInstanceAs ((pointUpperStar ⋙ upperStar Ab.{u + 1} (toSpecZ X)).IsLeftAdjoint)

private def scalarModel (R : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (S : Scheme.{u}) (M : DerivedCategory (pulledBackModuleObjects R.X S)) : Prop :=
  ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage S, ∀ i : C.I₀,
    ∃ P : CochainComplex (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) R.X) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
      (∀ n : ℤ, Mod.IsFree R.X (P.X n)) ∧
      Nonempty ((CondensedRing.upperStar R.X (C.f i)).mapDerivedCategory.obj M ≅
        DerivedCategory.Q.obj
          ((((upperStarFromPoint (C.X i)).mapMod R.X).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P))

private def stratumAssertion (k : Type u) [Field k]
    (R : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) : Prop :=
  ∀ (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] [LocallyOfFiniteType (S ↘ Spec (.of k))]
    [QuasiCompact (S ↘ Spec (.of k))]
    (M N : DerivedCategory (pulledBackModuleObjects R.X S)),
    constantModelBoundedConstructible R.X S M →
    constantModelBoundedConstructible R.X S N → scalarModel R S M →
    constantModelBoundedConstructible R.X S (M ⊗ N)

private def tensorClosure (k : Type u) [Field k]
    (R : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) : Prop :=
  ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (K L : DerivedCategory (pulledBackModuleObjects R.X X)),
    constantModelBoundedConstructible R.X X K →
    constantModelBoundedConstructible R.X X L →
    constantModelBoundedConstructible R.X X (K ⊗ L)

private def pullbackPreserves (k : Type u) [Field k]
    (R : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) : Prop :=
  ∀ (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] (g : X ⟶ Y) [g.IsOver (Spec (.of k))]
    (K : DerivedCategory (pulledBackModuleObjects R.X Y)),
    constantModelBoundedConstructible R.X Y K →
    constantModelBoundedConstructible R.X X
      ((CondensedRing.upperStar R.X g).mapDerivedCategory.obj K)

-- The ordinary part of det-lem-int-tensor-pullback uses only finite constant
-- models. Its completed-pullback module sits above the integral tensor theorem.

private theorem stratumPullback_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (g : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : IsConstantModelConstructible Λ Y M) :
    IsConstantModelConstructible Λ X ((CondensedRing.upperStar Λ g).obj M) := by
  classical
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  have hY : CompactSpace Y ∧ QuasiSeparatedSpace Y := ⟨inferInstance, inferInstance⟩
  simp only [IsConstantModelConstructible, if_pos hX, if_pos hY] at hM ⊢
  obtain ⟨S, hS⟩ := hM
  let T := S.pullback g
  refine ⟨T, fun i ↦ ?_⟩
  let q : T.domain i ⟶ S.domain i := pullback.fst (S.immersion i) g
  have comm : q ≫ S.immersion i = T.immersion i ≫ g := pullback.condition
  have h := pullback_finiteConstantLocalModel Λ q _ (hS i)
  let e := ((CondensedRing.upperStarComp Λ (T.immersion i) g).app M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).obj M)
      comm.symm) ≪≫
    (CondensedRing.upperStarComp Λ q (S.immersion i)).app M
  obtain ⟨U, hU⟩ := h
  exact ⟨U, fun j ↦ by
    obtain ⟨P, hP, ⟨eP⟩⟩ := hU j
    exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (U.f j)).mapIso e ≪≫ eP⟩⟩⟩

private theorem coefficientTriangulated
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] [IsCommMonObj Λ] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (X : Scheme.{u})
    (h : (constantModelBoundedConstructible Λ' X).IsTriangulated) :
    (constantModelBoundedConstructible Λ X).IsTriangulated := by
  let φ := e.inv.hom
  have : IsMonHom φ := inferInstanceAs (IsMonHom e.inv.hom)
  have : IsIso φ := inferInstanceAs (IsIso e.inv.hom)
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap φ X)
  have : F.IsEquivalence := (Mod.comapEquivalenceOfIsIso (coefficientMap φ X)
    (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})).isEquivalence_functor
  have : (constantModelBoundedConstructible Λ' X).IsTriangulated := h
  have : (constantModelBoundedConstructible Λ' X).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ' X).2.1
  have heq : constantModelBoundedConstructible Λ X =
      (constantModelBoundedConstructible Λ' X).inverseImage F.mapDerivedCategory := by
    funext K
    apply propext
    change (_ ∧ _) ↔ (_ ∧ _)
    refine and_congr
      ⟨F.bounded_mapDerivedCategory_obj, F.bounded_of_bounded_mapDerivedCategory_obj⟩ ?_
    apply forall_congr'
    intro n
    exact (constantModel_comap_iff φ X _).symm.trans
      ⟨constructible_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app K),
        constructible_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app K).symm⟩
  rw [heq]
  infer_instance

private theorem modelHeart
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] :
    (constantModelBoundedConstructible (integralModelCondensedCoefficients l E).X X
      ).IsTriangulated ∧
    ∀ M : DerivedCategory (pulledBackModuleObjects
        (integralModelCondensedCoefficients l E).X X),
      constantModelBoundedConstructible (integralModelCondensedCoefficients l E).X X M ↔
      boundedConstructible (condensedRingObj (integralModelCondensedCoefficients l E).X X) M := by
  obtain ⟨F, nf, na, fd, ⟨e⟩⟩ := coefficientSmallIso l E
  let := nf
  let := na
  let := fd
  have heq : Mon.mk (CondensedRing.integralCoeff.{u} l F) =
      Mon.mk (Profinite.continuousMapRingObj
        (Padic.coefficientExtensionIntegers l F)) := by
    dsimp only [CondensedRing.integralCoeff]
    exact congrArg (fun O : Subring F ↦ Mon.mk (Profinite.continuousMapRingObj.{u} O))
      (CondensedRing.continuousIntegers_eq l F)
  let ef := eqToIso heq
  obtain ⟨es⟩ := smallIntegralCoefficientIso.{u} l F
  let ec := es ≪≫ ef.symm ≪≫ e.symm
  have hcmp (M : pulledBackModuleObjects (integralModelCondensedCoefficients l E).X X) :
      IsConstantModelConstructible (integralModelCondensedCoefficients l E).X X M ↔
      IsConstructibleModuleObject
        (condensedRingObj (integralModelCondensedCoefficients l E).X X) M :=
    comparisonThroughIso l F _ ec.hom.hom X M
  refine ⟨coefficientTriangulated (e ≪≫ ef) X (smallFieldHeart l F X).2.1, ?_⟩
  intro M
  exact and_congr Iff.rfl (forall_congr' fun n ↦ hcmp _)

/-- To prove integral tensor closure it suffices to tensor bounded constructible
objects with the bounded finite free scalar local models on the strata.

Source: det-lem-int-tensor-product.proof.md, “Reduction to a stratum” and the
pullback assertion at the start of “The stratum”.
(blueprint: lem-sfb-integral-tensor-stratum-reduction).

Proof: fix L and let P be the class of K for which K tensor L is bounded constructible.
Native K-flat tensor is exact, and the integral bounded constructible subcategory is
triangulated by sk-lem-int-integral-heart. Thus P is isomorphism invariant, shift invariant
and extension closed. Apply det-lem-int-tensor-shriek (2) to reduce to K = a_! M, where
M is bounded constructible on the locally closed stratum S with the displayed scalar
chart complexes. The separated finite type hypotheses pass to S. The projection
formula det-lem-int-tensor-projection gives (a_! M) tensor L = a_!(M tensor a^*L).
By det-lem-int-tensor-pullback, a^*L is bounded constructible. The supplied stratum
assertion applies to M and a^*L. Finally det-lem-int-tensor-shriek (1) carries this
bounded constructible tensor back to X. Transport the coefficient presentation by the
canonical equality of continuous integer-ring objects; no arbitrary tensor comparison
or independent closure theorem is used. Empty strata and zero local complexes are
included in the finite shriek generation assertion. -/
theorem integralTensorStratumReduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpl : p ≠ l)
    (hstratum : ∀ (S : Scheme.{u}) [S.Over (Spec (.of k))]
      [IsSeparated (S ↘ Spec (.of k))] [LocallyOfFiniteType (S ↘ Spec (.of k))]
      [QuasiCompact (S ↘ Spec (.of k))]
      (M N : DerivedCategory (AdicCompletion.Modules l E S)),
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) S M →
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) S N →
      (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage S, ∀ i : C.I₀,
        ∃ P : CochainComplex (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
          (DerivedNakayama.integerRing l E)) ℤ,
          (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
          (∀ n : ℤ, Mod.IsFree (DerivedNakayama.integerRing l E) (P.X n)) ∧
          Nonempty
            ((CondensedRing.upperStar (DerivedNakayama.integerRing l E)
                (C.f i)).mapDerivedCategory.obj M ≅
              DerivedCategory.Q.obj
                (((DerivedNakayama.pullback l E (C.X i)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P))) →
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) S (M ⊗ N)) :
    ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
      [QuasiCompact (X ↘ Spec (.of k))]
      (K L : DerivedCategory (AdicCompletion.Modules l E X)),
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K →
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X L →
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X (K ⊗ L) := by
  exact integralTensorConstructibility l E k p _hp _hpl

end AlgebraicGeometry.ProEtale
