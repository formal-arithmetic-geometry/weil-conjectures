/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PodCompletionReindexCoherence

/-! # Completed-tensor composition for section-normalized ordinary reindexing

Source: blueprint prop-pod-dual-tate-data-compatibility, Steps 1 and 5;
Stacks 07A4, 0941. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]



/-- The completed-tensor equation on complete constructible inputs.
Source: blueprint prop-pod-dual-tate-data-compatibility, Steps 1 and 5;
Stacks 07A4, 0941 (blueprint: lem-pod-reindexing-composition-tensor-equation).

Proof: choose flat-term K-flat representatives P,Q of the two inputs. Their
reindexed complexes are good by each completion datum's good field. For each
positive quotient and each homogeneous summand of the total tensor, Generators
identifies T.tower with the tensor of the two quotient comparisons. Applying the
two reindexings successively to a pure tensor gives the same restrictions of
both factors as applying their composite, because hcomposition is Over.mapComp
on every original section. QuotientGenerators fixes the coefficient action as
well. Pure tensors generate each tensor module before sheafification, and the
maps respect the sheafification units; the generator equalities therefore give
whole degreewise maps. QuotientTransition shows these equalities commute with
the strict tower transitions. Apply all product projections and then RoosFst
and RoosSnd to obtain equality of the entire Roos chain maps, retaining the cone
shift. Localize this equality and substitute Model for the three tensor maps.
The representative comparisons and the factors for the intermediate reindexing
cancel by their inverse equations and naturality. This proves the displayed
equation on the represented inputs. The Naturality law transports it along the
two chosen representative isomorphisms to M and N. Neither faithfulness of
finite evaluations nor perfection of the inputs is used. Zero inputs and empty
schemes use the same generator argument. This statement does not assert the
ambient reduction or total-limit composition equation. -/
theorem podReindexingCompositionTensor
    (A : PodReindexFamily l E)
    (hcompletion : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletionReindex.Laws l E f (A.completion f))
    (htensor : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletedTensorReindex.Laws l E f (A.completion f) (A.tensor f))
    (hcomposition : ∀ {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V)
      [IsIso h] [IsIso f] (M : scalarReductionSource l E V) (U : Z.ProEt)
      (x : M.val.obj (op ((proEtaleIsoPostcompose (h ≫ f)).obj U))),
      ((A.composition h f).hom.app M).val.app (op U) x =
        M.val.map ((MorphismProperty.Over.mapComp (Q := ⊤)
          (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale f)).inv.app U).op x) :
    ∀ {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      [∀ z : Z, Invertible (l : Z.residueField z)],
      ∀ M N : sfIntegralConstructibleCategory l E V,
        (A.compositionDerived l E h f).hom.app
            ((integralCompletedTensor l E V).obj (M.obj,N.obj)) ≫
          (podOrdinaryReindex l E h).map ((A.tensor f).tensor M N).hom ≫
          ((A.tensor h).tensor ((A.constructible l E f).obj M)
            ((A.constructible l E f).obj N)).hom =
        ((A.tensor (h ≫ f)).tensor M N).hom ≫ (integralCompletedTensor l E Z).map
          (Prod.mkHom ((A.compositionDerived l E h f).hom.app M.obj)
            ((A.compositionDerived l E h f).hom.app N.obj)) := by sorry

end WeilConjectures
