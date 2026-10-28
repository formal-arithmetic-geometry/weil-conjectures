/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PodCompletionReindexCoherence

/-! # Total-limit composition for section-normalized ordinary reindexing

Source: blueprint prop-pod-dual-tate-data-compatibility, Steps 1 and 5;
Stacks 03EL, 0941. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]



/-- The total-limit equation, on arbitrary ambient coefficient systems.
Source: blueprint prop-pod-dual-tate-data-compatibility, Steps 1 and 5;
Stacks 03EL, 0941 (blueprint: lem-pod-reindexing-composition-limit-equation).

Proof: represent a coefficient system by a strict complex C. RestrictedGenerators
identifies the comparison between reindexing its restricted tower and restricting
its sequence pullback with the actual sectionwise adjunction-unit map. The unit
normalization of the strict sequence compositor makes the two iterated restricted
maps equal, including their transition morphisms. The ordinary compositor is fixed
on all original sections by hcomposition. Apply every product projection to the
product maps in the three Roos comparisons: both composite paths are restriction
along this same Over.mapComp arrow. RoosFst and RoosSnd then give equality on both
coordinates of the mapping cocone of 1-s, hence equality of the entire chain maps.
The intermediate source/target Roos models are identified using their computes
normalization on a simultaneous K-injective resolution. Naturality extends this
identification to C, so these model isomorphisms cancel in the pasted square.
Substitute the three LimitModel formulas and localize the strict square. The
localization factors are natural and their composition comparison is precisely
the one in A.compositionDerived and integralComparisonSystemComposition.
Every derived system is isomorphic to a localized complex; naturality transports
the resulting equality to it. No finite evaluation is treated as faithful.
For the zero complex or an empty scheme the same projection and coordinate
formulas apply. This statement assumes no tensor law and proves no reduction
or tensor composition equation. -/
theorem podReindexingCompositionLimit
    (A : PodReindexFamily l E)
    (hcompletion : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletionReindex.Laws l E f (A.completion f))
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
      ∀ N : coefficientSequenceDerived l E V,
        (A.compositionDerived l E h f).hom.app ((coefficientSequenceLimit l E V).obj N) ≫
          (podOrdinaryReindex l E h).map ((A.completion f).limit.hom.app N) ≫
          (A.completion h).limit.hom.app ((integralComparisonDerivedSequencePullback l E f).obj N) =
        (A.completion (h ≫ f)).limit.hom.app N ≫
          (coefficientSequenceLimit l E Z).map
            ((integralComparisonSystemComposition l E h f).hom.app N) := by sorry

end WeilConjectures
