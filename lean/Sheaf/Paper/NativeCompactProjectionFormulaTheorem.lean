module

public import Sheaf.Paper.NativeCompactProjectionFormula

/-! # Compact projection formula theorem

Source: blueprint latest, fix-lem-tensor-adjunction.proof.md, Step 1, second Hom
bijection (blueprint: lem-sf-derived-weil-compact-projection-formula).

## Main statements

* `AlgebraicGeometry.WeilComplex.native_compact_projection_formula`: the unchanged
  compactification projection formula, separated from its existing definitions so
  its future proof may import the native proper-projection theorem without a cycle.

All comparison and compactification definitions are reused from their original module.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.WeilComplex

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Compact projection for arbitrary bounded constructible derived Weil inputs.
The isomorphism is in the full bounded constructible category, natural in both
variables. Its underlying ambient map is exactly the chosen-compactification
composite: proper counit mate, open tensor comparison, balanced compositor.
All comparison data occur in the conclusion, with their representative and unit
normalizations, rather than as additional assumptions.

Source: blueprint latest, fix-lem-tensor-adjunction.proof.md, Step 1, second Hom
bijection (blueprint: lem-sf-derived-weil-compact-projection-formula).

Proof:
1. Let X --j--> Z --p--> Y be the framework's chosen compactification.
By lem-sf-native-weil-basic-comparisons, exact extension by zero sends M to a
bounded constructible A. Its cohomology is j! H^r(M), and extending a finite
stratification by the closed complement with rank zero preserves constructibility.
The proper map p is finite type, so Z is finite type by
lem-sfb-finite-type-composition-base-change. The diagonal of Z factors through
Z times_Y Z: the first factor is closed by properness and the second is the base
change of the closed diagonal of Y. Closed immersions compose. Thus Z is separated;
lem-pod-separated-finite-type-base-change gives the same geometric domain.
2. Apply lem-sf-native-proper-projection-realization to (A,T). Its normalized
balanced comparison gives C and its counit transpose is nativeProjectionProperMate.
Apply lem-sf-native-open-derived-tensor to (M,p* T), using its normalized gamma.
Compose alpha with Rp*(gamma), then Rp*j!(1 tensor the balanced compositor).
This is precisely the formula below and the compactification defining Rf!.
Each map and inverse is an actual derived Weil arrow, natural in both variables.
3. Pullback preservation (lem-sf-native-weil-pullback-star-preservation), tensor
closure (lem-sf-derived-weil-tensor-hom-adjunction), and compact-support
preservation (lem-sf-native-weil-shriek-triangulated) put both sides in WC^der(Y).
Fullness restricts the ambient isomorphism, its inverse, and its naturality
identities. No lisse or degree-zero condition on T was used. -/
theorem native_compact_projection_formula :
    ∃ (C : ProEtaleWeilSheaf.NativeProjectionTensorComparison k₀ l
          (nativeProjectionCompactification k₀ f).g)
      (s : ProEtaleWeilSheaf.NativeOpenTensorData k₀ l
          (nativeProjectionCompactification k₀ f).i)
      (d : ProEtaleWeilSheaf.NativeOpenDerivedTensorData k₀ l
          (nativeProjectionCompactification k₀ f).i s)
      (c : OpenTensorPresentation (ProEtaleWeilSheaf k₀ l X)
          (ProEtaleWeilSheaf k₀ l (nativeProjectionCompactification k₀ f).Z))
      (pi : nativeCompactProjectionLeft k₀ l f ≅ nativeCompactProjectionRight k₀ l f),
      ProEtaleWeilSheaf.NativeOpenPresentationCompatibility k₀ l
          (nativeProjectionCompactification k₀ f).i s d c ∧
      ∀ (M : WeilComplex k₀ l X) (T : WeilComplex k₀ l Y),
        (pi.hom.app (M, T)).hom =
          ProEtaleWeilSheaf.nativeProjectionProperMate k₀ l
            (nativeProjectionCompactification k₀ f).g C
            ((ProEtaleWeilSheaf.nativeOpenExtension k₀ l
              (nativeProjectionCompactification k₀ f).i).obj M.obj) T.obj ≫
          (ProEtaleWeilSheaf.lowerStar k₀ l
            (nativeProjectionCompactification k₀ f).g).rightDerivedFunctor.map
            (d.gamma.hom.app (M.obj,
              (ProEtaleWeilSheaf.nativeOpenPull k₀ l
                (nativeProjectionCompactification k₀ f).g).obj T.obj)) ≫
          (ProEtaleWeilSheaf.lowerStar k₀ l
            (nativeProjectionCompactification k₀ f).g).rightDerivedFunctor.map
            ((ProEtaleWeilSheaf.nativeOpenExtension k₀ l
              (nativeProjectionCompactification k₀ f).i).map
              ((ProEtaleWeilSheaf.nativeDerivedTensor k₀ l X).map
                (Prod.mkHom (𝟙 M.obj) ((nativeProjectionPullComp k₀ l f).hom.app T.obj)))) := by
  sorry


end AlgebraicGeometry.WeilComplex
