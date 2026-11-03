/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeWeilInduction.NativeWeilInductionComparisonData
import WeilConjectures.AlgebraicGeometry.NativeWeilInduction.NativeWeilHeartProperties
import WeilConjectures.AlgebraicGeometry.NativeWeilInduction.NativeWeilProperNormalization
import WeilConjectures.AlgebraicGeometry.NativeWeilInduction.NativeWeilInductionSummands
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Normalized native derived Weil induction comparison -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor

attribute [instance] AlgebraicGeometry.Compactification.over

namespace AlgebraicGeometry.NativeWeilInduction

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

variable {X Y : Scheme.{u}} [X.Over (Spec (.of k₀))] [Y.Over (Spec (.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k₀))] (c : Compactification f)

/-- The normalized native forgetting and induction comparison on ordinary unbounded
 derived categories. The recurrence for c fixes all integer exchanges from the actual
 native first exchange, including negative indices. The natural map kappa is the
 transpose under the specified derived free adjunction, rather than a chosen isomorphism.

Source: blueprint `cor-coef-verdier-weil-equivariance.proof.md`, final sentence;
`lem-fix-weil-operations.proof.md`, first two paragraphs; Stacks 079P, 08BJ, 070Y.
(blueprint: lem-sf-native-weil-derived-induction-comparison)

Proof plan:
1. Identify internal native modules with ring-sheaf modules and apply the ring-sheaf
Grothendieck theorem. Frobenius reindexes the site by an automorphism, with the identity
on locally finite coefficient functions. The inverse reindexing proves equivalence.
Exactness commutes with cohomology; constructible pullback preserves bounded
constructibles. The inverse-image localizing property then proves preservation of Loc.
2. Apply fixedPairDerivedForgetComparison and freeDerivedWeilResolution to these hearts.
The free exact left adjoint implies that forgetting preserves K-injectives. Termwise
coproducts compute derived coproducts, so derived forgetting preserves small sums and
cohomology detects its conservativity. This uses ordinary unbounded derived categories.
3. Pro-etale open localization identifies the native open operation with ringed-slice
extension by zero and identifies restricted coefficients literally. The slice adjunction
gives exactness. Direct image is the right adjoint to module inverse image, hence left
exact. Forgetting creates finite limits and colimits, so the lifts have the same properties.
The exact-functor and right-derived triangulated theorems give triangulated F and FW.
4. Apply common derived resolutions and the normalized K-injective exact-square theorem
with r=UZ, s=UY and H=p*. The native lift square is equality on objects and morphisms.
Both models on a K-injective Weil complex are p* UZ J, so the comparison is identity on
that model. Whisker with the exact termwise open identity to obtain comparison (beta).
5. Derive the native Frobenius exchanges using the exact-equivalence-square theorem.
Frobenius preserves K-injectives as right adjoint to its exact inverse, fixing the proper
exchange on these representatives. Set c0=identity and iterate c1 and its inverse. The
successor recurrence determines every negative and positive iterate and its naturality.
6. Localize the structure natural isomorphism. On a Weil resolution of open extension,
the native lift has structure p*(theta) after the native exchange. The resolution chain
map commutes with theta. The K-injective derived-map computation proves compatibility
with all derived morphisms, giving F(tau) after c1, and its iterates for every integer.
7. Transpose F(etaX) followed by beta inverse using the exact derived adjunction. This is
counitY after IY applied to that composite, exactly the equation for kappa below.
Naturality follows from the units, counits and beta. The free unit is the zeroth
coprojection; applying the n-th structure iterate gives inclusion n, also for n<0.
Step 6 and exchange naturality therefore give the asserted summand formula.
8. Apply the locally finite native compact-support coproduct theorem on the geometric
fibres. Quasi-compact locally finite type schemes are finite type; these properties,
properness and open immersion survive base change, and Z is finite type by composition.
Y is separated over k (blueprint standing convention). Step 1 places all PX^n A in LX.
The summand formula
identifies UY(kappa) followed by beta with the canonical F-coproduct comparison composed
with the sum of the c_n. Both are invertible on LX. Conservativity of UY reflects this.
-/
theorem nativeWeil_derived_induction_comparison
    [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]
    [LocallyOfFiniteType (Y ↘ Spec (.of k₀))]
    [QuasiCompact (Y ↘ Spec (.of k₀))] [QuasiSeparated (Y ↘ Spec (.of k₀))]
    [IsSeparated (Y ↘ Spec (.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of k₀))] [QuasiCompact (X ↘ Spec (.of k₀))] :
    HeartProperties k₀ l X ∧ HeartProperties k₀ l Y ∧ HeartProperties k₀ l c.Z ∧
    (ordinaryImage k₀ l f c).IsTriangulated ∧
    (ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c).IsTriangulated ∧
    ProperNormalization k₀ l f c ∧ OpenNormalization k₀ l f c ∧
    ∃ cN : ∀ (n : ℤ) (A : _root_.DerivedCategory
        (ProEtale.AdicSheaf l (X ↘ Spec (.of k₀)).geometricFiber)),
      IsoAlgebra.Free.obj (frobenius k₀ l Y) ((ordinaryImage k₀ l f c).obj A) n ≅
        (ordinaryImage k₀ l f c).obj (IsoAlgebra.Free.obj (frobenius k₀ l X) A n),
      (∀ (n : ℤ) (A B : _root_.DerivedCategory
          (ProEtale.AdicSheaf l (X ↘ Spec (.of k₀)).geometricFiber)) (g : A ⟶ B),
        IsoAlgebra.Free.objMap (frobenius k₀ l Y) ((ordinaryImage k₀ l f c).map g) n ≫
          (cN n B).hom = (cN n A).hom ≫ (ordinaryImage k₀ l f c).map
            (IsoAlgebra.Free.objMap (frobenius k₀ l X) g n)) ∧
      (∀ A, (cN 0 A).hom = 𝟙 _) ∧
      (∀ (n : ℤ) A,
        (frobenius k₀ l Y).map (cN n A).hom ≫
          (exchange k₀ l f c).hom.app (IsoAlgebra.Free.obj (frobenius k₀ l X) A n) ≫
          (ordinaryImage k₀ l f c).map (IsoAlgebra.Free.objSucc
            (frobenius k₀ l X) A n).hom =
        (IsoAlgebra.Free.objSucc (frobenius k₀ l Y)
          ((ordinaryImage k₀ l f c).obj A) n).hom ≫ (cN (n + 1) A).hom) ∧
      ∃ κ : ordinaryImage k₀ l f c ⋙ induction k₀ l Y ⟶
          induction k₀ l X ⋙ ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c,
        (∀ A, κ.app A = (induction k₀ l Y).map
          ((ordinaryImage k₀ l f c).map
              ((IsoAlgebra.freeWeilDerivedAdjunction
                (WeilSheaf.frobeniusPullback k₀ l X)).unit.app A) ≫
            (comparison k₀ l f c).inv.app ((induction k₀ l X).obj A)) ≫
          (IsoAlgebra.freeWeilDerivedAdjunction
            (WeilSheaf.frobeniusPullback k₀ l Y)).counit.app
              ((ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c).obj
                ((induction k₀ l X).obj A))) ∧
        ∀ A, ProEtale.nativeAdicConstructibleLocalizingHull l
            (X ↘ Spec (.of k₀)).geometricFiber A →
          IsIso (κ.app A) ∧ ∀ n : ℤ,
            inclusion k₀ l Y ((ordinaryImage k₀ l f c).obj A) n ≫
              (forget k₀ l Y).map (κ.app A) ≫
              (comparison k₀ l f c).hom.app ((induction k₀ l X).obj A) =
            (cN n A).hom ≫ (ordinaryImage k₀ l f c).map (inclusion k₀ l X A n)  := by
  refine ⟨nativeWeil_heart_properties k₀ l X, nativeWeil_heart_properties k₀ l Y,
    nativeWeil_heart_properties k₀ l c.Z, inferInstance, inferInstance,
    nativeWeil_proper_normalization k₀ l f c, ?_,
    nativeWeil_induction_summands k₀ l f c⟩
  exact exactForgetNormalization_proof _ _ _ _

end AlgebraicGeometry.NativeWeilInduction
