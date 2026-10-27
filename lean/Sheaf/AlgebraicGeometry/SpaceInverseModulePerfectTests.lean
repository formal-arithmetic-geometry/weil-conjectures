module

public import Sheaf.AlgebraicGeometry.SpaceInverseModuleDerivedLimit
public import Sheaf.AlgebraicGeometry.SpacePerfectTensorTestHolim
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Sheaf.Paper.StrictPerfectRingedPullbackModel
import Sheaf.AlgebraicGeometry.ProperSupportTensorPerfect
import WeilConjectures.AlgebraicGeometry.PerfectAffineBoundedProjective
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.AlgebraicGeometry.SpaceFlatComplexBaseChange
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
import Sheaf.AlgebraicGeometry.SpaceAffineModuleHigherImageVanishing
import Sheaf.AlgebraicGeometry.SpacePerfectUniformTor

/-! # Perfect tensor tests of inverse module systems

Source: Stacks Project, spaces-flat.tex, Tag 0CX6, lemma-compute-against-perfect,
clause (1), perfectness assertion, in Situation 0CX4, situation-existence
(blueprint: lem-sfb-space-inverse-module-perfect-tests).

Index n is the source's level n + 1. The homotopy limit and its products belong
to the full quasi-coherent derived category, and the tensor test has its canonical
structure-induced action of the inverse-limit ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every perfect tensor test of the quasi-coherent homotopy inverse limit is perfect
as a complex over the inverse-limit ring.
Source: Stacks Project, spaces-flat.tex, Tag 0CX6, lemma-compute-against-perfect (1),
with Situation 0CX4 (blueprint: lem-sfb-space-inverse-module-perfect-tests).

Proof:
1. Pull E back to X_n using the strict-perfect ringed pullback model. Base change
   preserves finite presentation and separatedness. Replace the proper carrier by
   scheme-theoretic support (lem-sfb-space-module-proper-carrier-support) and apply
   lem-sfb-proper-support-tensor-perfect. The scheme etale/Zariski comparison and
   etale detection of perfectness, followed by the affine bounded-projective and
   quasi-coherent derived equivalences, make C_n = RΓ(X_n,M_n tensor E_n) perfect.
   Pushforward composition identifies these sections with those of Rf_n,*.
2. The flat-complex base-change theorem and affine derived tensor formula identify
   C_(n+1) tensor A_n with C_n, using exactly the specified reduction isomorphism.
   Finite presentation makes the source qcqs; perfect-uniform-tor supplies the
   quasi-coherent cohomology needed for base change. The etale chart calculus
   respects the units and counits defining the transition maps.
3. Affine higher-image vanishing identifies Ri_n,* M_n with i_n,* M_n. The qcqs
   derived projection formula identifies its tensor test with C_n. Pushforward
   composition and the chart calculus make these identifications an isomorphism
   of towers, since both maps use the coefficient quotient and the identity on E.
4. Finite presentation over the affine base makes X qcqs. Apply
   lem-sfb-space-perfect-tensor-test-holim to the intrinsic D_QCoh product triangle
   supplied here. Thus the tensor test of K is isomorphic to Rlim C_n in D(A).
5. Apply lem-sfb-perfect-inverse-ring-reconstruction: each C_n is perfect, the
   scalar-extension adjuncts are isomorphisms, and the ring transitions are
   surjective with locally nilpotent kernels. Transport the bounded finite
   projective representative across the isomorphism from step 4.
-/
theorem inverseModule_perfectTensorTest
    (A : ℕ → CommRingCat.{u}) (r : ∀ n : ℕ, A (n + 1) ⟶ A n)
    (hsurj : ∀ n : ℕ, Function.Surjective (r n))
    (hnil : ∀ (n : ℕ) (a : A (n + 1)), (r n) a = 0 → IsNilpotent a)
    (c : Cone (Functor.ofOpSequence r)) (hc : IsLimit c)
    (X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    [HasDerivedCategory.{w} X.SmallModules]
    (f : X ⟶ schemeSpace (inverseModuleSpec c.pt))
    (hsep : MapIsSeparated f) (hfp : ProperQuotFinitePresentation f)
    (M : ∀ n : ℕ, (properQuotFibre f (inverseModuleTest c n)).Modules)
    (hqc : ∀ n : ℕ, (M n).IsQuasicoherent)
    (hfin : ∀ n : ℕ, (M n).IsFinitePresentation)
    (hflat : ∀ (n : ℕ) (U : (properQuotFibre f (inverseModuleTest c n)).EtaleSite),
      ((schemeRestriction _ U).obj (M n)).IsFlatOver
        (yoneda.preimage (U.obj.hom ≫ (properQuotSnd f (inverseModuleTest c n)).hom.hom)).left)
    (hsupp : ∀ n : ℕ, ∃ (Z : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
      (i : Z ⟶ properQuotFibre f (inverseModuleTest c n)),
      IsRepresentableWith (fun _ _ a ↦ IsClosedImmersion a.left) i.hom.hom ∧
      MapIsProper (i ≫ properQuotSnd f (inverseModuleTest c n)) ∧ ∃ G : Z.Modules,
        G.IsQuasicoherent ∧ G.IsFiniteType ∧ Nonempty ((moduleDirectImage i).obj G ≅ M n))
    (e : ∀ n : ℕ,
      (moduleTensorPullback (properQuotFibreMap f (inverseModuleTestMap c n))).obj
        (M (n + 1)) ≅ M n)
    (hq : ∀ n : ℕ,
      X.derivedQCohProperty (inverseModuleDerivedTerm f (inverseModuleTest c n) (M n)))
    [HasProduct (fun n : ℕ ↦
      inverseModuleQCohTerm f (inverseModuleTest c n) (M n) (hq n))]
    (K : X.DerivedQCoh)
    (p : K ⟶ ∏ᶜ (fun n : ℕ ↦
      inverseModuleQCohTerm f (inverseModuleTest c n) (M n) (hq n)))
    (δ : (∏ᶜ (fun n : ℕ ↦
      inverseModuleQCohTerm f (inverseModuleTest c n) (M n) (hq n))) ⟶ K⟦(1 : ℤ)⟧)
    (hK : IsDerivedLimitTriangle (fun n : ℕ ↦ inverseModuleDerivedTransition f
      (inverseModuleTestMap c n) (M n) (M (n + 1)) (e n) (hq n) (hq (n + 1))) K p δ)
    (E : X.DerivedModules)
    (hE : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
      X.smallStructureSheaf E) :
    DerivedCategory.IsPerfectRingComplex
      ((perfectTensorTest c.pt (inverseModuleSpec c.pt) (Iso.refl _) X f E).obj K) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
