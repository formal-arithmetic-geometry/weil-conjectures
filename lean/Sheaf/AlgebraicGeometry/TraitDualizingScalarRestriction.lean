/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q123
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.IsPrincipal
import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.CategoryTheory.Yoneda
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.ConstructibleSheaf.ConstantModuleLocallyConstant

/-!
# Scalar endomorphisms of the normalized trait dualizing complex

Source: ILO, Travaux de Gabber, Expose XVI, proof of Lemma 3.5.9, printed p.250,
with the complete mixed-characteristic traits of section 3.7
(blueprint: lem-per-trait-dualizing-scalar-restriction).

Endomorphisms are computed in the ambient derived category. The bounded-below clauses
place the objects in its full subcategory D+, whose Hom sets are the same.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The actual normalization `p! A_S(-e)[-2e]`, using the ordinary exceptional adjoint,
the published signed finite Tate sheaf, derived tensor, and the cochain shift.
The coefficient field is `F_l` lifted to the module-sheaf universe.
Source: ILO XVI, proof of Lemma 3.5.9, p.250
(blueprint: lem-per-trait-dualizing-scalar-restriction). -/
noncomputable def traitNormalizedDualizing (l : ℕ) [Fact l.Prime]
    {T S : Scheme.{u}} (p : T ⟶ S) [HasCompactification p] (e : ℤ) :
    DerivedCategoryModule (ULift.{u + 1} (ZMod l)) T :=
  (shiftFunctor _ (-2 * e)).obj
    (((derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod l))) T).obj
      (dualizingComplex (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod l))) p)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf (ULift.{u + 1} (ZMod l)) l T
            (CharP.cast_eq_zero (ULift.{u + 1} (ZMod l)) l) (-e))))

/-- Scalar endomorphisms of the relative dualizing complex are detected on every
nonempty open, without punctual purity or invertibility of a Gysin class.
Source: ILO XVI, proof of Lemma 3.5.9, p.250, restricted to section 3.7
(blueprint: lem-per-trait-dualizing-scalar-restriction).

Proof plan:
1. Apply lem-per-complete-trait-constructible-biduality to the constant rank-one
   constructible sheaf. Evaluation and symmetry identify its biduality map with
   the scalar map A_T -> RHom(Q,Q), Q = p! A_S; this is an isomorphism.
2. The signed finite twist is an invertible line (lem-asd-etale-finite-twist-pullback).
   Tensoring by it and shifting are equivalences. Tensor-Hom adjunction and Yoneda
   (lem-sf-ringed-derived-closed-symmetric-monoidal, lem-galois-yoneda-fully-faithful)
   identify RHom(K,K) with RHom(Q,Q), carrying scalar action to scalar action.
3. An open immersion is etale and its slice site is the site's localization
   (lem-weil-pbc-open-immersion-etale, lem-weil-pbc-etale-site-localization-open).
   Restrict internal Hom using lem-weil-pbc-ringed-internal-hom-exact-restriction.
   Evaluation restricts to evaluation, so the restricted scalar map is an isomorphism.
4. By lem-pur-rhom-global-sections, degree-zero global sections compute End(K).
   Module sheaves are Grothendieck abelian, hence have enough injectives
   (lem-weil-pbc-module-sheaves-grothendieck-abelian, lem-sp-grothendieck-enough-injectives).
   Bounded-below injective resolutions are K-injective and left-exact global sections
   have degree-zero cohomology equal to ordinary sections
   (lem-weil-pbc-bounded-below-injectives-kinjective,
   lem-weil-pbc-left-exact-injective-resolution-degree-zero). Thus scalar sections
   biject with End(K). The same argument applies after open restriction.
5. Integrality makes T and every nonempty open irreducible, connected and nonempty.
   By lem-weil-pbc-constant-module-locally-constant, sections of A are locally constant
   functions, hence constant, uniquely. This proves both scalar bijections.
   Inverse image preserves scalar multiplication and identity, so restriction is the
   identity on A under these bijections and is injective. The normalized objects are
   bounded below by trait biduality and the finite line/shift normalization.
-/
theorem traitDualizing_scalar_restriction (l : ℕ) [Fact l.Prime]
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsDomain R]
    [IsStrictlyHenselianLocalRing R] [CharZero R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (hdim : ringKrullDim R = 1) (hprincipal : (IsLocalRing.maximalIdeal R).IsPrincipal)
    (hmixed : 0 < ringChar (IsLocalRing.ResidueField R)) (hl : IsUnit (l : R))
    {T : Scheme.{u}} [IsIntegral T] (p : T ⟶ Spec (.of R))
    [LocallyOfFiniteType p] [QuasiCompact p] (hregular : IsRegularScheme T)
    (hprojective : ∃ (n : ℕ)
      (i : T ⟶ ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of R))),
      IsImmersion i ∧ i ≫ ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of R)) ↘
        Spec (.of R) = p)
    [HasCompactification p] (e : ℤ)
    (hvirtual : ∀ x : T, ∃ (V : T.Opens), x ∈ V ∧
      ∃ (W : Scheme.{u}) (i : V.toScheme ⟶ W) (q : W ⟶ Spec (.of R)) (r c : ℕ),
        i ≫ q = V.ι ≫ p ∧ IsRegularImmersion c i ∧ SmoothOfRelativeDimension r q ∧
          e = (r : ℤ) - (c : ℤ)) :
    _root_.DerivedCategory.TStructure.t.plus (traitNormalizedDualizing l p e) ∧
    Function.Bijective (fun a : ULift.{u + 1} (ZMod l) =>
      a • 𝟙 (traitNormalizedDualizing l p e)) ∧
    ∀ {U : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] [Nonempty U],
      _root_.DerivedCategory.TStructure.t.plus
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod l))) j).leftDerivedFunctor.obj
          (traitNormalizedDualizing l p e)) ∧
      Function.Bijective (fun a : ULift.{u + 1} (ZMod l) =>
        a • 𝟙 ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod l))) j).leftDerivedFunctor.obj
           (traitNormalizedDualizing l p e))) ∧
      (∀ a : ULift.{u + 1} (ZMod l),
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod l))) j).leftDerivedFunctor.map
          (a • 𝟙 (traitNormalizedDualizing l p e)) =
        a • 𝟙 ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod l))) j).leftDerivedFunctor.obj
           (traitNormalizedDualizing l p e))) ∧
      Function.Injective (fun f : traitNormalizedDualizing l p e ⟶
          traitNormalizedDualizing l p e =>
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod l))) j).leftDerivedFunctor.map f) := by
  sorry

end AlgebraicGeometry.Etale
