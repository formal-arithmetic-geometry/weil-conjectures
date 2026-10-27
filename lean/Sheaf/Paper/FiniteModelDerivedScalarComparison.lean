/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K6
-/
module

public import Sheaf.Paper.FinitePerfectQuotientModelData
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
import Sheaf.Paper.FiniteModelConstantScalarExtensionCore
import Sheaf.Paper.FiniteModelCoefficientTransport

/-! # Derived scalar extension of the constant realization of an algebraic complex

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 0G7E, and 0D6D;
sites-modules.tex, Tag 093J.
(blueprint: lem-weil-pbc-finite-model-derived-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Constant realization intertwines algebraic and sheaf derived scalar extension,
including transport of the output ring by a ring equivalence. This is independent
of adic data, local charts, and completed-coefficient objects.

Source: Stacks Project, sites-cohomology.tex, lemma-derived-base-change (06YY),
lemma-pullback-K-flat (0G7E), lemma-derived-pullback-composition (0D6D);
sites-modules.tex, lemma-constant-exact (093J).
(blueprint: lem-weil-pbc-finite-model-derived-scalar-comparison).

Proof: take a filtered-free K-projective resolution of P in the original module
universe. Lift its coefficients and module carriers to the universe of the site.
The lifted resolution is still filtered-free and K-flat: the filtration is unchanged,
and each free basis is sent to the same basis by the module universe-lift functor.
Termwise tensor commutes with this lift by the mutually inverse pure-tensor maps.
Apply constantRealizationDerivedScalarExtension to the lifted ring homomorphism.
Its ordinary comparison is balanced multiplication on constant generators. Its
derived comparison is invertible on flat-term K-flat resolutions.
The specified functor L and counit epsilon are the total left derived scalar
extension, so uniqueness of the left derived pair identifies this computation with
L. Scalar restriction along rho inverse is an exact equivalence, equal to extension
along rho. Transitivity identifies extension along rho composed with q with the
successive extensions. Finally replace L(Q(P)) by its canonical localization
representative and use exact constant realization of the coefficient transport.
All identifications are in the output coefficient category, and hold for arbitrary
unbounded complexes, zero rings, and empty sites. -/
theorem finiteModel_derivedScalarComparison
    (X : Scheme.{t}) {B C D : Type t} [CommRing B] [CommRing C] [CommRing D]
    (q : B →+* C) (ρ : C ≃+* D)
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    [(koszulConstantFunctor X D).PreservesZeroMorphisms]
    (P : CochainComplex (ModuleCat.{t} B) ℤ)
    (L : DerivedCategory (ModuleCat.{t} B) ⥤ DerivedCategory (ModuleCat.{t} C))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _ (ModuleCat.extendScalars q)
        (ModuleCat.extendRestrictScalarsAdj q).left_adjoint_additive
        (.up ℤ) ⋙ DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))) :
    let K := ((ModuleCat.restrictScalars.{t} ρ.symm.toRingHom).mapHomologicalComplex
      (.up ℤ)).obj (DerivedCategory.Q.objPreimage (L.obj (DerivedCategory.Q.obj P)))
    Nonempty
      ((completedAdicDerivedChange X (adicConstantMap X (ρ.toRingHom.comp q))).obj
          (DerivedCategory.Q.obj (finiteModelConstantComplex X B P)) ≅
        DerivedCategory.Q.obj (finiteModelConstantComplex X D K)) := by
  dsimp
  obtain ⟨e₁⟩ := finiteModel_constantScalarExtension_core X
    (ρ.toRingHom.comp q) P
  obtain ⟨e₂⟩ := finiteModel_derivedRepresentative_transport X q ρ P L ε hL
  exact ⟨e₁ ≪≫ e₂⟩

end AlgebraicGeometry.Scheme
