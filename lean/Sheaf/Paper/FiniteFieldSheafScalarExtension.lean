/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
public import Sheaf.Paper.BoundedConstructibleTower
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Finite-field scalar extension of constructible pro-etale complexes

Source: Stacks Project, Tag 093V, lemma-tensor-product-locally-constant;
finite-field coefficient specialization in the Weil conjectures blueprint
(blueprint: lem-sf-finite-field-sheaf-scalar-extension).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The map of constant coefficient ring sheaves induced by a field homomorphism.
Source: Stacks Project, Tag 093V (blueprint: lem-sf-finite-field-sheaf-scalar-extension). -/
noncomputable def finiteFieldConstantRingMap
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k']
    (f : k →+* k') : adicLisseConstantRing Y (ULift.{u + 1} k) ⟶
      adicLisseConstantRing Y (ULift.{u + 1} k') :=
  (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f))

/-- Tensor extension of pro-etale module sheaves along a finite-field map.
Source: Stacks Project, Tag 093V (blueprint: lem-sf-finite-field-sheaf-scalar-extension). -/
noncomputable def finiteFieldScalarExtension
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k']
    (f : k →+* k') :
    pbcModules Y (adicLisseConstantRing Y (ULift.{u + 1} k)) ⥤
      pbcModules Y (adicLisseConstantRing Y (ULift.{u + 1} k')) :=
  pbcExtend (finiteFieldConstantRingMap Y f)

/-- Scalar extension is additive, hence preserves zero morphisms.
Source: Stacks Project, Tag 093V, lemma-tensor-product-locally-constant;
finite-field coefficient specialization (blueprint: lem-sf-finite-field-sheaf-scalar-extension). -/
noncomputable instance finiteFieldScalarExtension_additive
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k']
    (f : k →+* k') :
    (finiteFieldScalarExtension Y f).Additive :=
  pbcExtend_additive (finiteFieldConstantRingMap Y f)

/-- Termwise application of scalar extension to a cochain complex.
Source: Stacks Project, Tag 010N (blueprint: lem-sf-finite-field-sheaf-scalar-extension). -/
noncomputable def finiteFieldScalarExtensionComplex
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k']
    (f : k →+* k')
    (C : CochainComplex
      (pbcModules Y (adicLisseConstantRing Y (ULift.{u + 1} k))) ℤ) :
    CochainComplex (pbcModules Y (adicLisseConstantRing Y (ULift.{u + 1} k'))) ℤ :=
  ((finiteFieldScalarExtension Y f).mapHomologicalComplex (ComplexShape.up ℤ)).obj C

/-- Finite-field scalar extension is exact, preserves finite constructibility with the
same local strata and covers, identifies each local model with its tensor extension, and
commutes with all cohomology objects of cochain complexes.

Source: Stacks Project, Tag 093V, lemma-tensor-product-locally-constant; Tags 0GMW,
03EL and 010N (blueprint: lem-sf-finite-field-sheaf-scalar-extension).
Proof: Regard `k'` as a finite `k`-module. A finite basis identifies sheaf tensor
extension with a finite direct sum, proving preservation of kernels and cokernels.
On every stratum and its pro-etale localization, the tensor of a constant sheaf is
the constant sheaf of the tensor module, with the right-factor `k'` action; finite
stalks and the original finite stratification are therefore preserved. Apply the
exact-functor homology comparison to the three consecutive terms of each complex.
The zero and bounded-interval clauses follow termwise, including the case of an
empty stratum or `r = s`.
-/
theorem finiteFieldSheafScalarExtension
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k'] [Finite k] [Finite k']
    (f : k →+* k') :
    PreservesFiniteLimits (finiteFieldScalarExtension Y f) ∧
      PreservesFiniteColimits (finiteFieldScalarExtension Y f) ∧
      (∀ (F : pbcModules Y (adicLisseConstantRing Y (ULift.{u + 1} k))),
        IsConstructibleProEtaleCoefficientModuleSheaf Y (ULift.{u + 1} k) F →
          IsConstructibleProEtaleCoefficientModuleSheaf Y (ULift.{u + 1} k')
            ((finiteFieldScalarExtension Y f).obj F) ∧
          (∀ (S : LocallyClosedStratification Y) (i : Fin S.n)
              (K : Sieve (⊤_ (S.domain i).ProEt)),
            K ∈ ProEt.topology (S.domain i) (⊤_ (S.domain i).ProEt) →
            ∀ (V : (S.domain i).ProEt) (g : V ⟶ ⊤_ (S.domain i).ProEt), K g →
              ∀ (M : ModuleCat.{u + 1} (ULift.{u + 1} k)),
                Finite M →
                Nonempty ((SheafOfModules.overFunctor _ V).obj
                  ((proEtaleModuleInverseImage (S.immersion i)
                    (adicLisseConstantRing Y (ULift.{u + 1} k))).obj F) ≅
                  (SheafOfModules.overFunctor _ V).obj
                    ((proEtaleModuleInverseImage (S.immersion i)
                      (adicLisseConstantRing Y (ULift.{u + 1} k))).obj
                      ((adicLisseConstantModules Y (ULift.{u + 1} k)).obj M))) →
                Nonempty ((SheafOfModules.overFunctor _ V).obj
                  ((proEtaleModuleInverseImage (S.immersion i)
                    (adicLisseConstantRing Y (ULift.{u + 1} k'))).obj
                    ((finiteFieldScalarExtension Y f).obj F)) ≅
                  (SheafOfModules.overFunctor _ V).obj
                    ((proEtaleModuleInverseImage (S.immersion i)
                      (adicLisseConstantRing Y (ULift.{u + 1} k'))).obj
                      ((adicLisseConstantModules Y (ULift.{u + 1} k')).obj
                        ((ModuleCat.extendScalars
                          (RingHom.ulift.{u + 1, u + 1} f)).obj M))))) ∧
      (∀ (C : CochainComplex
          (pbcModules Y (adicLisseConstantRing Y (ULift.{u + 1} k))) ℤ) (i : ℤ),
        ∃ e : (finiteFieldScalarExtensionComplex Y f C).homology i ≅
            (finiteFieldScalarExtension Y f).obj (C.homology i),
          (∀ (r s : ℤ), r ≤ s →
            (∀ j : ℤ, IsConstructibleProEtaleCoefficientModuleSheaf Y
              (ULift.{u + 1} k) (C.homology j)) →
            (∀ j : ℤ, j < r ∨ s < j → IsZero (C.homology j)) →
            (∀ j : ℤ, (IsConstructibleProEtaleCoefficientModuleSheaf Y
              (ULift.{u + 1} k')
                ((finiteFieldScalarExtensionComplex Y f C).homology j)) ∧
            (∀ j : ℤ, j < r ∨ s < j →
              IsZero ((finiteFieldScalarExtensionComplex Y f C).homology j)))))) := by
  sorry

end AlgebraicGeometry.Scheme
