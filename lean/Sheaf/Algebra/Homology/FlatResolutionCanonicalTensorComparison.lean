/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.ProperBaseChange.SingletonSiteModuleComparison
import Sheaf.TraceFormula.OnePointDerivedRingIdentification
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.Single
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat

/-! # Canonical scalar-extension comparison for a flat resolution

Source: Stacks Project, cotangent.tex Tag 08QP, more-algebra.tex Tag 064K,
derived.tex Tag 06XN and sites-cohomology.tex Tag 06YY.
(blueprint: lem-trf-flat-resolution-canonical-tensor-comparison).

The universal pair is formulated on homotopy categories. Chain maps below are
sent through the homotopy quotient before localization. Scalar extension uses
Mathlib's order `A' ⊗[A] N`, canonically the node's `N ⊗[A] A'` by tensor symmetry.
The identification of scalar extension of `N[0]` with its degree-zero tensor is
`HomologicalComplex.singleMapHomologicalComplex (ModuleCat.extendScalars φ) (.up ℤ) 0`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- A bounded-above flat resolution computes every universal scalar-extension pair,
with its own counit identifying the tensor augmentation.
Source: Stacks Tags 08QP, 064K, 06XN and 06YY
(blueprint: lem-trf-flat-resolution-canonical-tensor-comparison).

Proof:
1. Apply `lem-pc-module-bounded-flat-kflat` to the given bound and termwise flatness;
   its acyclic-tensor criterion is `def-pc-module-kflat-complex`.
2. On the one-point site, `lem-trf-ringed-scalar-universal-resolution-comparison`
   supplies a universal sheaf pair. Transport it using
   `lem-trf-one-point-derived-ring-identification`, preserving its K-flat counit.
3. The universal property of `lem-pur-left-derived-from-kflat-class` gives unique
   counit-compatible transformations between this pair and any supplied pair.
   Their composites are identities by uniqueness, so the supplied counit at `C`
   is invertible as well.
4. The quasi-isomorphism `q` becomes invertible under localization
   (`def-weil-abstract-derived-category`); its image under `L` is invertible.
   Composing it with the inverse counit gives the displayed isomorphism `j`.
5. Naturality at `q`, followed by cancellation of the invertible counit at `C`,
   gives `j.hom ≫ γ_N = Q'(T(q))`. Termwise scalar extension
   (`def-weil-module-base-change`) sends `N[0]` to `(A' ⊗[A] N)[0]` via the
   canonical `singleMapHomologicalComplex` isomorphism. No flatness of `φ` is used. -/
theorem flatResolution_canonical_tensor_comparison
    {A A' : Type u} [CommRing A] [CommRing A']
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} A')]
    (φ : A →+* A') (N : ModuleCat.{u} A) (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (q : C ⟶ (HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).obj N)
    [QuasiIso q]
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (C.X i))
    (hflat : ∀ i : ℤ, Module.Flat A (C.X i)) :
    (∃ (L : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A'))
      (γ : DerivedCategory.Qh ⋙ L ⟶
        (extendScalars φ).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      L.IsLeftDerivedFunctor γ (HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ))) ∧
    ∀ (L : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A'))
      (γ : DerivedCategory.Qh ⋙ L ⟶
        (extendScalars φ).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      L.IsLeftDerivedFunctor γ (HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ)) →
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat C ∧
      ∃ (hγ : IsIso (γ.app ((HomotopyCategory.quotient _ _).obj C)))
        (j : DerivedCategory.Qh.obj
            (((extendScalars φ).mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient _ _).obj C)) ≅
          L.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
            ((HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).obj N)))),
        j.hom = @CategoryTheory.inv _ _ _ _
            (γ.app ((HomotopyCategory.quotient _ _).obj C)) hγ ≫
          L.map (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map q)) ∧
        j.hom ≫ γ.app ((HomotopyCategory.quotient _ _).obj
            ((HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).obj N)) =
          DerivedCategory.Qh.map
            (((extendScalars φ).mapHomotopyCategory (.up ℤ)).map
              ((HomotopyCategory.quotient _ _).map q)) := by
  sorry

/-- The scalar-extension pair on the punctual ringed site transports to an ordinary
universal pair through evaluation, with its specified universal counit.
Source: Stacks Tags 03CW, 06YY and 06XN
(blueprint: lem-trf-flat-resolution-canonical-tensor-comparison).

Proof:
1. Use the exact evaluation equivalences and the actual sheaf extension functor
   of `lem-trf-one-point-derived-ring-identification`. Its object and morphism
   formulas are the termwise tensor formulas of `def-weil-module-base-change`.
2. Apply `lem-trf-ringed-scalar-universal-resolution-comparison` on this small site
   to obtain the sheaf universal pair; it is the pair of
   `lem-pur-derived-change-of-rings` up to its unique counit-compatible isomorphism.
3. Transport both localizations through evaluation and its inverse. Conjugation
   transports the universal natural-transformation bijection, giving the ordinary
   universal pair and the natural isomorphism `c` between the derived functors.
4. The displayed counit square is precisely the conjugated counit: it uses the
   localization comparisons `kA`, `kB` and the termwise scalar comparison `s`.
   Thus it specifies the transported counit, rather than an unrelated map.
5. The preceding theorem applies to this pair and to every universal pair by
   uniqueness, giving its bounded-flat computation and augmentation equation. -/
theorem flatResolution_sheaf_pair_transport
    {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A') :
    ∃ (E : singletonModuleCategory A ⥤ singletonModuleCategory A')
      (h : ∀ M : singletonModuleCategory A, E.obj M = singletonSheafExtensionObj φ M)
      (_ : ∀ {M N : singletonModuleCategory A} (f : M ⟶ N),
        E.map f = eqToHom (h M) ≫ singletonSheafExtensionMap φ f ≫ eqToHom (h N).symm)
      (_ : E.Additive)
      (s : E ⋙ singletonEvaluation A' ≅ singletonEvaluation A ⋙ extendScalars φ)
      (_ : HasDerivedCategory.{u + 1} (singletonModuleCategory A))
      (_ : HasDerivedCategory.{u + 1} (singletonModuleCategory A'))
      (_ : HasDerivedCategory.{u + 1} (ModuleCat.{u} A))
      (_ : HasDerivedCategory.{u + 1} (ModuleCat.{u} A'))
      (dA : DerivedCategory (singletonModuleCategory A) ≌ DerivedCategory (ModuleCat.{u} A))
      (dB : DerivedCategory (singletonModuleCategory A') ≌ DerivedCategory (ModuleCat.{u} A'))
      (kA : DerivedCategory.Qh ⋙ dA.functor ≅
        (singletonEvaluation A).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
      (kB : DerivedCategory.Qh ⋙ dB.functor ≅
        (singletonEvaluation A').mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
      (LS : DerivedCategory (singletonModuleCategory A) ⥤
        DerivedCategory (singletonModuleCategory A'))
      (ε : DerivedCategory.Qh ⋙ LS ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
      (L : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A'))
      (γ : DerivedCategory.Qh ⋙ L ⟶
        (extendScalars φ).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
      (c : dA.functor ⋙ L ≅ LS ⋙ dB.functor),
      LS.IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso (singletonModuleCategory A) (.up ℤ)) ∧
      L.IsLeftDerivedFunctor γ (HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ)) ∧
      ∀ H : HomotopyCategory (singletonModuleCategory A) (.up ℤ),
        L.map (kA.hom.app H) ≫
            γ.app (((singletonEvaluation A).mapHomotopyCategory (.up ℤ)).obj H) =
          c.hom.app (DerivedCategory.Qh.obj H) ≫ dB.functor.map (ε.app H) ≫
            kB.hom.app ((E.mapHomotopyCategory (.up ℤ)).obj H) ≫
            DerivedCategory.Qh.map ((singletonExtensionHomotopyComparison φ E s).hom.app H) := by
  sorry

end ModuleCat
