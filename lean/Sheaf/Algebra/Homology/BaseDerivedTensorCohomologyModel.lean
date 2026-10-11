/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.RingTheory.TensorProduct.Basic
/-!
# Models of base-derived tensor cohomology and its localization comparison

Source: Stacks Project, Tag 08IB, lemma-compare-base-change, and Tag 06Y6,
lemma-derived-base-change (blueprint: def-pc-base-derived-tensor-cohomology-model).

The model records a total left derived functor with its universal counit, actual
cohomology objects with their tensor-algebra action, and the comparison maps.
Commuting squares fix the maps; no isomorphism of comparison maps is assumed.
-/

set_option autoImplicit false

universe uR uA uB uD v w uS uT

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

/-- (blueprint: def-pc-base-derived-tensor-cohomology-model) Stacks, Tag 06Y6.
Extension of scalars is additive. Proof: its maps send `s ⊗ x` to `s ⊗ f x`;
the sum of two maps thus gives `s ⊗ (f x + g x)`, the sum of their two images.
Tensor induction proves equality on all tensors. -/
@[instance]
theorem extendScalars_additive {S : Type uS} {T : Type uT} [CommRing S] [CommRing T]
    (f : S →+* T) : (extendScalars.{uS, uT, v} f).Additive := by
  sorry

variable (R : Type uR) (A : Type uA) (B : Type uB) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uA uB uD v} R)]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uA uB uD v} B)]

/-- (blueprint: def-pc-base-derived-tensor-cohomology-model) Stacks, Tags 08IB and
06Y6. A model of the cohomology of `Q ⊗ᴸ_R B`, its `A ⊗_R B`-action, and its
canonical comparison after extension to `D`. The derived functor is characterized
by its universal counit. `ordinaryIso` is the tensor-associativity identification,
fixed on generators. `comparison_eq` identifies the comparison with the counit
on cohomology. `cohomologyIso_smul` makes `a ⊗ 1` act as the derived functor
applied to multiplication by `a` on `Q`, so the action is the canonical one.
`localized_eq` fixes the localized comparison by scalar-extension
adjunction and the map `e ⊗ q ↦ e ⊗ q` into the localized complex. -/
structure BaseDerivedTensorCohomologyModel
    (Q : CochainComplex (ModuleCat.{max uR uA uB uD v} A) ℤ)
    (D : Type uD) [CommRing D] [Algebra (A ⊗[R] B) D] where
  derived : DerivedCategory (ModuleCat.{max uR uA uB uD v} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uB uD v} B)
  counit : DerivedCategory.Qh ⋙ derived ⟶
    (extendScalars.{_, _, max uR uA uB uD v} (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh
  universal : derived.IsLeftDerivedFunctor counit
    (HomotopyCategory.quasiIso (ModuleCat.{max uR uA uB uD v} R) (.up ℤ))
  ordinaryIso :
    ((extendScalars.{_, _, max uR uA uB uD v} (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
      (((restrictScalars.{max uR uA uB uD v} (algebraMap R A)).mapHomologicalComplex (.up
      ℤ)).obj Q) ≅
    ((restrictScalars.{max uR uA uB uD v}
      Algebra.TensorProduct.includeRight.toRingHom).mapHomologicalComplex
      (.up ℤ)).obj
      (((extendScalars.{_, _, max uR uA uB uD v} (algebraMap A (A ⊗[R]
      B))).mapHomologicalComplex (.up ℤ)).obj Q)
  ordinaryIso_tmul : ∀ (i : ℤ) (b : B) (q : Q.X i),
    ordinaryIso.hom.f i (b ⊗ₜ[R, algebraMap R B] q) =
      (Algebra.TensorProduct.includeRight b ⊗ₜ[A, algebraMap A (A ⊗[R] B)] q)
  cohomology : ℤ → ModuleCat.{max uR uA uB uD v} (A ⊗[R] B)
  cohomologyIso : ∀ i : ℤ,
    (restrictScalars.{max uR uA uB uD v} Algebra.TensorProduct.includeRight.toRingHom).obj
      (cohomology i) ≅
    (DerivedCategory.homologyFunctor (ModuleCat.{max uR uA uB uD v} B) i).obj
      (derived.obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ _).obj
          (((restrictScalars.{max uR uA uB uD v} (algebraMap R A)).mapHomologicalComplex (.up
      ℤ)).obj Q))))
  cohomologyIso_smul : ∀ (i : ℤ) (a : A),
    (restrictScalars.{max uR uA uB uD v} Algebra.TensorProduct.includeRight.toRingHom).map
        ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • 𝟙 (cohomology i)) ≫
      (cohomologyIso i).hom =
    (cohomologyIso i).hom ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{max uR uA uB uD v} B) i).map
        (derived.map (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
          (((restrictScalars.{max uR uA uB uD v} (algebraMap R A)).mapHomologicalComplex
            (.up ℤ)).map (a • 𝟙 Q)))))
  comparison : ∀ i : ℤ, cohomology i ⟶
    (((extendScalars.{_, _, max uR uA uB uD v} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
      (.up ℤ)).obj Q).homology i
  comparison_eq : ∀ i : ℤ,
    (restrictScalars.{max uR uA uB uD v} Algebra.TensorProduct.includeRight.toRingHom).map
      (comparison i) ≫
      (((((extendScalars.{_, _, max uR uA uB uD v} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
        (.up ℤ)).obj Q).sc i).mapHomologyIso
         (restrictScalars.{max uR uA uB uD v} Algebra.TensorProduct.includeRight.toRingHom)).inv =
    (cohomologyIso i).hom ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{max uR uA uB uD v} B) i).map
        (counit.app ((HomotopyCategory.quotient _ _).obj
          (((restrictScalars.{max uR uA uB uD v} (algebraMap R A)).mapHomologicalComplex (.up
      ℤ)).obj Q))) ≫
      (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{max uR uA uB uD v} B) i).hom.app
        ((HomotopyCategory.quotient _ _).obj
          (((extendScalars.{_, _, max uR uA uB uD v} (algebraMap R B)).mapHomologicalComplex
      (.up ℤ)).obj
            (((restrictScalars.{max uR uA uB uD v} (algebraMap R A)).mapHomologicalComplex (.up
      ℤ)).obj Q))) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{max uR uA uB uD v} B) (.up ℤ)
      i).hom.app _
      ≫
      HomologicalComplex.homologyMap ordinaryIso.hom i
  ordinaryToLocalized :
    ((extendScalars.{_, _, max uR uA uB uD v} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
      (.up ℤ)).obj Q ⟶
    ((restrictScalars.{max uR uA uB uD v} (algebraMap (A ⊗[R] B) D)).mapHomologicalComplex (.up
      ℤ)).obj
      (((extendScalars.{_, _, max uR uA uB uD v} ((algebraMap (A ⊗[R] B) D).comp
        (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q)
  ordinaryToLocalized_tmul : ∀ (i : ℤ) (e : A ⊗[R] B) (q : Q.X i),
    ordinaryToLocalized.f i (e ⊗ₜ[A, algebraMap A (A ⊗[R] B)] q) =
      (algebraMap (A ⊗[R] B) D e ⊗ₜ[A,
        (algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B))] q)
  localizedComparison : ∀ i : ℤ,
    (extendScalars.{_, _, max uR uA uB uD v} (algebraMap (A ⊗[R] B) D)).obj (cohomology i) ⟶
    (((extendScalars.{_, _, max uR uA uB uD v} ((algebraMap (A ⊗[R] B) D).comp
      (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q).homology i
  localized_eq : ∀ i : ℤ,
    (extendRestrictScalarsAdj.{max uR uA uB uD v, _, _} (algebraMap (A ⊗[R] B) D)).unit.app
      (cohomology i) ≫
      (restrictScalars.{max uR uA uB uD v} (algebraMap (A ⊗[R] B) D)).map (localizedComparison i) =
    comparison i ≫ HomologicalComplex.homologyMap ordinaryToLocalized i ≫
      ((((extendScalars.{_, _, max uR uA uB uD v} ((algebraMap (A ⊗[R] B) D).comp
        (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q).sc i
        |>.mapHomologyIso (restrictScalars.{max uR uA uB uD v} (algebraMap (A ⊗[R] B) D))).hom

/-- (blueprint: def-pc-base-derived-tensor-cohomology-model) Stacks, Tags 06Y6 and
08IB: the model exists without flatness or Tor-independence assumptions.

Proof: resolve complexes of R-modules by K-flat complexes and apply extension of
scalars to B. The localization universal property supplies the total left derived
functor and its counit. Apply its cohomology functors. Multiplication by A on Q
and by B on the tensor factor induces commuting actions on this cohomology;
the two R-actions agree, hence give the A-tensor-B action; this proves
cohomologyIso_smul. The counit is compatible
with these actions. The ordinary associativity identification sends b tensor q to
(1 tensor b) tensor q and is an isomorphism, its inverse sending
(a tensor b) tensor q to b tensor (a q). Both commute with the differentials.
This constructs comparison and proves comparison_eq. The termwise map from the
ordinary complex to its D-extension sends e tensor q to the image of e tensor q.
Taking cohomology gives an E-linear map to the restriction of the D-cohomology.
Composing it with comparison and transposing by extension/restriction adjunction
constructs localizedComparison and proves localized_eq. None of these steps
asserts that comparison or localizedComparison is an isomorphism. -/
theorem nonempty_baseDerivedTensorCohomologyModel
    (Q : CochainComplex (ModuleCat.{max uR uA uB uD v} A) ℤ)
    (D : Type uD) [CommRing D] [Algebra (A ⊗[R] B) D] :
    Nonempty (BaseDerivedTensorCohomologyModel R A B Q D) := by
  sorry

/-- (blueprint: def-pc-base-derived-tensor-cohomology-model) Stacks, Tags 06Y6 and
08IB. Choose a model of derived tensor cohomology and its canonical localization
comparison. Only the existence proof is deferred, in the named theorem
`nonempty_baseDerivedTensorCohomologyModel`; the data are selected by choice. -/
noncomputable def baseDerivedTensorCohomologyModel
    (Q : CochainComplex (ModuleCat.{max uR uA uB uD v} A) ℤ)
    (D : Type uD) [CommRing D] [Algebra (A ⊗[R] B) D] :
    BaseDerivedTensorCohomologyModel R A B Q D :=
  Classical.choice (nonempty_baseDerivedTensorCohomologyModel R A B Q D)

end ModuleCat

