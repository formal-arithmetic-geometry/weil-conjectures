/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Paper.SiteLocallyConstantFiniteType
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.Free
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Sheaf.Algebra.Homology.BoundedFlatReplacement
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat
import WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-! # Comparing tensor cohomology with local finite free models

Source: Stacks Project, Cohomology on Sites, Tag 094H
(blueprint: lem-weil-pbc-site-tensor-local-model-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u} [Category.{u} C]

set_option quotPrecheck false in
set_option hygiene false in
local notation "𝓡(" J ", " B ")" => (sheafCompose J
  (forget₂ CommRingCat.{u} RingCat.{u})).obj
    ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of B))
set_option quotPrecheck false in
set_option hygiene false in
local notation "cB(" J ", " B ")" => strictPerfectConstantPresheaf (C := C) B ⋙
  PresheafOfModules.sheafification.{u} (R := 𝓡(J, B)) (Functor.whiskerRight
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B)))
    (forget₂ CommRingCat.{u} RingCat.{u}))

set_option synthInstance.maxSize 2048 in
/-- Local finite free models of the two relevant good truncations compute a fixed
degree of the original K-flat tensor. The comparison needs neither Noetherianity nor
local constancy hypotheses: the models are given.

Source: Stacks Project, Cohomology on Sites, Tag 094H, truncation and finite-free
computation; Tags 06YS, 06YQ, and Modules on Sites, Tag 0E8J.
(blueprint: lem-weil-pbc-site-tensor-local-model-comparison).

Proof: Replace the factors by bounded-above flat complexes with their cohomological
upper bounds. K-flatness and the mapping-cone criterion show independence from the
given representatives. Restriction is exact, commutes with sheaf tensor and coproducts,
and preserves flatness, so it commutes with these derived tensor computations. For
cutoffs a = i-bQ and c = i-bP, the discarded lower truncation has upper cohomological
bound a-1, respectively c-1. Its tensor with the other factor has upper bound at most
i-1. The truncation triangle therefore gives an isomorphism on degree-i cohomology.
This also handles a cutoff larger than the upper bound: the corresponding object and
the relevant tensor cohomology are zero. Use the two given derived isomorphisms.
The constant realizations of E and F are termwise flat, since finite free modules
realize as finite sums of the ring sheaf; they are K-flat by their upper term bounds.
Their total tensor is the constant realization of the algebraic total tensor T:
the tensor-basis comparison in each bidegree commutes with both differentials and the
sign (-1)^p, and constant realization preserves coproducts. Taking cohomology on the slice
gives the asserted isomorphism. The comparison makes no assertion
about finite generation of the algebraic tensor or its cohomology. -/
theorem site_tensor_local_model_comparison
    (J : GrothendieckTopology C) (B : Type u) [CommRing B]
    (P Q : CochainComplex (SheafOfModules.{u} (𝓡(J, B))) ℤ)
    (hP : P.IsAcyclicTensorKFlat) (hQ : Q.IsAcyclicTensorKFlat)
    (bP bQ : ℤ)
    (hPb : ∀ j : ℤ, bP < j → IsZero (P.homology j))
    (hQb : ∀ j : ℤ, bQ < j → IsZero (Q.homology j))
    (i : ℤ) (U : C) :
    letI := HasDerivedCategory.standard (SheafOfModules.{u} ((𝓡(J, B)).over U))
    ∀ (E F : CochainComplex (ModuleCat.{u} B) ℤ)
    (hEb : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero (E.X j))
    (hFb : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero (F.X j))
    (hE : ∀ j : ℤ, Module.Free B (E.X j) ∧ Module.Finite B (E.X j))
    (hF : ∀ j : ℤ, Module.Free B (F.X j) ∧ Module.Finite B (F.X j))
    (eE : Nonempty
      (DerivedCategory.Q.obj
          (((overFunctor.{u} (𝓡(J, B)) U).mapHomologicalComplex (.up ℤ)).obj
            (P.truncGE (i - bQ))) ≅
        DerivedCategory.Q.obj
          ((((cB(J, B)) ⋙ overFunctor.{u} (𝓡(J, B)) U).mapHomologicalComplex (.up ℤ)).obj E)))
    (eF : Nonempty
      (DerivedCategory.Q.obj
          (((overFunctor.{u} (𝓡(J, B)) U).mapHomologicalComplex (.up ℤ)).obj
            (Q.truncGE (i - bP))) ≅
        DerivedCategory.Q.obj
          ((((cB(J, B)) ⋙ overFunctor.{u} (𝓡(J, B)) U).mapHomologicalComplex (.up ℤ)).obj F))),
    let T := CochainComplex.mapBifunctor E F (MonoidalCategory.curriedTensor (ModuleCat B))
    Nonempty
      ((((overFunctor.{u} (𝓡(J, B)) U).mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor P Q
            (@MonoidalCategory.curriedTensor _ _ (monoidalCategory
              ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of B)))))).homology i ≅
        ((((cB(J, B)) ⋙ overFunctor.{u} (𝓡(J, B)) U).mapHomologicalComplex
          (.up ℤ)).obj T).homology i) := by
  sorry

end SheafOfModules
