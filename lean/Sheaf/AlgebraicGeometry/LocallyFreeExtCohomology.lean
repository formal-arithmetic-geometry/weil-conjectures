/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import WeilConjectures.AlgebraicGeometry.Modules.Ext
import WeilConjectures.AlgebraicGeometry.Modules.HomTensor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# The canonical locally free Ext comparison

Source: Weil conjectures blueprint, `lem-sc-ext-locally-free`, proof
(blueprint: lem-sc-ext-locally-free).
-/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- The evaluation morphism `dualTensorHom F G : Fᵛ ⊗ G ⟶ Hom(F,G)` of the source is an
isomorphism when the first module is finite locally free.
Source: blueprint `lem-sc-ext-locally-free`, proof, first sentence.
Proof: on an open where F is free of finite rank, the tensor-dual and Hom are both finite
copies of G, and evaluation sends the dual basis to the coordinate maps. These local
isomorphisms imply the sheaf morphism is an isomorphism, by lem-sc-ext-evaluation.
(blueprint: lem-sc-ext-locally-free). -/
theorem isIso_dualTensorHom_of_isFiniteLocallyFree {X : Scheme.{u}} (F G : X.Modules)
    [F.IsFiniteLocallyFree] : IsIso (dualTensorHom F G) := sorry

/-- The additive functor `G ↦ Hom(F,G)` followed by forgetting module structure.
Source: blueprint `lem-sc-ext-locally-free`, proof, first sentence
(blueprint: lem-sc-ext-locally-free). -/
def locallyFreeHomAbelianFunctor {X : Scheme.{u}} (F : X.Modules) :
    X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (SheafOfModules.homFunctor X.sheaf).obj (op F) ⋙
    SheafOfModules.toSheaf X.ringCatSheaf

/-- Internal Hom in a finite locally free first argument is additive and exact.
Source: blueprint `lem-sc-ext-locally-free`, proof, evaluation and exactness sentences.
Proof: lem-sc-ext-evaluation identifies Hom(F,-) with Fᵛ tensor -. The dual is finite
locally free with the same local ranks, so lem-sc-ext-tensor-exact applies. Forgetting
module structure is exact since kernels and cokernels are formed in abelian sheaves.
(blueprint: lem-sc-ext-locally-free). -/
theorem locallyFreeHomAbelianFunctor_exact {X : Scheme.{u}} (F : X.Modules)
    [F.IsFiniteLocallyFree] :
    (locallyFreeHomAbelianFunctor F).Additive ∧
      PreservesFiniteLimits (locallyFreeHomAbelianFunctor F) ∧
      PreservesFiniteColimits (locallyFreeHomAbelianFunctor F) := sorry

/-- The canonical comparison sends an extension through the exact internal Hom functor,
then precomposes with the identity section, and applies inverse evaluation.
Source: blueprint `lem-sc-ext-locally-free`, proof
(blueprint: lem-sc-ext-locally-free). -/
def locallyFreeExtComparison {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (F G : X.Modules) [F.IsFiniteLocallyFree] (i : ℕ) : Ext F G i →+ (Fᵛ ⊗ G).H i :=
  letI : (locallyFreeHomAbelianFunctor F).Additive :=
    (locallyFreeHomAbelianFunctor_exact F).1
  letI : PreservesFiniteLimits (locallyFreeHomAbelianFunctor F) :=
    (locallyFreeHomAbelianFunctor_exact F).2.1
  letI : PreservesFiniteColimits (locallyFreeHomAbelianFunctor F) :=
    (locallyFreeHomAbelianFunctor_exact F).2.2
  letI := isIso_dualTensorHom_of_isFiniteLocallyFree F G
  let η := (H.zeroLinearEquiv (homObj F F)).symm
    (((SheafOfModules.homObjSectionsEquiv F F).symm (𝟙 F)).val (op ⊤))
  (H.map (inv (dualTensorHom F G)) i).comp
    ((η.precomp ((locallyFreeHomAbelianFunctor F).obj G) (Nat.zero_add i)).comp
      ((locallyFreeHomAbelianFunctor F).mapExtAddHom F G i))

/-- The canonical comparison is bijective.
Source: blueprint `lem-sc-ext-locally-free`, proof.
Proof: evaluation and the global-sections description of sheaf Hom identify Hom(F,-)
with Gamma composed with Fᵛ tensor -. This tensor functor is exact. The tensor-Hom
adjunction makes it preserve injectives (lem-sp-right-adjoint-preserves-injectives),
which are Gamma-acyclic. Scheme modules have enough injectives. The derived-composite
comparison therefore gives the claimed isomorphism, and the Ext identification via
injective resolutions agrees with the displayed map. For F = O, evaluation and the
unit tensor isomorphism give Ext(O,G) = H(G).
(blueprint: lem-sc-ext-locally-free). -/
theorem bijective_locallyFreeExtComparison {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (F G : X.Modules) [F.IsFiniteLocallyFree] (i : ℕ) :
    Function.Bijective (locallyFreeExtComparison F G i) := sorry

/-- The canonical additive isomorphism of Ext with cohomology of the dual tensor.
Source: blueprint `lem-sc-ext-locally-free`, statement and proof
(blueprint: lem-sc-ext-locally-free). -/
def locallyFreeExtAddEquivH {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (F G : X.Modules) [F.IsFiniteLocallyFree] (i : ℕ) : Ext F G i ≃+ (Fᵛ ⊗ G).H i :=
  AddEquiv.ofBijective (locallyFreeExtComparison F G i)
    (bijective_locallyFreeExtComparison F G i)


/-- For the structure sheaf as first argument, the canonical Ext comparison has target
`H^i(X,G)`, by the evaluation identification of the dual of the tensor unit with the unit.
Source: blueprint `lem-sc-ext-locally-free`, final clause
(blueprint: lem-sc-ext-locally-free). -/
def locallyFreeUnitExtAddEquivH {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (G : X.Modules) (i : ℕ) : Ext (SheafOfModules.unit X.ringCatSheaf) G i ≃+ G.H i :=
  let O : X.Modules := 𝟙_ X.Modules
  letI : O.IsInvertible := isInvertible_tensorUnit (X := X)
  letI : O.IsFiniteLocallyFree := SheafOfModules.IsInvertible.isFiniteLocallyFree O
    (h := IsInvertible.sheafOfModules_isInvertible O)
  (locallyFreeExtAddEquivH O G i).trans
    (H.mapLinearEquiv
      (whiskerRightIso ((λ_ Oᵛ).symm ≪≫ asIso (dualEvaluation O)) G ≪≫ λ_ G) i).toAddEquiv

end

end AlgebraicGeometry.Scheme.Modules
