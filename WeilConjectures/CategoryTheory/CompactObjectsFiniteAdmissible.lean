/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Brown.BrownHypothesesDefinitions
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesCriteria
import WeilConjectures.CategoryTheory.CompactObjectFiniteThickFactor

/-! Compact objects in a localizing closure are the thick closure of compact generators.

Source: Stacks Project Tags 09SN, 09SP, and 094A, as used by the
`det-ctf-finite-compact-generators` detail node.  The proof builds the telescope supplied
by `compactGenerators_buildObjects`, factors the identity of a compact object through a
finite stage with `compact_hom_hocolim`, and applies `compact_factorThrough_thickClosure`.
(blueprint: det-ctf-finite-compact-objects-eq)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace CategoryTheory

/-- The compact-object characterization from the Brown bundle.

Source: `det-ctf-finite-compact-generators`, compact objects paragraph
(blueprint: det-ctf-finite-compact-objects-eq).

Proof: take a small model of the constructible finite-Tor subcategory and use the Brown
bundle's compactness and generation for its representatives. A compact object retracts from
an object in the thick envelope of a finite representative sum by the telescope argument.
The inverse image of the constructible finite-Tor property under the full inclusion is
triangulated and retract stable, and contains every representative and its finite sums.
The universal property of the thick envelope and then retract closure put the compact
object in this property. The reverse implication is the Brown compactness criterion. -/
theorem compact_objects_eq_finite_admissible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (hB : BrownHypothesesFor Λ X) :
    ∃ hTri : (localizingClosureProEtale Λ X).IsTriangulated,
      letI := hTri
      ∃ hSums : HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory,
        letI := hSums
        ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
          @IsCompactObject _ _ _ hSums K ↔
            (constantModelBoundedConstructible Λ X K.obj ∧
              DerivedCategory.finiteTorAmplitude _ K.obj) := by
  classical
  obtain ⟨_, _, _, _, _, hcompact⟩ := (brownHypothesesFor_iff Λ X).mp hB
  obtain ⟨hsmall, hTri, hLIso, hSTri, hSIso, hSRet, hEss, _, hSums, hgen⟩ := hB
  let S := constantModelBoundedConstructible Λ X ⊓
    fun K ↦ DerivedCategory.finiteTorAmplitude _ K
  let L := localizingClosureProEtale Λ X
  let _ := hTri
  let _ := hSums
  let _ := hsmall
  let _ := hSTri
  let _ := hSIso
  let _ := hSRet
  have hSL : S ≤ L := by
    intro K hK P hP hSP
    exact hSP K hK
  let _ : ObjectProperty.EssentiallySmall.{u + 1} S := hEss
  let _ : LocallySmall.{u + 1} S.FullSubcategory :=
    locallySmall_of_faithful (ObjectProperty.ιOfLE hSL)
  obtain ⟨Q, hQ, hQS, hSQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le S
  let _ : LocallySmall.{u + 1} Q.FullSubcategory :=
    locallySmall_of_faithful (ObjectProperty.ιOfLE hQS)
  let _ : (ObjectProperty.ιOfLE hQS).IsEquivalence :=
    (ObjectProperty.isEquivalence_ιOfLE_iff hQS).mpr hSQ
  let _ : EssentiallySmall.{u + 1} S.FullSubcategory :=
    (essentiallySmall_congr (ObjectProperty.ιOfLE hQS).asEquivalence).mp
      (essentiallySmall_of_small_of_locallySmall _)
  let G := SmallModel.{u + 1} S.FullSubcategory
  let e := (equivSmallModel.{u + 1} S.FullSubcategory).symm
  have hL (g : G) : L (e.functor.obj g).obj :=
    hSL _ (e.functor.obj g).property
  let E : G → L.FullSubcategory := fun g ↦ ⟨(e.functor.obj g).obj, hL g⟩
  obtain ⟨hc, hg⟩ := hgen G e hL
  let R : ObjectProperty L.FullSubcategory := S.inverseImage L.ι
  let _ : R.IsStableUnderRetracts := ⟨fun r h ↦ S.prop_of_retract (r.map L.ι) h⟩
  have hE (g : G) : R (E g) := (e.functor.obj g).property
  refine ⟨hTri, hSums, fun K ↦ ⟨?_, hcompact K⟩⟩
  intro hK
  obtain ⟨J, T, hT, ⟨r⟩⟩ := compact_mem_finite_thick_of_generators E hc hg K hK
  have hsum : R (∐ fun i : {i : G // i ∈ J} ↦ E i.1) := by
    let F := fun i : {i : G // i ∈ J} ↦ E i.1
    have : HasFiniteCoproducts L.FullSubcategory := hasFiniteCoproducts_of_hasCoproducts _
    have : HasFiniteBiproducts L.FullSubcategory := HasFiniteBiproducts.of_hasFiniteCoproducts
    apply R.prop_of_iso ((biproduct.isoCoproduct F).symm ≪≫ biproduct.isoProduct F).symm
    exact R.prop_product (fun i ↦ hE i.1)
  have hRT : R T := ((ObjectProperty.triangEnvelope_le_iff _).mpr
    (ObjectProperty.singleton_le_iff.mpr hsum)) T hT
  exact R.prop_of_retract r hRT

end CategoryTheory
