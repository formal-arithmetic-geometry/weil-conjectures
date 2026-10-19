/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward
import Sheaf.AlgebraicGeometry.EllAdicConstructibleConstantComparison
import Sheaf.AlgebraicGeometry.EllAdicRationalConstantModelCohomology
import Sheaf.AlgebraicGeometry.EllAdicIntegralConstantModelCohomology
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-! # Constructibility of the cohomology of the localizing exceptional object
(blueprint: lem-sfb-adic-localizing-exceptional-cohomology)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- Geometric restriction on the hull of finite-constant-model constructible complexes.
Source: det-existence-restriction.proof.md, the integral and rational bullets.
Proof: for fields and the finite-subextension-valued algebraic closure, compare Dbc
with Dctf using the finite-Tor theorem. Choose the identity compactification of the
proper map, so its lower shriek is its ambient derived pushforward. Apply rational
geometric restriction, using affine closed-immersion/smooth-projection factorizations
and finite-open gluing. For integral coefficients the Brown adjoint on Loc(Dbc)
is the same adjoint by its counit; integral geometric restriction gives the result.
The fixed coproduct universe is u+1 throughout; the full inclusions and uniqueness
of adjoints identify these with the supplied G. Take cohomology in each degree.
Empty schemes, zero complexes, torsion and arbitrary cohomological degrees are allowed.
-/
private theorem ellAdic_constantModel_rightAdjoint_homology_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {Z Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (g : Z ⟶ Y) [IsProper g.left]
    (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)
    (h : ∀ K, localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Λ Z.left) K →
      localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Λ Y.left)
        ((R((g.left)_*⟦Λ⟧)).obj K))
    (G : (localizingClosureOfSize.{u + 1}
        (constantModelBoundedConstructible Λ Y.left)).FullSubcategory ⥤
      (localizingClosureOfSize.{u + 1}
        (constantModelBoundedConstructible Λ Z.left)).FullSubcategory)
    (adj : (localizingClosureOfSize.{u + 1}
        (constantModelBoundedConstructible Λ Y.left)).lift
      ((localizingClosureOfSize.{u + 1}
        (constantModelBoundedConstructible Λ Z.left)).ι ⋙ R((g.left)_*⟦Λ⟧))
      (fun K ↦ h K.obj K.property) ⊣ G)
    (K : (constantModelBoundedConstructible Λ Y.left).FullSubcategory) :
    ∀ n : ℤ, IsConstantModelConstructible Λ Z.left
      ((DerivedCategory.homologyFunctor _ n).obj
        (G.obj ((ObjectProperty.ιOfLE (constantModel_le_localizingClosure Λ Y.left)).obj
          K)).obj) := by
  cases hΛ with
  | continuous E =>
    exact ellAdic_rational_constantModel_rightAdjoint_homology_constructible
      _ ℓ g (.continuous E) h G adj K
  | integral E =>
    exact ellAdic_integral_constantModel_rightAdjoint_homology_constructible
      ℓ E g h G adj K
  | algebraicClosure =>
    exact ellAdic_rational_constantModel_rightAdjoint_homology_constructible
      _ ℓ g .algebraicClosure h G adj K


variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

/-- Every cohomology object of the supplied localizing right adjoint on a bounded
constructible input is constructible.

Source: blueprint `sk-thm-existence` (4), `det-existence-restriction.proof.md`, Part (2).
Proof: compare local finite-presentation charts with the field, algebraic-closure, and
integral adic models using the cited local triviality and resolution theorems.  The smooth
and closed local restriction calculations preserve constructibility; finite affine descent
and uniqueness of right adjoints identify the result with the supplied `G`.
(blueprint: lem-sfb-adic-localizing-exceptional-cohomology)
-/
theorem ellAdic_localizing_rightAdjoint_obj_homology_constructible
    (G : (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory ⥤
      (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory)
    (adj : ellAdicLocalizingLowerStar Λ ℓ g hΛ ⊣ G)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    ∀ n : ℤ, IsConstructibleModuleObject (condensedRingObj Λ Z.left)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((G.obj ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj)) := by
  have hc (X : Scheme.{u}) [IsNoetherian X] :
      boundedConstructible (condensedRingObj Λ X) =
        constantModelBoundedConstructible Λ X := by
    funext K
    apply propext
    change (_ ∧ _) ↔ (_ ∧ _)
    exact and_congr Iff.rfl (forall_congr' fun n ↦
      ellAdic_constructible_iff_constantModel Λ ℓ hΛ X _)
  have hull (X : Scheme.{u}) [IsNoetherian X] :
      boundedConstructibleLocalizingClosure Λ X =
        localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Λ X) := by
    funext K
    apply propext
    constructor
    · intro hK P hP hSP
      let : P.IsTriangulated := hP.1
      let : P.IsClosedUnderIsomorphisms := hP.2.1
      have (I : Type (u + 1)) : P.IsClosedUnderColimitsOfShape (Discrete I) := by
        apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
        rintro L ⟨D, hD⟩
        exact hP.2.2 D inferInstance (fun i ↦ hD (.mk i))
      have hh : boundedConstructibleLocalizingClosure Λ X ≤ P := by
        apply sInf_le
        exact ⟨fun L hL ↦ hSP L (le_of_eq (hc X) L hL), inferInstance,
          inferInstance, fun _ ↦ inferInstance⟩
      exact hh K hK
    · intro hK
      rw [boundedConstructibleLocalizingClosure, unary_relation_sInf_iff]
      intro P hP
      let Q : ObjectProperty (DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) := P
      let : Q.IsTriangulated := hP.2.2.1
      let : Q.IsClosedUnderIsomorphisms := hP.2.1
      refine hK Q ⟨hP.2.2.1, hP.2.1, ?_⟩
        (fun L hL ↦ hP.1 L (le_of_eq (hc X).symm L hL))
      intro I D hD hp
      let := hD
      let : Q.IsClosedUnderColimitsOfShape (Discrete I) := hP.2.2.2 I
      exact Q.prop_colimit D (fun i ↦ hp i.as)
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsNoetherian Z.left := ⟨⟩
  have : IsNoetherian Y.left := ⟨⟩
  let CZ := localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Λ Z.left)
  let CY := localizingClosureOfSize.{u + 1} (constantModelBoundedConstructible Λ Y.left)
  let iZ := ObjectProperty.ιOfLE (le_of_eq (hull Z.left).symm)
  let iY := ObjectProperty.ιOfLE (le_of_eq (hull Y.left).symm)
  let jZ := ObjectProperty.ιOfLE (le_of_eq (hull Z.left))
  let Gc : CY.FullSubcategory ⥤ CZ.FullSubcategory := iY ⋙ G ⋙ jZ
  have h : ∀ L, CZ L → CY ((R((g.left)_*⟦Λ⟧)).obj L) := by
    intro L hL
    exact le_of_eq (hull Y.left) _
      (ellAdic_localizing_rightDerivedLowerStar_obj Λ ℓ g hΛ L
        (le_of_eq (hull Z.left).symm _ hL))
  let Fc : CZ.FullSubcategory ⥤ CY.FullSubcategory :=
    CY.lift (CZ.ι ⋙ R((g.left)_*⟦Λ⟧)) (fun L ↦ h L.obj L.property)
  have eF : iZ ⋙ ellAdicLocalizingLowerStar Λ ℓ g hΛ ≅ Fc ⋙ iY :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by simp; rfl)
  have eG : iY ⋙ G ≅ Gc ⋙ iZ :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by simp; rfl)
  have adjc : Fc ⊣ Gc := adj.restrictFullyFaithful
    (ObjectProperty.fullyFaithfulιOfLE _) (ObjectProperty.fullyFaithfulιOfLE _) eF eG
  let Kc : (constantModelBoundedConstructible Λ Y.left).FullSubcategory :=
    ⟨K.obj, le_of_eq (hc Y.left) K.obj K.property⟩
  intro n
  have hn := ellAdic_constantModel_rightAdjoint_homology_constructible
    Λ ℓ g hΛ h Gc adjc Kc n
  exact (ellAdic_constructible_iff_constantModel Λ ℓ hΛ Z.left _).mpr hn

end AlgebraicGeometry.ProEtale.CondensedRing
