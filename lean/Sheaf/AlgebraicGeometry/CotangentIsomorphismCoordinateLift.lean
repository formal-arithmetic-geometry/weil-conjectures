/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q152
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap

import Sheaf.AlgebraicGeometry.EtaleLocalNormalForm

/-!
# Compatible etale coordinates from cotangent-fibre isomorphisms

Source: Stacks Project, morphisms.tex, Tags 054L and 02GU; algebra.tex, Tag 0H93;
the compatible-coordinate argument in DAG Steps 1--6
(blueprint: lem-trf-cotangent-isomorphism-coordinate-lift).

We use the canonical pullback map on differential sheaves, take its stalk and extend
scalars to the residue field. Its source is canonically the ambient differential fibre
over that same residue field. The final open of X is the full inverse image of both
ambient opens. Agreement is equality of scheme morphisms, retaining nilpotents.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Every supplied etale chart near the second marked point can be retained and lifted
through the first closed immersion. The g_j are actual functions, and their differential
classes form a basis of the first ambient differential fibre. Its residue field is
canonically kappa(x), since the ambient morphism is a closed immersion. Allowing any
number n of supplied coordinates also records that n equals the intrinsic dimension.
Source: Stacks Tags 054L, 02GU and 0H93; the refinement in DAG Steps 1--6
(blueprint: lem-trf-cotangent-isomorphism-coordinate-lift).

Proof:
1. Restrict the supplied chart to an affine neighbourhood. The etale differential basis
   of lem-trf-etale-coordinate-derivations-jacobian and the second fibre isomorphism show
   that n is the intrinsic dimension, including n=0.
2. Avoid the closed image in M_1 of the complement of the chart in X. On an affine first
   ambient open the closed quotient is surjective on sections. Lift each restricted
   coordinate to an actual function g_j and use AffineSpace.homOfVector to define e_1.
3. Canonical functoriality sends dg_j and the second coordinate differential to the same
   intrinsic class. Invert the first fibre map to obtain the asserted basis.
4. The chosen-coordinate criterion lem-pur-etale-at-point-from-differentials makes e_1
   etale near the marked point; take a principal affine subneighbourhood there.
5. Synchronize inverse images using the common-principal-neighbourhood calculation:
   D(g) inside D(f), with g=a/f^N there, is D(fa) in the other affine chart. Lift the
   defining equations through the two affine closed quotients. Localization of a quotient
   shows the resulting inverse images equal W as open subschemes.
6. Restrict g_j and the supplied chart. Open restrictions preserve etaleness. Equality
   on W holds coordinate by coordinate in its unreduced section ring; hence it holds as
   a scheme morphism. Restriction and the closed-immersion residue-field identification
   preserve the differential basis. These are precisely the six steps of the node. -/
theorem Scheme.Hom.exists_lift_of_etale_coordinates_of_cotangent_isomorphisms
    (k : Type u) [Field k] {X M₁ M₂ : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (q₁ : M₁ ⟶ Spec (.of k)) [LocallyOfFiniteType q₁] [QuasiCompact q₁] [Smooth q₁]
    (q₂ : M₂ ⟶ Spec (.of k)) [LocallyOfFiniteType q₂] [QuasiCompact q₂] [Smooth q₂]
    (i₁ : X ⟶ M₁) [IsClosedImmersion i₁] (i₂ : X ⟶ M₂) [IsClosedImmersion i₂]
    (hi₁ : i₁ ≫ q₁ = p) (hi₂ : i₂ ≫ q₂ = p) (x : X)
    (hα₁ : IsIso ((ModuleCat.extendScalars (X.residue x).hom).map
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
        (q₁.relativeDifferentialsPullbackMap i₁))))
    (hα₂ : IsIso ((ModuleCat.extendScalars (X.residue x).hom).map
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
        (q₂.relativeDifferentialsPullbackMap i₂))))
    (n : ℕ) (V₂ : M₂.Opens) (hx₂ : i₂ x ∈ V₂)
    (e₂ : V₂.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)))
    [Etale e₂]
    (he₂ : e₂ ≫ (AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)) ↘ Spec (.of k)) =
      V₂.ι ≫ q₂) :
    n = Module.finrank (X.residueField x)
        ((ModuleCat.extendScalars (X.residue x).hom).obj
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj p.relativeDifferentials)) ∧
    ∃ (V₁ : M₁.Opens) (V₂' : M₂.Opens) (W : X.Opens)
      (hx₁ : i₁ x ∈ V₁) (hV₂ : V₂' ≤ V₂)
      (hW₁ : W ≤ i₁ ⁻¹ᵁ V₁) (hW₂ : W ≤ i₂ ⁻¹ᵁ V₂')
      (g : Fin n → Γ(V₁.toScheme, ⊤))
      (b : Module.Basis (Fin n)
        (IsLocalRing.ResidueField (V₁.toScheme.presheaf.stalk ⟨i₁ x, hx₁⟩))
        (IsLocalRing.ResidueField (V₁.toScheme.presheaf.stalk ⟨i₁ x, hx₁⟩)
          ⊗[V₁.toScheme.presheaf.stalk ⟨i₁ x, hx₁⟩]
            ((RingedSpace.moduleStalkFunctor V₁.toScheme.toRingedSpace ⟨i₁ x, hx₁⟩).obj
              (V₁.ι ≫ q₁).relativeDifferentials))),
      IsAffineOpen V₁ ∧ IsAffineOpen V₂' ∧ IsAffineOpen W ∧ x ∈ W ∧
      W = i₁ ⁻¹ᵁ V₁ ∧ W = i₂ ⁻¹ᵁ V₂' ∧
      (∀ j : Fin n, b j = TensorProduct.tmul (V₁.toScheme.presheaf.stalk ⟨i₁ x, hx₁⟩)
        (N := (RingedSpace.moduleStalkFunctor V₁.toScheme.toRingedSpace ⟨i₁ x, hx₁⟩).obj
          (V₁.ι ≫ q₁).relativeDifferentials)
        (1 : IsLocalRing.ResidueField (V₁.toScheme.presheaf.stalk ⟨i₁ x, hx₁⟩))
        ((V₁.ι ≫ q₁).relativeDifferentials.presheaf.germ ⊤ ⟨i₁ x, hx₁⟩ trivial
          ((V₁.ι ≫ q₁).relativeDifferentialsDerivation.d (g j)))) ∧
      Etale (AffineSpace.homOfVector (V₁.ι ≫ q₁)
        (fun j : ULift.{u} (Fin n) ↦ g j.down)) ∧
      i₁.resLE V₁ W hW₁ ≫
          AffineSpace.homOfVector (V₁.ι ≫ q₁) (fun j : ULift.{u} (Fin n) ↦ g j.down) =
        i₂.resLE V₂' W hW₂ ≫ M₂.homOfLE hV₂ ≫ e₂ := by
  sorry

/-- Two smooth closed ambient schemes with invertible canonical differential-fibre maps
admit compatible etale charts on affine neighbourhoods. The natural number d is the
dimension of the intrinsic differential fibre over kappa(x).
Source: Stacks Tags 054L, 02GU and 0H93, and the agent compatible-coordinate consequence
(blueprint: lem-trf-cotangent-isomorphism-coordinate-lift).

Proof:
1. Apply sbc-thm-etale-local-normal-form to the second smooth ambient scheme. On an affine
   chart its etale coordinate differentials are a basis by
   lem-trf-etale-coordinate-derivations-jacobian. The second stipulated isomorphism
   identifies their fibre with the intrinsic fibre, so the number of coordinates is d.
2. Choose an affine first ambient neighbourhood whose inverse image in X lies in the
   second chart. A closed immersion is an affine quotient, so lift the actual restricted
   coordinate sections through that quotient, without reducing X.
3. Functoriality of the universal derivation identifies their intrinsic differentials.
   Transport the second coordinate basis through the two given fibre isomorphisms.
4. Apply lem-pur-etale-at-point-from-differentials to the lifted functions. Shrink the
   first ambient scheme to a principal affine neighbourhood on which its map is etale.
5. The two affine inverse-image opens of X have a common neighbourhood principal in both:
   choose D(f) in one inside the other, then D(g) in the other inside D(f); expressing
   g as a/f^N on D(f) gives D(g)=D(fa) in the first. Lift both principal equations through
   the respective closed quotients, obtaining affine ambient opens with identical
   scheme-theoretic inverse image W, which is affine and contains x.
6. Restrict both charts. Etaleness persists under open restriction by
   lem-weil-pbc-etale-composition-cancellation. Their restrictions to W are equal because
   the polynomial-coordinate ring maps agree already in the quotient, including nilpotents. -/
theorem Scheme.Hom.exists_compatible_etale_coordinates_of_cotangent_isomorphisms
    (k : Type u) [Field k] {X M₁ M₂ : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (q₁ : M₁ ⟶ Spec (.of k)) [LocallyOfFiniteType q₁] [QuasiCompact q₁] [Smooth q₁]
    (q₂ : M₂ ⟶ Spec (.of k)) [LocallyOfFiniteType q₂] [QuasiCompact q₂] [Smooth q₂]
    (i₁ : X ⟶ M₁) [IsClosedImmersion i₁] (i₂ : X ⟶ M₂) [IsClosedImmersion i₂]
    (hi₁ : i₁ ≫ q₁ = p) (hi₂ : i₂ ≫ q₂ = p) (x : X)
    (hα₁ : IsIso ((ModuleCat.extendScalars (X.residue x).hom).map
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
        (q₁.relativeDifferentialsPullbackMap i₁))))
    (hα₂ : IsIso ((ModuleCat.extendScalars (X.residue x).hom).map
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
        (q₂.relativeDifferentialsPullbackMap i₂)))) :
    ∃ (d : ℕ) (V₁ : M₁.Opens) (V₂ : M₂.Opens) (W : X.Opens)
      (hW₁ : W ≤ i₁ ⁻¹ᵁ V₁) (hW₂ : W ≤ i₂ ⁻¹ᵁ V₂)
      (e₁ : V₁.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) (Spec (.of k)))
      (e₂ : V₂.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) (Spec (.of k))),
      d = Module.finrank (X.residueField x)
        ((ModuleCat.extendScalars (X.residue x).hom).obj
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj p.relativeDifferentials)) ∧
      IsAffineOpen V₁ ∧ IsAffineOpen V₂ ∧ IsAffineOpen W ∧ x ∈ W ∧
      W = i₁ ⁻¹ᵁ V₁ ∧ W = i₂ ⁻¹ᵁ V₂ ∧
      Etale e₁ ∧ Etale e₂ ∧
      e₁ ≫ (AffineSpace (ULift.{u} (Fin d)) (Spec (.of k)) ↘ Spec (.of k)) = V₁.ι ≫ q₁ ∧
      e₂ ≫ (AffineSpace (ULift.{u} (Fin d)) (Spec (.of k)) ↘ Spec (.of k)) = V₂.ι ≫ q₂ ∧
      i₁.resLE V₁ W hW₁ ≫ e₁ = i₂.resLE V₂ W hW₂ ≫ e₂ := by
  -- Initialize a supplied chart using the smooth local normal form.
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    M₂.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (i₂ x)) isOpen_univ
  obtain ⟨n, U, V₂, -, -, -, hx₂, hVU, e, he, hproj⟩ :=
    q₂.exists_etale_to_affineSpace_of_exists_smooth_appLE (i₂ x)
      ⟨⊤, isAffineOpen_top _, V, hV, hxV, le_top,
        q₂.smooth_appLE (isAffineOpen_top _) hV le_top⟩
  have : Etale e := he
  have : Etale (AffineSpace.map (ULift.{u} (Fin n)) U.ι) :=
    MorphismProperty.of_isPullback (P := @Etale)
      (AffineSpace.isPullback_map U.ι).flip inferInstance
  let e₂ := e ≫ AffineSpace.map (ULift.{u} (Fin n)) U.ι
  have he₂ : e₂ ≫ (AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)) ↘ Spec (.of k)) =
      V₂.ι ≫ q₂ := by
    dsimp only [e₂]
    rw [Category.assoc, AffineSpace.map_over, ← Category.assoc, hproj,
      Scheme.Hom.resLE_comp_ι]
  -- The supplied-chart clause also gives the dimension and the full inverse-image opens.
  obtain ⟨hd, V₁, V₂', W, hx₁, hV₂, hW₁, hW₂, g, b,
      hV₁, hV₂', hW, hxW, hW₁eq, hW₂eq, -, hg, hcompat⟩ :=
    Scheme.Hom.exists_lift_of_etale_coordinates_of_cotangent_isomorphisms
      k p q₁ q₂ i₁ i₂ hi₁ hi₂ x hα₁ hα₂ n V₂ hx₂ e₂ he₂
  have : Etale (AffineSpace.homOfVector (V₁.ι ≫ q₁)
      (fun j : ULift.{u} (Fin n) ↦ g j.down)) := hg
  refine ⟨n, V₁, V₂', W, hW₁, hW₂,
    AffineSpace.homOfVector (V₁.ι ≫ q₁) (fun j : ULift.{u} (Fin n) ↦ g j.down),
    M₂.homOfLE hV₂ ≫ e₂, hd, hV₁, hV₂', hW, hxW, hW₁eq, hW₂eq,
    inferInstance, inferInstance, AffineSpace.homOfVector_over _ _, ?_, ?_⟩
  · rw [Category.assoc, he₂, ← Category.assoc, Scheme.homOfLE_ι]
  · simpa only [Category.assoc] using hcompat


end AlgebraicGeometry
