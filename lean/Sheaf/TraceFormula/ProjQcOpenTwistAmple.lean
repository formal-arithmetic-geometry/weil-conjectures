/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties
import Sheaf.AlgebraicGeometry.ProjTwistSectionBasicOpen
import Sheaf.TraceFormula.ProjCommonDegreeTwistInvertible

/-!
# Sufficiently divisible twists on a quasi-compact Proj open

Source: Stacks Project, Constructions, Tag 01MW and Properties, Tag 01Q2
(blueprint: lem-trf-proj-qc-open-twist-ample).

The statement records the common positive degree whose restricted Proj twists are
invertible and ample, together with the canonical tensor-power identification.

This stage-2 statement record was revalidated by group Q16 on 2026-10-18.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- The pure tensor of a tuple of local sections of a restricted Proj twist.
The empty tuple is the section `1` of the tensor unit; a nonempty tuple tensors
its first section with the tensor of its tail. This is the pure tensor used to
specify the canonical multiplication map in Stacks, Constructions, Equation
(multiply) and Tag 01MW (blueprint: lem-trf-proj-qc-open-twist-ample). -/
def Proj.twistTensorSection
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {U : Scheme.{u}} (j : U ⟶ Proj 𝒜) [IsOpenImmersion j]
    (e : ℕ) (V : U.Opens) :
    ∀ k : ℕ, (Fin k → Γ((Proj.twist 𝒜 (Int.ofNat e)).restrict j, V)) →
      Γ(((Proj.twist 𝒜 (Int.ofNat e)).restrict j).tensorPow k, V)
  | 0, _ => Scheme.Modules.unitSectionsEquiv V 1
  | k + 1, s => Scheme.Modules.tmulSection (s 0)
      (Proj.twistTensorSection 𝒜 j e V k (Fin.tail s))

/-- Sufficiently divisible positive twists are ample on a quasi-compact open of Proj.

Source: Stacks Project, Constructions, Tag 01MW, clauses (2), (3), and (7), and
Properties, Tag 01Q2 (blueprint: lem-trf-proj-qc-open-twist-ample).

Proof: for the empty open take `e = 1`. Otherwise use the standard-open basis and
quasi-compactness (`lem-weil-pbc-proj-standard-open-inclusion`) to choose a finite
positive-degree homogeneous cover, and take a positive common multiple `e` of the
degrees. The common-degree lemma (`lem-trf-proj-common-degree-twist-invertible`)
puts the open inside the invertibility locus W_e and gives the invertibility of
every restricted twist of degree e*k and of the canonical multiplication maps.
Those maps multiply homogeneous local fractions, hence have the displayed action
on every tuple of local sections. Pure tensors locally generate the sheaf tensor
power, so this action specifies the multiplication morphism uniquely.
By `lem-trf-proj-twist-section-basic-open`, homogeneous sections have the standard
opens as their nonvanishing loci, and the affine ones form an open basis. For a
fixed positive k, replace their defining homogeneous elements by their k-th
powers. The nonvanishing loci stay the same and the degrees become multiples of
e*k. Use the multiplication identifications to view these sections as sections
of powers of O_U(e*k). This affine nonvanishing basis and quasi-compactness are
exactly `Scheme.Modules.IsAmple` for O_U(e*k). -/
theorem exists_common_degree_twist_ample
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {U : Scheme.{u}} (j : U ⟶ Proj 𝒜) [IsOpenImmersion j] [CompactSpace U] :
    ∃ e : ℕ, 0 < e ∧
      ∀ k : ℕ, 0 < k →
        ∃ hL : ((Proj.twist 𝒜 (Int.ofNat (e * k))).restrict j).IsInvertible,
          @Scheme.Modules.IsAmple U
            ((Proj.twist 𝒜 (Int.ofNat (e * k))).restrict j) hL ∧
          ∃ μ : ((Proj.twist 𝒜 (Int.ofNat e)).restrict j).tensorPow k ⟶
              (Proj.twist 𝒜 (Int.ofNat (e * k))).restrict j,
            IsIso μ ∧
            ∀ (V : U.Opens)
              (s : Fin k → Γ((Proj.twist 𝒜 (Int.ofNat e)).restrict j, V))
              (x : j ''ᵁ V),
              (((Proj.twist 𝒜 (Int.ofNat (e * k))).restrictAppIso j V).hom
                (Scheme.Modules.Hom.app μ V (Proj.twistTensorSection 𝒜 j e V k s))).val x =
              ∏ i : Fin k,
                ((((Proj.twist 𝒜 (Int.ofNat e)).restrictAppIso j V).hom (s i)).val x :
                  Localization.AtPrime x.val.asHomogeneousIdeal.toIdeal) := by
  sorry

end AlgebraicGeometry
