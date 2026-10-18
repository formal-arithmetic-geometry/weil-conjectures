/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.AlgebraicGeometry.ProEtaleUnitsSheaf
public import Sheaf.CategoryTheory.TorsionSheafConstantModule
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-! # Roots of unity on the small pro-etale site

Source: Stacks Project, Section 59.28, Tag 03PK; Definition 59.23.1, Tag 03P4
(blueprint: def-pur-roots-of-unity-sheaf).

The power map, kernel, constant-ring module and transition maps use the original
sectionwise global-sections rings. No invertibility hypothesis on the exponent is imposed.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The `N`-th power morphism on `G_m`, written additively as `N • 𝟙`.
Source: Stacks Project, Tag 03PK (blueprint: def-pur-roots-of-unity-sheaf). -/
def proEtaleUnitsPower (S : Scheme.{u}) (N : ℕ) :
    proEtaleUnitsSheaf S ⟶ proEtaleUnitsSheaf S :=
  N • 𝟙 (proEtaleUnitsSheaf S)

/-- The sheaf of `N`-th roots of unity, the kernel of the power map on `O_Sˣ`.
Source: Stacks Project, Tags 03PK and 03P4 (blueprint: def-pur-roots-of-unity-sheaf). -/
noncomputable def proEtaleRootsOfUnitySheaf (S : Scheme.{u}) (N : ℕ) :
    Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1} :=
  kernel (proEtaleUnitsPower S N)

/-- The canonical inclusion of roots of unity into units.
Source: Stacks Project, Tags 03PK and 03P4 (blueprint: def-pur-roots-of-unity-sheaf). -/
noncomputable def proEtaleRootsOfUnityInclusion (S : Scheme.{u}) (N : ℕ) :
    proEtaleRootsOfUnitySheaf S N ⟶ proEtaleUnitsSheaf S :=
  kernel.ι (proEtaleUnitsPower S N)

/-- The canonical sectionwise identification of the kernel with the roots-of-unity group
is uniquely determined by its compatibility with the inclusion into units.
Source: Stacks Project, Tags 03PK and 03P4 (blueprint: def-pur-roots-of-unity-sheaf).
Proof: the inclusion of abelian sheaves into presheaves creates kernels and evaluation
preserves them. Thus its sectionwise kernel is the subgroup of units whose `N`-th power
is one, precisely Mathlib's `rootsOfUnity`. The inclusion determines the identification
uniquely because it is injective. Universe lifting and additive notation change no elements. -/
theorem existsUnique_proEtaleRootsOfUnitySections (S : Scheme.{u}) (N : ℕ) (U : S.ProEtᵒᵖ) :
    ∃! e : (proEtaleRootsOfUnitySheaf S N).obj.obj U ≃+
        Additive (rootsOfUnity N ((proEtaleStructureSheaf S).obj.obj U)),
      ∀ x, ULift.up (Additive.ofMul (Additive.toMul (e x)).val) =
        (proEtaleRootsOfUnityInclusion S N).hom.app U x := by
  sorry

/-- Sections of the roots-of-unity sheaf, identified by the canonical kernel inclusion.
Source: Stacks Project, Tags 03PK and 03P4 (blueprint: def-pur-roots-of-unity-sheaf).
The selected equivalence is uniquely characterized, rather than an arbitrary isomorphism. -/
noncomputable def proEtaleRootsOfUnitySections (S : Scheme.{u}) (N : ℕ) (U : S.ProEtᵒᵖ) :
    (proEtaleRootsOfUnitySheaf S N).obj.obj U ≃+
      Additive (rootsOfUnity N ((proEtaleStructureSheaf S).obj.obj U)) :=
  (existsUnique_proEtaleRootsOfUnitySections S N U).exists.choose

/-- Every group of sections is killed by `N`.
Source: Stacks Project, Tag 03PK (blueprint: def-pur-roots-of-unity-sheaf).
Proof: use the sectionwise kernel description: a section is a unit `x` with `x^N = 1`.
In additive notation this equality is `N • x = 0`. Injectivity of the kernel inclusion
then proves the same equality in the roots-of-unity sheaf. -/
theorem proEtaleRootsOfUnity_nsmul (S : Scheme.{u}) (N : ℕ)
    (U : S.ProEtᵒᵖ) (x : (proEtaleRootsOfUnitySheaf S N).obj.obj U) : N • x = 0 := by
  sorry

/-- The constant coefficient ring in the ambient universe of pro-etale abelian sheaves.
Source: Stacks Project, Tags 03PK and 03CY (blueprint: def-pur-roots-of-unity-sheaf). -/
noncomputable abbrev proEtaleRootsOfUnityCoefficientRing (S : Scheme.{u}) (N : ℕ) :
    Sheaf (ProEt.topology S) RingCat.{u + 1} :=
  constantZModRingSheaf.{u + 1} (ProEt.topology S) N

/-- The canonical module sheaf over the constant ring sheaf `Z/N` for positive `N`.
Source: Stacks Project, Tags 03PK and 03CY (blueprint: def-pur-roots-of-unity-sheaf). -/
noncomputable def proEtaleRootsOfUnityModule (S : Scheme.{u}) (N : ℕ) (hN : 0 < N) :
    ringedSiteModules.{u + 1} (proEtaleRootsOfUnityCoefficientRing S N) :=
  torsionSheafModule.{u + 1} (ProEt.topology S) N hN (proEtaleRootsOfUnitySheaf S N)
    (proEtaleRootsOfUnity_nsmul S N)

/-- Taking the `(N'/N)`-th power of an `N'`-th root lands in the kernel of `[N]`.
Source: Stacks Project, Tag 03PK (blueprint: def-pur-roots-of-unity-sheaf).
Proof: from `N ∣ N'` and positive `N`, obtain `(N'/N)*N = N'`. Compose the two
power maps and use the kernel equation for `[N']`; sectionwise this is
`(x^(N'/N))^N = x^N' = 1`. -/
theorem proEtaleRootsOfUnityTransition_condition (S : Scheme.{u}) (N N' : ℕ)
    (hN : 0 < N) (hN' : 0 < N') (h : N ∣ N') :
    (proEtaleRootsOfUnityInclusion S N' ≫
      ((N' / N) • 𝟙 (proEtaleUnitsSheaf S))) ≫ proEtaleUnitsPower S N = 0 := by
  sorry

/-- The transition morphism, induced by `x ↦ x^(N'/N)` on units via the kernel property.
Source: Stacks Project, Tag 03PK (blueprint: def-pur-roots-of-unity-sheaf). -/
noncomputable def proEtaleRootsOfUnityTransition (S : Scheme.{u}) (N N' : ℕ)
    (hN : 0 < N) (hN' : 0 < N') (h : N ∣ N') :
    proEtaleRootsOfUnitySheaf S N' ⟶ proEtaleRootsOfUnitySheaf S N :=
  kernel.lift (proEtaleUnitsPower S N)
    (proEtaleRootsOfUnityInclusion S N' ≫ ((N' / N) • 𝟙 (proEtaleUnitsSheaf S)))
    (proEtaleRootsOfUnityTransition_condition S N N' hN hN' h)

/-- For divisible exponents both sheaves are killed by the larger exponent.
Source: Stacks Project, Tag 03PK (blueprint: def-pur-roots-of-unity-sheaf).
Proof: write `N' = N*k`; an `N`-th root raised to `N'` is `(x^N)^k = 1`.
Apply the sectionwise kernel description. -/
theorem proEtaleRootsOfUnity_nsmul_of_dvd (S : Scheme.{u}) (N N' : ℕ) (h : N ∣ N')
    (U : S.ProEtᵒᵖ) (x : (proEtaleRootsOfUnitySheaf S N).obj.obj U) : N' • x = 0 := by
  sorry

/-- The transition is linear over the constant `Z/N'` sheaf, for the unique canonical actions.
Source: Stacks Project, Tags 03PK and 03CY (blueprint: def-pur-roots-of-unity-sheaf).
Proof: both sheaves are killed by `N'`, by their kernel descriptions and divisibility.
The transition is an additive sheaf morphism. Apply part (2) of
`lem-pur-torsion-sheaf-constant-module` to get sectionwise linearity. -/
theorem proEtaleRootsOfUnityTransition_linear (S : Scheme.{u}) (N N' : ℕ)
    (hN : 0 < N) (hN' : 0 < N') (h : N ∣ N') :
    ∀ (U : S.ProEtᵒᵖ)
      (a : (proEtaleRootsOfUnityCoefficientRing S N').obj.obj U)
      (x : (proEtaleRootsOfUnitySheaf S N').obj.obj U),
      (proEtaleRootsOfUnityTransition S N N' hN hN' h).hom.app U
        (@SMul.smul _ _ (torsionSheafModuleStructure.{u + 1} (ProEt.topology S) N' hN'
          (proEtaleRootsOfUnitySheaf S N') (proEtaleRootsOfUnity_nsmul S N') U).toSMul a x) =
        @SMul.smul _ _ (torsionSheafModuleStructure.{u + 1} (ProEt.topology S) N' hN'
          (proEtaleRootsOfUnitySheaf S N)
          (proEtaleRootsOfUnity_nsmul_of_dvd S N N' h) U).toSMul a
          ((proEtaleRootsOfUnityTransition S N N' hN hN' h).hom.app U x) := by
  sorry

/-- The transition as a morphism of sheaves of modules over the larger constant ring.
Source: Stacks Project, Tags 03PK and 03CY (blueprint: def-pur-roots-of-unity-sheaf). -/
noncomputable def proEtaleRootsOfUnityTransitionModule (S : Scheme.{u}) (N N' : ℕ)
    (hN : 0 < N) (hN' : 0 < N') (h : N ∣ N') :
    torsionSheafModule.{u + 1} (ProEt.topology S) N' hN' (proEtaleRootsOfUnitySheaf S N')
      (proEtaleRootsOfUnity_nsmul S N') ⟶
    torsionSheafModule.{u + 1} (ProEt.topology S) N' hN' (proEtaleRootsOfUnitySheaf S N)
      (proEtaleRootsOfUnity_nsmul_of_dvd S N N' h) :=
  ⟨PresheafOfModules.homMk (proEtaleRootsOfUnityTransition S N N' hN hN' h).hom
    (proEtaleRootsOfUnityTransition_linear S N N' hN hN' h)⟩

/-- For a prime `ℓ`, the transition between consecutive powers is `x ↦ x^ℓ`.
Source: Stacks Project, Tag 03PK (blueprint: def-pur-roots-of-unity-sheaf).
Proof: since `ℓ > 0`, division gives `ℓ^(r+2) / ℓ^(r+1) = ℓ`. The kernel lift's
composite with the inclusion is the power map with this quotient exponent. Evaluate
that equality at `U` and the section `x`. -/
theorem proEtaleRootsOfUnityTransition_prime (S : Scheme.{u}) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (r : ℕ) (U : S.ProEtᵒᵖ)
    (x : (proEtaleRootsOfUnitySheaf S (ℓ ^ (r + 2))).obj.obj U) :
    (proEtaleRootsOfUnityInclusion S (ℓ ^ (r + 1))).hom.app U
      ((proEtaleRootsOfUnityTransition S (ℓ ^ (r + 1)) (ℓ ^ (r + 2))
        (pow_pos hℓ.pos _) (pow_pos hℓ.pos _)
        (pow_dvd_pow ℓ (Nat.le_succ (r + 1)))).hom.app U x) =
      ℓ • (proEtaleRootsOfUnityInclusion S (ℓ ^ (r + 2))).hom.app U x := by
  sorry

/-- The inverse system indexed by `r ≥ 1`; the natural-number index `r` denotes `r+1`.
Source: Stacks Project, Tag 03PK and the coefficient-twist blueprint
(blueprint: def-pur-roots-of-unity-sheaf).
Each successor transition is the specified power map; arbitrary transitions are composites. -/
noncomputable def proEtaleRootsOfUnityTower (S : Scheme.{u}) (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ℕᵒᵖ ⥤ Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1} :=
  Functor.ofOpSequence
    (X := fun r ↦ proEtaleRootsOfUnitySheaf S (ℓ ^ (r + 1))) (fun r ↦
    proEtaleRootsOfUnityTransition S (ℓ ^ (r + 1)) (ℓ ^ (r + 2))
      (pow_pos hℓ.pos _) (pow_pos hℓ.pos _) (pow_dvd_pow ℓ (Nat.le_succ (r + 1))))

end AlgebraicGeometry.Scheme
