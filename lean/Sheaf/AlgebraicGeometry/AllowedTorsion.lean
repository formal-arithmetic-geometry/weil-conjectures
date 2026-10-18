/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q105
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Smooth morphisms and globally allowed torsion

Source:
 literature/blueprint/main-20261015/blueprint/sec-smooth-base-change/sk-def-smooth/_section.md
(blueprint: sk-def-smooth)

The smoothness criterion is the existing
`smooth_iff_flat_locallyOfFinitePresentation_smooth_fiberToSpecResidueField`.
Affine-space smoothness is the existing `AffineSpace.smoothOfRelativeDimension_over`.
Allowed torsion is the existing `Scheme.IsTorsionSheafOfInvertibleOrder`, with a separate
positive globally invertible annihilator for every geometric-stalk element. These notions
and statements are reused, not redeclared. This module supplies the specified divisibility
colimit and the global-versus-local counterexample.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
open Scheme

/-- The positive integers whose scalar is a unit in the ring of global sections of `S`.
Source:
 literature/blueprint/main-20261015/blueprint/sec-smooth-base-change/sk-def-smooth/_section.md
(blueprint: sk-def-smooth) -/
def allowedTorsionIntegers (S : Scheme.{u}) : Type :=
  {d : ℕ // 0 < d ∧ IsUnit (d : Γ(S, ⊤))}

/-- Divisibility orders the globally invertible positive integers.
Source: blueprint `sec-smooth-base-change/sk-def-smooth`, filtered-union clause
(blueprint: sk-def-smooth). -/
instance (S : Scheme.{u}) : LE (allowedTorsionIntegers S) where
  le d e := d.1 ∣ e.1

/-- The divisibility preorder on the allowed indices.
Source: blueprint `sec-smooth-base-change/sk-def-smooth`, filtered-union clause
(blueprint: sk-def-smooth). -/
instance (S : Scheme.{u}) : Preorder (allowedTorsionIntegers S) where
  le_refl d := dvd_refl d.1
  le_trans _ _ _ h₁ h₂ := dvd_trans h₁ h₂

/-- The allowed integers form a small filtered category under divisibility.
Source: blueprint `sec-smooth-base-change/sk-def-smooth`, proof step 3
(blueprint: sk-def-smooth).
Proof: `1` is positive and a global unit, so the category is nonempty. For two indices
`d` and `e`, their product is positive and a global unit, and both divide it. Parallel
arrows in a preorder are equal, so the parallel-arrow condition is automatic. The index
type is a subtype of the natural numbers and hence small. -/
@[instance] theorem allowedTorsionIntegers_isFiltered (S : Scheme.{u}) :
    IsFiltered (allowedTorsionIntegers S) := by
  sorry

/-- The subsheaf killed by an integer, as the underlying object of the categorical kernel.
Source:
 literature/blueprint/main-20261015/blueprint/sec-smooth-base-change/sk-def-smooth/_section.md
(blueprint: sk-def-smooth) -/
noncomputable def allowedTorsionSubsheaf {Λ : Type (u + 1)} [CommRing Λ]
    {T : Scheme.{u}} (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (d : ℕ) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (Subobject.underlying).obj (kernelSubobject (d • 𝟙 F))

/-- Divisibility gives the canonical inclusion between integer-torsion kernels.
Source: blueprint `sec-smooth-base-change/sk-def-smooth`, proof step 3
(blueprint: sk-def-smooth).
Proof: write `e = d * r` using `h`. The endomorphism `e • 𝟙 F` is the composite of
`d • 𝟙 F` and `r • 𝟙 F`, by bilinearity of composition. Apply
`kernelSubobject_comp_le` to these two endomorphisms. Thus any section killed by `d`
is killed by `e`; this is exactly the asserted order relation on kernel subobjects. -/
lemma allowedTorsionSubsheaf_mono {Λ : Type (u + 1)} [CommRing Λ]
    {T : Scheme.{u}} (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {d e : ℕ} (h : d ∣ e) :
    kernelSubobject (d • 𝟙 F) ≤ kernelSubobject (e • 𝟙 F) := by
  sorry

/-- The divisibility diagram of the integer-torsion subsheaves of `F`.
Source:
 literature/blueprint/main-20261015/blueprint/sec-smooth-base-change/sk-def-smooth/_section.md
(blueprint: sk-def-smooth) -/
noncomputable def allowedTorsionDiagram {Λ : Type (u + 1)} [CommRing Λ]
    (S T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    allowedTorsionIntegers S ⥤ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) := by
  let h : Monotone (fun d : allowedTorsionIntegers S ↦
      kernelSubobject (d.1 • 𝟙 F)) := fun d e hde ↦ allowedTorsionSubsheaf_mono F hde
  exact h.functor ⋙ Subobject.underlying

/-- The canonical cocone from the allowed-torsion subsheaves to `F`.
Source:
 literature/blueprint/main-20261015/blueprint/sec-smooth-base-change/sk-def-smooth/_section.md
(blueprint: sk-def-smooth) -/
noncomputable def allowedTorsionCocone {Λ : Type (u + 1)} [CommRing Λ]
    (S T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Cocone (allowedTorsionDiagram S T F) := by
  let α : allowedTorsionDiagram S T F ⟶ (Functor.const _).obj F :=
    { app := fun d ↦ (kernelSubobject (d.1 • 𝟙 F)).arrow
      naturality := by
        intro d e f
        simp [allowedTorsionDiagram] }
  exact { pt := F, ι := α }

/-- A sheaf with globally allowed torsion is the filtered union of its subsheaves killed by
positive integers invertible on the base: the canonical map from the chosen colimit of the
allowed-torsion diagram to `F` is an isomorphism.
Source:
 literature/blueprint/main-20261015/blueprint/sec-smooth-base-change/sk-def-smooth/_section.md
(blueprint: sk-def-smooth)
Proof, following node steps 3--5 (steps 1--2 use the existing smoothness results above;
step 6 is `allowedTorsionLocalCounterexample_properties` below):
1. The kernel defines a module subsheaf: its sections are killed by `d`, and addition,
negatives, scalar multiplication and restrictions preserve this equation. The sheaf axiom
glues these sections. The forgetful functor preserves kernels
(`def-pur-abelian-sheaf-kernel`, `lem-weil-pbc-module-sheaves-colimits-forgetful`).
2. If `d` divides `e`, writing `e = d * r` gives the kernel inclusion
`allowedTorsionSubsheaf_mono`; uniqueness as subobject inclusions gives composition.
`allowedTorsionIntegers_isFiltered` gives nonemptiness and product upper bounds. The
module-sheaf colimit exists, and the compatible kernel arrows give the displayed map
(`def-weil-pbc-category-colimit`, `lem-weil-pbc-module-sheaves-colimits-forgetful`).
3. Forget scalars. Exact filtered colimits preserve the objectwise monomorphism from this
kernel diagram to the constant diagram with value `F`
(`lem-weil-pbc-abelian-etale-sheaves-grothendieck`). The constant diagram has colimit `F`,
since any two indices map into their product and hence cocone components coincide.
Thus the underlying canonical map is monic.
4. A geometric-stalk element `x` is killed by an allowed `d`. Exact stalks identify the
stalk of the kernel subsheaf with the kernel of multiplication by `d`, so `x` lifts to
that kernel stalk (`prop-weil-pbc-geometric-stalks-exact`). Its image under the colimit
coprojection maps to `x`. Thus the map is surjective on stalks; it is injective there by
exactness and step 3. Conservative geometric stalks make the abelian map an isomorphism
(`lemma-weil-pbc-geometric-stalk-conservative`). Its inverse is module-linear because
applying the injective canonical map to both sides of scalar linearity gives the same
section. No cofinality in all positive integers is assumed. -/
theorem allowedTorsion_colimit_map_isIso {Λ : Type (u + 1)} [CommRing Λ]
    (S T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfInvertibleOrder S F] :
    IsIso (colimit.desc (allowedTorsionDiagram S T F) (allowedTorsionCocone S T F)) := by
  sorry

/-- The open `D(2)` in `Spec ℤ`, used in the global-versus-local torsion example.
Source: blueprint `sec-smooth-base-change/sk-def-smooth`, paragraph 2
(blueprint: sk-def-smooth). -/
def allowedTorsionCounterexampleOpen : (Spec (.of ℤ)).Opens :=
  PrimeSpectrum.basicOpen (2 : ℤ)

/-- The actual extension by zero of the constant `ℤ/2ℤ` module sheaf from `D(2)`.
The harmless `ULift` puts the coefficient ring in the standard module-sheaf universe.
Source: blueprint `sec-smooth-base-change/sk-def-smooth`, paragraph 2; Stacks Tag 03S5
(blueprint: sk-def-smooth). -/
noncomputable def allowedTorsionLocalCounterexample :
    Sheaf (Spec (.of ℤ)).smallEtaleTopology (ModuleCat.{1} (ULift.{1} (ZMod 2))) :=
  (Etale.openImmersionLowerShriek (ModuleCat.{1} (ULift.{1} (ZMod 2)))
    allowedTorsionCounterexampleOpen.ι).obj
      ((constantSheaf allowedTorsionCounterexampleOpen.toScheme.smallEtaleTopology
        (ModuleCat.{1} (ULift.{1} (ZMod 2)))).obj
          (ModuleCat.of (ULift.{1} (ZMod 2)) (ULift.{1} (ZMod 2))))

/-- The displayed `j_!(ℤ/2ℤ)` has annihilators invertible near each underlying point,
but does not have torsion orders globally invertible on `Spec ℤ`.
Source: blueprint `sec-smooth-base-change/sk-def-smooth`, paragraph 2 and proof step 6;
Stacks Tags 03PT, 03S5 (blueprint: sk-def-smooth).
Proof: the constant sheaf has stalk `ℤ/2ℤ` on `D(2)` by
`lem-weil-pbc-constant-sheaf-geometric-stalk`. The extension-by-zero stalk formula
`lem-weil-pbc-extension-by-zero-stalks` gives these stalks on `D(2)` and zero elsewhere.
On `D(2)`, choose the annihilator `2` and the neighbourhood `D(2)`; off this open, choose
`1` and the whole scheme. These annihilators are units on the stated neighbourhoods.
For failure of the global condition, choose a geometric point over the generic point,
which lies in `D(2)`, and the nonzero element of its `ℤ/2ℤ` stalk. The global sections
of `Spec ℤ` are `ℤ`, whose only positive unit is `1`, which cannot kill this element. -/
theorem allowedTorsionLocalCounterexample_properties :
    (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of ℤ))
      (x : ↥((pointSmallEtale t).sheafFiber.obj allowedTorsionLocalCounterexample)),
      ∃ (U : (Spec (.of ℤ)).Opens) (d : ℕ),
        t (IsLocalRing.closedPoint Ω) ∈ U ∧ 0 < d ∧
          IsUnit (d : Γ(U.toScheme, ⊤)) ∧ d • x = 0) ∧
    ¬ Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of ℤ))
      allowedTorsionLocalCounterexample := by
  sorry

end AlgebraicGeometry
