/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.IsFlatOver
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.Flat
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.Modules
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.Proper

/-!
# Noetherian models of proper flat families

Let `V` be an affine scheme, `f : X ⟶ V` proper and of finite presentation, and `ℱ` an
`𝒪_X`-module of finite presentation which is flat over `V`. Then `(f, ℱ)` is the base change of
a pair `(p, 𝒢)` over an affine scheme `S` with Noetherian ring of global sections: `p : Y ⟶ S`
is proper and of finite presentation, `𝒢` is of finite presentation and flat over `S`, and there
is a cartesian square
```
X ---h---> Y
|          |
f          p
v          v
V ---π---> S
```
with `h^* 𝒢 ≅ ℱ` (EGA IV₃, 8.9.1, 8.10.5, 11.2.6; Stacks, Tags 01ZM, 081F, 01ZR).

## Proof

`V` is the limit of the spectra of the finitely generated subrings of `Γ(V, ⊤)`
(`AlgebraicGeometry.Scheme.NoetherianApproximation.ofIsAffine`). The morphism `f` descends to a
separated morphism of finite presentation over a stage (Stacks 01ZQ), the module `ℱ` descends to
a later stage (Stacks 01ZR), and properness (Stacks 081F) and flatness (EGA IV₃ 11.2.6) hold at
all sufficiently large stages.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme.NoetherianApproximation

lemma Scheme.isSeparated_of_isSeparated_hom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
    [Y.IsSeparated] : X.IsSeparated :=
  ⟨by rw [← terminal.comp_from f]; infer_instance⟩

namespace Scheme.Modules

/-- **Noetherian models of proper flat families** (EGA IV₃, 8.9.1, 8.10.5, 11.2.6). Let `V` be an
affine scheme, `f : X ⟶ V` proper and locally of finite presentation, and `ℱ` an `𝒪_X`-module of
finite presentation which is flat over `V`. Then there are an affine scheme `S` with Noetherian
ring of global sections, a morphism `π : V ⟶ S`, a proper morphism `p : Y ⟶ S` of finite
presentation, a module `𝒢` of finite presentation on `Y` which is flat over `S`, and a cartesian
square `h : X ⟶ Y` over `π` with `h^* 𝒢 ≅ ℱ`. -/
theorem exists_isNoetherianRing_model {X V : Scheme.{u}} [IsAffine V] (f : X ⟶ V)
    (ℱ : X.Modules) [IsProper f] [LocallyOfFinitePresentation f] [ℱ.IsFinitePresentation]
    (hℱ : ℱ.IsFlatOver f) :
    ∃ (S Y : Scheme.{u}) (_ : IsAffine S) (_ : IsNoetherianRing Γ(S, ⊤)) (π : V ⟶ S)
      (p : Y ⟶ S) (_ : IsProper p) (_ : LocallyOfFinitePresentation p) (𝒢 : Y.Modules)
      (_ : 𝒢.IsFinitePresentation) (h : X ⟶ Y),
      𝒢.IsFlatOver p ∧ IsPullback h f p π ∧ Nonempty ((Modules.pullback h).obj 𝒢 ≅ ℱ) := by
  let N := ofIsAffine V
  -- Step 1: descend `f` to a separated morphism of finite presentation over a stage.
  obtain ⟨i₁, Y₁, p₁, _, _, _, h₁, H₁⟩ :=
    Scheme.exists_isPullback_of_finitePresentation_of_isSeparated N.isLimit f
  -- Step 2: descend `ℱ` to a stage of the base changed system.
  have (j : Over i₁) : ((baseChangeDiagram N.D p₁).obj j).IsSeparated :=
    have : IsSeparated (pullback.snd p₁ (N.D.map j.hom)) := inferInstance
    have : IsAffine (N.D.obj j.left) :=
      inferInstanceAs (IsAffine (Spec (.of j.left.unop.1)))
    isSeparated_of_isSeparated_hom (pullback.snd p₁ (N.D.map j.hom))
  have : CompactSpace Y₁ := QuasiCompact.compactSpace_of_compactSpace p₁
  let e₁ := H₁.isoPullback
  let ℱ₁ : (pullback p₁ (N.π.app i₁)).Modules := (Modules.pullback e₁.inv).obj ℱ
  obtain ⟨j₂, 𝒢₂, h𝒢₂, ⟨e₂⟩⟩ :=
    exists_isFinitePresentation_pullback_iso_of_isLimit
      (isLimitBaseChangeCone N.D (Cone.mk V N.π) p₁ N.isLimit) ℱ₁
  sorry

end Scheme.Modules

end AlgebraicGeometry
