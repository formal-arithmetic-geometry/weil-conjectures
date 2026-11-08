/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.ConstructibleSheaf.KernelCokernel
public import Submission.WeilConjectures.ConstructibleSheaf.StalkCardinality
public import Submission.WeilConjectures.ConstructibleSheaf.Pullback
public import Mathlib.Topology.NoetherianSpace
public import Submission.WeilConjectures.CategoryTheory.Abelian.AdicImageTower

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Exact `ℓ`-adic towers from uniformly Artin-Rees towers of étale sheaves

Let `X` be a scheme and `(Hₙ)` a tower of étale sheaves of `Λ`-modules on `X` which is
**uniformly Artin-Rees** with constant `c` (`AlgebraicGeometry.Etale.IsArtinReesTower`): at every
geometric point `s`, with `L_s` the limit of the tower of stalks `((Hₙ)_s)ₙ`, the kernel of
`L_s ⟶ (Hₘ)_s` is `ℓᵐ L_s`, the image of `(Hₘ₊꜀)_s ⟶ (Hₘ)_s` is contained in that of `L_s`, and
`ℓᶜ` kills the `ℓ`-power torsion of `L_s`. This is the situation of the higher direct images
`Hₙ = Rʲf_* Gₙ` of an `ℓ`-adic tower along a smooth proper morphism.

Then the `ℓ`-adic image tower `G'ₘ = ℓᶜ · im(H_{m+2c} ⟶ H_{m+c}) ⊆ H_{m+c}`
(`CategoryTheory.Functor.adicImageTower`) is an exact `ℓ`-adic tower:

- its transition maps `G'ₖ ⟶ G'ₙ` are cokernels of `ℓⁿ`
  (`AlgebraicGeometry.Etale.IsArtinReesTower.isColimitCokernelCofork`) and it is flat, so that it
  carries an `ℓ`-adic tower structure
  (`AlgebraicGeometry.Etale.IsArtinReesTower.adicTowerStructure`);
- its terms are finite locally constant if the `Hₙ` are, `Λ` being noetherian
  (`AlgebraicGeometry.Etale.isFiniteLocallyConstantSheaf_adicImageTower`);
- over a discrete valuation ring `Λ` in which `ℓ` is a nonzero nonunit, the stalks of `G'ₘ` are
  `ℓᶜL_s / ℓᵐ⁺ᶜL_s ≅ (Λ / ℓᵐ)ʳ`
  (`AlgebraicGeometry.Etale.IsArtinReesTower.exists_linearEquiv_sheafFiber`).

The inclusion `G'ₘ ⟶ H_{m+c}` is a monomorphism whose cokernel is killed by `ℓ²ᶜ` as soon as
`ℓᶜ : Hₙ ⟶ Hₙ` factors through the transition map `H_{n+c} ⟶ Hₙ`
(`CategoryTheory.Functor.pow_smul_cokernel_π_adicImageTowerι_eq_zero`).

Exactness is checked on the stalks at the geometric points `X.algClosurePoint x`, which form a
conservative family (`AlgebraicGeometry.Etale.exact_of_forall_sheafFiber`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite ZeroObject

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- The stalk functors of étale sheaves of modules are additive. -/
instance {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- An étale sheaf of `Λ`-modules whose stalks at all the geometric points `X.algClosurePoint x`
vanish is zero. -/
lemma isZero_of_forall_isZero_sheafFiber_algClosurePoint
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (h : ∀ x : X, IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ) |>.obj F)) :
    IsZero F := by
  have : IsIso (0 : F ⟶ 0) := Scheme.isIso_of_isIso_sheafFiber_map _ fun x ↦
    (NatIso.isIso_map_iff (GrothendieckTopology.Point.uliftSheafFiberIso.{u + 1}
      (pointSmallEtale (X.algClosurePoint x)) (ModuleCat.{u + 1} Λ)) _).2
      (isIso_of_source_target_iso_zero _ (h x).isoZero
        (Functor.map_isZero _ (isZero_zero _)).isoZero)
  exact (isZero_zero _).of_iso (asIso (0 : F ⟶ 0))

/-- **Exactness of étale sheaves is checked on stalks**: a short complex of étale sheaves of
`Λ`-modules is exact if it is exact on the stalks at all geometric points `X.algClosurePoint x`. -/
lemma exact_of_forall_sheafFiber
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h : ∀ (x : X) (y : (pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ) |>.obj S.X₂),
      (pointSmallEtale (X.algClosurePoint x)).sheafFiber.map S.g y = 0 →
        ∃ z, (pointSmallEtale (X.algClosurePoint x)).sheafFiber.map S.f z = y) :
    S.Exact := by
  rw [S.exact_iff_isZero_homology]
  exact isZero_of_forall_isZero_sheafFiber_algClosurePoint fun x ↦
    ((S.map (pointSmallEtale (X.algClosurePoint x)).sheafFiber).exact_iff_isZero_homology.1
      ((S.map (pointSmallEtale (X.algClosurePoint x)).sheafFiber).moduleCat_exact_iff.2
        (h x))).of_iso
      (S.mapHomologyIso (pointSmallEtale (X.algClosurePoint x)).sheafFiber).symm

/-- A morphism of étale sheaves of `Λ`-modules which is surjective on the stalks at all geometric
points `X.algClosurePoint x` is an epimorphism. -/
lemma epi_of_forall_surjective_sheafFiber_map
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G)
    (h : ∀ x : X, Function.Surjective
      ((pointSmallEtale (X.algClosurePoint x)).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.map φ)) :
    Epi φ :=
  (ShortComplex.exact_iff_epi (ShortComplex.mk φ (0 : G ⟶ 0) Limits.comp_zero)
    rfl).1 (exact_of_forall_sheafFiber fun x y _ ↦ h x y)

/-- On stalks, `n • 𝟙` is multiplication by `n`. -/
lemma sheafFiber_map_nsmul_id_apply {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ)
    (z : (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj F) :
    (pointSmallEtale s).sheafFiber.map (n • 𝟙 F) z = n • z := by
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
  rfl

/-- The image of a morphism between finite locally constant sheaves of modules over a noetherian
ring is finite locally constant. -/
lemma isFiniteLocallyConstantSheaf_image [IsNoetherianRing Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G)
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F]
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) G] :
    IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (image φ) :=
  have := IsFiniteLocallyConstantSheaf.cokernel φ
  have := IsFiniteLocallyConstantSheaf.kernel (cokernel.π φ)
  IsFiniteLocallyConstantSheaf.of_iso (Abelian.imageIsoImage φ)

variable (H : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (ℓ c : ℕ)

/-- The terms of the `ℓ`-adic image tower of a tower of finite locally constant sheaves of modules
over a noetherian ring are finite locally constant. -/
instance isFiniteLocallyConstantSheaf_adicImageTower [IsNoetherianRing Λ]
    [∀ n : ℕ, IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (H.obj (op n))] (m : ℕ) :
    IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) ((H.adicImageTower ℓ c).obj (op m)) :=
  isFiniteLocallyConstantSheaf_image (H.adicImageTowerMap ℓ c m)

/-- A tower `(Hₙ)` of étale sheaves of `Λ`-modules is **uniformly Artin-Rees** with constant `c`
if at every geometric point `s`, with `L_s` the limit of the tower of stalks `((Hₙ)_s)ₙ`, the
image of `(Hₘ₊꜀)_s ⟶ (Hₘ)_s` is contained in that of `L_s`, the kernel of `L_s ⟶ (Hₘ)_s` is
`ℓᵐ L_s`, and `ℓᶜ` kills the `ℓ`-power torsion of `L_s`. -/
structure IsArtinReesTower : Prop where
  exists_eval_eq {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) (m : ℕ)
    (z : (H ⋙ (pointSmallEtale s).sheafFiber).obj (op (m + c))) :
    ∃ x : ModuleCat.sectionsSubmodule (H ⋙ (pointSmallEtale s).sheafFiber),
      x.1 (op m) = ModuleCat.towerMap _ (Nat.le_add_right m c) z
  eval_eq_zero_iff {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) (m : ℕ)
    (x : ModuleCat.sectionsSubmodule (H ⋙ (pointSmallEtale s).sheafFiber)) :
    x.1 (op m) = 0 ↔ ∃ y, ℓ ^ m • y = x
  pow_smul_eq_zero {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (y : ModuleCat.sectionsSubmodule (H ⋙ (pointSmallEtale s).sheafFiber)) (k : ℕ) :
    ℓ ^ k • y = 0 → ℓ ^ c • y = 0

namespace IsArtinReesTower

variable {H ℓ c} (hH : IsArtinReesTower H ℓ c)
  (hzero : ∀ n : ℕ, ℓ ^ n • 𝟙 (H.obj (op n)) = 0)

include hH in
/-- The transition maps of the `ℓ`-adic image tower are epimorphisms. -/
lemma epi_adicImageTower_map {n k : ℕ} (h : n ≤ k) :
    Epi ((H.adicImageTower ℓ c).map (homOfLE h).op) :=
  epi_of_forall_surjective_sheafFiber_map _ fun x ↦
    H.surjective_map_adicImageTower_map ℓ c _ (hH.exists_eval_eq (X.algClosurePoint x)) h

/-- **The transition maps `G'ₖ ⟶ G'ₙ` of the `ℓ`-adic image tower are cokernels of `ℓⁿ`.** -/
noncomputable def isColimitCokernelCofork {n k : ℕ} (h : n ≤ k) :
    IsColimit (CokernelCofork.ofπ ((H.adicImageTower ℓ c).map (homOfLE h).op)
      (AdicTowerStructure.pow_smul_id_comp_map_eq_zero _ ℓ
        (H.adicImageTower_pow_smul_id_eq_zero ℓ c hzero) h)) :=
  have := hH.epi_adicImageTower_map h
  ShortComplex.Exact.gIsCokernel (S := ShortComplex.mk _ _
    (AdicTowerStructure.pow_smul_id_comp_map_eq_zero _ ℓ
      (H.adicImageTower_pow_smul_id_eq_zero ℓ c hzero) h))
    (exact_of_forall_sheafFiber fun x y hy ↦ by
      obtain ⟨w, hw⟩ := H.exists_pow_smul_eq_of_map_adicImageTower_map_eq_zero ℓ c _
        (hH.exists_eval_eq (X.algClosurePoint x)) (hH.eval_eq_zero_iff (X.algClosurePoint x))
        h y hy
      exact ⟨w, (sheafFiber_map_nsmul_id_apply _ _ _ _).trans hw⟩)

include hH in
/-- **The `ℓ`-adic image tower is flat**: `G'ₙ₊ₘ --ℓⁿ--> G'ₙ₊ₘ --ℓᵐ--> G'ₙ₊ₘ` is exact. -/
lemma exact_pow_smul_adicImageTower (n m : ℕ) :
    (ShortComplex.mk _ _ (AdicTowerStructure.pow_smul_id_comp_pow_smul_id_eq_zero _ ℓ
      (H.adicImageTower_pow_smul_id_eq_zero ℓ c hzero) n m)).Exact :=
  exact_of_forall_sheafFiber fun x y hy ↦ by
    obtain ⟨w, hw⟩ := H.exists_pow_smul_eq_of_pow_smul_eq_zero_adicImageTower ℓ c _
      (hH.exists_eval_eq (X.algClosurePoint x)) (hH.eval_eq_zero_iff (X.algClosurePoint x))
      (hH.pow_smul_eq_zero (X.algClosurePoint x)) n m y
      ((sheafFiber_map_nsmul_id_apply _ _ _ _).symm.trans hy)
    exact ⟨w, (sheafFiber_map_nsmul_id_apply _ _ _ _).trans hw⟩

/-- **The `ℓ`-adic image tower of a uniformly Artin-Rees tower is an `ℓ`-adic tower**: its
transition maps are cokernels of powers of `ℓ` and it is flat
(`CategoryTheory.AdicTowerStructure.ofIsColimit`). -/
noncomputable def adicTowerStructure : AdicTowerStructure (H.adicImageTower ℓ c) ℓ :=
  AdicTowerStructure.ofIsColimit _ ℓ (H.adicImageTower_pow_smul_id_eq_zero ℓ c hzero)
    (fun h ↦ hH.isColimitCokernelCofork hzero h) (hH.exact_pow_smul_adicImageTower hzero)

include hH in
/-- **The stalks of the `ℓ`-adic image tower are `(Λ / ℓᵐ)ʳ`.** Over a discrete valuation ring
`Λ` in which `ℓ` is a nonzero nonunit, if the limit `L_s` of the tower of stalks of `H` at a
geometric point `s` is finitely generated, then there is `r` (the rank of `ℓᶜ L_s`) such that the
stalk of `G'ₘ` at `s` is isomorphic to `(Λ / ℓᵐ)ʳ` for every `m`. -/
theorem exists_linearEquiv_sheafFiber [IsDomain Λ] [IsDiscreteValuationRing Λ]
    (hℓ : (ℓ : Λ) ≠ 0) (hℓ' : ¬IsUnit (ℓ : Λ)) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X)
    [Module.Finite Λ (ModuleCat.sectionsSubmodule (H ⋙ (pointSmallEtale s).sheafFiber))] :
    ∃ r : ℕ, ∀ m : ℕ, Nonempty ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj
      ((H.adicImageTower ℓ c).obj (op m)) ≃ₗ[Λ] (Fin r → Λ ⧸ Ideal.span {(ℓ : Λ) ^ m})) :=
  H.exists_linearEquiv_map_adicImageTower ℓ c _ (hH.exists_eval_eq s) (hH.eval_eq_zero_iff s)
    hℓ hℓ' (hH.pow_smul_eq_zero s)

end IsArtinReesTower


end AlgebraicGeometry.Etale
