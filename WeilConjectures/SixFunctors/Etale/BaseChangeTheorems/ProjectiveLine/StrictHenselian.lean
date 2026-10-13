/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
public import WeilConjectures.CategoryTheory.Sites.CoinduceZMod
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyModules
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.FiniteLowerStarLift
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.BaseChange.DerivedForget
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMapDevissage
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# The projective line over a strictly henselian local ring

Let `A` be a strictly henselian local ring with residue field `κ`, let `X = ℙ¹_A` and let
`X₀ = ℙ¹_κ` be its closed fibre, with closed immersion `ι : X₀ ⟶ X` (the base change of
`Spec κ ⟶ Spec A`). For a sheaf `F` on `X_ét` write `F₀ = ι⁻¹ F`. This file records the
comparison between the cohomology of `X` and of `X₀`:

* for an injective sheaf `I` of `𝔽_r`-modules on `X`, the restriction `I₀` has no higher
  cohomology on `X₀`; in degrees `≥ 2` this is a general bound for schemes over a henselian
  pair covered by finitely many affine opens, and in degree `1` it uses the representation of
  `H¹`-classes through finite pushforwards of constant sheaves together with the `H¹`
  comparison for finite constant sheaves;
* restriction `Hᵠ(X, F) ⟶ Hᵠ(X₀, F₀)` is bijective for every torsion sheaf `F`.

The strict-local exchange (blueprint `prop-weil-pbc-strict-local-exchange`), which uses the
proper base change for `ℙ¹`, is in
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk`.

The coefficients `𝔽_r` are `ZMod r` with `r` prime; a sheaf of `𝔽_r`-modules is a sheaf of
`ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))`-modules, following the universe convention of
the `SixFunctors` folder.

## Main statements

- `AlgebraicGeometry.Etale.subsingleton_H_upperStar_of_injective_of_iSup_eq_top`: the
  acyclicity bound for the restriction of an injective sheaf to the closed fibre of a
  separated scheme of finite type over a henselian pair covered by `n + 1` affine opens.
- `AlgebraicGeometry.Etale.exists_sum_eq_of_injective_projectiveLine`: the representation of
  an `H¹`-class of `I₀` by classes of finite pushforwards of constant sheaves.
- `AlgebraicGeometry.Etale.subsingleton_H_projectiveLine_closedFibre_of_injective_of_one_lt`:
  its case of degrees `q ≥ 2`.
- `AlgebraicGeometry.Etale.subsingleton_H_projectiveLine_closedFibre_of_injective`: the
  acyclicity of `I₀` on `ℙ¹_κ`.
- `AlgebraicGeometry.Etale.subsingleton_H_projectiveLine_residueField_of_injective`: an alias
  of the previous statement, recording the `Γ(X₀, -)`-acyclicity of `I₀`.
- `AlgebraicGeometry.Etale.bijective_cohomologyMap_projectiveLine_residueField`: the strictly
  henselian comparison `Hᵠ(ℙ¹_A, F) ≅ Hᵠ(ℙ¹_κ, F₀)`.

## References

- Stacks Project, Section 59.91, <https://stacks.math.columbia.edu/tag/0A3S>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- **Acyclicity bound for restricted injectives.** Let `(A, I)` be a henselian pair, let
`f : Y ⟶ Spec A` be separated and locally of finite type, and let `i : Y₀ ⟶ Y` be the closed
fibre over `Spec A/I`. Suppose `Y` is covered by `n + 1` affine opens. Then for every
injective torsion sheaf `J` of `Λ`-modules on `Y_ét`, the restriction `J|_{Y₀}` has vanishing
cohomology in degrees `q > n`.

Here torsion is required, as in Gabber's affine comparison, which is the input of the case
`n = 0`; the induction on `n` is the Mayer–Vietoris sequence of the closed fibre.
(blueprint: `lemma-weil-pbc-injective-restriction-acyclicity`) -/
theorem Etale.subsingleton_H_upperStar_of_injective_of_iSup_eq_top
    (Λ : Type (u + 1)) [CommRing Λ] {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {Y Y₀ : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [LocallyOfFiniteType f] [IsSeparated f]
    (i : Y₀ ⟶ Y) (f₀ : Y₀ ⟶ Spec (.of (A ⧸ I)))
    (h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    (n : ℕ) (U : Fin (n + 1) → Y.Opens) (hU : ∀ j, IsAffineOpen (U j)) (hcov : ⨆ j, U j = ⊤)
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J] [IsTorsionModuleSheaf J]
    (q : ℕ) (hq : n < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((i)^*[ModuleCat.{u + 1} Λ].obj J)) q) :=
  sorry

section StrictlyHenselian

variable (A : Type u) [CommRing A] [HenselianLocalRing A]
  [IsSepClosed (IsLocalRing.ResidueField A)]

/-- **Representation of an `H¹`-class of a restricted injective.** Let `A` be strictly
henselian, `X = ℙ¹_A`, `ι : X₀ = ℙ¹_κ ⟶ X` the closed fibre, `r` a prime and `I` an injective
sheaf of `𝔽_r`-modules on `X`. Every class `c ∈ H¹(X₀, I₀)` is a finite sum
`c = ∑ⱼ ψⱼ(xⱼ)` of images of classes `xⱼ ∈ H¹(X₀, ((hⱼ)_* Mⱼ)₀)`, where `hⱼ : Vⱼ ⟶ X` is finite
and of finite presentation, `Mⱼ` is a finite `𝔽_r`-module with constant sheaf `Mⱼ` on `Vⱼ`,
and `ψⱼ : (hⱼ)_* Mⱼ ⟶ I` is a morphism of sheaves. (Equivalently `c` is the image of a class
of `H¹(X₀, (⊕ⱼ (hⱼ)_* Mⱼ)₀)` under a map `⊕ⱼ (hⱼ)_* Mⱼ ⟶ I`.)
(blueprint: `lemma-weil-pbc-h1-constructible-representation`) -/
theorem Etale.exists_sum_eq_of_injective_projectiveLine (r : ℕ) [Fact r.Prime]
    (I : Sheaf (ProjectiveLine (Spec (.of A))).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) [Injective I]
    (c : Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
      AddCommGrpCat.{u + 1})).obj ((ProjectiveSpace.map _
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))^*[ModuleCat.{u + 1}
          (ULift.{u + 1} (ZMod r))].obj I)) 1) :
    ∃ (n : ℕ) (V : Fin n → Scheme.{u}) (h : ∀ j, V j ⟶ ProjectiveLine (Spec (.of A)))
      (_ : ∀ j, IsFinite (h j)) (_ : ∀ j, LocallyOfFinitePresentation (h j))
      (M : Fin n → ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) (_ : ∀ j, Finite (M j))
      (ψ : ∀ j, (h j)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))].obj
        ((constantSheaf (V j).smallEtaleTopology _).obj (M j)) ⟶ I)
      (x : ∀ j, Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
        AddCommGrpCat.{u + 1})).obj ((ProjectiveSpace.map _
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))^*[ModuleCat.{u + 1}
            (ULift.{u + 1} (ZMod r))].obj ((h j)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))].obj
              ((constantSheaf (V j).smallEtaleTopology _).obj (M j))))) 1),
      ∑ j, Sheaf.H.map ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
        AddCommGrpCat.{u + 1})).map ((ProjectiveSpace.map _
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))^*[ModuleCat.{u + 1}
            (ULift.{u + 1} (ZMod r))].map (ψ j))) 1 (x j) = c :=
  sorry

omit [IsSepClosed (IsLocalRing.ResidueField A)] in
/-- **Acyclicity on the closed projective line in degrees at least two.** Let `A` be strictly
henselian, `X = ℙ¹_A`, `ι : X₀ = ℙ¹_κ ⟶ X` the closed fibre and `r` a prime. For every injective
sheaf `I` of `𝔽_r`-modules on `X`, `Hᵠ(X₀, I₀) = 0` for `q ≥ 2`: this is the acyclicity bound
`AlgebraicGeometry.Etale.subsingleton_H_upperStar_of_injective_of_iSup_eq_top` for the cover of
`ℙ¹_A` by its two standard affine opens. This is the first step of the proof of the blueprint
node `prop-weil-pbc-p1-acyclicity`. -/
theorem Etale.subsingleton_H_projectiveLine_closedFibre_of_injective_of_one_lt (r : ℕ)
    [Fact r.Prime] (I : Sheaf (ProjectiveLine (Spec (.of A))).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) [Injective I] (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
      AddCommGrpCat.{u + 1})).obj ((ProjectiveSpace.map _
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))^*[ModuleCat.{u + 1}
          (ULift.{u + 1} (ZMod r))].obj I)) q) :=
  Etale.subsingleton_H_upperStar_of_injective_of_iSup_eq_top (ULift.{u + 1} (ZMod r))
    (IsLocalRing.maximalIdeal A) (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A))
    (ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))
    (show _ ⟶ Spec (.of (IsLocalRing.ResidueField A)) from
      ProjectiveLine (Spec (.of (IsLocalRing.ResidueField A))) ↘ _)
    (ProjectiveSpace.isPullback_map _ _) 1
    (fun j ↦ ProjectiveSpace.standardOpen _ _ (ULift.up j))
    (fun j ↦ ProjectiveSpace.isAffineOpen_standardOpen _ _ _)
    (by
      rw [← ProjectiveSpace.iSup_standardOpen _ (Spec (.of A))]
      exact Equiv.ulift.symm.iSup_comp (g := ProjectiveSpace.standardOpen _ _))
    I q hq

/-- **Acyclicity on the closed projective line.** Let `A` be strictly henselian, `X = ℙ¹_A`,
`ι : X₀ = ℙ¹_κ ⟶ X` the closed fibre and `r` a prime. For every injective sheaf `I` of
`𝔽_r`-modules on `X`, `Hᵠ(X₀, I₀) = 0` for `q > 0`. Degrees `q ≥ 2` are
`AlgebraicGeometry.Etale.subsingleton_H_projectiveLine_closedFibre_of_injective_of_one_lt`. In
degree `1`, write a class as `∑ⱼ ψⱼ(xⱼ)` with `xⱼ ∈ H¹(X₀, ((hⱼ)_* Mⱼ)₀)`
(`AlgebraicGeometry.Etale.exists_sum_eq_of_injective_projectiveLine`); each `xⱼ` lifts to
`H¹(X, (hⱼ)_* Mⱼ)`
(`AlgebraicGeometry.Etale.surjective_cohomologyMap_one_lowerStar_constantSheaf`),
and its image in `H¹(X, I)` vanishes since the underlying abelian sheaf of `I` is acyclic
(`CategoryTheory.Sheaf.subsingleton_H_forget₂_of_injective`).
(blueprint: `prop-weil-pbc-p1-acyclicity`) -/
theorem Etale.subsingleton_H_projectiveLine_closedFibre_of_injective (r : ℕ) [Fact r.Prime]
    (I : Sheaf (ProjectiveLine (Spec (.of A))).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) [Injective I] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
      AddCommGrpCat.{u + 1})).obj ((ProjectiveSpace.map _
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))^*[ModuleCat.{u + 1}
          (ULift.{u + 1} (ZMod r))].obj I)) q) := by
  obtain rfl | hq := (Nat.one_le_iff_ne_zero.2 hq.ne').eq_or_lt
  · set ι := ProjectiveSpace.map (ULift.{u} (Fin 2))
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))
    let Λ := ULift.{u + 1} (ZMod r)
    let fo := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
    let e := (asIso (upperStarForget₂ Λ ι).natTrans).symm
    refine ⟨fun c₁ c₂ ↦ ?_⟩
    suffices ∀ c : Sheaf.H ((sheafCompose _ fo).obj ((ι)^*[ModuleCat.{u + 1} Λ].obj I)) 1,
        c = 0 by rw [this c₁, this c₂]
    intro c
    obtain ⟨n, V, h, hfin, -, M, hM, ψ, x, rfl⟩ :=
      Etale.exists_sum_eq_of_injective_projectiveLine A r I c
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    let G := (h j)_*[ModuleCat.{u + 1} Λ].obj
      ((constantSheaf (V j).smallEtaleTopology _).obj (M j))
    let β : (sheafCompose _ fo).obj G ≅ ((h j)_*[AddCommGrpCat.{u + 1}]).obj
        ((constantSheaf (V j).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (M j))) :=
      (lowerStarCompForget₂Iso Λ (h j)).app _ ≪≫
        ((h j)_*[AddCommGrpCat.{u + 1}]).mapIso
          ((constantSheafSheafComposeForget₂Iso (Y := V j) Λ).app (M j))
    have hS := surjective_cohomologyMap_one_lowerStar_constantSheaf
      (IsLocalRing.maximalIdeal A) (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A)) ι
      (show _ ⟶ Spec (.of (IsLocalRing.ResidueField A)) from
        ProjectiveLine (Spec (.of (IsLocalRing.ResidueField A))) ↘ _)
      (ProjectiveSpace.isPullback_map _ _) (h j) (pullback.fst (h j) ι)
      (pullback.snd (h j) ι) (IsPullback.of_hasPullback _ _) (M j)
    obtain ⟨z, hz⟩ := hS (Sheaf.H.map ((ι)^*[AddCommGrpCat.{u + 1}].map β.hom) 1
      (Sheaf.H.map ((e.app G).hom) 1 (x j)))
    have hx : x j = Sheaf.H.map (e.app G).inv 1
        (cohomologyMap ι ((sheafCompose _ fo).obj G) 1 (Sheaf.H.map β.inv 1 z)) := by
      rw [cohomologyMap_map, hz, ← Sheaf.H.map_comp_apply, ← Functor.map_comp,
        Iso.hom_inv_id, CategoryTheory.Functor.map_id, Sheaf.H.map_id_apply,
        ← Sheaf.H.map_comp_apply, Iso.hom_inv_id, Sheaf.H.map_id_apply]
    have : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩
    have hI := CategoryTheory.Sheaf.subsingleton_H_forget₂_of_injective.{u + 1, u + 1, u, u + 1}
      Λ I 0
    have hψ : (e.app G).inv ≫ (sheafCompose _ fo).map ((ι)^*[ModuleCat.{u + 1} Λ].map (ψ j)) =
        (ι)^*[AddCommGrpCat.{u + 1}].map ((sheafCompose _ fo).map (ψ j)) ≫ (e.app I).inv :=
      (e.inv.naturality (ψ j)).symm
    rw [hx]
    refine (Sheaf.H.map_comp_apply (f := (e.app G).inv) _ _).symm.trans ?_
    rw [hψ, Sheaf.H.map_comp_apply]
    refine (congrArg (Sheaf.H.map (e.app I).inv 1)
      (cohomologyMap_map ι 1 ((sheafCompose _ fo).map (ψ j)) _).symm).trans ?_
    rw [Subsingleton.elim (Sheaf.H.map ((sheafCompose _ fo).map (ψ j)) 1 _) 0,
      map_zero, map_zero]
  exact Etale.subsingleton_H_projectiveLine_closedFibre_of_injective_of_one_lt A r I q hq

/-- **Acyclicity of injectives on `ℙ¹_κ`.** Let `A` be strictly henselian, `X = ℙ¹_A` and
`ι : X₀ = ℙ¹_κ ⟶ X` the closed fibre. For a prime `ℓ` and an injective sheaf `I` of
`𝔽_ℓ`-modules on `X`, the restriction `I₀` is `Γ(X₀, -)`-acyclic: `Hᵠ(X₀, I₀) = 0` for all
`q > 0`. In Lean this is the same statement as
`AlgebraicGeometry.Etale.subsingleton_H_projectiveLine_closedFibre_of_injective`.
(blueprint: `lemma-weil-pbc-p1-injective-acyclic`) -/
alias Etale.subsingleton_H_projectiveLine_residueField_of_injective :=
  Etale.subsingleton_H_projectiveLine_closedFibre_of_injective

omit [IsSepClosed (IsLocalRing.ResidueField A)] in
/-- **The comparison for `ℙ¹` in degree zero.** For every étale sheaf `F` of `Λ`-modules on
`ℙ¹_A`, restriction `Γ(ℙ¹_A, F) ⟶ Γ(ℙ¹_κ, F₀)` is bijective: `ℙ¹_A` is proper over the
henselian local ring `A`, so this is
`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_of_henselianRing`. -/
theorem Etale.bijective_cohomologyMap_zero_projectiveLine_residueField
    (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf (ProjectiveLine (Spec (.of A))).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Bijective (Etale.cohomologyMap
      (ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) 0) :=
  (Etale.bijective_cohomologyMap_zero_iff _ _).2
    ((Etale.isIso_globalSectionsUpperStarMap_iff_forget₂ Λ _ F).1
      (Etale.isIso_globalSectionsUpperStarMap_of_henselianRing Λ (IsLocalRing.maximalIdeal A)
        (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A))
        (ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))
        (show _ ⟶ Spec (.of (IsLocalRing.ResidueField A)) from
          ProjectiveLine (Spec (.of (IsLocalRing.ResidueField A))) ↘ _)
        (ProjectiveSpace.isPullback_map _ _) F))

open Abelian in
/-- **The comparison for `ℙ¹` with `𝔽_r`-coefficients.** For a prime `r` and every sheaf `F`
of `𝔽_r`-modules on `ℙ¹_A`, restriction `Hᵠ(ℙ¹_A, F) ⟶ Hᵠ(ℙ¹_κ, F₀)` is bijective. By
induction on `q`, embedding `F` into an injective sheaf `I` of `𝔽_r`-modules: the underlying
abelian sheaves of `I` and of `I₀` have no higher cohomology
(`CategoryTheory.Sheaf.subsingleton_H_forget₂_of_injective` and
`AlgebraicGeometry.Etale.subsingleton_H_projectiveLine_closedFibre_of_injective`), and a
diagram chase in the long exact sequences of `0 ⟶ F ⟶ I ⟶ I/F ⟶ 0` on `ℙ¹_A` and `ℙ¹_κ`
concludes. -/
theorem Etale.bijective_cohomologyMap_projectiveLine_residueField_zmod (r : ℕ) [Fact r.Prime]
    (F : Sheaf (ProjectiveLine (Spec (.of A))).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap
      (ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
        AddCommGrpCat.{u + 1})).obj F) q) := by
  set ι := ProjectiveSpace.map (ULift.{u} (Fin 2))
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))
  let Λ := ULift.{u + 1} (ZMod r)
  let fo := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩
  induction q generalizing F with
  | zero => exact Etale.bijective_cohomologyMap_zero_projectiveLine_residueField A Λ F
  | succ n ih =>
    let i := Injective.ι F
    let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
    have hS : (S.map (sheafCompose _ fo)).ShortExact :=
      shortExact_map_forget₂ Λ { exact := ShortComplex.exact_cokernel i }
    have hS₀ := hS.map_of_exact ((ι)^*[AddCommGrpCat.{u + 1}])
    have hI : Subsingleton (Sheaf.H ((sheafCompose _ fo).obj (Injective.under F)) (n + 1)) :=
      CategoryTheory.Sheaf.subsingleton_H_forget₂_of_injective.{u + 1, u + 1, u, u + 1} Λ _ n
    have hI₀ : Subsingleton (Sheaf.H ((ι)^*[AddCommGrpCat.{u + 1}].obj
        ((sheafCompose _ fo).obj (Injective.under F))) (n + 1)) := by
      have := Etale.subsingleton_H_projectiveLine_closedFibre_of_injective A r
        (Injective.under F) (n + 1) n.succ_pos
      exact ⟨fun a b ↦ (bijective_sheafHMap_hom
        ((asIso (upperStarForget₂ Λ ι).natTrans).app (Injective.under F)) _).1
          (@Subsingleton.elim _ this _ _)⟩
    refine ⟨?_, fun η ↦ ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro ξ hξ
      obtain ⟨z, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS ξ (@Subsingleton.elim _ hI _ _) rfl
      replace hξ := (cohomologyMap_comp_extClass _ hS z).symm.trans hξ
      obtain ⟨w, hw⟩ := Ext.covariant_sequence_exact₃ _ hS₀ _ rfl hξ
      obtain ⟨v, rfl⟩ := (ih _).2 w
      have hvz : v.comp (Ext.mk₀ (S.map (sheafCompose _ fo)).g) (add_zero n) = z :=
        (ih (cokernel i)).1 ((cohomologyMap_comp_mk₀ _ _ v).trans hw)
      rw [← hvz, Ext.comp_assoc _ _ _ (add_zero n) (zero_add 1) (by omega)]
      exact (congrArg (fun t ↦ v.comp t (show n + 1 = n + 1 from rfl)) hS.comp_extClass).trans
        (Ext.comp_zero _ _ _ _ _)
    · obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ hS₀ η (@Subsingleton.elim _ hI₀ _ _) rfl
      obtain ⟨z, rfl⟩ := (ih (cokernel i)).2 y
      exact ⟨z.comp hS.extClass rfl, (cohomologyMap_comp_extClass _ hS z).trans hy⟩

/-- **The strictly henselian comparison for `ℙ¹`.** Let `A` be strictly henselian with
residue field `κ` and `ι : ℙ¹_κ ⟶ ℙ¹_A` the closed fibre. For every torsion sheaf `F` of
`Λ`-modules on `ℙ¹_A` and every `q ≥ 0`, restriction `Hᵠ(ℙ¹_A, F) ⟶ Hᵠ(ℙ¹_κ, F₀)` is
bijective.
(blueprint: `prop-weil-pbc-p1-strict-henselian-comparison`) -/
theorem Etale.bijective_cohomologyMap_projectiveLine_residueField
    (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf (ProjectiveLine (Spec (.of A))).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap
      (ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) := by
  let p := ProjectiveLine (Spec (.of A)) ↘ Spec (.of A)
  let p₀ := ProjectiveLine (Spec (.of (IsLocalRing.ResidueField A))) ↘
    Spec (.of (IsLocalRing.ResidueField A))
  have : CompactSpace (ProjectiveLine (Spec (.of A))) :=
    QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace (ProjectiveLine (Spec (.of A))) :=
    quasiSeparatedSpace_of_quasiSeparated p
  have : CompactSpace (ProjectiveLine (Spec (.of (IsLocalRing.ResidueField A)))) :=
    QuasiCompact.compactSpace_of_compactSpace p₀
  have : QuasiSeparatedSpace (ProjectiveLine (Spec (.of (IsLocalRing.ResidueField A)))) :=
    quasiSeparatedSpace_of_quasiSeparated p₀
  refine bijective_cohomologyMap_of_isTorsion _ (fun r hr G hG q ↦ ?_) _
    ((isTorsionModuleSheaf_iff_isTorsion F).1 inferInstance) q
  have : Fact r.Prime := ⟨hr⟩
  have : (coindZMod.{u + 1} r).IsRightAdjoint := (forget₂CoindZModAdj r).isRightAdjoint
  have : PreservesLimitsOfSize.{u, u + 1} (coindZMod.{u + 1} r) :=
    (forget₂CoindZModAdj r).rightAdjoint_preservesLimits
  have : IsIso (CategoryTheory.Sheaf.coindCounit _ r G) := by
    have : IsIso (CategoryTheory.Sheaf.coindCounit _ r G).hom := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro U
      have hU := forget₂CoindZModAdj_counit_shortExact.{u + 1} r (G.obj.obj U)
      refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨hU.1, fun a ↦ hU.2 a ?_⟩
      have h1 := congr(((sheafToPresheaf _ _).map $hG).app U a)
      simp only [Functor.map_nsmul, NatTrans.app_nsmul, Functor.map_zero, NatTrans.app_zero,
        AddCommGrpCat.hom_nsmul, AddCommGrpCat.hom_zero, AddMonoidHom.nsmul_apply,
        AddMonoidHom.zero_apply] at h1
      rw [natCast_zsmul]
      exact h1
    have : IsIso ((sheafToPresheaf _ _).map (CategoryTheory.Sheaf.coindCounit _ r G)) := this
    exact isIso_of_fully_faithful (sheafToPresheaf _ _) _
  exact bijective_cohomologyMap_of_iso _ (asIso (CategoryTheory.Sheaf.coindCounit _ r G)) q
    (Etale.bijective_cohomologyMap_projectiveLine_residueField_zmod A r _ q)

end StrictlyHenselian

end AlgebraicGeometry
