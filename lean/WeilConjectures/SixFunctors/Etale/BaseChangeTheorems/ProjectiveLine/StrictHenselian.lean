/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
import Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image
import Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass
import Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding

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
* restriction `Hᵠ(X, F) ⟶ Hᵠ(X₀, F₀)` is bijective for every torsion sheaf `F`;
* for a local morphism `A ⟶ B` of strictly henselian local rings, the stalk at the closed
  geometric point of the exchange morphism of `ℙ¹` is the pullback map between the
  cohomologies of the two closed fibres.

The coefficients `𝔽_r` are `ZMod r` with `r` prime; a sheaf of `𝔽_r`-modules is a sheaf of
`ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))`-modules, following the universe convention of
the `SixFunctors` folder.

## Main statements

- `AlgebraicGeometry.Etale.subsingleton_H_upperStar_of_injective_of_iSup_eq_top`: the
  acyclicity bound for the restriction of an injective sheaf to the closed fibre of a
  separated scheme of finite type over a henselian pair covered by `n + 1` affine opens.
- `AlgebraicGeometry.Etale.exists_sum_eq_of_injective_projectiveLine`: the representation of
  an `H¹`-class of `I₀` by classes of finite pushforwards of constant sheaves.
- `AlgebraicGeometry.Etale.subsingleton_H_projectiveLine_closedFibre_of_injective`: the
  acyclicity of `I₀` on `ℙ¹_κ`.
- `AlgebraicGeometry.Etale.subsingleton_H_projectiveLine_residueField_of_injective`: an alias
  of the previous statement, recording the `Γ(X₀, -)`-acyclicity of `I₀`.
- `AlgebraicGeometry.Etale.bijective_cohomologyMap_projectiveLine_residueField`: the strictly
  henselian comparison `Hᵠ(ℙ¹_A, F) ≅ Hᵠ(ℙ¹_κ, F₀)`.
- `AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_strictLocal`: the
  strict-local exchange, and
  `AlgebraicGeometry.Etale.isIso_sheafFiber_baseChangeHomologyMap_strictLocal`: its stalk is an
  isomorphism when the residue field map is.

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
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J] [IsTorsionSheaf J]
    (q : ℕ) (hq : n < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((i)^*[ModuleCat.{u + 1} Λ].obj J)) q) :=
  sorry

section StrictlyHenselian

variable (A : Type u) [CommRing A] [HenselianLocalRing A]
  [IsSepClosed (IsLocalRing.ResidueField A)]

set_option linter.unusedSectionVars false in
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
            (ULift.{u + 1} (ZMod r))].map (ψ j))) 1 (x j) = c := by
  classical
  have : CompactSpace (ProjectiveLine (Spec (.of A))) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A))
  have : QuasiSeparatedSpace (ProjectiveLine (Spec (.of A))) :=
    quasiSeparatedSpace_of_quasiSeparated (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A))
  have : CompactSpace (ProjectiveLine (Spec (.of (IsLocalRing.ResidueField A)))) :=
    QuasiCompact.compactSpace_of_compactSpace
      (ProjectiveLine (Spec (.of (IsLocalRing.ResidueField A))) ↘
        Spec (.of (IsLocalRing.ResidueField A)))
  have : QuasiSeparatedSpace (ProjectiveLine (Spec (.of (IsLocalRing.ResidueField A)))) :=
    quasiSeparatedSpace_of_quasiSeparated
      (ProjectiveLine (Spec (.of (IsLocalRing.ResidueField A))) ↘
        Spec (.of (IsLocalRing.ResidueField A)))
  let Λ := ULift.{u + 1} (ZMod r)
  let i := ProjectiveSpace.map (ULift.{u} (Fin 2))
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))
  have : (sheafCompose
      (ProjectiveLine (Spec (.of (IsLocalRing.ResidueField A)))).smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).Additive :=
    ⟨by intros; rfl⟩
  let T := (i)^*[ModuleCat.{u + 1} Λ] ⋙
    sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  obtain ⟨G, hG, a, z, hz⟩ := Etale.exists_constructible_restriction_class i Λ I 1 c
  obtain ⟨n, V, h, hh, hfp, M, hM, ι, hι⟩ :=
    Etale.finite_pushforward_embedding_of_isConstructibleEtaleModuleSheaf Λ G hG
  let E (j : Fin n) := (h j)_*[ModuleCat.{u + 1} Λ].obj
    ((constantSheaf (V j).smallEtaleTopology _).obj (M j))
  let := hι
  let ψ := Injective.factorThru a ι
  let z' := Sheaf.H.map (T.map ι) 1 z
  refine ⟨n, V, h, hh, hfp, M, hM,
    (fun j ↦ biproduct.ι E j ≫ ψ),
    (fun j ↦ Sheaf.H.map (T.map (biproduct.π E j)) 1 z'), ?_⟩
  change ∑ j, Sheaf.H.map (T.map (biproduct.ι E j ≫ ψ)) 1
    (Sheaf.H.map (T.map (biproduct.π E j)) 1 z') = c
  simp_rw [← Sheaf.H.map_comp_apply, ← T.map_comp, ← Category.assoc]
  let H := T ⋙ Sheaf.functorH _ 1
  have he : ∑ j, H.map (biproduct.π E j ≫ biproduct.ι E j ≫ ψ) = H.map ψ := by
    rw [← H.map_sum]
    simp only [← Category.assoc]
    rw [← Preadditive.sum_comp, IsBilimit.total (biproduct.isBilimit E), Category.id_comp]
  dsimp [H] at he
  have he' := congrArg (fun f ↦ AddCommGrpCat.homAddEquiv f z') he
  rw [map_sum, AddMonoidHom.finsetSum_apply] at he'
  change ∑ j, Sheaf.H.map (T.map (biproduct.π E j ≫ biproduct.ι E j ≫ ψ)) 1 z' =
    Sheaf.H.map (T.map ψ) 1 z' at he'
  simp only [Category.assoc]
  rw [he']
  dsimp [z']
  rw [← Sheaf.H.map_comp_apply, ← T.map_comp, Injective.comp_factorThru]
  exact hz

/-- **Acyclicity on the closed projective line.** Let `A` be strictly henselian, `X = ℙ¹_A`,
`ι : X₀ = ℙ¹_κ ⟶ X` the closed fibre and `r` a prime. For every injective sheaf `I` of
`𝔽_r`-modules on `X`, `Hᵠ(X₀, I₀) = 0` for `q > 0`.
(blueprint: `prop-weil-pbc-p1-acyclicity`) -/
theorem Etale.subsingleton_H_projectiveLine_closedFibre_of_injective (r : ℕ) [Fact r.Prime]
    (I : Sheaf (ProjectiveLine (Spec (.of A))).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) [Injective I] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
      AddCommGrpCat.{u + 1})).obj ((ProjectiveSpace.map _
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))^*[ModuleCat.{u + 1}
          (ULift.{u + 1} (ZMod r))].obj I)) q) := by
  classical
  let k := IsLocalRing.ResidueField A
  let i := ProjectiveSpace.map (ULift.{u} (Fin 2))
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))
  have sq := ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2))
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))
  by_cases hq1 : q = 1
  · subst q
    refine subsingleton_of_forall_eq 0 fun c ↦ ?_
    obtain ⟨n, V, h, hh, hfp, M, hM, ψ, x, hx⟩ :=
      Etale.exists_sum_eq_of_injective_projectiveLine A r I c
    have hz (j : Fin n) :
        Sheaf.H.map ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
          AddCommGrpCat.{u + 1})).map ((i)^*[ModuleCat.{u + 1}
            (ULift.{u + 1} (ZMod r))].map (ψ j))) 1 (x j) = 0 := by
      let := hh j
      let := hfp j
      let := hM j
      exact Etale.finite_pushforward_H_one_image_eq_zero_of_henselianLocalRing
        (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A)) i
        (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) sq
        (ULift.{u + 1} (ZMod r)) I (h j) (M j) (ψ j) (x j)
    rw [← hx]
    exact Finset.sum_eq_zero fun j _ ↦ hz j
  · have hq2 : 1 < q := by omega
    let U : Fin (1 + 1) → (ProjectiveLine (Spec (.of A))).Opens :=
      fun j ↦ ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (.of A)) ⟨j⟩
    have hU (j : Fin (1 + 1)) : IsAffineOpen (U j) :=
      ProjectiveSpace.isAffineOpen_standardOpen _ _ _
    have hcov : ⨆ j, U j = ⊤ := by
      simpa [U, ← Equiv.ulift.symm.iSup_comp] using
        ProjectiveSpace.iSup_standardOpen (ULift.{u} (Fin 2)) (Spec (.of A))
    exact Etale.subsingleton_H_upperStar_of_injective_of_iSup_eq_top
      (ULift.{u + 1} (ZMod r)) (IsLocalRing.maximalIdeal A)
      (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A)) i
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) sq 1 U hU hcov I q hq2

/-- **Acyclicity of injectives on `ℙ¹_κ`.** Let `A` be strictly henselian, `X = ℙ¹_A` and
`ι : X₀ = ℙ¹_κ ⟶ X` the closed fibre. For a prime `ℓ` and an injective sheaf `I` of
`𝔽_ℓ`-modules on `X`, the restriction `I₀` is `Γ(X₀, -)`-acyclic: `Hᵠ(X₀, I₀) = 0` for all
`q > 0`. In Lean this is the same statement as
`AlgebraicGeometry.Etale.subsingleton_H_projectiveLine_closedFibre_of_injective`.
(blueprint: `lemma-weil-pbc-p1-injective-acyclic`) -/
alias Etale.subsingleton_H_projectiveLine_residueField_of_injective :=
  Etale.subsingleton_H_projectiveLine_closedFibre_of_injective

/-- **The strictly henselian comparison for `ℙ¹`.** Let `A` be strictly henselian with
residue field `κ` and `ι : ℙ¹_κ ⟶ ℙ¹_A` the closed fibre. For every torsion sheaf `F` of
`Λ`-modules on `ℙ¹_A` and every `q ≥ 0`, restriction `Hᵠ(ℙ¹_A, F) ⟶ Hᵠ(ℙ¹_κ, F₀)` is
bijective.
(blueprint: `prop-weil-pbc-p1-strict-henselian-comparison`) -/
theorem Etale.bijective_cohomologyMap_projectiveLine_residueField
    (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf (ProjectiveLine (Spec (.of A))).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap
      (ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) :=
  sorry

end StrictlyHenselian

section StrictLocalExchange

variable (Λ : Type (u + 1)) [CommRing Λ]
  {A B : Type u} [CommRing A] [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)]
  [CommRing B] [HenselianLocalRing B] [IsSepClosed (IsLocalRing.ResidueField B)]
  (φ : A →+* B) [IsLocalHom φ]

/-- **The strict-local exchange for `ℙ¹`.** Let `φ : A ⟶ B` be a local morphism of strictly
henselian local rings, with residue fields `κ_A`, `κ_B` and induced map `κ_A ⟶ κ_B`, and
consider the cartesian square
```
ℙ¹_B --g'--> ℙ¹_A
 |            |
 v            v
Spec B -g-> Spec A
```
Let `F` be a torsion sheaf of `Λ`-modules on `ℙ¹_A` and `q ≥ 0`. Then the stalk at the closed
geometric point `Spec κ_B ⟶ Spec B` of the degree-`q` exchange morphism
`g⁻¹ Rᵠp_* F ⟶ Rᵠp'_* g'⁻¹ F` is, up to isomorphisms of its source and target, the pullback
map `Hᵠ(ℙ¹_{κ_A}, F₀) ⟶ Hᵠ(ℙ¹_{κ_B}, F₀|)` along `ℙ¹_{κ_B} ⟶ ℙ¹_{κ_A}`. The isomorphisms are
the strictly henselian comparisons on the two closed fibres.

**Form of the statement.** The blueprint asks for the canonical restriction maps. This
statement only asserts that *some* isomorphisms `e₁`, `e₂` make the square commute, which is
weaker, for the same reason as
`AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine`:
the project has no edge map yet comparing the stalks of the higher direct images `Rᵠp_*`
(homology in `DerivedCategory.Plus`) with the `Ext`-groups `CategoryTheory.Sheaf.H`. The
`sorry` must be filled through the canonical maps. Once the edge map exists, `e₁` and `e₂`
should be replaced by it, composed with the restrictions to the closed fibres.
(blueprint: `prop-weil-pbc-strict-local-exchange`) -/
theorem Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_strictLocal
    (F : Sheaf (ProjectiveLine (Spec (.of A))).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionSheaf F] (q : ℕ) :
    ∃ (e₁ : ((pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeSourceFunctor Λ (Spec.map (CommRingCat.ofHom φ))
            (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A)) q).obj F) ≃+
        Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))^*[
            ModuleCat.{u + 1} Λ].obj F)) q)
      (e₂ : ((pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeTargetFunctor Λ (ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom φ)))
            (ProjectiveLine (Spec (.of B)) ↘ Spec (.of B)) q).obj F) ≃+
        Sheaf.H ((ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom
            (IsLocalRing.ResidueField.map φ))))^*[AddCommGrpCat.{u + 1}].obj
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))^*[
              ModuleCat.{u + 1} Λ].obj F))) q),
      ∀ x, e₂ ((((pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).map (Etale.baseChangeHomologyMap Λ
            (ProjectiveSpace.isPullback_map _ (Spec.map (CommRingCat.ofHom φ))) q F)).hom x) =
        Etale.cohomologyMap (ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom
            (IsLocalRing.ResidueField.map φ))))
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))^*[
              ModuleCat.{u + 1} Λ].obj F)) q (e₁ x) :=
  sorry

/-- If the residue field map `κ_A ⟶ κ_B` of a local morphism of strictly henselian local
rings is an isomorphism, the stalk at the closed geometric point of `Spec B` of the
exchange morphism of `ℙ¹` is an isomorphism. This is the second assertion of the
blueprint node `prop-weil-pbc-strict-local-exchange`, deduced from
`AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_strictLocal`: the
pullback along the isomorphism `ℙ¹_{κ_B} ⟶ ℙ¹_{κ_A}` is bijective on cohomology. -/
theorem Etale.isIso_sheafFiber_baseChangeHomologyMap_strictLocal
    (hφ : Function.Bijective (IsLocalRing.ResidueField.map φ))
    (F : Sheaf (ProjectiveLine (Spec (.of A))).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionSheaf F] (q : ℕ) :
    IsIso (((pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).map (Etale.baseChangeHomologyMap Λ
        (ProjectiveSpace.isPullback_map _ (Spec.map (CommRingCat.ofHom φ))) q F)) := by
  obtain ⟨e₁, e₂, he⟩ := Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_strictLocal
    Λ φ F q
  have : IsIso (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hφ
  have : IsIso (ProjectiveSpace.map (ULift.{u} (Fin 2))
      (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)))) :=
    ⟨ProjectiveSpace.map _ (inv (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)))),
      by rw [← ProjectiveSpace.map_comp, IsIso.hom_inv_id, ProjectiveSpace.map_id],
      by rw [← ProjectiveSpace.map_comp, IsIso.inv_hom_id, ProjectiveSpace.map_id]⟩
  rw [ConcreteCategory.isIso_iff_bijective, ← e₂.bijective.of_comp_iff']
  have hfun : e₂ ∘ _ = Etale.cohomologyMap (ProjectiveSpace.map (ULift.{u} (Fin 2))
      (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ))))
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))^*[
          ModuleCat.{u + 1} Λ].obj F)) q ∘ e₁ := funext he
  rw [hfun]
  exact (Etale.cohomologyMap_bijective _ _ q).comp e₁.bijective

end StrictLocalExchange

end AlgebraicGeometry
