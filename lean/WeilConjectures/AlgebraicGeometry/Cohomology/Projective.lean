/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.UniformAffinePullbackCohomologyBound
import Sheaf.AlgebraicGeometry.ProjectiveAffineFiniteCohomologyIndependent
import Sheaf.AlgebraicGeometry.AffineOpenHigherDirectImageSectionsIso
import Sheaf.AlgebraicGeometry.OpenModuleCohomologyComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre

/-!
# Coherent cohomology of projective schemes

Let `A` be a noetherian ring. The cohomology of a coherent sheaf on a closed subscheme of
`ℙⁿ_A` consists of finite `A`-modules, and vanishes above `n`. In relative form, the higher
direct images of a coherent sheaf along a projective morphism `f : X ⟶ S` to a locally noetherian
scheme are coherent, and vanish above the dimension of the ambient projective space. For a
quasi-compact and quasi-separated morphism to a quasi-compact base, the higher direct images of
quasi-coherent sheaves vanish in degrees bounded uniformly in the sheaf and the base change.

A projective morphism `f : X ⟶ S` is presented through a closed immersion `i : X ⟶ ℙ(n; S)` over
`S`, as in the blueprint's definition of (H-)projective morphisms. The cohomology `ℱ.H q` of a
sheaf on a scheme `X` over `Spec A` is an `A`-module through the structure morphism; this is
`AlgebraicGeometry.Scheme.Modules.moduleHOfSpec`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_of_isPullback`: the uniform
  vanishing bound for a quasi-compact quasi-separated morphism over a quasi-compact base.
- `AlgebraicGeometry.ProjectiveSpace.finite_H`: the cohomology of a coherent sheaf on `ℙⁿ_A` is
  finite over `A`.
- `AlgebraicGeometry.Scheme.Modules.finite_H_of_isClosedImmersion` and
  `subsingleton_H_of_isClosedImmersion`: the same for a closed subscheme of `ℙⁿ_A`, together with
  the vanishing above `n`.
- `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage_of_isClosedImmersion`
  and `isZero_higherDirectImage_of_isClosedImmersion`: coherence and vanishing of the higher
  direct images along a projective morphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X T : Scheme.{u}}

/-- **Uniform vanishing of the higher direct images.** Let `f : X ⟶ T` be quasi-compact and
quasi-separated, with `T` quasi-compact. There is an integer `n` such that `R^p f'_* ℱ' = 0` for
all `p ≥ n`, all base changes `f' : X' ⟶ T'` of `f` along morphisms `g : T' ⟶ T`, and all
quasi-coherent `𝒪_{X'}`-modules `ℱ'`.

Source: Stacks Project, Tag 01XJ, proof of (3). On each affine open `U` of `T`,
quasi-compact-open induction bounds cohomology after every affine morphism to `f⁻¹(U)`:
the affine case vanishes in positive degrees, and Mayer–Vietoris glues three bounds by
`max (max a b) c + 1`. Choose a finite affine cover of `T` and take the maximum bound.
After arbitrary base change, affine opens `V` mapping into a selected `U` cover `T'`;
the map `f'⁻¹(V) ⟶ f⁻¹(U)` is affine as a base change of the affine morphism `V ⟶ U`.
Apply its bound, the open cohomology comparison and the affine-open sections comparison.
The resulting higher direct image has zero sections on this affine cover. Quasi-coherence
makes its zero endomorphism epi, so cancellation gives `id = 0` and the sheaf is zero.

(blueprint: `lem-pc-finite-support-hi`) -/
theorem exists_isZero_higherDirectImage_of_isPullback [CompactSpace T] (f : X ⟶ T)
    [QuasiCompact f] [QuasiSeparated f] :
    ∃ n : ℕ, ∀ {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
      [HasInjectiveResolutions X'.Modules], IsPullback g' f' f g →
      ∀ (ℱ' : X'.Modules) [SheafOfModules.IsQuasicoherent (R := X'.ringCatSheaf) ℱ'],
      ∀ p ≥ n, IsZero ((higherDirectImage f' p).obj ℱ') := by
  classical
  choose U hU ht htop using fun t : T ↦ exists_isAffineOpen_mem_and_subset
    (show t ∈ (⊤ : T.Opens) from trivial)
  have bounds (t : T) : ∃ n : ℕ,
      ∀ {Y : Scheme.{u}} (h : Y ⟶ (f ⁻¹ᵁ U t).toScheme) [IsAffineHom h]
        (F : Y.Modules) [F.IsQuasicoherent], ∀ p : ℕ, n ≤ p → Subsingleton (F.H p) := by
    have : IsAffine (U t).toScheme := hU t
    have : CompactSpace (f ⁻¹ᵁ U t).toScheme :=
      QuasiCompact.compactSpace_of_compactSpace (f ∣_ U t)
    have : QuasiSeparatedSpace (f ⁻¹ᵁ U t).toScheme :=
      quasiSeparatedSpace_of_quasiSeparated (f ∣_ U t)
    exact exists_uniform_affine_pullback_openCohomology_bound _
  choose n hn using bounds
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun t ↦ (U t : Set T))
    (fun t ↦ (U t).isOpen) (fun t _ ↦ Set.mem_iUnion.mpr ⟨t, ht t⟩)
  refine ⟨s.sup n, ?_⟩
  intro T' X' g g' f' _ sq F' _ p hp
  have : QuasiCompact f' := MorphismProperty.of_isPullback sq inferInstance
  have : QuasiSeparated f' := MorphismProperty.of_isPullback sq inferInstance
  let M := (higherDirectImage f' p).obj F'
  have : M.IsQuasicoherent := isQuasicoherent_higherDirectImage f' F' p
  let J := Σ t : s, {V : T'.affineOpens // V.1 ≤ g ⁻¹ᵁ U t}
  let W : J → T'.Opens := fun j ↦ j.2.1.1
  have hcov : ⨆ j, W j = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨t, hts, hxt⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ (g x)))
    obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ g ⁻¹ᵁ U t from hxt)
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨⟨t, hts⟩, ⟨⟨V, hV⟩, hVU⟩⟩, hxV⟩
  have hsections (j : J) : Subsingleton Γ(M, W j) := by
    let t : T := j.1
    let V : T'.Opens := W j
    have hV : IsAffineOpen V := j.2.1.2
    have hVU : V ≤ g ⁻¹ᵁ U t := j.2.2
    let UX := f ⁻¹ᵁ U t
    let UY := f' ⁻¹ᵁ V
    have hUY : UY ≤ g' ⁻¹ᵁ UX := by
      change f' ⁻¹ᵁ V ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ U t)
      rw [← Scheme.Hom.comp_preimage, sq.w, Scheme.Hom.comp_preimage]
      exact f'.preimage_mono hVU
    let h := g'.resLE UX UY hUY
    have hsq := Scheme.Hom.isPullback_resLE sq hVU
      (show UX ≤ f ⁻¹ᵁ U t from le_rfl)
      (show UY = g' ⁻¹ᵁ UX ⊓ f' ⁻¹ᵁ V from (inf_eq_right.mpr hUY).symm)
    have : IsAffine (U t).toScheme := hU t
    have : IsAffine V.toScheme := hV
    have : IsAffineHom h := MorphismProperty.of_isPullback hsq.flip inferInstance
    let F := (restrictFunctor UY.ι).obj F'
    have : F.IsQuasicoherent := isQuasicoherent_restrictFunctor UY.ι F'
    have hz : Subsingleton (F.H p) := hn t h F p
      ((Finset.le_sup j.1.property).trans hp)
    obtain ⟨b⟩ := nonempty_openModuleCohomology_addEquiv_restrict_H X' F' UY p
    obtain ⟨c⟩ := nonempty_affineOpen_higherDirectImage_sections_iso f' V hV F'
      inferInstance p
    exact ⟨fun x y ↦ c.addCommGroupIsoToAddEquiv.symm.injective
      (b.injective (hz.elim _ _))⟩
  have : Epi (0 : M ⟶ M) := epi_of_surjective_app 0 W
    (fun j ↦ j.2.1.2) hcov (fun j x ↦ ⟨0, (hsections j).elim _ _⟩)
  apply (IsZero.iff_id_eq_zero M).mpr
  apply (cancel_epi (0 : M ⟶ M)).mp
  simp

/-- The cohomology of a sheaf of modules on a scheme `X` with a morphism `f : X ⟶ Spec A` is an
`A`-module, by restriction of scalars of the `Γ(X, ⊤)`-module structure along
`A ≅ Γ(Spec A, ⊤) ⟶ Γ(X, ⊤)`.

This is not an instance, since `f` cannot be inferred. -/
abbrev moduleHOfSpec {A : Type u} [CommRing A] (f : X ⟶ Spec (.of A)) (M : X.Modules) (q : ℕ) :
    Module A (M.H q) :=
  Module.compHom (M.H q) ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom

end Scheme.Modules

open Scheme.Modules

variable {n : Type u} [Finite n]

/-- **Coherent cohomology of projective space over a noetherian ring.** Let `A` be noetherian
and `ℱ` a coherent module on `ℙⁿ_A`. Then each `H^q(ℙⁿ_A, ℱ)` is a finite `A`-module.

By descending induction on `q`, for all coherent modules at once: for `q > n` the cohomology
vanishes; in general, a surjection `ℰ ⟶ ℱ` from a finite sum `ℰ` of twists `𝒪(m)` with coherent
kernel `𝒦` gives an exact sequence `H^q(ℰ) ⟶ H^q(ℱ) ⟶ H^{q+1}(𝒦)` whose outer terms are finite.
The proof reuses this induction in `finite_H_projective_affine_independent` for the identity
embedding, and transports scalars along `Γ(Spec A, ⊤) ≅ A` by an identity semilinear surjection.
Source: Stacks Project, Tag 01YS, Lemma 30.14.1 (3).

(blueprint: `lem-pc-projective-space-coherent-finiteness`) -/
theorem ProjectiveSpace.finite_H (A : Type u) [CommRing A] [IsNoetherianRing A]
    (ℱ : (ℙ(n; Spec (.of A))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ℙ(n; Spec (.of A))).ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := (ℙ(n; Spec (.of A))).ringCatSheaf) ℱ] (q : ℕ) :
    letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) ℱ q
    Module.Finite A (ℱ.H q) := by
  classical
  let T := Spec (.of A)
  have : IsNoetherianRing Γ(T, ⊤) :=
    isNoetherianRing_of_ringEquiv _ (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm
  let : Module Γ(T, ⊤) (ℱ.H q) :=
    Module.compHom _ (ℙ(n; T) ↘ T).appTop.hom
  have : Module.Finite Γ(T, ⊤) (ℱ.H q) := by
    simpa using finite_H_projective_affine_independent n (𝟙 (ℙ(n; T))) ℱ q
  let := moduleHOfSpec (ℙ(n; T) ↘ T) ℱ q
  let e := (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv
  let f : ℱ.H q →ₛₗ[e.toRingHom] ℱ.H q :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a x ↦ by
        change (ℙ(n; T) ↘ T).appTop a • x =
          (ℙ(n; T) ↘ T).appTop ((Scheme.ΓSpecIso (.of A)).inv
            ((Scheme.ΓSpecIso (.of A)).hom a)) • x
        rw [Iso.hom_inv_id_apply] }
  exact Module.Finite.of_surjective f Function.surjective_id

variable {X : Scheme.{u}}

/-- **Coherent cohomology of a projective scheme over a noetherian ring.** Let `A` be
noetherian, `i : X ⟶ ℙⁿ_A` a closed immersion and `ℱ` a coherent `𝒪_X`-module. Then each
`H^q(X, ℱ)` is a finite `A`-module. Apply the independent affine-base projective finiteness
argument to `i`, which uses the finite-source twist cohomology segment and descending induction.
The action in that theorem is through `Γ(Spec A, ⊤)`. The identity map on `H^q(X, ℱ)` is
semilinear along `Γ(Spec A, ⊤) ≅ A`; its scalar identity is the inverse law of `ΓSpecIso`.
Transport finite generation through this surjection to obtain precisely `moduleHOfSpec`.
Source: Stacks Project, Tag 01YS, Lemma 30.14.1 (3).

(blueprint: `lem-pc-projective-coherent-finiteness`) -/
theorem Scheme.Modules.finite_H_of_isClosedImmersion (A : Type u) [CommRing A]
    [IsNoetherianRing A] (i : X ⟶ ℙ(n; Spec (.of A))) [IsClosedImmersion i] (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    letI := moduleHOfSpec (i ≫ ℙ(n; Spec (.of A)) ↘ Spec (.of A)) ℱ q
    Module.Finite A (ℱ.H q) := by
  classical
  let T := Spec (.of A)
  have : IsNoetherianRing Γ(T, ⊤) :=
    isNoetherianRing_of_ringEquiv _ (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm
  let : Module Γ(T, ⊤) (ℱ.H q) :=
    Module.compHom _ (i ≫ (ℙ(n; T) ↘ T)).appTop.hom
  have : Module.Finite Γ(T, ⊤) (ℱ.H q) :=
    finite_H_projective_affine_independent n i ℱ q
  let := moduleHOfSpec (i ≫ ℙ(n; T) ↘ T) ℱ q
  let e := (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv
  let f : ℱ.H q →ₛₗ[e.toRingHom] ℱ.H q :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a x ↦ by
        change (i ≫ (ℙ(n; T) ↘ T)).appTop a • x =
          (i ≫ (ℙ(n; T) ↘ T)).appTop ((Scheme.ΓSpecIso (.of A)).inv
            ((Scheme.ΓSpecIso (.of A)).hom a)) • x
        rw [Iso.hom_inv_id_apply] }
  exact Module.Finite.of_surjective f Function.surjective_id

/-- **Vanishing of the cohomology of a projective scheme above the dimension.** Let
`i : X ⟶ ℙᵈ_A` be a closed immersion, `ℙᵈ_A = ℙ(n; Spec A)` with `Nat.card n = d + 1`, and
`ℱ` a quasi-coherent `𝒪_X`-module. Then `H^q(X, ℱ) = 0` for `q > d`: the cohomology of `ℱ` is
that of `i_* ℱ`, computed by the Čech complex of the `d + 1` standard affine opens.

This is the vanishing clause of the blueprint lemma.

(blueprint: `lem-pc-projective-coherent-finiteness`) -/
theorem Scheme.Modules.subsingleton_H_of_isClosedImmersion (A : Type u) [CommRing A]
    (i : X ⟶ ℙ(n; Spec (.of A))) [IsClosedImmersion i] (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] {d : ℕ} (hn : Nat.card n = d + 1)
    {q : ℕ} (hq : d < q) : Subsingleton (ℱ.H q) := by
  have : ((pushforward i).obj ℱ).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom i ℱ
  have : Subsingleton (((pushforward i).obj ℱ).H q) :=
    ProjectiveSpace.subsingleton_H_of_lt n A hn ((pushforward i).obj ℱ) hq
  obtain ⟨e⟩ := nonempty_functorH_iso_pushforwardAb_of_isAffineHom i q
  let F : (cechAcyclicOnAffines X).FullSubcategory :=
    ⟨(SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ,
      cechAcyclicOnAffines_of_isQuasicoherent ℱ⟩
  let a := (e.app F).addCommGroupIsoToAddEquiv
  have ht : Subsingleton (Sheaf.H
      ((TopCat.Sheaf.pushforwardAb i.base).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ)) q) := by
    change Subsingleton (((pushforward i).obj ℱ).H q)
    infer_instance
  exact ⟨fun x y ↦ a.injective (ht.elim (a x) (a y))⟩

namespace Scheme.Modules

variable {S : Scheme.{u}} (f : X ⟶ S) (i : X ⟶ ℙ(n; S)) [IsClosedImmersion i]
  (hi : i ≫ ℙ(n; S) ↘ S = f) [HasInjectiveResolutions X.Modules] (ℱ : X.Modules)
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

include hi in
/-- **Coherence of the higher direct images of a projective morphism.** Let `S` be locally
noetherian, `f : X ⟶ S` projective, i.e. `f = π ∘ i` for a closed immersion `i : X ⟶ ℙⁿ_S`,
and `ℱ` a coherent `𝒪_X`-module. Then every `R^q f_* ℱ` is coherent.

A projective morphism is proper, so this is a case of
`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage`. (The blueprint proves
it directly, as the input of the proper case: over an affine open `Spec A` of `S`, the Čech
complex of a finite affine cover of `f⁻¹(Spec A)` localises, so `R^q f_* ℱ` is the sheaf
associated with the finite `A`-module `H^q(f⁻¹(Spec A), ℱ)`.)

(blueprint: `lem-pc-projective-coherent-higher-images`) -/
theorem isFinitePresentation_higherDirectImage_of_isClosedImmersion [IsLocallyNoetherian S]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    ((higherDirectImage f q).obj ℱ).IsFinitePresentation := by
  subst hi
  have : LocallyOfFinitePresentation (i ≫ ℙ(n; S) ↘ S) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType).mpr inferInstance
  exact isFinitePresentation_higherDirectImage _ ℱ q

include hi in
/-- **Vanishing of the higher direct images of a projective morphism.** In the situation of
`isFinitePresentation_higherDirectImage_of_isClosedImmersion`, with `Nat.card n = d + 1`, the
higher direct images `R^q f_* ℱ` vanish for `q > d`: over an affine open `Spec A` of `S`, they
are the sheaves associated with the `H^q(f⁻¹(Spec A), ℱ)`, which vanish by
`AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_isClosedImmersion`.

(blueprint: `lem-pc-projective-coherent-higher-images`) -/
theorem isZero_higherDirectImage_of_isClosedImmersion {d : ℕ} (hn : Nat.card n = d + 1)
    {q : ℕ} (hq : d < q) : IsZero ((higherDirectImage f q).obj ℱ) := by
  classical
  subst hi
  let f := i ≫ ℙ(n; S) ↘ S
  let M := (higherDirectImage f q).obj ℱ
  have : M.IsQuasicoherent := isQuasicoherent_higherDirectImage f ℱ q
  have hsections (U : S.affineOpens) : Subsingleton Γ(M, U.1) := by
    let V := f ⁻¹ᵁ U.1
    let T := U.1.toScheme
    let a := f ∣_ U.1
    have : IsAffine T := U.2
    let w : a ≫ U.1.ι = (V.ι ≫ i) ≫ ℙ(n; S) ↘ S := by
      simpa only [Category.assoc] using (isPullback_morphismRestrict f U.1).w
    let j := ProjectiveSpace.liftBaseChange a (V.ι ≫ i) w
    have : IsClosedImmersion j := MorphismProperty.of_isPullback
      (ProjectiveSpace.isPullback_liftBaseChange a
        (isPullback_morphismRestrict f U.1).flip w) inferInstance
    let e := T.isoSpec
    have : IsClosedImmersion (ProjectiveSpace.map n e.hom) :=
      MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map n e.hom).flip inferInstance
    let j' := j ≫ ProjectiveSpace.map n e.hom
    let F := (restrictFunctor V.ι).obj ℱ
    have : F.IsQuasicoherent := isQuasicoherent_restrictFunctor V.ι ℱ
    have hz : Subsingleton (F.H q) :=
      subsingleton_H_of_isClosedImmersion (Γ(T, ⊤)) j' F hn hq
    obtain ⟨b⟩ := nonempty_openModuleCohomology_addEquiv_restrict_H X ℱ V q
    obtain ⟨c⟩ := nonempty_affineOpen_higherDirectImage_sections_iso f U.1 U.2 ℱ
      inferInstance q
    exact ⟨fun x y ↦ c.addCommGroupIsoToAddEquiv.symm.injective
      (b.injective (hz.elim _ _))⟩
  have : Epi (0 : M ⟶ M) := epi_of_surjective_app 0
    (fun U : S.affineOpens ↦ U.1) (fun U ↦ U.2) (iSup_affineOpens_eq_top S)
    (fun U x ↦ ⟨0, (hsections U).elim _ _⟩)
  apply (IsZero.iff_id_eq_zero M).mpr
  apply (cancel_epi (0 : M ⟶ M)).mp
  simp

end Scheme.Modules

end AlgebraicGeometry
