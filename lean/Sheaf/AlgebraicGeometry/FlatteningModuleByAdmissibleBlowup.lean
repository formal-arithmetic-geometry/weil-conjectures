/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q120
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.Blowup.AdmissibleBlowup
public import Sheaf.AlgebraicGeometry.ModuleStrictTransform
public import WeilConjectures.AlgebraicGeometry.FiniteTypeIdealModule
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.AlgebraicGeometry.FlatteningSmoothAffineReduction
import Sheaf.AlgebraicGeometry.FlatteningSmoothSupportInduction
import Sheaf.AlgebraicGeometry.FlatModulePresentationAfterBoundaryBlowup
import Sheaf.AlgebraicGeometry.ModuleAdmissibleBlowupCalculus
import Sheaf.AlgebraicGeometry.PullbackModelFlatnessComparison
import WeilConjectures.AlgebraicGeometry.RelativelyFlatModulePullback
import WeilConjectures.AlgebraicGeometry.RelativeFlatModuleStalk
import WeilConjectures.AlgebraicGeometry.TensorPullbackOpenSquare
import WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion

/-!
# Flattening a module by an admissible blowup

Source: Stacks Project, Tag 0815, `flat.tex`, Theorem `theorem-flatten-module`
(blueprint: lem-trf-flattening-module-by-admissible-blowup).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem ideal_ofFiniteType_of_module {S : Scheme.{u}} (I : S.IdealSheafData)
    [I.toModules.IsFiniteType] : I.ofFiniteType := by
  have := SheafOfModules.isQuasicoherent_unit (R := I.subscheme.ringCatSheaf)
  have := SheafOfModules.isQuasicoherent_unit (R := S.ringCatSheaf)
  have : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((SheafOfModules.pushforward I.subschemeι.toRingCatSheafHom).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf)) :=
    Scheme.Modules.isQuasicoherent_pushforward_of_isClosedImmersion I.subschemeι _
  have : I.toModules.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_kernel I.toPushforwardSubscheme
  intro V _
  have := Scheme.Modules.finite_sections_of_finiteType I.toModules V.2
  let l : Γ(I.toModules, V.1) →ₗ[Γ(S, V.1)] Γ(S, V.1) :=
    (I.toModulesι.val.app (Opposite.op V.1)).hom
  have hrange : LinearMap.range l = I.ideal V := by
    apply SetLike.coe_injective
    exact I.range_toModulesι_app V
  rw [← hrange]
  exact Submodule.fg_range l

private theorem strictTransform_restrict_finitePresentation
    {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent]
    (U : S.Opens) (hU : IsCompact (U : Set S))
    (hfp : (F.restrict (f ⁻¹ᵁ U).ι).IsFinitePresentation) (B : IsAdmissible S U) :
    ((@Scheme.Modules.moduleStrictTransform X S f B.I
      (B.I.isFiniteType_toModules_sheaf B.finiteType) F inferInstance).restrict
        ((pullback.snd f B.I.blowupMap) ⁻¹ᵁ (B.I.blowupMap ⁻¹ᵁ U)).ι).IsFinitePresentation := by
  open Scheme.Modules in
  classical
  let := B.I.isFiniteType_toModules_sheaf B.finiteType
  let p := pullback.fst f B.I.blowupMap
  let q := pullback.snd f B.I.blowupMap
  let P := (tensorPullback p).obj F
  let M := moduleStrictTransform f B.I F
  let V := f ⁻¹ᵁ U
  let W := q ⁻¹ᵁ (B.I.blowupMap ⁻¹ᵁ U)
  have hW : W = p ⁻¹ᵁ V := by
    change (q ≫ B.I.blowupMap) ⁻¹ᵁ U = (p ≫ f) ⁻¹ᵁ U
    rw [pullback.condition]
  obtain ⟨_, _, _, hquot, _⟩ := moduleAdmissibleBlowupPermanence U hU f F B
  let φ : P ⟶ M := moduleStrictTransformQuotient f B.I F
  have : IsIso ((SheafOfModules.overFunctor _ W).map φ) := hquot
  have hcomp : IsIso ((overEquiv W).functor.map
      ((SheafOfModules.overFunctor _ W).map φ)) := inferInstance
  have : IsIso ((restrictFunctor W.ι).map φ) :=
    (NatIso.isIso_map_iff (overFunctorEquiv W) φ).mp hcomp
  have hP : (P.restrict W.ι).IsFinitePresentation := by
    rw [hW]
    obtain ⟨e, _⟩ := exists_tensorPullback_openSquare (p ⁻¹ᵁ V).ι p V (p ∣_ V)
      (by simp) (morphismRestrict_ι p V).symm F
    have : (F.restrict V.ι).IsFinitePresentation := hfp
    have := isFinitePresentation_tensorPullback (p ∣_ V) (F.restrict V.ι)
    exact isFinitePresentation_of_iso e.symm
  have := hP
  exact isFinitePresentation_of_iso (asIso ((restrictFunctor W.ι).map φ))

private theorem flat_finitePresentation_of_iso_square
    {P Q T R : Scheme.{u}} (m : P ⟶ Q) [IsIso m] (e : T ≅ R)
    (p : P ⟶ T) (q : Q ⟶ R) (hcomm : m ≫ q = p ≫ e.hom)
    (M : Q.Modules) [M.IsQuasicoherent] (N : P.Modules) [N.IsQuasicoherent]
    (a : N ≅ (Scheme.Modules.tensorPullback m).obj M)
    (hflat : N.IsFlatOver p) (hfp : N.IsFinitePresentation) :
    M.IsFlatOver q ∧ M.IsFinitePresentation := by
  open Scheme.Modules in
  classical
  have hinv : inv m ≫ p = q ≫ e.inv := by
    apply (cancel_mono e.hom).mp
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
    rw [← hcomm, IsIso.inv_hom_id_assoc]
  have hp : IsPullback (inv m) q p e.inv := IsPullback.of_horiz_isIso ⟨hinv⟩
  have hbase := relativelyFlat_module_pullback p e.inv N hflat
  have hlocal : ((tensorPullback (inv m)).obj N).IsFlatOver q :=
    (isFlatOver_tensorPullback_iff_of_isPullback hp
      (IsPullback.of_hasPullback p e.inv) N).mpr hbase
  obtain ⟨comp⟩ := nonempty_tensorPullbackComp (inv m) m
  obtain ⟨id⟩ := nonempty_tensorPullbackId Q
  let cancel : (tensorPullback m ⋙ tensorPullback (inv m)) ≅ 𝟭 Q.Modules :=
    comp.symm ≪≫ eqToIso (congrArg tensorPullback (IsIso.inv_hom_id m)) ≪≫ id
  let a' : (tensorPullback (inv m)).obj N ≅ M :=
    (tensorPullback (inv m)).mapIso a ≪≫ cancel.app M
  have := hfp
  have := isFinitePresentation_tensorPullback (inv m) N
  exact ⟨flatOver_of_iso q a'.symm hlocal, isFinitePresentation_of_iso a'⟩

/-- A finite-type quasi-coherent module, finitely presented and flat over the preserved
quasi-compact open, becomes flat and finitely presented after an admissible base blowup.
The centre is retained in `B`, and the transform is the canonical module strict transform.
Source: Stacks Project, Tag 0815, Theorem `theorem-flatten-module`
(blueprint: lem-trf-flattening-module-by-admissible-blowup).

Proof:
1. First prove flatness by strong induction on a uniform bound for fibre-support dimension
   (`lem-fin-finite-type-fibre-dimension-bound`). For empty fibre supports the finite-type
   support criterion (`lem-weil-pbc-support-pullback-finite-type`) makes the module zero;
   the unit-ideal blowup suffices.
2. Use `lem-trf-etale-flattening-descent` to pass to finitely many affine neighbourhoods.
   Include empty-source diagrams over base charts to cover base points missed by the source.
3. Apply `lem-trf-elementary-module-devissage`: replace the module locally by a module on a
   closed subscheme finite over a smooth affine family with geometrically integral fibres.
   Its finite pushforward is finite type (`lem-pc-f3-finite-pushforward-finite-type`).
4. Preserve finite presentation over the open: the closed immersion and finite map are
   finitely presented by the affine finite-presentation and algebra-presentation lemmas.
   Descend the presentation across the quotient ring, then use finite algebra as finite
   module and `lem-pc-module-finite-presentation-transitive`. Use
   `lem-weil-pbc-quasi-coherent-finite-type-affine` to identify module and sheaf presentations.
5. Etale source pullback preserves base flatness by `lem-weil-pbc-etale-algebra-flat`.
   Etale base neighbourhoods are unramified, by the diagonal and Kahler-differential
   criteria (`lem-weil-pbc-formally-unramified-ring-iff-kahler-zero`), and
   `lem-sc-unramified-flat-of-base-flat` upgrades base flatness to the new base.
6. Affine pushforward preserves and reflects relative flatness by
   `lem-pc-affine-chart-relative-flat-criterion`. It commutes with strict transform by
   `lem-trf-strict-transform-affine-pushforward`, so it suffices to flatten the module
   on the smooth family.
7. Apply `lem-trf-generic-free-blowup` to obtain a finite locally free locus meeting every
   fibre. Base change preserves smoothness and geometric fibre dimension
   (`lem-pc-proper-base-change`, `lem-pc-dim-base-change`). The admissible-blowup calculus
   preserves finite type and the restriction over the open and composes successive blowups.
8. At a fibre generic point choose module sections giving a basis over its residue field.
   Their map from a finite free module is an isomorphism on a neighbourhood. The open-map
   theorem (`lem-weil-pbc-flat-finite-presentation-open`) permits shrinking the base so this
   neighbourhood meets every fibre.
9. By `lem-trf-free-subtraction-flatness` the free-module map is universally injective and
   its cokernel has the same relative flat locus. The cokernel remains finitely presented
   over the open by `lem-weil-pbc-module-finite-presentation-cokernel`.
10. Its fibre support is a proper closed subset of an integral fibre, so its dimension
    drops strictly; in dimension zero it is empty. Apply the induction hypothesis.
11. Use `lem-trf-strict-transform-universal-exact` for the transformed exact sequence.
    The calculus identifies the free term with the free pullback and retains the generic
    basis locus. The free-subtraction flatness criterion transfers flatness from the
    transformed cokernel to the transformed module.
12. Compose the preliminary and induction blowups by
    `lem-trf-module-admissible-blowup-calculus`, then descend along the finite etale covers
    using `lem-trf-etale-flattening-descent` and the affine-pushforward comparison.
13. Choose a finite-type ideal cutting out the boundary by
    `lemma-nagata-qc-open-complement-ideal-exists`, and apply
    `det-nagata-boundary-divisor-cartier` to make the preserved open schematically dense.
    Flatness makes the further strict transform the ordinary pullback, still flat and
    finite type. Local finite presentation of the ambient morphism survives base change
    (`lem-weil-pbc-finite-presentation-base-change-composition`). The preserved open is
    retrocompact on the qcqs base. Apply `lem-trf-flat-finite-type-dense-presentation`
    and compose the two blowups with the module strict-transform comparison. -/
theorem exists_flat_finitePresentation_moduleStrictTransform_admissibleBlowup
    {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) [QuasiCompact f] [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (U : S.Opens) (hU : IsCompact (U : Set S))
    (hfp : ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj F).IsFinitePresentation)
    (hflat : ∀ x : X, f x ∈ U → Module.Flat (S.presheaf.stalk (f x))
      ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F))) :
    ∃ B : IsAdmissible S U,
      (∀ x : (Limits.pullback f B.I.blowupMap : Scheme.{u}),
        Module.Flat (B.I.blowup.presheaf.stalk ((pullback.snd f B.I.blowupMap) x))
          ((ModuleCat.restrictScalars ((pullback.snd f B.I.blowupMap).stalkMap x).hom).obj
            ((RingedSpace.moduleStalkFunctor
              (Limits.pullback f B.I.blowupMap).toRingedSpace x).obj
                (@Scheme.Modules.moduleStrictTransform X S f B.I
                  (B.I.isFiniteType_toModules_sheaf B.finiteType) F inferInstance)))) ∧
      (@Scheme.Modules.moduleStrictTransform X S f B.I
        (B.I.isFiniteType_toModules_sheaf B.finiteType) F inferInstance).IsFinitePresentation := by
  classical
  open Scheme.Modules in
  have hbounded : ∀ d : ℕ,
      ∀ (S X : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
        (f : X ⟶ S) [QuasiCompact f] [LocallyOfFinitePresentation f]
        (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
        (U : S.Opens), IsCompact (U : Set S) →
        (F.restrict (f ⁻¹ᵁ U).ι).IsFinitePresentation →
        (∀ x : X, f x ∈ U → Module.Flat (S.presheaf.stalk (f x))
          ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
            ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F))) →
        (∀ s : S, topologicalKrullDim {x : f.fiber s |
          ¬ Subsingleton (((tensorPullback (f.fiberι s)).obj F).presheaf.stalk x)} <
            (d : WithBot ℕ∞)) →
        ∃ B : IsAdmissible S U,
          (@moduleStrictTransform _ _ f B.I
            (B.I.isFiniteType_toModules_sheaf B.finiteType) F inferInstance).IsFlatOver
              (pullback.snd f B.I.blowupMap) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro S X _ _ f _ _ F _ _ U hU hfp hflat hdim
      apply exists_flat_moduleStrictTransform_of_smooth_affine d ?_ f F U hU hfp hflat hdim
      intro n hn S X _ f _ _ _ F _ _ U hU hfp hflat
      exact exists_flat_moduleStrictTransform_smooth_of_lower_support n
        (ih n hn) f F U hU hfp hflat
  obtain ⟨d, hd⟩ := exists_fibre_dimension_bound f
  have hdim : ∀ s : S, topologicalKrullDim {x : f.fiber s |
      ¬ Subsingleton (((Scheme.Modules.tensorPullback (f.fiberι s)).obj F).presheaf.stalk x)} <
        ((d + 1 : ℕ) : WithBot ℕ∞) := by
    intro s
    exact (topologicalKrullDim_subspace_le (f.fiber s) _).trans_lt
      ((hd s).trans_lt (by exact_mod_cast Nat.lt_succ_self d))
  obtain ⟨B, hBflat⟩ := hbounded (d + 1) S X f F U hU hfp hflat hdim
  let := B.I.isFiniteType_toModules_sheaf B.finiteType
  let f₁ := pullback.snd f B.I.blowupMap
  let F₁ := Scheme.Modules.moduleStrictTransform f B.I F
  let U₁ := B.I.blowupMap ⁻¹ᵁ U
  obtain ⟨_, hF₁qc, _, _, hF₁ft, _, hcompact, hqs⟩ :=
    Scheme.Modules.moduleAdmissibleBlowupPermanence U hU f F B
  let : F₁.IsQuasicoherent := hF₁qc
  let : F₁.IsFiniteType := hF₁ft inferInstance
  let : CompactSpace B.I.blowup := hcompact
  let : QuasiSeparatedSpace B.I.blowup := hqs
  have hU₁ : IsCompact (U₁ : Set B.I.blowup) := by
    have := B.isProper_blowupMap
    exact B.I.blowupMap.isCompact_preimage hU
  have hfp₁ := strictTransform_restrict_finitePresentation f F U hU hfp B
  obtain ⟨⟨I, hI, hsupport⟩, hboundary⟩ :=
    Scheme.Modules.flatModulePresentationAfterBoundaryBlowup f₁ F₁ hBflat U₁ hU₁ hfp₁
  obtain ⟨⟨C, hCI⟩, _, _, _, _, _, _, hCflat, hCfp⟩ := hboundary I hI hsupport
  subst I
  obtain ⟨_, _, hqc, K, hK, hKsupport, e, m, hm, he, hmq, hmiso, a, ha, _⟩ :=
    Scheme.Modules.moduleAdmissibleBlowupCalculus U hU f F B C
  let := hK
  let D : IsAdmissible S U :=
    { I := K
      finiteType := ideal_ofFiniteType_of_module K
      disjoint_support := by
        apply Set.disjoint_left.mpr
        intro s hs hKs
        rw [hKsupport] at hKs
        rcases hKs with hsB | ⟨t, ht, rfl⟩
        · exact Set.disjoint_left.mp B.disjoint_support hs hsB
        · exact Set.disjoint_left.mp C.disjoint_support hs ht }
  obtain ⟨_, hNqc, _⟩ :=
    Scheme.Modules.moduleAdmissibleBlowupPermanence U₁ hU₁ f₁ F₁ C
  obtain ⟨_, hMqc, _⟩ :=
    Scheme.Modules.moduleAdmissibleBlowupPermanence U hU f F D
  let := hmiso
  let := ha.1
  let := hNqc
  let := hMqc
  obtain ⟨hflatD, hfpD⟩ := flat_finitePresentation_of_iso_square m e
    (pullback.snd f₁ C.I.blowupMap) (pullback.snd f K.blowupMap) hmq
    _ _ (asIso a) hCflat hCfp
  refine ⟨D, ?_, hfpD⟩
  intro x
  let := ((pullback.snd f K.blowupMap).stalkMap x).hom.toAlgebra
  exact relative_flat_module_stalk _ _ hflatD x rfl

end AlgebraicGeometry
