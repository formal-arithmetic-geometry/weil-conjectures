/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import Sheaf.AlgebraicGeometry.ProperFlatCechModel
import Sheaf.AlgebraicGeometry.FlatModelFiniteFreeShortening
import Sheaf.AlgebraicGeometry.FiniteFreeResidueLocusOpen
import Sheaf.AlgebraicGeometry.FinitePresentationIntegralFiltration
import Sheaf.AlgebraicGeometry.IntegralIdealProperCohomology
import Sheaf.AlgebraicGeometry.CohomologyFiniteExtension
import Sheaf.AlgebraicGeometry.FiniteFreePullbackResidueCriterion

/-!
# Higher direct images are computed by finite free complexes

For a proper morphism of finite presentation and a coherent sheaf flat over the base, the higher
direct images are locally computed by bounded complexes of finite free modules
(`AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`); in
particular they are coherent.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}
variable (f : X ⟶ T) (ℱ : X.Modules)

/-- `IsFiniteFreeComplex P d` says that the cochain complex `P` of `𝒪_X`-modules is a **bounded
complex of finite free modules in degrees `[0, d]`**: it vanishes outside `[0, d]`, and each
`P.X n` is isomorphic to a free module `𝒪_X^r` of finite rank. -/
structure IsFiniteFreeComplex (P : CochainComplex X.Modules ℤ) (d : ℕ) : Prop where
  isStrictlyGE : P.IsStrictlyGE 0
  isStrictlyLE : P.IsStrictlyLE d
  exists_iso_free (n : ℤ) :
    ∃ r : ℕ, Nonempty (P.X n ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)))

/-- `IsFiniteLocallyFreeInDegree M i r` says that the family `M = (M q)_{q : ℕ}` of `𝒪_X`-modules,
thought of as the cohomology sheaves `H^q(E)` of an object `E` of the derived category of
`𝒪_X`-modules, is that of a **finite locally free module of rank `r` placed in degree `i`**:
`M q = 0` for `q ≠ i`, and `M i` is finite locally free of rank `r`.

For an object `E` represented by a complex this is the same as `E ≅ ℰ[-i]` with `ℰ` finite
locally free of rank `r`: a complex whose cohomology is concentrated in degree `i` is
quasi-isomorphic to its `i`-th cohomology placed in degree `i`. There is no derived category of
`X.Modules` with derived pushforward available, so the condition is stated on the cohomology
sheaves. The case `i = 0`, `r = 1` is an *invertible module placed in degree `0`*
(`isFiniteLocallyFreeInDegree_zero_one_iff`).

(blueprint: `def-pc-invertible-in-degree-zero`) -/
structure IsFiniteLocallyFreeInDegree (M : ℕ → X.Modules) (i r : ℕ) : Prop where
  isZero (q : ℕ) (hq : q ≠ i) : IsZero (M q)
  isFiniteLocallyFreeOfRank : (M i).IsFiniteLocallyFreeOfRank r

/-- A family of modules is that of an invertible module placed in degree `0` if and only if it
vanishes in nonzero degrees and is invertible in degree `0`.

(blueprint: `def-pc-invertible-in-degree-zero`) -/
theorem isFiniteLocallyFreeInDegree_zero_one_iff (M : ℕ → X.Modules) :
    IsFiniteLocallyFreeInDegree M 0 1 ↔
      (∀ q ≠ 0, IsZero (M q)) ∧ SheafOfModules.IsInvertible (R := X.ringCatSheaf) (M 0) :=
  ⟨fun h ↦ ⟨h.isZero, (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one (M 0)).2
      h.isFiniteLocallyFreeOfRank⟩,
    fun h ↦ ⟨h.1, (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one (M 0)).1 h.2⟩⟩

/-- **The perfect locus of a bounded complex of finite free modules.** Let `P` be a bounded complex
of finite free `𝒪_Y`-modules, representing a perfect object `E` of the derived category of `Y`, and
fix `i r : ℕ`. There is an open subscheme `U` of `Y` such that a morphism `g : Y' ⟶ Y` factors
through `U` if and only if `L g^* E = g^* P` is a finite locally free module of rank `r` placed in
degree `i` (`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeInDegree`).

The pullback `g^* P` computes `L g^* E` because the terms of `P` are free. The proof splits
contractible summands off `P` over the local rings of `Y`, until every differential has entries in
the maximal ideal; the remaining complex is then `𝒪^r[-i]` near every point whose derived fibre has
cohomology `κ(y)^r` concentrated in degree `i`, and `U` is the set of such points. The converse
direction uses that extension of fields is faithfully flat.

(blueprint: `lem-pc-perfect-locus`) -/
theorem IsFiniteFreeComplex.exists_opens_range_subset_iff {Y : Scheme.{u}}
    {P : CochainComplex Y.Modules ℤ} {d : ℕ} (hP : IsFiniteFreeComplex P d) (i r : ℕ) :
    ∃ U : Y.Opens, ∀ {Y' : Scheme.{u}} (g : Y' ⟶ Y), Set.range g.base ⊆ U ↔
      IsFiniteLocallyFreeInDegree
        (fun q : ℕ ↦ (((Modules.pullback g).mapHomologicalComplex _).obj P).homology q) i r := by
  let U : Y.Opens := ⟨_, isOpen_finiteFree_residue_locus P d
    hP.isStrictlyGE hP.isStrictlyLE hP.exists_iso_free i r⟩
  refine ⟨U, fun g ↦ ?_⟩
  have h := finiteFree_pullback_single_iff_residue P d
    hP.isStrictlyGE hP.isStrictlyLE hP.exists_iso_free i r g
  constructor
  · intro hg
    obtain ⟨hz, hf⟩ := h.mpr hg
    exact ⟨hz, hf⟩
  · intro hg
    exact h.mp ⟨hg.isZero, hg.isFiniteLocallyFreeOfRank⟩

section Coherence

variable [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
  [HasInjectiveResolutions X.Modules] [ℱ.IsFinitePresentation]

/-- **Perfectness of the higher direct images, with base change.** With `f : X ⟶ T` proper of
finite presentation and `ℱ` an `𝒪_X`-module of finite presentation which is flat over `T`, every
point `t` of `T` has an open neighbourhood `U` over which `R f_* ℱ` is represented by a bounded
complex `P` of finite free `𝒪_U`-modules whose formation commutes with every base change: for
every `g : T' ⟶ U`, with `f' : X' ⟶ T'` the base change of `f` along `g ≫ U.ι` in the cartesian
square `sq`
```
X' ------g'-------> X
|                   |
f'                  f
v                   v
T' --g--> U --U.ι--> T
```
and `ℱ'` the pullback of `ℱ` to `X'`, the cohomology of the pullback `g^* P` is `R^q f'_* ℱ'`.

Taking `g = 𝟙 U` and for `sq` the square `(isPullback_morphismRestrict f U).flip`, and
combining with `AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_iso_restrict`, the
cohomology of `P` itself is `R^q f_* ℱ|_U`.

The isomorphisms are only required to exist for each `g` and `q` separately: they are not
asserted to be the canonical base-change maps, nor to be compatible with composition of the
`g`. This suffices for semicontinuity of the fibre dimension and for the perfect locus, but not
for the clause of Grauert's theorem saying that the canonical maps
`R^q f_* ℱ ⊗ κ(t) → H^q(X_t, ℱ_t)` are isomorphisms; stating that needs the base-change map of
higher direct images, which is not available.

The proof needs, over a Noetherian affine base, Mumford's complex, obtained from the Čech complex
of a finite affine cover, which is a bounded complex of flat modules by the flatness of `ℱ`,
together with `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage`; the
general case reduces to this by Noetherian approximation of `(f, ℱ)` [EGA IV₃, §8 and §11.2].
Alternatively, it follows from Kiehl's theorem that `R f_* ℱ` is pseudo-coherent, and finite
Tor-amplitude coming from flatness [Stacks, Tags 0B91 and 0A1H].

(blueprint: `sk-thm-picard-coherence`) -/
theorem exists_isFiniteFreeComplex_higherDirectImage (hℱ : ℱ.IsFlatOver f) (t : T) :
    ∃ (U : T.Opens) (P : CochainComplex U.toScheme.Modules ℤ) (d : ℕ), t ∈ U ∧
      IsFiniteFreeComplex P d ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ)) := by
    obtain ⟨U, C, Q, d, ht, hCge, hCle, hCflat, hQle, hQfree, ⟨e, he⟩, hC⟩ :=
      exists_proper_flat_cech_model f ℱ hℱ t
    obtain ⟨V, hVU, P, htV, hPge, hPle, hPfree, hPC⟩ :=
      exists_local_finiteFree_shortening U C Q d hCge hCle hCflat hQle hQfree e he t ht
    refine ⟨V, P, d, htV, ⟨hPge, hPle, hPfree⟩, ?_⟩
    intro T' X' g g' f' _ sq q
    obtain ⟨ePC⟩ := hPC g q
    have sqU : IsPullback g' f' f ((g ≫ T.homOfLE hVU) ≫ U.ι) := by
      simpa only [Category.assoc, Scheme.homOfLE_ι] using sq
    obtain ⟨eC⟩ := hC (g ≫ T.homOfLE hVU) g' f' sqU q
    exact ⟨ePC ≪≫ eC⟩

/-- **Finiteness of the cohomology of a proper morphism over a Noetherian affine base.** With
`f : X ⟶ T` proper, `T` affine with Noetherian ring of global sections `Γ(T, ⊤)` and `ℱ` a coherent
`𝒪_X`-module, the global sections `Γ(T, R^q f_* ℱ) = H^q(X, ℱ)` of the higher direct image form a
finite `Γ(T, ⊤)`-module for every `q` [Stacks, Tag 02O6], [EGA III₁, 3.2.1].

This is the affine clause of the blueprint lemma `lem-pc-coherent-hi`; for a general proper `f`
the blueprint discharges it by the cited classical input (Chow's lemma and the projective case,
Stacks 02O5/02O6). It is the only input to
`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage` beyond the formal
properties of the higher direct images.

(blueprint: `lem-pc-coherent-hi`) -/
theorem finite_sections_higherDirectImage [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Module.Finite Γ(T, ⊤) Γ((higherDirectImage f q).obj ℱ, ⊤) := by
  classical
  have : IsLocallyNoetherian T := isLocallyNoetherian_of_isOpenImmersion T.isoSpec.hom
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  let R := Γ(T, ⊤)
  let P (M : X.Modules) : Prop := ∀ n : ℕ,
    letI : Module R (M.H n) := Module.compHom _ f.appTop.hom
    Module.Finite R (M.H n)
  have hzero (M : X.Modules) (hM : IsZero M) : P M := by
    intro n
    let : Module R (M.H n) := Module.compHom _ f.appTop.hom
    have hz (x : M.H n) : x = 0 := by
      have h := congrArg (fun φ ↦ H.map φ n x) (hM.eq_of_src (𝟙 M) 0)
      simpa only [H.map_id_apply, H.map_zero_apply] using h
    have : Subsingleton (M.H n) := ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
    infer_instance
  have hiso {M N : X.Modules} (e : M ≅ N) (hM : P M) : P N := by
    intro n
    let : Module R (M.H n) := Module.compHom _ f.appTop.hom
    let : Module R (N.H n) := Module.compHom _ f.appTop.hom
    let eR : M.H n ≃ₗ[R] N.H n :=
      { H.mapLinearEquiv e n with
        map_smul' := fun a x ↦ (H.mapLinearEquiv e n).map_smul (f.appTop a) x }
    have := hM n
    exact Module.Finite.equiv eR
  obtain ⟨m, c, hc, hbot, htop, hpieces⟩ :=
    exists_finitePresentation_integral_filtration X ℱ
  have hpc : ∀ j : Fin (m + 1), P (c j : X.Modules) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      apply hzero
      exact (Subobject.isoOfEq _ _ hbot ≪≫ Subobject.botCoeIsoZero).isZero_iff.mpr
        (isZero_zero X.Modules)
    | succ j ih =>
      let a := Subobject.ofLE (c j.castSucc) (c j.succ) (hc j.castSucc_le_succ)
      let S := ShortComplex.mk a (cokernel.π a) (cokernel.condition a)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel a }
      obtain ⟨Z, i, hi, hZ, I, ⟨e⟩⟩ := hpieces j
      have := hi
      have := hZ
      have hI : P ((pushforward i).obj I.toModules) := by
        intro n
        exact finite_H_pushforward_integral_ideal f Z i I n
      have hQ : P (cokernel a) := hiso e.symm hI
      intro n
      exact finite_H_of_shortExact R f.appTop.hom S hS n (ih n) (hQ n)
  have hF : P ℱ := hiso
    (Subobject.isoOfEq _ _ htop ≪≫ asIso (⊤ : Subobject ℱ).arrow) (hpc _)
  let : Module R (ℱ.H q) := Module.compHom _ f.appTop.hom
  have := hF q
  obtain ⟨e, he⟩ := exists_bijective_semilinearMap_sections_higherDirectImage_H f ℱ q
  let eR : Γ((higherDirectImage f q).obj ℱ, ⊤) →ₗ[R] ℱ.H q :=
    { e.toAddMonoidHom with map_smul' := fun a x ↦ e.map_smulₛₗ a x }
  exact Module.Finite.equiv (LinearEquiv.ofBijective eR he).symm

/-- **Coherence of the higher direct images over a locally Noetherian base.** With
`f : X ⟶ T` proper, `T` locally Noetherian and `ℱ` a coherent `𝒪_X`-module, the higher direct
image `R^q f_* ℱ` is a coherent `𝒪_T`-module for every `q` [EGA III₁, 3.2.1],
[Stacks, Tag 02O5]. Coherence is spelled as quasi-coherence together with finite presentation;
quasi-coherence of `R^q f_* ℱ` is
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_higherDirectImage`, so only finite
presentation is stated here.

The Noetherian hypothesis cannot be dropped, even for `ℱ` flat over `T`. Let `k` be a field,
`V` an infinite-dimensional `k`-vector space, `T = Spec (k ⊕ V)` with `V` a square-zero ideal,
`E` an elliptic curve over `k` and `f : E × T ⟶ T` the projection. Line bundles on `E × T`
which are trivial on `E` are classified by `H¹(E, 𝒪_E) ⊗_k V ≅ V`; let `ℒ` be the one with class
a nonzero `v ∈ V`. The sequence `0 ⟶ 𝒪_E ⊗_k V ⟶ ℒ ⟶ 𝒪_E ⟶ 0` has connecting map
`k ⟶ H¹(E, 𝒪_E) ⊗_k V` sending `1` to `v`, so `f_* ℒ` corresponds to the module `V`, which is
killed by `V` and infinite-dimensional over `k`, hence not of finite type over `k ⊕ V`.

(blueprint: `sk-thm-picard-coherence`) -/
theorem isFinitePresentation_higherDirectImage [IsLocallyNoetherian T]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    ((higherDirectImage f q).obj ℱ).IsFinitePresentation := by
  have hP (V : T.Opens) (hV : IsAffineOpen V) :
      ∃ P : (((higherDirectImage f q).obj ℱ).restrict hV.fromSpec).Presentation, P.IsFinite := by
    have := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    have : IsNoetherianRing Γ(Spec Γ(T, V), ⊤) :=
      isNoetherianRing_of_ringEquiv _ (Scheme.ΓSpecIso Γ(T, V)).commRingCatIsoToRingEquiv.symm
    have := isGrothendieckAbelian (Limits.pullback f hV.fromSpec)
    obtain ⟨e⟩ := nonempty_higherDirectImage_iso_restrict f ℱ hV.fromSpec _ _
      (IsPullback.of_hasPullback f hV.fromSpec) q
    have : ((Modules.pullback (pullback.fst f hV.fromSpec)).obj ℱ).IsFinitePresentation :=
      (SheafOfModules.isFinitePresentation (Limits.pullback f hV.fromSpec).ringCatSheaf).prop_of_iso
        ((restrictFunctorIsoPullback _).app ℱ) (isFinitePresentation_restrictFunctor _ ℱ)
    have : ((Modules.pullback (pullback.fst f hV.fromSpec)).obj ℱ).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent (Limits.pullback f hV.fromSpec).ringCatSheaf).prop_of_iso
        ((restrictFunctorIsoPullback _).app ℱ) (isQuasicoherent_restrictFunctor _ ℱ)
    have := finite_sections_higherDirectImage (pullback.snd f hV.fromSpec)
      ((Modules.pullback (pullback.fst f hV.fromSpec)).obj ℱ) q
    let φ : Γ((higherDirectImage (pullback.snd f hV.fromSpec) q).obj
        ((Modules.pullback (pullback.fst f hV.fromSpec)).obj ℱ), ⊤) →ₗ[Γ(Spec Γ(T, V), ⊤)]
        Γ(((higherDirectImage f q).obj ℱ).restrict hV.fromSpec, ⊤) :=
      { toFun := e.hom.app ⊤, map_add' := map_add _, map_smul' := Hom.app_smul e.hom }
    have : Module.Finite Γ(Spec Γ(T, V), ⊤)
        Γ(((higherDirectImage f q).obj ℱ).restrict hV.fromSpec, ⊤) :=
      Module.Finite.of_surjective φ (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).2
    have := finite_sections_top_of_finite
      (((higherDirectImage f q).obj ℱ).restrict hV.fromSpec)
    have := isQuasicoherent_higherDirectImage f ℱ q
    exact exists_presentation_isFinite _
  have (V : T.affineOpens) : IsOpenImmersion (IsAffineOpen.fromSpec (U := V.1) V.2) :=
    IsAffineOpen.isOpenImmersion_fromSpec V.2
  choose P _ using fun V : T.affineOpens ↦ hP V.1 V.2
  refine isFinitePresentation_of_iSup_opensRange_eq_top _ _ ?_ P
  exact (iSup_congr fun V ↦ IsAffineOpen.opensRange_fromSpec V.2).trans
    (iSup_affineOpens_eq_top T)

end Coherence

end AlgebraicGeometry.Scheme.Modules
