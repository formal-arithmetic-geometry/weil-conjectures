/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.AlgebraicGeometry.BertiniSingularFibreCoordinates
public import Sheaf.AlgebraicGeometry.BertiniLocalFirstJets
import Sheaf.AlgebraicGeometry.BertiniFibreJetComparison
import Sheaf.AlgebraicGeometry.ReducedPullbackSectionVanishing
import Sheaf.AlgebraicGeometry.HypersurfaceNonzeroRelativeDifferential
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.SmoothRelativeDifferentialsFiniteLocallyFree
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The universal first-jet relation on the singular fibre

Source: Stacks Project, Varieties, Tag 0FD6, final paragraph of `lemma-bertini`,
using the one-way hypersurface criterion of Algebra Tag 00T7.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  bertiniSingularFibreRingMap bertiniLocalFirstJet bertiniUniversalSection

private theorem zeroLocus_coefficient_eq_zero
    {X : Scheme.{u}} (M : X.Modules) [M.IsInvertible]
    (φ : Scheme.Modules.unit X ⟶ M) (U : X.Opens)
    (e : Γ(M, U)) (he : Scheme.Modules.IsFreeGenerator e)
    (a : Γ(X, U)) (ha : φ.app U (1 : Γ(X, U)) = a • e) :
    φ.zeroLocus.subschemeι.app U a = 0 := by
  have : SheafOfModules.IsInvertible.{u, u, u} M :=
    Scheme.Modules.IsInvertible.sheafOfModules_isInvertible M
  have : SheafOfModules.IsInvertible.{u, u, u} (Scheme.Modules.unit X) :=
    Scheme.Modules.IsInvertible.sheafOfModules_isInvertible (MonoidalCategory.tensorUnit X.Modules)
  apply TopCat.Presheaf.section_ext φ.zeroLocus.subscheme.sheaf
  intro z hz
  change φ.zeroLocus.subscheme.presheaf.germ _ z hz _ = _
  erw [map_zero, ← Scheme.Hom.germ_stalkMap_apply]
  change X.presheaf.germ U (φ.zeroLocus.subschemeι z) hz a ∈
    RingHom.ker (φ.zeroLocus.subschemeι.stalkMap z).hom
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hz U.isOpen
  have haV := Scheme.Modules.Hom.app_presheaf_map_of_eq φ (homOfLE hVU) ha
  change φ.app V (X.presheaf.map (homOfLE hVU).op (1 : Γ(X, U))) =
    X.presheaf.map (homOfLE hVU).op a • M.presheaf.map (homOfLE hVU).op e at haV
  rw [map_one] at haV
  rw [Scheme.Hom.ker_stalkMap _ ⟨V, hV⟩ z hzV,
    Scheme.IdealSheafData.ker_subschemeι,
    Scheme.Modules.Hom.ideal_zeroLocus φ ⟨V, hV⟩
      (Scheme.Modules.isFreeGenerator_one V) (he.map hVU) haV,
    Ideal.map_span, Set.image_singleton]
  rw [← X.presheaf.germ_res_apply (homOfLE hVU) _ hzV a]
  exact Ideal.mem_span_singleton_self _

private theorem differential_zero_of_nonsmooth_zeroLocus
    {X S : Scheme.{u}} (p : X ⟶ S) [Smooth p]
    (M : X.Modules) [M.IsInvertible] (φ : Scheme.Modules.unit X ⟶ M)
    (z : φ.zeroLocus.subscheme) (V : X.Opens)
    (hz : φ.zeroLocus.subschemeι z ∈ V)
    (e : Γ(M, V)) (he : Scheme.Modules.IsFreeGenerator e)
    (a : Γ(X, V)) (ha : φ.app V (1 : Γ(X, V)) = a • e)
    (hsing : ¬ ∃ Q : φ.zeroLocus.subscheme.Opens, z ∈ Q ∧
      Smooth (Q.ι ≫ φ.zeroLocus.subschemeι ≫ p)) :
    letI : Module (X.presheaf.stalk (φ.zeroLocus.subschemeι z))
        (X.residueField (φ.zeroLocus.subschemeι z)) :=
      Module.compHom _ (X.residue (φ.zeroLocus.subschemeι z)).hom
    (p.relativeDifferentials.presheaf.germ V (φ.zeroLocus.subschemeι z) hz
      (p.relativeDifferentialsDerivation.d (X := op V) a) ⊗ₜ[X.presheaf.stalk
        (φ.zeroLocus.subschemeι z)]
      (1 : X.residueField (φ.zeroLocus.subschemeι z))) = 0 := by
  obtain ⟨s, rfl⟩ := M.unitHomEquiv.symm.surjective φ
  by_contra hda
  apply hsing
  have hda' : Scheme.Hom.relativeDifferentialValue p V
      ((Scheme.Modules.Hom.zeroLocus (M.unitHomEquiv.symm s)).subschemeι z) hz a := by
    dsimp only [Scheme.Hom.relativeDifferentialValue]
    exact hda
  exact Scheme.Hom.smooth_zeroLocus_of_relativeDifferentialValue p M s z V hz e he a ha hda'

/-- The first jet of the universal equation is zero on the actual singular fibre.
This concerns only the value and differential of the universal equation, with its
fixed geometric coordinate functions; it does not assert affineness, construct a
coordinate-ring presentation, or quantify over polynomial quotients.

Source: Stacks Project, Varieties, Tag 0FD6, final paragraph of `lemma-bertini`;
Algebra Tag 00T7 supplies the one-way smooth hypersurface criterion.
(blueprint: lem-zl-bertini-singular-fibre-jet-tensor).

Proof: Pull the frame e back to coefficient affine space times W. The coefficient
of the universal section in that frame is F = sum_i x_i a_i. Its relative
differential over coefficient affine space is sum_i x_i da_i, because the x_i
come from that base. The value F vanishes on the universal zero scheme.
At any point of this zero scheme where dF in the ambient cotangent fibre is
nonzero, the smooth hypersurface criterion gives a smooth open neighbourhood
over coefficient affine space. Thus dF vanishes at every point of the singular
subset. The ambient relative differential module is locally free, since f is
smooth. In a local basis, every coordinate of dF vanishes in the residue field
at each singular point. Each coordinate therefore belongs to the vanishing
ideal of that subset, so dF restricts to zero on its reduced closed subscheme.
Pull back these two zero sections to the fibre at z. Restriction from Y to W
and then to U preserves the germ at z. Base change for relative differentials
identifies the pulled-back differential fibre with the scalar extension of
bertiniCotangentFibre f U z. Under this identification the two sections together
are the sum of x_i tensor (a_i(z), da_i(z)). Their coordinate functions are exactly
bertiniSingularFibreRingMap applied to X i, by its defining projection identities.
This proves the displayed tensor relation. The same argument covers an empty
fibre (its ring of sections is zero), an empty index set, and cotangent rank zero. -/
theorem bertini_singular_fibre_jet_tensor
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [Smooth f]
    (L : Y.Modules) [L.IsInvertible]
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤))
    (U : Y.Opens) (z : U) (W : Y.Opens) (hz : U.ι z ∈ W)
    (e : Γ(L, W)) (he : Scheme.Modules.IsFreeGenerator e) :
    let K := (U : Scheme).residueField z
    let A := Γ((bertiniSingularToSource f L s ∣_ U).fiber z, ⊤)
    let ρ := bertiniSingularFibreRingMap f L s U z
    letI : Algebra K A := (ρ.comp MvPolynomial.C).toAlgebra
    (∑ i, ρ (MvPolynomial.X i) ⊗ₜ[K]
      bertiniLocalFirstJet f U z W hz
        (he.coeff (L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s i))) :
      A ⊗[K] (K × bertiniCotangentFibre f U z)) = 0 := by
  classical
  dsimp only
  let c := Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))
  let p := pullback.fst c f
  let M := (Scheme.Modules.tensorPullback (pullback.snd c f)).obj L
  let V := (pullback.snd c f) ⁻¹ᵁ W
  let t := (bertiniSingularToSource f L s ∣_ U).fiberι z ≫
    ((bertiniSingularToSource f L s) ⁻¹ᵁ U).ι
  let i := (bertiniSingularIdeal f L s).subschemeι ≫
    (bertiniUniversalIdeal f L s).subschemeι
  let g := t ≫ i
  obtain ⟨hV, ep, hep, J, hJ, hcomp⟩ :=
    exists_bertini_fibre_jet_comparison f L s U z W hz e he
  let F := hep.coeff (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
    (bertiniUniversalSection f L s))
  let E := ((Classical.choose
    (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd c f))).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd c f))).app L
  have : M.IsInvertible := Scheme.Modules.IsInvertible.of_iso E.symm
  let φ := Scheme.Modules.homOfGlobalSection M (bertiniUniversalSection f L s)
  have hF : φ.app V (1 : Γ(pullback c f, V)) = F • ep := by
    rw [Scheme.Modules.homOfGlobalSection_app_one]
    exact (hep.coeff_smul _).symm
  have hvalue : g.appLE V ⊤ hV F = 0 := by
    have hzero := zeroLocus_coefficient_eq_zero M φ V ep hep F hF
    change (bertiniUniversalIdeal f L s).subschemeι.app V F = 0 at hzero
    have hzero' := congrArg
      ((t ≫ (bertiniSingularIdeal f L s).subschemeι).appLE
        ((bertiniUniversalIdeal f L s).subschemeι ⁻¹ᵁ V) ⊤ hV) hzero
    simpa only [Scheme.Hom.comp_appLE, Scheme.Hom.comp_app,
      Scheme.Hom.comp_preimage, CommRingCat.comp_apply, map_zero,
      g, i, Category.assoc] using hzero'
  have : Smooth p := inferInstance
  have : p.relativeDifferentials.IsFiniteLocallyFree :=
    p.isFiniteLocallyFree_relativeDifferentials
  have : IsReduced (bertiniSingularIdeal f L s).subscheme := by
    dsimp only [bertiniSingularIdeal]
    infer_instance
  have hdiff := Scheme.Modules.tensorPullbackSection_eq_zero_of_reduced_factor i t
    p.relativeDifferentials V (p.relativeDifferentialsDerivation.d (X := op V) F) ?_ ⊤ hV
  · apply hJ
    exact hcomp.trans ((Prod.ext hvalue hdiff).trans (map_zero J).symm)
  · intro r hr
    apply differential_zero_of_nonsmooth_zeroLocus p M φ
      ((bertiniSingularIdeal f L s).subschemeι r) V hr ep hep F hF
    intro hQ
    have hrSing : (bertiniSingularIdeal f L s).subschemeι r ∈
        bertiniUniversalSingularLocus f L s := by
      exact (bertiniSingularHomeomorph f L s r).property
    apply hrSing
    simpa only [bertiniUniversalProjection, bertiniUniversalIdeal, φ, M, p, c] using hQ

end AlgebraicGeometry
