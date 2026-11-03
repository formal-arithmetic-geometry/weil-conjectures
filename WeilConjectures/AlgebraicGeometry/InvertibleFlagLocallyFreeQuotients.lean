/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import WeilConjectures.AlgebraicGeometry.Modules.LocalSectionOfEpi
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Ambient quotients of a flag with invertible successive quotients

Source: Stacks Project, Tag 0FI5, invertible-subbundle argument, and Tags 01C6 and 0BCI.
(blueprint: lem-pur-invertible-flag-locally-free-quotients).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

private def locallySplit {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    IsSplitMono ((restrictFunctor U.ι).map f)

private theorem splitMono_natIso {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) {A B : C} (f : A ⟶ B) [IsSplitMono (F.map f)] :
    IsSplitMono (G.map f) := by
  apply IsSplitMono.mk'
  refine ⟨e.inv.app B ≫ retraction (F.map f) ≫ e.hom.app A, ?_⟩
  rw [← Category.assoc, e.inv.naturality, Category.assoc,
    ← Category.assoc (F.map f), IsSplitMono.id, Category.id_comp, e.inv_hom_id_app]

private theorem splitMono_smaller {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) {U V : X.Opens} (h : U ≤ V)
    [IsSplitMono ((restrictFunctor V.ι).map f)] :
    IsSplitMono ((restrictFunctor U.ι).map f) := by
  let G := restrictFunctor (X.homOfLE h)
  let e := restrictFunctorCongr (X.homOfLE_ι h).symm ≪≫
    restrictFunctorComp (X.homOfLE h) V.ι
  have : IsSplitMono ((restrictFunctor V.ι ⋙ G).map f) := by
    change IsSplitMono (G.map ((restrictFunctor V.ι).map f))
    infer_instance
  exact splitMono_natIso e.symm f

private theorem locallySplit_comp {X : Scheme.{u}} {M N Q : X.Modules}
    (f : M ⟶ N) (g : N ⟶ Q) (hf : locallySplit f) (hg : locallySplit g) :
    locallySplit (f ≫ g) := by
  intro x
  obtain ⟨U, hxU, hU⟩ := hf x
  obtain ⟨V, hxV, hV⟩ := hg x
  have := splitMono_smaller f (inf_le_left : U ⊓ V ≤ U)
  have := splitMono_smaller g (inf_le_right : U ⊓ V ≤ V)
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, ?_⟩
  rw [Functor.map_comp]
  infer_instance

private theorem locallySplit_of_invertible_cokernel {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) [Mono f] [(cokernel f).IsInvertible] : locallySplit f := by
  have : (cokernel f).IsFiniteLocallyFree := inferInstance
  intro x
  obtain ⟨U, hx, s, hs⟩ := exists_local_section_of_epi (cokernel.π f) x
  let R := restrictFunctor U.ι
  let T := (ShortComplex.cokernelSequence f).map R
  have h0 : (ShortComplex.cokernelSequence f).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact f
      mono_f := by dsimp only [ShortComplex.cokernelSequence]; infer_instance
      epi_g := by dsimp only [ShortComplex.cokernelSequence]; infer_instance }
  have hT : T.ShortExact := h0.map_of_exact R
  let t := ShortComplex.Splitting.ofExactOfSection T hT.exact s hs hT.mono_f
  exact ⟨U, hx, IsSplitMono.mk' ⟨t.r, t.f_r⟩⟩

private theorem finiteLocallyFree_cokernel_splitMono
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    [N.IsFiniteLocallyFree] [IsSplitMono f] : (cokernel f).IsFiniteLocallyFree := by
  have : N.IsQuasicoherent := inferInstance
  have hqc := isQuasicoherent_cokernel (retraction f ≫ f)
  have : (cokernel f).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (cokernelEpiComp (retraction f) f) hqc
  let T := ShortComplex.cokernelSequence f
  let t := ShortComplex.Splitting.ofExactOfRetraction T
    (ShortComplex.cokernelSequence_exact f) (retraction f) (IsSplitMono.id f)
    (by dsimp [T, ShortComplex.cokernelSequence]; infer_instance)
  apply isFiniteLocallyFree_of_isAffineOpen
  intro U hU
  obtain ⟨hfp, hproj⟩ := finitePresentation_projective_sections N hU
  let E := SheafOfModules.evaluation X.ringCatSheaf (Opposite.op U)
  have : E.Additive := by
    dsimp [E, SheafOfModules.evaluation]
    infer_instance
  let s := t.map E
  let q : Γ(N, U) →ₗ[Γ(X, U)] Γ(cokernel f, U) := ((T.map E).g).hom
  let j : Γ(cokernel f, U) →ₗ[Γ(X, U)] Γ(N, U) := s.s.hom
  have hsplit : q.comp j = LinearMap.id := by
    have h := congrArg ModuleCat.Hom.hom s.s_g
    change q.comp j = LinearMap.id at h
    exact h
  have : Module.Finite Γ(X, U) Γ(cokernel f, U) :=
    Module.Finite.of_surjective q (fun y ↦ ⟨j y, DFunLike.congr_fun hsplit y⟩)
  have : Module.Projective Γ(X, U) Γ(cokernel f, U) :=
    Module.Projective.of_split j q hsplit
  exact ⟨Module.finitePresentation_of_projective _ _, inferInstance⟩

private theorem finiteLocallyFree_cokernel_locallySplit
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) [N.IsFiniteLocallyFree]
    (h : locallySplit f) : (cokernel f).IsFiniteLocallyFree := by
  classical
  choose U hx hs using h
  apply isFiniteLocallyFree_of_isOpenImmersion (cokernel f) (fun x ↦ (U x).ι)
  · simpa only [Scheme.Opens.opensRange_ι] using
      (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩ :
        (⨆ x, U x) = ⊤)
  · intro x
    let R := restrictFunctor (U x).ι
    have : IsSplitMono (R.map f) := hs x
    have : (R.obj N).IsFiniteLocallyFree :=
      SheafOfModules.IsFiniteLocallyFree.of_iso (R := (U x).toScheme.ringCatSheaf)
        ((restrictFunctorIsoPullback (U x).ι).symm.app N)
    have : (cokernel (R.map f)).IsFiniteLocallyFree :=
      finiteLocallyFree_cokernel_splitMono (R.map f)
    exact SheafOfModules.IsFiniteLocallyFree.of_iso (R := (U x).toScheme.ringCatSheaf)
      ((PreservesCokernel.iso R f).symm ≪≫
        (restrictFunctorIsoPullback (U x).ι).app (cokernel f))

/-- Every ambient quotient of a filtration with invertible successive quotients is finite
locally free. Only the ambient module is assumed finite locally free; no rank, zero first
member, quasi-coherence of the intermediate members, or globally split filtration is needed.

Source: Stacks Project, Tag 0FI5, invertible-subbundle paragraph, and Tags 01C6 and 0BCI.
(blueprint: lem-pur-invertible-flag-locally-free-quotients).

Proof: Each step is monic by compatibility with its monic ambient inclusion. Its cokernel
is a line bundle, so the cokernel projection has local sections by finite-basis lifting.
The exact cokernel sequence then gives a local retraction of the step. Starting with the
last ambient inclusion, which is an isomorphism, descend through the finite flag. Intersect
the two splitting neighbourhoods and compose retractions, proving every ambient inclusion
locally split. Its cokernel is therefore locally a retract of the finite locally free
ambient module. For completeness, quasi-coherence of this cokernel follows by expressing
it as the cokernel of the ambient endomorphism retraction followed by inclusion. On affine
opens its sections are finite projective retracts of the ambient sections; hence they are
finitely presented and flat. The affine criterion and open-cover locality give the result.
The same argument includes length zero and the empty scheme. -/
theorem invertibleFlag_finiteLocallyFree_cokernels {X : Scheme.{u}}
    (F : X.Modules) [F.IsFiniteLocallyFree] (r : ℕ)
    (H : Fin (r + 1) → X.Modules) (ι : ∀ i : Fin (r + 1), H i ⟶ F)
    (d : ∀ j : Fin r, H j.castSucc ⟶ H j.succ)
    (hmono : ∀ i : Fin (r + 1), Mono (ι i))
    (hcompat : ∀ j : Fin r, d j ≫ ι j.succ = ι j.castSucc)
    (hfull : IsIso (ι (Fin.last r)))
    (hQ : ∀ j : Fin r,
      SheafOfModules.IsInvertible (R := X.ringCatSheaf) (cokernel (d j))) :
    ∀ i : Fin (r + 1), (cokernel (ι i)).IsFiniteLocallyFree := by
  have hsplit : ∀ i : Fin (r + 1), locallySplit (ι i) := by
    apply Fin.reverseInduction
    · intro x
      exact ⟨⊤, trivial, inferInstance⟩
    · intro j hj
      have := hmono j.castSucc
      have : Mono (d j) := mono_of_mono_fac (hcompat j)
      have := hQ j
      rw [← hcompat j]
      exact locallySplit_comp (d j) (ι j.succ)
        (locallySplit_of_invertible_cokernel (d j)) hj
  intro i
  exact finiteLocallyFree_cokernel_locallySplit (ι i) (hsplit i)

private theorem cokernel_rank_of_split
    {Z : Scheme.{u}} {M N : Z.Modules} (f : M ⟶ N) (k b : ℕ)
    [M.IsFiniteLocallyFreeOfRank b] [N.IsFiniteLocallyFreeOfRank k] [IsSplitMono f] :
    (cokernel f).IsFiniteLocallyFreeOfRank (k - b) := by
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree M b
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree N k
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree N k
  have := isQuasicoherent_cokernel (X := Z) f
  let T := ShortComplex.cokernelSequence f
  let t := ShortComplex.Splitting.ofExactOfRetraction T
    (ShortComplex.cokernelSequence_exact f) (retraction f) (IsSplitMono.id f)
    (by dsimp [T, ShortComplex.cokernelSequence]; infer_instance)
  apply isFiniteLocallyFreeOfRank_of_isAffineOpen
  intro U hU
  obtain ⟨hfp, hproj⟩ := finitePresentation_projective_sections N hU
  let F := SheafOfModules.evaluation Z.ringCatSheaf (Opposite.op U)
  have : F.Additive := by
    dsimp [F, SheafOfModules.evaluation]
    infer_instance
  let s := t.map F
  let e : Γ(N, U) ≃ₗ[Γ(Z, U)] Γ(M, U) × Γ(cokernel f, U) :=
    (s.isoBinaryBiproduct ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv
  let q : Γ(N, U) →ₗ[Γ(Z, U)] Γ(cokernel f, U) := ((T.map F).g).hom
  let j : Γ(cokernel f, U) →ₗ[Γ(Z, U)] Γ(N, U) := s.s.hom
  have hsplit : q.comp j = LinearMap.id := by
    have h := congrArg ModuleCat.Hom.hom s.s_g
    change q.comp j = LinearMap.id at h
    exact h
  have hQfin : Module.Finite Γ(Z, U) Γ(cokernel f, U) :=
    Module.Finite.of_surjective q (by
      intro y
      exact ⟨j y, DFunLike.congr_fun hsplit y⟩)
  have hQproj : Module.Projective Γ(Z, U) Γ(cokernel f, U) :=
    Module.Projective.of_split j q hsplit
  have hQfp := Module.finitePresentation_of_projective Γ(Z, U) Γ(cokernel f, U)
  have hQflat : Module.Flat Γ(Z, U) Γ(cokernel f, U) := inferInstance
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M b
  obtain ⟨hMfp, hMproj⟩ := finitePresentation_projective_sections M hU
  refine ⟨hQfp, hQflat, ?_⟩
  intro p
  have hr := congrFun (Module.rankAtStalk_eq_of_equiv e) p
  have hsum := congrFun (Module.rankAtStalk_prod (R := Γ(Z, U)) Γ(M, U)
    Γ(cokernel f, U)) p
  have hM := rankAtStalk_sections_eq M (r := b) hU p
  have hN := rankAtStalk_sections_eq N (r := k) hU p
  change Module.rankAtStalk Γ(N, U) p =
    Module.rankAtStalk (Γ(M, U) × Γ(cokernel f, U)) p at hr
  rw [hN, hsum, Pi.add_apply, hM] at hr
  omega


private theorem cokernel_rank_of_local_split {X : Scheme.{u}}
    {M N : X.Modules} (f : M ⟶ N) (k b : ℕ)
    [M.IsFiniteLocallyFreeOfRank b] [N.IsFiniteLocallyFreeOfRank k]
    (h : locallySplit f) : (cokernel f).IsFiniteLocallyFreeOfRank (k - b) := by
  classical
  choose U hx hs using h
  apply isFiniteLocallyFreeOfRank_of_iSup_eq_top _ U
  · exact eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  · intro x
    let H := restrictFunctor (U x).ι
    have : IsSplitMono (H.map f) := hs x
    have : (H.obj M).IsFiniteLocallyFreeOfRank b := inferInstance
    have : (H.obj N).IsFiniteLocallyFreeOfRank k := inferInstance
    have := cokernel_rank_of_split (H.map f) k b
    exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (PreservesCokernel.iso H f).symm

/-- The quotient by the first line of an invertible flag has the expected constant rank.
Source: Stacks Project, Tag 0FI5, quotient filtration in the induction, and Tag 0BCI.
(blueprint: lem-pur-first-line-quotient-rank).

Proof: the zero first member identifies the first successive cokernel with H_1, so H_1
has rank one. The ambient inclusion is locally split by descending induction through
the flag. Locally its cokernel is a summand of the ambient bundle. On affine opens the
splitting identifies the ambient sections with the product of the first-line sections
and quotient sections; additivity of rank at every prime gives rank r minus one. The
affine criterion and locality give the constant-rank assertion, also on the empty base. -/
theorem invertibleFlag_firstQuotient_rank {X : Scheme.{u}} (n : ℕ)
    (F : X.Modules) [F.IsFiniteLocallyFreeOfRank (n + 1)]
    (H : Fin (n + 2) → X.Modules) (ι : ∀ i, H i ⟶ F)
    (d : ∀ j : Fin (n + 1), H j.castSucc ⟶ H j.succ)
    (hm : ∀ i, Mono (ι i)) (hc : ∀ j, d j ≫ ι j.succ = ι j.castSucc)
    (hz : IsZero (H 0)) (hf : IsIso (ι (Fin.last (n + 1))))
    (hQ : ∀ j : Fin (n + 1),
      SheafOfModules.IsInvertible (R := X.ringCatSheaf) (cokernel (d j))) :
    (cokernel (ι (0 : Fin (n + 1)).succ)).IsFiniteLocallyFreeOfRank n := by
  have hsplit : ∀ i : Fin (n + 2), locallySplit (ι i) := by
    apply Fin.reverseInduction
    · intro x
      exact ⟨⊤, trivial, inferInstance⟩
    · intro j hj
      have := hm j.castSucc
      have : Mono (d j) := mono_of_mono_fac (hc j)
      have := hQ j
      rw [← hc j]
      exact locallySplit_comp (d j) (ι j.succ)
        (locallySplit_of_invertible_cokernel (d j)) hj
  have hd : d 0 = 0 := hz.eq_of_src _ _
  let e : cokernel (d 0) ≅ H (0 : Fin (n + 1)).succ :=
    cokernelIsoOfEq hd ≪≫ cokernelZeroIsoTarget
  have := hQ 0
  have : (cokernel (d 0)).IsFiniteLocallyFreeOfRank 1 :=
    (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one
      (R := X.ringCatSheaf) _).mp inferInstance
  have : (H (0 : Fin (n + 1)).succ).IsFiniteLocallyFreeOfRank 1 :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (R := X.ringCatSheaf) e
  simpa using cokernel_rank_of_local_split (ι (0 : Fin (n + 1)).succ) (n + 1) 1
    (hsplit (0 : Fin (n + 1)).succ)

end AlgebraicGeometry.Scheme.Modules
