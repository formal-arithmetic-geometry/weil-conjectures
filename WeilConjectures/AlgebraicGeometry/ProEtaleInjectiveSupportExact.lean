/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicClosedSupport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedEssentialImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenUnitEvaluation
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# The supported exact sequence for pro-etale injective complexes

Source: Stacks Project, Tags 03EJ, 03EI, 03DA, 09BN and 09AH;
(blueprint: lem-pur-support-exact).

The supported kernel is the intrinsic constant-coefficient kernel from
`sfIntrinsicSectionsWithSupport`.  The two arrows are the kernel inclusion and
the unit of the actual pro-etale module adjunction, applied to cochain
complexes.  The final clause records the quasi-compact closed-support
identification supplied by Tag 09AH.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

section InjectiveRestriction

universe w vC

variable {C : Type w} [Category.{vC} C] {J : GrothendieckTopology C}

private noncomputable def freeEvaluationEquiv
    {R : Cᵒᵖ ⥤ RingCat.{vC + 1}} {M : PresheafOfModules.{vC + 1} R} {V : C} :
    ((PresheafOfModules.free R).obj (uliftYoneda.{vC + 1}.obj V) ⟶ M) ≃
      M.obj (Opposite.op V) :=
  PresheafOfModules.freeHomEquiv.trans uliftYonedaEquiv

variable (R : Sheaf J RingCat.{vC + 1})

private theorem freeEvaluation_precomp {M : PresheafOfModules.{vC + 1} R.obj}
    {V W : C} (a : W ⟶ V)
    (h : (PresheafOfModules.free R.obj).obj (uliftYoneda.{vC + 1}.obj V) ⟶ M) :
    freeEvaluationEquiv ((PresheafOfModules.free R.obj).map (uliftYoneda.map a) ≫ h) =
      M.map a.op (freeEvaluationEquiv h) := by
  simp only [freeEvaluationEquiv, Equiv.trans_apply,
    ← PresheafOfModules.freeAdjunction_homEquiv]
  exact (congrArg uliftYonedaEquiv
    ((PresheafOfModules.freeAdjunction R.obj).homEquiv_naturality_left
      (uliftYoneda.map a) h)).trans
    (uliftYonedaEquiv_naturality
      ((PresheafOfModules.freeAdjunction R.obj).homEquiv _ _ h) a.op).symm

variable [HasSheafify J AddCommGrpCat.{vC + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{vC + 1}]

-- Sheafify the free basis inclusion, then extend the map corresponding to the section.
private theorem injective_restriction_surjective
    (M : SheafOfModules.{vC + 1} R) [Injective M] {V W : C} (a : W ⟶ V) [Mono a] :
    Function.Surjective (M.val.map a.op) := by
  let F := PresheafOfModules.free R.obj
  let S := PresheafOfModules.sheafification (𝟙 R.obj)
  let f := F.map (uliftYoneda.{vC + 1}.map a)
  have : Mono f := by
    apply PresheafOfModules.mono_of_injective
    intro T
    apply Finsupp.mapDomain_injective
    intro b c h
    apply ULift.ext
    exact (cancel_mono a).1 (congrArg ULift.down h)
  have : Mono (S.map f) := inferInstance
  intro m
  let g : S.obj (F.obj (uliftYoneda.{vC + 1}.obj W)) ⟶ M :=
    (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
      (freeEvaluationEquiv.symm m)
  obtain ⟨h, hh⟩ := Injective.factors g (S.map f)
  let h' := PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) h
  refine ⟨freeEvaluationEquiv h', ?_⟩
  have he : f ≫ h' = freeEvaluationEquiv.symm m := by
    calc
      f ≫ h' = (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _
          (S.map f ≫ h) :=
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_left
          f h).symm
      _ = _ := congrArg (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)) hh
      _ = _ := Equiv.apply_symm_apply _ _
  exact (freeEvaluation_precomp R a h').symm.trans
    ((congrArg freeEvaluationEquiv he).trans (Equiv.apply_symm_apply _ _))

end InjectiveRestriction

namespace AlgebraicGeometry.Scheme

private theorem openProjection_mono {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (V : X.ProEt) : Mono (proEtaleOpenSectionProjection j V) := by
  refine ⟨fun {T} b c h ↦ ?_⟩
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono (pullback.fst V.hom j)).1
  exact congrArg (fun z ↦ z.left) h

private theorem openProjection_comp_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (W : U.ProEt) :
    IsIso (proEtaleOpenSectionProjection j ((proEtaleOpenComposition j).obj W)) := by
  let V := (proEtaleOpenComposition j).obj W
  let a := proEtaleOpenSectionProjection j V
  let b : V ⟶ (proEtaleOpenComposition j).obj ((proEtaleBaseChange j).obj V) :=
    MorphismProperty.Over.homMk
      (pullback.lift (𝟙 W.left) W.hom (by exact Category.id_comp _))
      (by
        change pullback.lift _ _ _ ≫ pullback.snd _ _ ≫ j = W.hom ≫ j
        rw [pullback.lift_snd_assoc])
  have hb : b ≫ a = 𝟙 V := by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_fst _ _ _
  have : Mono a := openProjection_mono j V
  change IsIso a
  refine ⟨⟨b, ?_, hb⟩⟩
  apply (cancel_mono a).1
  simp only [Category.assoc, hb, Category.comp_id, Category.id_comp]

private theorem supported_open_isZero {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A]
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) :
    IsZero ((sfConstantModulePullback j A).obj ((sfIntrinsicSectionsWithSupport j A).obj M)) := by
  obtain ⟨d, hd, rho, hlin, hres, hnat, hunit⟩ := proEtaleOpenUnitEvaluation j A
  let eta := (sfConstantModuleAdjunction j A).unit.app M
  let K := (sfIntrinsicSectionsWithSupport j A).obj M
  have hzero (W : U.ProEt)
      (k : K.val.obj (Opposite.op ((proEtaleOpenComposition j).obj W))) : k = 0 := by
    let V := (proEtaleOpenComposition j).obj W
    have : IsIso (proEtaleOpenSectionProjection j V) := openProjection_comp_isIso j W
    have hi := (ConcreteCategory.bijective_of_isIso
      (M.val.presheaf.map (proEtaleOpenSectionProjection j V).op)).1
    have heta : Function.Injective (eta.val.app (Opposite.op V)) := by
      intro x y h
      apply hi
      exact (hunit M V x).symm.trans
        ((congrArg (rho M ((proEtaleBaseChange j).obj V)) h).trans (hunit M V y))
    have : Mono ((kernel.ι eta).val) :=
      inferInstanceAs (Mono ((SheafOfModules.forget _).map (kernel.ι eta)))
    apply PresheafOfModules.injective_of_mono (kernel.ι eta).val (Opposite.op V)
    apply heta
    have hc := congrArg (fun f ↦ f.val.app (Opposite.op V) k) (kernel.condition eta)
    change eta.val.app (Opposite.op V) ((kernel.ι eta).val.app (Opposite.op V) k) = 0 at hc
    simpa only [map_zero] using hc
  apply (IsZero.iff_id_eq_zero _).2
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext m
  apply (rho K W.unop).injective
  change rho K W.unop m = rho K W.unop 0
  simpa only [map_zero] using hzero W.unop (rho K W.unop m)

private theorem injective_openUnit_epi {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A]
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) [Injective M] :
    Epi ((sfConstantModuleAdjunction j A).unit.app M) := by
  obtain ⟨d, hd, rho, hlin, hres, hnat, hunit⟩ := proEtaleOpenUnitEvaluation j A
  have hsurj (V : X.ProEt) :
      Function.Surjective (((sfConstantModuleAdjunction j A).unit.app M).val.app
        (Opposite.op V)) := by
    have : Mono (proEtaleOpenSectionProjection j V) := openProjection_mono j V
    intro m
    obtain ⟨n, hn⟩ := injective_restriction_surjective
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing X A)) M (proEtaleOpenSectionProjection j V)
      (rho M ((proEtaleBaseChange j).obj V) m)
    refine ⟨n, ?_⟩
    apply (rho M ((proEtaleBaseChange j).obj V)).injective
    exact (hunit M V n).trans hn
  have : Epi (((sfConstantModuleAdjunction j A).unit.app M).val) :=
    PresheafOfModules.epi_of_surjective (fun {V} ↦ hsurj V.unop)
  exact (SheafOfModules.forget _).epi_of_epi_map this

/-- The canonical inclusion of the recorded pointwise supported kernel.
Source: Stacks Project, Tag 03DA (blueprint: lem-pur-support-exact). -/
noncomputable def sfIntrinsicSectionsWithSupport_inclusion
    {U X : Scheme.{u}} (j : U ⟶ X) (Λ : Type u) [CommRing Λ] [Finite Λ] :
    sfIntrinsicSectionsWithSupport j Λ ⟶ 𝟭 _ where
  app M := kernel.ι ((sfConstantModuleAdjunction j Λ).unit.app M)
  naturality M N f := by
    simp [sfIntrinsicSectionsWithSupport]

/-- The termwise kernel inclusion followed by the open module-adjunction unit.
Source: Stacks Project, Tags 03DA and 09BN (blueprint: lem-pur-support-exact). -/
noncomputable def sfIntrinsicSupportComplexSequence
    {U X : Scheme.{u}} (j : U ⟶ X) (Λ : Type u) [CommRing Λ] [Finite Λ]
    (I : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X Λ)) ℤ) :
    ShortComplex (CochainComplex
      (proEtaleRingModules X (proEtaleConstantRing X Λ)) ℤ) :=
  ShortComplex.mk
    (((sfIntrinsicSectionsWithSupport_inclusion j Λ).mapHomologicalComplex (.up ℤ)).app I)
    (((sfConstantModuleAdjunction j Λ).unit.mapHomologicalComplex (.up ℤ)).app I)
    (by
      apply HomologicalComplex.hom_ext
      intro n
      exact kernel.condition ((sfConstantModuleAdjunction j Λ).unit.app (I.X n)))

/--
For a closed immersion and its complementary open immersion, a
termwise-injective integer-indexed complex of finite constant-coefficient
pro-etale module sheaves has the canonical supported-kernel short exact
sequence.  If the open complement is quasi-compact, the canonical comparison
from the supported kernel to the direct image of the intrinsic closed upper
shriek is an isomorphism.

Source: Stacks Project, Tags 03EJ, 03EI, 03DA, 09BN and 09AH;
blueprint `lem-pur-support-exact`.

Proof plan, following the four steps of the node:
1. Put $\mathcal O=\Lambda_X$ and work on the fixed small site. For an object $V$ and
$W=V\times_XU$, the arrow $a:W\to V$ is monic: two arrows to $W$ over $V$ agree because the map
$U\to X$ identifies an open subscheme. Thus $\operatorname{Hom}(T,W)\to\operatorname{Hom}(T,V)$
is injective for every $T$. Use the free presheaves $P_Y=\mathcal O[h_Y]$ of [lem-weil-pbc-free-
yoneda-presheaf-module]. The map $P_W\to P_V$ sends $e_b$ to $e_{ab}$, hence is injective
sectionwise: distinct basis vectors have distinct images. Its inverse on that subset of the
basis, extended by zero on the other basis vectors, is a sectionwise linear left inverse;
naturality of this left inverse is not needed to check monicity. By exact module sheafification
[lem-weil-pbc-ringed-site-module-sheafification-exact], $P_W^\#\to P_V^\#$ is monic. The free-
presheaf bijection and the sheafification adjunction [def-weil-presheaf-modules-sheafification]
identify $\operatorname{Hom}(P_Y^\#,M)$ with $M(Y)$. Precomposition by the displayed
monomorphism is exactly restriction $M(V)\to M(W)$: evaluation on $e_{\mathrm{id}_W}$ gives
$M(a)(m)$.

2. For an injective module sheaf $I$ and every $m\in I(W)$, regard $m$ as a map $P_W^\#\to I$.
The defining extension property [def-sp-injective-resolutions], applied to the monomorphism of
step 1, extends it to $P_V^\#\to I$. The corresponding element of $I(V)$ restricts to $m$.
Therefore $I(V)\to I(V\times_XU)$ is surjective for every $V$. By [lem-pur-proetale-open-unit-
evaluation], these are exactly the components of the actual module-adjunction unit $\eta_{j,I}$,
after its specified coefficient-linear evaluation isomorphisms. In particular $\eta_{j,I}$ is an
epimorphism: two sheaf maps agreeing after it agree on every section of every object.

3. Apply step 2 to every $I^n$. Naturality of the unit gives
$\eta_{j,I^{n+1}}d^n=(j_*j^*d^n)\eta_{j,I^n}$, so $d^n$ restricts to a differential on $\mathcal
G_ZI^n$; its square is zero since the kernel inclusion is monic. Kernels in module sheaves are
sectionwise [def-weil-sheaf-of-modules-category]. Thus in every degree the kernel inclusion is
monic with image exactly $\ker\eta_{j,I^n}$, and the final arrow is epic by step 2. This is
short exactness [def-weil-pbc-exact-sequence]. It also gives the short exact sequence in the
complex category [def-pc-cochain-complex-modules]: a chain map killed by the unit factors
uniquely through these degreewise kernels, and the factor commutes with the differential by
cancelling the kernel inclusion; a map killed after the unit is zero degreewise by its
epimorphic components. There is no comparison of resolutions or infinite totalization in this
argument.

4. Assume now that $j$ is quasi-compact. Put $G^n=\mathcal G_ZI^n$. For a test object $W\to U$,
the restriction formula of [lem-pur-proetale-open-unit-evaluation] identifies $(j^*G^n)(W)$ with
$G^n(W\to X)$. The latter is zero: $W\times_XU\cong W$, and the unit on $I^n$ evaluated there is
the identity restriction, whose kernel is zero. Thus $j^*G^n=0$. Apply [lem-exc-proetale-closed-
essential-image] with the actual constant coefficient identifications: its hypotheses are
precisely the closed immersion, complementary open and quasi-compactness now assumed. It gives
the canonical isomorphism $G^n\xrightarrow{\sim}s_*s^*G^n=s_*s^!I^n$, with $s^!$ as constructed
in [def-exc-proetale-sections-with-support]. Naturality of this unit for the restricted
differentials gives a chain isomorphism. Compose its inverse with the kernel inclusion to obtain
the first map of the asserted $s_*s^!$ sequence; exactness follows from step 3.
(blueprint: lem-pur-support-exact)
-/
theorem proEtaleInjectiveSupportExact
    {X Z U : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion s] [IsOpenImmersion j]
    (hcomp : IsCompl (Set.range s.base) (Set.range j.base))
    (Λ : Type u) [CommRing Λ] [Finite Λ]
    (I : CochainComplex
      (proEtaleRingModules X (proEtaleConstantRing X Λ)) ℤ)
    (hI : ∀ n : ℤ, Injective (I.X n)) :
    (sfIntrinsicSupportComplexSequence j Λ I).ShortExact ∧
    (∀ [QuasiCompact j],
      ∃ e : ((sfIntrinsicSectionsWithSupport j Λ).mapHomologicalComplex (.up ℤ)).obj I ≅
          ((sfIntrinsicClosedUpperShriek s j Λ ⋙
            sfConstantModuleDirectImage s Λ).mapHomologicalComplex (.up ℤ)).obj I,
        e.hom =
          (((Functor.whiskerLeft (sfIntrinsicSectionsWithSupport j Λ)
              (sfConstantModuleAdjunction s Λ).unit).mapHomologicalComplex
            (.up ℤ)).app I) ∧
        ∃ hz : (e.inv ≫ (sfIntrinsicSupportComplexSequence j Λ I).f) ≫
            (sfIntrinsicSupportComplexSequence j Λ I).g = 0,
          (ShortComplex.mk (e.inv ≫ (sfIntrinsicSupportComplexSequence j Λ I).f)
            (sfIntrinsicSupportComplexSequence j Λ I).g hz).ShortExact) := by
  have hS : (sfIntrinsicSupportComplexSequence j Λ I).ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    let := hI n
    change (ShortComplex.kernelSequence
      ((sfConstantModuleAdjunction j Λ).unit.app (I.X n))).ShortExact
    exact
      { exact := ShortComplex.kernelSequence_exact _
        mono_f := by change Mono (kernel.ι _); infer_instance
        epi_g := by
          change Epi ((sfConstantModuleAdjunction j Λ).unit.app (I.X n))
          exact injective_openUnit_epi j Λ (I.X n) }
  refine ⟨hS, ?_⟩
  intro
  let t := Functor.whiskerLeft (sfIntrinsicSectionsWithSupport j Λ)
    (sfConstantModuleAdjunction s Λ).unit
  have htm (M : proEtaleRingModules X (proEtaleConstantRing X Λ)) : IsIso (t.app M) :=
    (proEtaleRingModule_closed_essImage_iff_and_unit_isIso s j hcomp.compl_eq.symm
      (proEtaleConstantRing X Λ) (proEtaleConstantRing Z Λ) (proEtaleConstantRing U Λ)
      (sfConstantCoefficientIso s Λ) (sfConstantCoefficientIso j Λ)
      ((sfIntrinsicSectionsWithSupport j Λ).obj M)).2 (supported_open_isZero j Λ M)
  have : IsIso t := NatIso.isIso_of_isIso_app t
  let e := (NatIso.mapHomologicalComplex (asIso t) (.up ℤ)).app I
  refine ⟨e, rfl, ?_⟩
  have hz : (e.inv ≫ (sfIntrinsicSupportComplexSequence j Λ I).f) ≫
      (sfIntrinsicSupportComplexSequence j Λ I).g = 0 := by
    rw [Category.assoc, ShortComplex.zero, comp_zero]
  refine ⟨hz, ?_⟩
  exact ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (S₁ := sfIntrinsicSupportComplexSequence j Λ I)
      (S₂ := ShortComplex.mk (e.inv ≫ (sfIntrinsicSupportComplexSequence j Λ I).f)
        (sfIntrinsicSupportComplexSequence j Λ I).g hz)
      e (Iso.refl _) (Iso.refl _) (by simp) (by simp)) hS

end AlgebraicGeometry.Scheme
