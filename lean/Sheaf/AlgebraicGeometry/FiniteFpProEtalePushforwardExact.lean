/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.RingTheory.ProEtale.WContractible
import Sheaf.RingTheory.FiniteWContractible
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Exact pro-etale direct image for finite locally finitely presented morphisms

Source: Stacks Project, Tag 09A8, `proetale-lemma-finite`, and its module consequence
by forgetting scalars (blueprint: lem-zl-finite-fp-proetale-pushforward-exact).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem finite_over_contractible
    {T : Scheme.{u}} (W : T.ProEt) (R : CommRingCat.{u}) [IsWContractibleRing R]
    (g : W.left ⟶ Spec R) [IsFinite g] [LocallyOfFinitePresentation g] :
    (ProEt.topology T).IsWeaklyContractible.{u + 1} W := by
  have : IsAffine W.left := isAffine_of_isAffineHom g
  let φ : R ⟶ Γ(W.left, ⊤) := Spec.preimage (W.left.isoSpec.inv ≫ g)
  have hφ : Spec.map φ = W.left.isoSpec.inv ≫ g := Spec.map_preimage _
  have : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have : LocallyOfFinitePresentation (Spec.map φ) := by rw [hφ]; infer_instance
  algebraize [φ.hom]
  have : Module.Finite R Γ(W.left, ⊤) := (IsFinite.SpecMap_iff φ).mp inferInstance
  have : Algebra.FinitePresentation R Γ(W.left, ⊤) :=
    (LocallyOfFinitePresentation.SpecMap_iff φ).mp inferInstance
  have : IsWContractibleRing Γ(W.left, ⊤) :=
    isWContractibleRing_of_finite_finitePresentation R Γ(W.left, ⊤)
  exact ProEt.isWeaklyContractible_of_iso W.left.isoSpec

private theorem finite_contractible_cover
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [LocallyOfFinitePresentation f]
    (V : Y.ProEt) :
    ∃ (ι : Type u) (W : ι → Y.ProEt) (a : ∀ i, W i ⟶ V),
      (∀ i, (ProEt.topology X).IsWeaklyContractible.{u + 1}
        ((proEtaleBaseChange f).obj (W i))) ∧
      Sieve.ofArrows W a ∈ ProEt.topology Y V := by
  classical
  have 𝒜 : V.left.AffineOpenCover := V.left.affineOpenCover
  choose D iD iA hind hff hw using fun x : 𝒜.I₀ ↦ exists_isWContractibleRing (𝒜.X x)
  let φ (x : 𝒜.I₀) : 𝒜.X x ⟶ CommRingCat.of (D x) := CommRingCat.ofHom (algebraMap _ _)
  have (x : 𝒜.I₀) : WeaklyEtale (Spec.map (φ x)) := by
    rw [WeaklyEtale.Spec_iff]
    exact RingHom.IndEtale.weaklyEtale ((RingHom.IndEtale.algebraMap_iff _ _).2 (hind x))
  have (x : 𝒜.I₀) : Surjective (Spec.map (φ x)) :=
    ((flat_and_surjective_SpecMap_iff (φ x)).2
      (RingHom.faithfullyFlat_algebraMap_iff.2 (hff x))).2
  let U (x : 𝒜.I₀) := ProEt.ofOpenImmersion V (𝒜.f x)
  let W (x : 𝒜.I₀) : Y.ProEt := ProEt.mk (Spec.map (φ x) ≫ (U x).hom)
  let w (x : 𝒜.I₀) : W x ⟶ U x := MorphismProperty.Over.homMk (Spec.map (φ x)) rfl
  refine ⟨𝒜.I₀, W, fun x ↦ w x ≫ ProEt.ofOpenImmersionHom V (𝒜.f x), ?_, ?_⟩
  · intro x
    have := hw x
    exact finite_over_contractible ((proEtaleBaseChange f).obj (W x))
      (CommRingCat.of (D x)) (pullback.fst (W x).hom f)
  · have hU : Sieve.ofArrows U (fun x ↦ ProEt.ofOpenImmersionHom V (𝒜.f x)) ∈
        ProEt.topology Y V :=
      ProEt.mem_topology_of_openImmersion _ 𝒜.f (fun y ↦ ⟨_, 𝒜.covers y⟩)
        (fun x ↦ Sieve.ofArrows_mk _ _ x)
    refine (ProEt.topology Y).transitive hU _ fun Z g hg ↦ ?_
    obtain ⟨_, c, _, ⟨x⟩, rfl⟩ := hg
    rw [Sieve.pullback_comp]
    refine (ProEt.topology _).pullback_stable c ((ProEt.topology _).superset_covering ?_
      (Precoverage.generate_mem_toGrothendieck (R := .singleton (w x)) ?_))
    · rintro _ _ ⟨_, d, _, ⟨⟩, rfl⟩
      rw [Sieve.pullback_apply, Category.assoc]
      exact (Sieve.ofArrows _ _).downward_closed (Sieve.ofArrows_mk _ _ x) d
    · rw [ProEt.mem_precoverage_iff, Presieve.map_singleton]
      exact Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) (f := Spec.map (φ x))
        inferInstance

private theorem finite_directImage_epi
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [LocallyOfFinitePresentation f]
    {F G : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}} (e : F ⟶ G) [Epi e] :
    Epi ((proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).map e) := by
  apply (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1}
    ((proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).map e)).mp
  have he := (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1} e).mpr inferInstance
  have he' := (Presheaf.isLocallySurjective_iff_whisker_forget (ProEt.topology X) e.hom).mp he
  refine ⟨fun {V} s ↦ ?_⟩
  obtain ⟨ι, W, a, hW, hcov⟩ := finite_contractible_cover f V
  refine (ProEt.topology Y).superset_covering ?_ hcov
  rintro _ _ ⟨_, b, _, ⟨i⟩, rfl⟩
  apply (Presheaf.imageSieve _ s).downward_closed _ b
  exact hW i ((sheafCompose (ProEt.topology X)
    (CategoryTheory.forget AddCommGrpCat.{u + 1})).map e)
    he' (G.obj.map ((proEtaleBaseChange f).map (a i)).op s)

/-- Direct image on the small pro-etale sites is exact for a finite morphism locally
of finite presentation, both for abelian sheaves and for modules over arbitrary
commutative ring sheaves with a specified inverse-image ring map. Exactness is expressed
as preservation of finite limits and finite colimits; in these abelian categories this
is equivalent to preservation of every short exact sequence. The module action is
restriction of scalars along the actual adjoint of `c`, with no invertibility assumption.

Source: Stacks Project, Tag 09A8, `proetale-lemma-finite`; Modules on Sites, Tag 03D7
(blueprint: lem-zl-finite-fp-proetale-pushforward-exact).

Proof:
1. Cover each object W of Y_proet by affine opens W' over affine opens Spec A of Y.
   Weak-etale source locality makes these objects of the site; quasi-compactness of
   affine opens makes the resulting family a pro-etale cover. Over Spec A the finite
   morphism is Spec B -> Spec A with B a finite A-module and a finitely presented
   A-algebra, by LocallyOfFinitePresentation.finitePresentation_appLE.
2. Choose a faithfully flat ind-etale w-contractible A'-algebra D for W'=Spec A'
   by exists_isWContractibleRing. Ind-etale stability makes Spec D a site object and
   its surjective affine map to W' a cover. The pullback of X is Spec C with
   C=D tensor_A B. Finite generation and finite presentation survive this base change.
   The finite-w-contractibility lemma (Tag 0986) makes C w-contractible, including C=0.
3. An epimorphism of abelian sheaves is locally surjective. Weak contractibility of
   Spec C makes evaluation on this pullback surjective. By sectionwise direct image,
   the pushed epimorphism is therefore surjective on sections over each Spec D.
4. The composites Spec D -> W cover every W. Thus the pushed map is locally
   surjective and hence epi by the abelian-sheaf epi criterion. Kernels are computed
   sectionwise, so direct image also preserves kernels. It is additive, hence exact,
   equivalently preserves finite limits and finite colimits.
5. For modules, the underlying abelian sheaf of SheafOfModules.pushforward is this
   same direct image. Its scalar action is through the adjoint of c, as in the
   ringed-topoi module adjunction. The faithful exact forgetful functor
   moduleSheaves_colimits_forgetful reflects exactness. Apply steps 1--4 to the
   underlying sequence. No constructibility, torsion or flatness is used. -/
theorem finite_fp_proEtale_pushforward_exact
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [LocallyOfFinitePresentation f] :
    PreservesFiniteLimits (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}) ∧
    PreservesFiniteColimits (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}) ∧
    ∀ (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
      (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
      (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ⟶ R_X),
      PreservesFiniteLimits
        (SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
          (J := ProEt.topology Y) (K := ProEt.topology X)
          (S := (sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Y)
          (R := (sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
          ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
              ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv R_Y R_X c))) ∧
      PreservesFiniteColimits
        (SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
          (J := ProEt.topology Y) (K := ProEt.topology X)
          (S := (sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Y)
          (R := (sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
          ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
              ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv R_Y R_X c))) := by
  let P := proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}
  have : P.PreservesEpimorphisms := ⟨fun e _ ↦ finite_directImage_epi f e⟩
  have : PreservesFiniteLimits P := inferInstance
  have : P.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels P
  have : PreservesFiniteColimits P := Functor.preservesFiniteColimits_of_preservesHomology P
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro R_Y R_X c
  let S := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Y
  let R := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X
  let φ : S ⟶ ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology Y) (ProEt.topology X)).obj R :=
    (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv R_Y R_X c)
  let Q := SheafOfModules.pushforward.{u + 1} φ
  have : Q.Additive := ⟨by intros; rfl⟩
  let G := SheafOfModules.toSheaf.{u + 1} S
  let H := SheafOfModules.toSheaf.{u + 1} R
  let e : Q ⋙ G ≅ H ⋙ P := Iso.refl _
  have : PreservesFiniteLimits (Q ⋙ G) := preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteLimits Q := preservesFiniteLimits_of_reflects_of_preserves Q G
  have : PreservesFiniteColimits H := (moduleSheaves_colimits_forgetful R).2.2.1
  have : Q.PreservesEpimorphisms := by
    constructor
    intro M N a ha
    apply G.epi_of_epi_map
    change Epi (P.map (H.map a))
    infer_instance
  have : Q.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels Q
  exact ⟨inferInstance, Functor.preservesFiniteColimits_of_preservesHomology Q⟩

end AlgebraicGeometry.Scheme
