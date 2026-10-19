module
public import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf
public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful

/-!
# Normalized reconstruction from two successive support conditions

Source: Stacks Project, Pro-etale Cohomology, Tag 09AH; Categories, Tag 0037
(blueprint: lem-sfb-proetale-supported-reconstruction).

The statement records the canonical reconstruction of a module sheaf supported on a
closed subscheme and then on an open stratum.  The underlying ring sheaf is transported
to additive sheaves only to use the published module-object realization; no coefficient
or functor is chosen privately.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

section AdjunctionAlgebra
universe u₁ u₂ v₁ v₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable {L : D ⥤ C} {H : C ⥤ D} (a : L ⊣ H)
variable {N : C} {M : D} (σ : H.obj N ≅ M)
private theorem normalized_restrict
    [IsIso (L.map σ.inv ≫ a.counit.app N)] :
    H.map (inv (L.map σ.inv ≫ a.counit.app N)) = σ.hom ≫ a.unit.app M := by
  apply (cancel_mono (H.map (L.map σ.inv ≫ a.counit.app N))).1
  simp only [← H.map_comp, IsIso.inv_hom_id, H.map_id]
  rw [H.map_comp]
  have hu := a.unit.naturality σ.inv
  dsimp at hu
  rw [Category.assoc, ← Category.assoc (a.unit.app M), ← hu]
  simp only [Category.assoc, a.right_triangle_components, Category.comp_id, σ.hom_inv_id]
  rfl

private theorem normalized_unique
    [IsIso (L.map σ.inv ≫ a.counit.app N)] (q : N ⟶ L.obj M)
    (hq : H.map q = σ.hom ≫ a.unit.app M) :
    q = inv (L.map σ.inv ≫ a.counit.app N) := by
  apply (cancel_epi (L.map σ.inv ≫ a.counit.app N)).1
  rw [IsIso.hom_inv_id]
  calc
    (L.map σ.inv ≫ a.counit.app N) ≫ q =
        L.map σ.inv ≫ L.map (H.map q) ≫ a.counit.app (L.obj M) := by
      have hc := a.counit.naturality q
      dsimp at hc
      rw [Category.assoc, hc]
    _ = L.map (a.unit.app M) ≫ a.counit.app (L.obj M) := by
      rw [hq, ← L.map_comp_assoc]
      simp
    _ = 𝟙 _ := a.left_triangle_components M

private theorem normalized_natural {N' : C} {M' : D}
    (σ' : H.obj N' ≅ M') (c : N ⟶ N') (b : M ⟶ M')
    (h : H.map c ≫ σ'.hom = σ.hom ≫ b) :
    L.map b ≫ (L.map σ'.inv ≫ a.counit.app N') =
      (L.map σ.inv ≫ a.counit.app N) ≫ c := by
  have he : b ≫ σ'.inv = σ.inv ≫ H.map c := by
    apply (cancel_mono σ'.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h, Iso.inv_hom_id_assoc]
  rw [← L.map_comp_assoc, he, L.map_comp, Category.assoc]
  have hc := a.counit.naturality c
  dsimp at hc
  rw [hc, Category.assoc]

end AdjunctionAlgebra

private theorem abelian_open_supported_counit {X Z U : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (N : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (hi : IsZero ((upperStar Ab.{u + 1} i).obj N)) :
    IsIso ((openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).counit.app N) := by
  let F := upperStar Ab.{u + 1} i
  let G := lowerStar Ab.{u + 1} i
  let H := upperStar Ab.{u + 1} j
  let L := openImmersionLowerShriek Ab.{u + 1} j
  let ai := upperStarLowerStarAdjunction Ab.{u + 1} i
  let aj := openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j
  have hz (P : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :
      IsZero (H.obj (G.obj P)) :=
    isZero_upperStar_lowerStar_of_disjoint Ab.{u + 1} i j
      (compl_eq_iff_isCompl.mp hij.symm).disjoint P
  have hzi (P : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) :
      IsZero (F.obj (L.obj P)) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply (ai.homEquiv _ _).injective
    apply (aj.homEquiv _ _).injective
    exact (hz _).eq_of_tgt _ _
  have hdetect (P : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (hp : IsZero (F.obj P)) (hq : IsZero (H.obj P)) : IsZero P := by
    have : IsIso (ai.unit.app P) := (abelian_closed_support i j hij).2 P hq
    exact (G.map_isZero hp).of_iso (asIso (ai.unit.app P))
  have : IsIso aj.unit := aj.unit_isIso_of_L_fully_faithful
  have hH : IsIso (H.map (aj.counit.app N)) := by
    have ht := aj.right_triangle_components (Y := N)
    rw [← IsIso.inv_eq_of_hom_inv_id ht]
    infer_instance
  have hF : IsIso (F.map (aj.counit.app N)) :=
    (hzi _).isIso hi _
  let f := aj.counit.app N
  have hker : IsZero (kernel f) := hdetect _
    ((isZero_kernel_of_mono (F.map f)).of_iso (PreservesKernel.iso F f))
    ((isZero_kernel_of_mono (H.map f)).of_iso (PreservesKernel.iso H f))
  have hcoker : IsZero (cokernel f) := hdetect _
    ((isZero_cokernel_of_epi (F.map f)).of_iso (PreservesCokernel.iso F f))
    ((isZero_cokernel_of_epi (H.map f)).of_iso (PreservesCokernel.iso H f))
  have : Mono f := Preadditive.mono_of_isZero_kernel f hker
  have : Epi f := Preadditive.epi_of_isZero_cokernel f hcoker
  exact isIso_of_mono_of_epi f

/-- Additive realization of a commutative pro-etale ring sheaf.
Source: Stacks, Tag 03D1 (blueprint: def-weil-proetale-inverse-image). -/
noncomputable abbrev supportedRingAb {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (AlgebraicGeometry.Scheme.proEtaleModuleCoefficients R)

/-- The monoid object transported along a pro-etale inverse image.
Source: Stacks, Tags 03D1 and 09A5 (blueprint: def-weil-proetale-inverse-image). -/
noncomputable abbrev supportedRingMon {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    Mon (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) :=
  (f)^*[Ab.{u + 1}].mapMon.obj (Mon.mk (supportedRingAb R))

/-- The monoid object after a second inverse-image transport.
Source: Stacks, Tags 03D1 and 09A5 (blueprint: def-weil-proetale-inverse-image). -/
noncomputable abbrev supportedRingMonComp {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    Mon (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :=
  (g)^*[Ab.{u + 1}].mapMon.obj (supportedRingMon f R)

/-- Closed inverse-image and direct-image module functors used by reconstruction.
Source: Stacks, Tags 03D1 and 03D3 (blueprint: def-weil-proetale-inverse-image). -/
noncomputable abbrev supportedClosedPullback {X Z : Scheme.{u}} (i : Z ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  ringSheafInverseImage i (supportedRingAb R)

noncomputable abbrev supportedClosedPushforward {X Z : Scheme.{u}} (i : Z ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  ringSheafDirectImage i (supportedRingAb R)

/-- Open inverse-image module functor after the closed coefficient transport.
Source: Stacks, Tags 03D1 and 03D3 (blueprint: def-weil-proetale-inverse-image). -/
noncomputable abbrev supportedOpenPullback {X Z S : Scheme.{u}}
    (i : Z ⟶ X) (u : S ⟶ Z)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  ringSheafInverseImage u (supportedRingMon i R).X

/-- Extension by zero from the open stratum after the closed coefficient transport.
Source: Stacks, Tags 03DI and 03DJ (blueprint: lem-sfb-proetale-supported-reconstruction). -/
noncomputable abbrev supportedOpenExtension {X Z S : Scheme.{u}}
    (i : Z ⟶ X) (u : S ⟶ Z) [IsOpenImmersion u]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  ringSheafOpenExtension u (supportedRingMon i R).X

/-- The normalized open counit map in the reconstruction statement.
Source: Stacks, Tag 09AH (blueprint: lem-sfb-proetale-supported-reconstruction). -/
noncomputable def supportedLambda {X Z S : Scheme.{u}}
    (i : Z ⟶ X) (u : S ⟶ Z) [IsOpenImmersion u]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (A : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (supportedRingAb R))
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (supportedRingMonComp i u R).X)
    (σ : (supportedOpenPullback i u R).obj ((supportedClosedPullback i R).obj A) ≅ M) :
    (supportedOpenExtension i u R).obj M ⟶ (supportedClosedPullback i R).obj A :=
  (supportedOpenExtension i u R).map σ.inv ≫
    (ringSheafOpenAdjunction u (supportedRingMon i R).X).counit.app
      ((supportedClosedPullback i R).obj A)

/-- The support hypotheses make the normalized open map invertible.
Source: Stacks, Tag 09AH (blueprint: lem-sfb-proetale-supported-reconstruction).
The two localization sequences identify the closed unit and open counit with
isomorphisms; this named fact supplies the inverse used by `supportedTheta`. -/
theorem supportedLambda_isIso {X Z S B K : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (e : B ⟶ Z) [IsClosedImmersion e]
    (k : K ⟶ X) [IsOpenImmersion k] [QuasiCompact k]
    (u : S ⟶ Z) [IsOpenImmersion u] [QuasiCompact u]
    (hk : Set.range k = (Set.range i)ᶜ)
    (hu : Set.range u = (Set.range e)ᶜ)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (A : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (supportedRingAb R))
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (supportedRingMonComp i u R).X)
    (σ : (supportedOpenPullback i u R).obj
      ((supportedClosedPullback i R).obj A) ≅ M)
    (hK : IsZero ((ringSheafInverseImage k (supportedRingAb R)).obj A))
    (hB : IsZero ((ringSheafInverseImage e (supportedRingMon i R).X).obj
      ((supportedClosedPullback i R).obj A))) :
    IsIso (supportedLambda i u R A M σ) := by
  have _ := hk
  have _ := hK
  let : MonObj ((upperStar Ab.{u + 1} i).obj (supportedRingAb R)) :=
    (supportedRingMon i R).mon
  have hzero : IsZero ((upperStar Ab.{u + 1} e).obj
      ((supportedClosedPullback i R).obj A).X) :=
    (Mod.forget ((upperStar Ab.{u + 1} e).mapMon.obj
      (supportedRingMon i R)).X).map_isZero hB
  have hc := abelian_open_supported_counit e u hu
    ((supportedClosedPullback i R).obj A).X hzero
  have hlin : IsIso ((ringSheafOpenAdjunction u (supportedRingMon i R).X).counit.app
      ((supportedClosedPullback i R).obj A)) := by
    have hh : IsIso ((Mod.forget (supportedRingMon i R).X).map
        ((ringSheafOpenAdjunction u (supportedRingMon i R).X).counit.app
          ((supportedClosedPullback i R).obj A))) := by
      change IsIso (((ringSheafOpenAdjunction u (supportedRingMon i R).X).counit.app
        ((supportedClosedPullback i R).obj A)).hom)
      dsimp [ringSheafOpenAdjunction, Adjunction.mapModLeftAdjunction,
        Adjunction.mkOfHomEquiv, Adjunction.mk', Mod.Hom.mk']
      rw [Adjunction.homEquiv_counit]
      simp only [Mod.id_hom']
      erw [CategoryTheory.Functor.map_id, Category.id_comp]
      exact hc
    exact isIso_of_reflects_iso _ (Mod.forget _)
  dsimp only [supportedLambda]
  infer_instance

/-- The closed-adjunction transpose of the normalized map.
Source: Stacks, Tag 0037 (blueprint: lem-sfb-proetale-supported-reconstruction).
-/
noncomputable def supportedTheta {X Z S B K : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (e : B ⟶ Z) [IsClosedImmersion e]
    (k : K ⟶ X) [IsOpenImmersion k] [QuasiCompact k]
    (u : S ⟶ Z) [IsOpenImmersion u] [QuasiCompact u]
    (hk : Set.range k = (Set.range i)ᶜ)
    (hu : Set.range u = (Set.range e)ᶜ)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (A : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (supportedRingAb R))
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (supportedRingMonComp i u R).X)
    (σ : (supportedOpenPullback i u R).obj
      ((supportedClosedPullback i R).obj A) ≅ M)
    (hK : IsZero ((ringSheafInverseImage k (supportedRingAb R)).obj A))
    (hB : IsZero ((ringSheafInverseImage e (supportedRingMon i R).X).obj
      ((supportedClosedPullback i R).obj A))) :
    A ⟶ (supportedClosedPushforward i R).obj
      ((supportedOpenExtension i u R).obj M) := by
  letI := supportedLambda_isIso i e k u hk hu R A M σ hK hB
  exact (ringSheafAdjunction i (supportedRingAb R)).unit.app A ≫
    (supportedClosedPushforward i R).map (inv (supportedLambda i u R A M σ))

/-- Normalized reconstruction from two successive support conditions.
Source: Stacks Project, Pro-etale Cohomology, Tag 09AH, and Categories, Tag 0037
(blueprint: lem-sfb-proetale-supported-reconstruction).
Proof: apply the arbitrary-ring open--closed localization sequence first to `(i,k)`
and then to `(e,u)`.  The two vanishing restrictions make the closed unit and open
counit invertible.  Transpose the inverse of `supportedLambda` through the closed
adjunction to obtain `supportedTheta`; the triangle identities give the displayed
restriction equation.  Transposing an arbitrary map with that equation and cancelling
the invertible open counit gives uniqueness.  Naturality follows from naturality of
both units and counits and the commuting equation for the two input morphisms.
-/
theorem supported_reconstruction
    {X Z S B K : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (e : B ⟶ Z) [IsClosedImmersion e]
    (k : K ⟶ X) [IsOpenImmersion k] [QuasiCompact k]
    (u : S ⟶ Z) [IsOpenImmersion u] [QuasiCompact u]
    (hk : Set.range k = (Set.range i)ᶜ)
    (hu : Set.range u = (Set.range e)ᶜ)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (A : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (supportedRingAb R))
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (supportedRingMonComp i u R).X)
    (σ : (supportedOpenPullback i u R).obj ((supportedClosedPullback i R).obj A) ≅ M)
    (hK : IsZero ((ringSheafInverseImage k (supportedRingAb R)).obj A))
    (hB : IsZero ((ringSheafInverseImage e (supportedRingMon i R).X).obj
      ((supportedClosedPullback i R).obj A))) :
    IsIso (supportedLambda i u R A M σ) ∧
      IsIso (supportedTheta i e k u hk hu R A M σ hK hB) ∧
      (supportedOpenPullback i u R).map
          ((supportedClosedPullback i R).map (supportedTheta i e k u hk hu R A M σ hK hB)) ≫
        (supportedOpenPullback i u R).map
          ((ringSheafAdjunction i (supportedRingAb R)).counit.app
            ((supportedOpenExtension i u R).obj M)) =
      σ.hom ≫ (ringSheafOpenAdjunction u (supportedRingMon i R).X).unit.app M ∧
      (∀ (h : A ⟶ (supportedClosedPushforward i R).obj
          ((supportedOpenExtension i u R).obj M)),
        (supportedOpenPullback i u R).map
            ((supportedClosedPullback i R).map h) ≫
          (supportedOpenPullback i u R).map
            ((ringSheafAdjunction i (supportedRingAb R)).counit.app
              ((supportedOpenExtension i u R).obj M)) =
        σ.hom ≫ (ringSheafOpenAdjunction u (supportedRingMon i R).X).unit.app M →
          h = supportedTheta i e k u hk hu R A M σ hK hB) ∧
      (∀ {A' : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (supportedRingAb R)}
          {M' : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
            (supportedRingMonComp i u R).X}
          (σ' : (supportedOpenPullback i u R).obj
            ((supportedClosedPullback i R).obj A') ≅ M')
          (hK' : IsZero ((ringSheafInverseImage k (supportedRingAb R)).obj A'))
          (hB' : IsZero ((ringSheafInverseImage e (supportedRingMon i R).X).obj
            ((supportedClosedPullback i R).obj A')))
          (a : A ⟶ A') (b : M ⟶ M'),
        (supportedOpenPullback i u R).map
              ((supportedClosedPullback i R).map a) ≫ σ'.hom = σ.hom ≫ b →
          ((supportedOpenExtension i u R).map b ≫
              supportedLambda i u R A' M' σ' =
            supportedLambda i u R A M σ ≫
              (supportedClosedPullback i R).map a) ∧
          (a ≫ supportedTheta i e k u hk hu R A' M' σ' hK' hB' =
            supportedTheta i e k u hk hu R A M σ hK hB ≫
              (supportedClosedPushforward i R).map
                ((supportedOpenExtension i u R).map b))) := by
  have hlambda := supportedLambda_isIso i e k u hk hu R A M σ hK hB
  have : IsIso (supportedLambda i u R A M σ) := hlambda
  have : IsIso ((supportedOpenExtension i u R).map σ.inv ≫
      (ringSheafOpenAdjunction u (supportedRingMon i R).X).counit.app
        ((supportedClosedPullback i R).obj A)) := hlambda
  have htheta : IsIso (supportedTheta i e k u hk hu R A M σ hK hB) := by
    have hzero : IsZero ((upperStar Ab.{u + 1} k).obj A.X) :=
      (Mod.forget ((upperStar Ab.{u + 1} k).mapMon.obj
        (Mon.mk (supportedRingAb R))).X).map_isZero hK
    have hi := (abelian_closed_support i k hk).2 A.X hzero
    have hi' : IsIso ((ringSheafAdjunction i (supportedRingAb R)).unit.app A) := by
      have hh : IsIso ((Mod.forget (supportedRingAb R)).map
          ((ringSheafAdjunction i (supportedRingAb R)).unit.app A)) := by
        change IsIso (((ringSheafAdjunction i (supportedRingAb R)).unit.app A).hom)
        rw [Adjunction.mapModAdjunction_unit_app_hom]
        exact hi
      exact isIso_of_reflects_iso _ (Mod.forget _)
    dsimp only [supportedTheta]
    infer_instance
  let F := supportedClosedPullback i R
  let G := supportedClosedPushforward i R
  let L := supportedOpenExtension i u R
  let H := supportedOpenPullback i u R
  let ac := ringSheafAdjunction i (supportedRingAb R)
  let ao := ringSheafOpenAdjunction u (supportedRingMon i R).X
  have ht : F.map (supportedTheta i e k u hk hu R A M σ hK hB) ≫
      ac.counit.app (L.obj M) = inv (supportedLambda i u R A M σ) := by
    change (ac.homEquiv _ _).symm ((ac.homEquiv _ _)
      (inv (supportedLambda i u R A M σ))) = _
    exact (ac.homEquiv _ _).symm_apply_apply _
  have hr : H.map (inv (supportedLambda i u R A M σ)) =
      σ.hom ≫ ao.unit.app M := normalized_restrict ao σ
  refine ⟨hlambda, htheta, ?_, ?_, ?_⟩
  · rw [← H.map_comp, ht, hr]
  · intro h he
    apply (ac.homEquiv _ _).symm.injective
    change F.map h ≫ ac.counit.app (L.obj M) =
      F.map (supportedTheta i e k u hk hu R A M σ hK hB) ≫ ac.counit.app (L.obj M)
    rw [ht]
    apply normalized_unique ao σ
    change H.map (F.map h ≫ ac.counit.app (L.obj M)) = _
    rw [H.map_comp]
    exact he
  · intro A' M' σ' hK' hB' a b hab
    have hn : L.map b ≫ supportedLambda i u R A' M' σ' =
        supportedLambda i u R A M σ ≫ F.map a :=
      normalized_natural ao σ σ' (F.map a) b hab
    refine ⟨hn, ?_⟩
    have := supportedLambda_isIso i e k u hk hu R A' M' σ' hK' hB'
    have hn' : F.map a ≫ inv (supportedLambda i u R A' M' σ') =
        inv (supportedLambda i u R A M σ) ≫ L.map b := by
      apply (cancel_epi (supportedLambda i u R A M σ)).1
      simpa only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp,
        Category.comp_id, Category.assoc, IsIso.hom_inv_id_assoc] using
        congrArg (fun t ↦ t ≫ inv (supportedLambda i u R A' M' σ')) hn.symm
    change a ≫ (ac.homEquiv _ _) (inv (supportedLambda i u R A' M' σ')) =
      (ac.homEquiv _ _) (inv (supportedLambda i u R A M σ)) ≫ G.map (L.map b)
    rw [← ac.homEquiv_naturality_left, ← ac.homEquiv_naturality_right, hn']


end AlgebraicGeometry.ProEtale
