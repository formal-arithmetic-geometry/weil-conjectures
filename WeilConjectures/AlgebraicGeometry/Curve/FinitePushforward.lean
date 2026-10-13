/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Devissage
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleEdgeMapBaseChange
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
public import WeilConjectures.SixFunctors.Finite.BaseChange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# The eight curve assertions pass to finite direct images

Let `k` be an algebraically closed field, `ν : X ⟶ Y` a finite morphism of curves over `k` and
`F` a torsion étale sheaf on `X`. If the eight curve assertions `C(X, F)` hold, then so do
`C(Y, ν_* F)`: the edge maps `Hᵠ(Y, ν_* F) ⟶ Hᵠ(X, F)` are isomorphisms compatible with
pullbacks along field extensions and open immersions.

## Main statements

- `AlgebraicGeometry.Etale.epi_counit_app_of_isFinite`: for a finite morphism `ν`, the counit
  `ν^* ν_* F ⟶ F` is an epimorphism.
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_lowerStar`: constructibility descends along
  a finite direct image.
- `AlgebraicGeometry.IsCurve.Assertions.lowerStar_of_isFinite`.

## References

- Stacks Project, Lemma 0A5D, <https://stacks.math.columbia.edu/tag/0A5D>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Helpers

variable {Λ} {X Y : Scheme.{u}}

/-- The geometric stalks of a pullback are `p`-primary if those of the sheaf are. -/
lemma Scheme.IsPrimaryTorsionSheaf.upperStar (ν : X ⟶ Y)
    {G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} {p : ℕ}
    (hG : Scheme.IsPrimaryTorsionSheaf Λ G p) :
    Scheme.IsPrimaryTorsionSheaf Λ ((ν)^*[ModuleCat.{u + 1} Λ].obj G) p := fun Ω _ _ s x ↦ by
  let e := (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) ν s).app G
  obtain ⟨n, hn⟩ := hG Ω (s ≫ ν) (e.hom x)
  refine ⟨n, ?_⟩
  refine (ModuleCat.mono_iff_injective e.hom).1 inferInstance ?_
  rw [map_nsmul, hn, map_zero]

/-- The geometric stalks of a pullback are torsion of orders invertible on `S` if those of the
sheaf are. -/
lemma Scheme.IsTorsionSheafOfInvertibleOrder.upperStar (S : Scheme.{u}) (ν : X ⟶ Y)
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfInvertibleOrder S G] :
    Scheme.IsTorsionSheafOfInvertibleOrder S ((ν)^*[ModuleCat.{u + 1} Λ].obj G) where
  exists_isUnit_nsmul_eq_zero Ω _ _ s x := by
    let e := (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) ν s).app G
    obtain ⟨n, hn, hu, hx⟩ := Scheme.IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero
      (S := S) Ω (s ≫ ν) (e.hom x)
    refine ⟨n, hn, hu, ?_⟩
    refine (ModuleCat.mono_iff_injective e.hom).1 inferInstance ?_
    rw [map_nsmul, hx, map_zero]

set_option synthInstance.maxHeartbeats 400000 in
/-- **The counit of a finite direct image is an epimorphism.** For a finite morphism `ν`, the
counit `ν^* ν_* F ⟶ F` is an epimorphism: at a geometric point `s` of `X` with algebraically
closed residue field it is the restriction `(ν_* F)_{s ≫ ν} ⟶ F_s`, a component of the
isomorphism of the stalk formula. -/
lemma Etale.epi_counit_app_of_isFinite (ν : X ⟶ Y) [IsFinite ν]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Epi ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) ν).counit.app F) := by
  refine (Scheme.jointlyReflectIsomorphisms_ulift_pointSmallEtale X
    (ModuleCat.{u + 1} Λ)).epi_of_epi_map _ ?_
  rintro ⟨-, ⟨s⟩⟩
  set t := X.algClosurePoint s
  have h₁ : Etale.stalkRestrict (ModuleCat.{u + 1} Λ) ν (t ≫ ν) ⟨t, rfl⟩ F =
      (Etale.stalkIsoPi (ModuleCat.{u + 1} Λ) ν (t ≫ ν) F).hom ≫ Pi.π _ ⟨t, rfl⟩ := by
    simp
  have : Epi (Etale.stalkRestrict (ModuleCat.{u + 1} Λ) ν (t ≫ ν) ⟨t, rfl⟩ F) := by
    rw [h₁]
    infer_instance
  rw [Etale.stalkRestrict_eq_counit] at this
  have : Epi ((pointSmallEtale t).sheafFiber.map
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) ν).counit.app F)) :=
    epi_of_epi ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) ν t).inv.app _) _
  change Epi (((pointSmallEtale t).ulift.{u + 1}).sheafFiber.map _)
  rw [← NatIso.naturality_2 ((pointSmallEtale t).uliftSheafFiberIso (ModuleCat.{u + 1} Λ))]
  exact epi_comp _ _

/-- **Constructibility descends along a finite direct image.** If `ν` is finite, `X` is
noetherian and `ν_* F` is constructible, then so is `F`: it is a quotient of the constructible
sheaf `ν^* ν_* F` by the counit, hence the cokernel of the inclusion of the (constructible)
kernel of the counit. (blueprint: `lem-weil-pbc-finite-pushforward-constructible-descent`) -/
theorem Scheme.IsConstructibleSheaf.of_lowerStar [IsNoetherianRing Λ]
    [TopologicalSpace.NoetherianSpace X] (ν : X ⟶ Y) [IsFinite ν]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf ((ν)_*[ModuleCat.{u + 1} Λ].obj F)] :
    Scheme.IsConstructibleSheaf F := by
  set ε := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) ν).counit.app F
  have := Etale.epi_counit_app_of_isFinite ν F
  have : Scheme.IsConstructibleSheaf (((ν)_*[ModuleCat.{u + 1} Λ] ⋙
      (ν)^*[ModuleCat.{u + 1} Λ]).obj F) :=
    Scheme.IsConstructibleSheaf.upperStar (A := ModuleCat.{u + 1} Λ) ν
      ((ν)_*[ModuleCat.{u + 1} Λ].obj F)
  have : Scheme.IsConstructibleSheaf (kernel ε) :=
    Scheme.IsConstructibleSheaf.of_mono (kernel.ι ε)
  have : Scheme.IsConstructibleSheaf (cokernel (kernel.ι ε)) :=
    Scheme.IsConstructibleSheaf.cokernel _
  exact Scheme.IsConstructibleSheaf.of_iso (F := cokernel (kernel.ι ε)) (F' := F)
    ((colimit.isColimit _).coconePointUniqueUpToIso
      (Abelian.epiIsCokernelOfKernel _ (limit.isLimit _)))

end Helpers

/-- **The eight curve assertions pass to finite direct images.** Let `k` be algebraically
closed, `f : X ⟶ Spec k` and `g : Y ⟶ Spec k` curves and `ν : X ⟶ Y` a finite `k`-morphism.
If the eight assertions `C(X, F)` hold for an étale sheaf `F` of `Λ`-modules on `X`, then the
eight assertions `C(Y, ν_* F)` hold.
(blueprint: `lem-weil-pbc-curve-assertions-finite-pushforward`) -/
@[stacks 0A5D]
theorem IsCurve.Assertions.lowerStar_of_isFinite [IsNoetherianRing Λ] {k : Type u} [Field k]
    [IsAlgClosed k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f]
    (g : Y ⟶ Spec (.of k)) [IsCurve g] (ν : X ⟶ Y) [IsFinite ν] (hν : ν ≫ g = f)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (h : IsCurve.Assertions Λ f F) :
    IsCurve.Assertions Λ g ((ν)_*[ModuleCat.{u + 1} Λ].obj F) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  set Φ := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  set G := Φ.obj F
  -- the edge maps `Hᵠ(Y, ν_* F) ⟶ Hᵠ(X, F)` are bijective
  have he (q : ℕ) := bijective_edgeMap_of_isFinite ν G q
  -- the coefficient hypotheses descend from `ν_* F` to `F`
  set ε := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) ν).counit.app F
  have := Etale.epi_counit_app_of_isFinite ν F
  have hprim {p : ℕ} (hp : Scheme.IsPrimaryTorsionSheaf Λ ((ν)_*[ModuleCat.{u + 1} Λ].obj F) p) :
      Scheme.IsPrimaryTorsionSheaf Λ F p :=
    Scheme.IsPrimaryTorsionSheaf.of_epi ε (Scheme.IsPrimaryTorsionSheaf.upperStar ν hp)
  have hinv (_ : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k))
      ((ν)_*[ModuleCat.{u + 1} Λ].obj F)) :
      Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F :=
    have : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k))
        (((ν)_*[ModuleCat.{u + 1} Λ] ⋙ (ν)^*[ModuleCat.{u + 1} Λ]).obj F) :=
      Scheme.IsTorsionSheafOfInvertibleOrder.upperStar (Spec (.of k)) ν
        ((ν)_*[ModuleCat.{u + 1} Λ].obj F)
    Scheme.IsTorsionSheafOfInvertibleOrder.of_epi _ ε
  -- compatibility of the edge maps with pullback along a cartesian square
  have hsq {Y' : Scheme.{u}} (a : Y' ⟶ Y) (q : ℕ) :
      ∃ ψ : Sheaf.H ((a)^*[AddCommGrpCat.{u + 1}].obj ((ν)_*[AddCommGrpCat.{u + 1}].obj G)) q →
          Sheaf.H ((pullback.fst ν a)^*[AddCommGrpCat.{u + 1}].obj G) q,
        Function.Bijective ψ ∧ cohomologyMap (pullback.fst ν a) G q ∘
          (fun x ↦ Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} ν).counit.app
            G) q (cohomologyMap ν _ q x)) =
          ψ ∘ cohomologyMap a ((ν)_*[AddCommGrpCat.{u + 1}].obj G) q := by
    have sq := IsPullback.of_hasPullback ν a
    have := (Etale.isIso_baseChangeMap_of_isFinite AddCommGrpCat.{u + 1} sq)
    have hb := bijective_edgeMap_baseChange sq G q inferInstance
    exact ⟨_, hb.2, congrArg DFunLike.coe (cohomology_edgeMap_baseChange sq G q)⟩
  have hbij {Y' : Scheme.{u}} (a : Y' ⟶ Y) (q : ℕ)
      (hX : Function.Bijective (cohomologyMap (pullback.fst ν a) G q)) :
      Function.Bijective (cohomologyMap a ((ν)_*[AddCommGrpCat.{u + 1}].obj G) q) := by
    obtain ⟨ψ, hψ, heq⟩ := hsq a q
    have hl := hX.comp (he q)
    rw [heq] at hl
    exact (hψ.of_comp_iff' _).1 hl
  have hpaste {k' : Type u} [Field k'] {Y' : Scheme.{u}} {ι : Spec (.of k') ⟶ Spec (.of k)}
      {f' : Y' ⟶ Spec (.of k')} {ι' : Y' ⟶ Y} (hι : IsPullback ι' f' g ι) :
      IsPullback (pullback.fst ν ι') (pullback.snd ν ι' ≫ f') f ι := by
    rw [← hν]
    exact (IsPullback.of_hasPullback ν ι').paste_vert hι
  refine ⟨fun q hq ↦ ?_, fun q hq ↦ ?_, fun p _ _ hp q hq ↦ ?_, fun q ↦ ?_, fun q ↦ ?_,
    fun k' _ _ Y' ι f' ι' hι q ↦ ?_, fun k' _ _ Y' ι f' ι' hι q ↦ ?_, fun {W} a _ ↦ ?_⟩
  · have : Subsingleton (Sheaf.H ((𝟭 _).obj G) q) := h.subsingleton_of_two_lt q hq
    exact (he q).1.subsingleton
  · have : IsAffine X := isAffine_of_isAffineHom ν
    have : Subsingleton (Sheaf.H ((𝟭 _).obj G) q) := h.subsingleton_of_one_lt_of_isAffine q hq
    exact (he q).1.subsingleton
  · have : Subsingleton (Sheaf.H ((𝟭 _).obj G) q) :=
      h.subsingleton_of_one_lt_of_isPrimaryTorsionSheaf p (hprim hp) q hq
    exact (he q).1.subsingleton
  · rename_i hc hi
    have := Scheme.IsConstructibleSheaf.of_lowerStar ν F
    have := hinv hi
    have : Finite (Sheaf.H ((𝟭 _).obj G) q) := h.finite_of_isTorsionSheafOfInvertibleOrder q
    exact Finite.of_injective _ (he q).1
  · have : IsProper f := hν ▸ inferInstance
    have := Scheme.IsConstructibleSheaf.of_lowerStar ν F
    have : Finite (Sheaf.H ((𝟭 _).obj G) q) := h.finite_of_isProper q
    exact Finite.of_injective _ (he q).1
  · rename_i hi _ _
    have := hinv hi
    exact hbij ι' q (h.bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder k'
      (hpaste hι) q)
  · have : IsProper f := hν ▸ inferInstance
    exact hbij ι' q (h.bijective_cohomologyMap_of_isProper k' (hpaste hι) q)
  · obtain ⟨ψ, hψ, heq⟩ := hsq a 2
    have hl := (h.surjective_cohomologyMap_of_isOpenImmersion (pullback.fst ν a)).comp (he 2).2
    rw [heq] at hl
    intro y
    obtain ⟨x, hx⟩ := hl (ψ y)
    exact ⟨x, hψ.1 hx⟩

end AlgebraicGeometry
