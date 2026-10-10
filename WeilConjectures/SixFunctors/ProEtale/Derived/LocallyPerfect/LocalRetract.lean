/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.LocallyPerfect.Retract

/-!
# Dualizable complexes are locally retracts of finite subcomplexes

Let `K ∈ D(X_proét, Λ)` be dualizable, represented by a complex `M`. There is a covering sieve
of the terminal object of `X_proét` such that for each of its members `V`, with structure
morphism `g : V ⟶ X`, the complex `g^* M` has finitely many global sections `xₖ` such that
`Q(g^* M)` is a retract of `Q(L')` for every subcomplex `L' ⊆ g^* M` containing the `xₖ`
(`AlgebraicGeometry.ProEtale.exists_sieve_retract`). This is the first step of Stacks,
Tag 0FPV, on the pro-étale site.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open _root_.AlgebraicGeometry.Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

open _root_.DerivedCategory in
/-- **Dualizable complexes are locally retracts of finite subcomplexes** (Stacks, Tag 0FPV,
first step). Let `K ∈ D(X_proét)` be dualizable and `K ≅ Q(M)`. There is a covering sieve of the
terminal object of `X_proét` such that for each member `V`, with structure morphism `g`, there
are finitely many global sections `xₖ` of `g^* M` such that `Q(g^* M)` is a retract of `Q(L')`
for every subcomplex `L' ⊆ g^* M` containing the `xₖ`. -/
theorem exists_sieve_retract
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : IsDualizable K)
    (M : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ)
    (e : K ≅ Q.obj M) :
    ∃ R ∈ Scheme.ProEt.topology X (terminalProEt X), ∀ ⦃V : X.ProEt⦄
      (f : V ⟶ terminalProEt X), R f → ∃ (m : ℕ) (p : Fin m → ℤ)
        (x : ∀ k, ((((V.hom)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj M).X
          (p k)).obj.obj (op (terminalProEt V.left))),
        ∀ (L' : CochainComplex (Sheaf (Scheme.ProEt.topology V.left) (ModuleCat.{u + 1} Λ)) ℤ)
          (ι : L' ⟶ ((V.hom)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj M),
          (∀ n, Mono (ι.f n)) → (∀ k, ∃ x' : (L'.X (p k)).obj.obj (op (terminalProEt V.left)),
            (ι.f (p k)).hom.app _ x' = x k) →
          ∃ r : Q.obj (((V.hom)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj M) ⟶
            Q.obj L', r ≫ Q.map ι = 𝟙 _ := by
  obtain ⟨_⟩ := hK
  -- a K-flat resolution of the dual by flat sheaves, which stays K-flat after pullback
  let Λr := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))).reduced
  have hι : (ObjectProperty.flat.ι : _ ⥤ Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} Λ)).essImage ≤ ObjectProperty.flat := ObjectProperty.flat.essImage_ι_le
  let LD := Q.objPreimage Kᘁ
  let F := Λr.resolutionFunctor.obj LD
  have hFflat (n : ℤ) : ObjectProperty.flat (F.X n) := by
    have := CochainComplex.closedUnderColimitsOfShape_flat
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ
    let c := Λr.colimitOfShapeResolutionFunctorObj LD
    exact ObjectProperty.prop_of_isColimit _
      (isColimitOfPreserves (HomologicalComplex.eval _ (.up ℤ) n) c.isColimit)
      (fun i ↦ hι _ ((c.prop_diag_obj i).1 n))
  have : IsIso (Q.map (Λr.resolutionNatTrans.app LD)) :=
    (isIso_Q_map_iff_quasiIso (C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
      _).2 inferInstance
  let eD : Kᘁ ≅ Q.obj F := (Q.objObjPreimageIso Kᘁ).symm ≪≫
    (asIso (Q.map (Λr.resolutionNatTrans.app LD))).symm
  obtain ⟨I, s, hs, φ, hu, R, hR, hloc⟩ := exists_sieve_sum_tensorSectionMap_of_Q_map M F
    (coevaluationQ K Kᘁ M F e eD)
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨m, p, x, y, w, hd, hsw⟩ := hloc f hf
  obtain rfl : f = (Scheme.ProEt.isTerminalMkId X).from V :=
    (Scheme.ProEt.isTerminalMkId X).hom_ext _ _
  refine ⟨m, p, fun k ↦ (sectionTransport V _).hom (x k), fun L' ι hι' hx ↦ ?_⟩
  choose x' hx' using hx
  have := hι'
  exact exists_retract_upperStar V K Kᘁ M F e eD hFflat
    ((V.hom)^*[ModuleCat.{u + 1} Λ].kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λr hι LD)
    I s φ hu p x y w hd hsw ι x' hx'

end AlgebraicGeometry.ProEtale
