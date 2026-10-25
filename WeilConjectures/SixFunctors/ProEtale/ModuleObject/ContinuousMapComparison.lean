/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafRing
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!
# The pullback of a condensed ring of continuous maps

Let `T` be a topological ring and `X` a scheme. The condensed ring `T̲ = C(-, T)` pulls back to the
ring object `T_X = p_X^* T̲` of abelian sheaves on `X_proét`, and there is also the sheaf of rings
`U ↦ C(U, T)` on `X_proét` (`AlgebraicGeometry.ProEtale.continuousMapRingSheaf`). This file
constructs the comparison morphism of ring objects
```
ψ_X : p_X^* T̲ ⟶ C(-, T)_X
```
(`AlgebraicGeometry.ProEtale.continuousMapComparison`), adjoint to the morphism of condensed rings
`T̲ ⟶ p_{X*} C(-, T)_X` which sends a continuous map `f : S → T` to `f ∘ pr_S` on the test object
`X[S] = Spec LC(S, ℤ) ×_{Spec ℤ} X`, where `pr_S : X[S] → Spec LC(S, ℤ) → S` is the projection
(`AlgebraicGeometry.ProEtale.profiniteTestObjectProj`). The underlying space of `Spec LC(S, ℤ)` is
`S × Spec ℤ` (`LocallyConstant.homeomorphPrimeSpectrum`), which gives the continuous map
`Spec LC(S, ℤ) → S` (`AlgebraicGeometry.ProEtale.specLocallyConstantToProfinite`).

The comparison is a morphism of ring objects
(`AlgebraicGeometry.ProEtale.isMonHom_continuousMapComparison`), natural in `T`
(`AlgebraicGeometry.ProEtale.continuousMapComparison_naturality`) and in `X`: for `g : X' ⟶ X`,
`g^* ψ_X` followed by the comparison `g^* C(-, T)_X ⟶ C(-, T)_{X'}` adjoint to the precomposition
with the projections `V ×_X X' → V` (`AlgebraicGeometry.ProEtale.continuousMapPullbackHom`) is
`α_g` followed by `ψ_{X'}`
(`AlgebraicGeometry.ProEtale.upperStar_map_continuousMapComparison_comp_continuousMapPullbackHom`).
The latter is a mate computation, reduced to an identity of projections of test objects
`X[S] ×_X X' ≅ X'[S]`.

## Sorried input

- `AlgebraicGeometry.ProEtale.isIso_continuousMapComparison`: by Bhatt–Scholze, *The pro-étale
  topology for schemes*, Lemma 4.2.12, `ψ_X` is an isomorphism for `T` locally compact, Hausdorff
  and totally disconnected: for a profinite set `S` the condensed set `S̲` pulls back to the
  representable sheaf of `X[S]`, whose sections over `U` are the continuous maps `U → S`, and `T̲`
  is the filtered colimit of the `K̲` over the compact subsets `K ⊆ T`, with which sections over
  quasi-compact quasi-separated objects commute.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

/-! ### The projection `Spec LC(S, ℤ) → S` -/

/-- The continuous map `Spec LC(S, ℤ) → S`: the underlying space of `Spec LC(S, ℤ)` is
`S × Spec ℤ` (`LocallyConstant.homeomorphPrimeSpectrum`), followed by the first projection. -/
noncomputable def specLocallyConstantToProfinite (S : Profinite.{u}) :
    C(profiniteToScheme.obj S, S) :=
  ⟨fun x ↦ ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm x).1,
    continuous_fst.comp (LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm.continuous⟩

lemma specLocallyConstantToProfinite_toPrimeSpectrum (S : Profinite.{u}) (s : S)
    (p : PrimeSpectrum ℤ) :
    specLocallyConstantToProfinite S (LocallyConstant.toPrimeSpectrum (s, p)) = s := by
  change ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm
    (LocallyConstant.homeomorphPrimeSpectrum (s, p))).1 = s
  rw [Homeomorph.symm_apply_apply]

/-- The projections `Spec LC(S, ℤ) → S` are natural in the profinite set `S`. -/
lemma specLocallyConstantToProfinite_naturality {S S' : Profinite.{u}} (f : S ⟶ S')
    (x : profiniteToScheme.obj S) :
    specLocallyConstantToProfinite S' ((profiniteToScheme.map f).base x) =
      f (specLocallyConstantToProfinite S x) := by
  obtain ⟨⟨s, p⟩, rfl⟩ := LocallyConstant.toPrimeSpectrum_surjective (T := S) (R := ℤ) x
  rw [specLocallyConstantToProfinite_toPrimeSpectrum]
  have : (profiniteToScheme.map f).base (LocallyConstant.toPrimeSpectrum (s, p)) =
      LocallyConstant.toPrimeSpectrum (f s, p) := by
    change PrimeSpectrum.comap (LocallyConstant.comapRingHom f.hom.hom)
      (LocallyConstant.toPrimeSpectrum (s, p)) = _
    ext g
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, LocallyConstant.mem_toPrimeSpectrum_asIdeal,
      LocallyConstant.mem_toPrimeSpectrum_asIdeal]
    rfl
  rw [this, specLocallyConstantToProfinite_toPrimeSpectrum]

/-! ### The projection `X[S] → S` -/

variable (X : Scheme.{u})

/-- The test object `X[S] = Spec LC(S, ℤ) ×_{Spec ℤ} X` of the pro-étale site of `X`. -/
noncomputable abbrev profiniteTestObject (S : Profinite.{u}) : X.ProEt :=
  (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)).obj (profiniteToProEt.obj S)

/-- The projection `X[S] → Spec LC(S, ℤ) → S` of the test object to the profinite set `S`. -/
noncomputable def profiniteTestObjectProj (S : Profinite.{u}) :
    C((profiniteTestObject X S).left, S) :=
  (specLocallyConstantToProfinite S).comp
    (pullback.fst (profiniteToProEt.obj S).hom (toSpecZ X)).base.hom

/-- The projections `X[S] → S` are natural in the profinite set `S`. -/
lemma profiniteTestObjectProj_naturality {S S' : Profinite.{u}} (f : S ⟶ S')
    (x : (profiniteTestObject X S).left) :
    profiniteTestObjectProj X S'
        (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)).map
          (profiniteToProEt.map f)).left.base x) =
      f (profiniteTestObjectProj X S x) := by
  have h : ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)).map
      (profiniteToProEt.map f)).left ≫ pullback.fst (profiniteToProEt.obj S').hom (toSpecZ X) =
      pullback.fst (profiniteToProEt.obj S).hom (toSpecZ X) ≫ profiniteToScheme.map f := by
    rw [MorphismProperty.Over.pullback_map_left, pullback.lift_fst]
    rfl
  have h' := congrArg (fun g ↦ g.base x) h
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h'
  rw [profiniteTestObjectProj, profiniteTestObjectProj, ContinuousMap.comp_apply,
    ContinuousMap.comp_apply, ← specLocallyConstantToProfinite_naturality]
  exact congrArg _ h'

/-! ### The comparison morphism -/

variable (T : Type) [TopologicalSpace T] [Ring T] [IsTopologicalRing T]

/-- The sheaf of rings `S ↦ C(X[S], T)` on profinite sets: the pushforward of the sheaf of rings
`U ↦ C(U, T)` on `X_proét` along `π_X : X ⟶ Spec ℤ` and then along `S ↦ Spec LC(S, ℤ)`. -/
noncomputable abbrev continuousMapRingSheafLowerStar :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  (profiniteToProEt.sheafPushforwardContinuous RingCat.{u + 1} (coherentTopology Profinite.{u})
    (ProEt.topology specZ)).obj
    (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)).sheafPushforwardContinuous
      RingCat.{u + 1} (ProEt.topology specZ) (ProEt.topology X)).obj
      (continuousMapRingSheaf X T))

/-- The morphism of condensed rings `T̲ ⟶ p_{X*} C(-, T)_X`, sending a continuous map `f : S → T`
to `f ∘ pr_S : X[S] → T`. -/
noncomputable def continuousMapRingSheafToLowerStar :
    Profinite.continuousMapRingSheaf.{u} T ⟶ continuousMapRingSheafLowerStar X T where
  hom :=
    { app S := RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        (((ContinuousMap.compRightAlgHom ℤ T (profiniteTestObjectProj X S.unop)).toRingHom).comp
          ULift.ringEquiv.toRingHom))
      naturality S S' f := by
        ext g
        refine ULift.ext _ _ (ContinuousMap.ext fun x ↦ ?_)
        change g.down (f.unop (profiniteTestObjectProj X S'.unop x)) =
          g.down (profiniteTestObjectProj X S.unop
            (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)).map
              (profiniteToProEt.map f.unop)).left.base x))
        rw [profiniteTestObjectProj_naturality] }

lemma continuousMapRingSheafToLowerStar_hom_app_apply (S : Profinite.{u}ᵒᵖ)
    (g : ULift.{u + 1} C(S.unop, T)) :
    (continuousMapRingSheafToLowerStar X T).hom.app S g =
      ULift.up (g.down.comp (profiniteTestObjectProj X S.unop)) :=
  rfl

/-- The adjunction `p_X^* ⊣ p_{X*}`, the composite of `p^* ⊣ p_*` and `π_X^* ⊣ π_{X*}`. -/
noncomputable abbrev upperStarFromPointAdjunction :
    upperStarFromPoint X ⊣ (toSpecZ X)_*[Ab.{u + 1}] ⋙ pointLowerStar :=
  pointUpperStarLowerStarAdjunction.comp (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))

/-- The morphism of ring objects `T̲ ⟶ p_{X*} C(-, T)_X` underlying
`continuousMapRingSheafToLowerStar`. -/
noncomputable abbrev continuousMapToLowerStar :
    Profinite.continuousMapRingObj.{u} T ⟶
      ((toSpecZ X)_*[Ab.{u + 1}] ⋙ pointLowerStar).obj
        ((sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (continuousMapRingSheaf X T)) :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (continuousMapRingSheafToLowerStar X T)

/-- **The comparison `ψ_X : p_X^* T̲ ⟶ C(-, T)_X`**, adjoint to the morphism of condensed rings
`T̲ ⟶ p_{X*} C(-, T)_X` given by precomposition with the projections `X[S] → S`. -/
noncomputable def continuousMapComparison :
    condensedRingObj (Profinite.continuousMapRingObj.{u} T) X ⟶
      (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf X T) :=
  ((upperStarFromPointAdjunction X).homEquiv _ _).symm (continuousMapToLowerStar X T)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) {T : Type} [TopologicalSpace T] [Ring T] [IsTopologicalRing T]

variable (T) in
/-- The comparison `ψ_X : p_X^* T̲ ⟶ C(-, T)_X` is a morphism of ring objects: it is adjoint, for
the monoidal adjunction `p_X^* ⊣ p_{X*}`, to the morphism of abelian sheaves underlying a morphism
of sheaves of rings. -/
instance isMonHom_continuousMapComparison : IsMonHom (continuousMapComparison X T) := by
  have : Functor.IsContinuous (C := specZ.{u}.ProEt) (D := X.ProEt)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)) (ProEt.topology specZ)
      (ProEt.topology X) :=
    ProEt.isContinuous_overPullback _
  have h₁ := Sheaf.monObjObj_sheafPushforwardContinuous_eq (J := ProEt.topology specZ.{u})
    (K := ProEt.topology X)
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)) (continuousMapRingSheaf X T)
  have h₂ := Sheaf.monObjObj_sheafPushforwardContinuous_eq
    (J := coherentTopology Profinite.{u}) (K := ProEt.topology specZ.{u}) profiniteToProEt
    (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)).sheafPushforwardContinuous
      RingCat.{u + 1} (ProEt.topology specZ) (ProEt.topology X)).obj (continuousMapRingSheaf X T))
  have h₃ := Functor.monObjObj_comp ((toSpecZ X)_*[Ab.{u + 1}]) pointLowerStar
    ((sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (continuousMapRingSheaf X T))
  have : IsMonHom (continuousMapToLowerStar X T) := by
    refine IsMonHom.of_eq _ rfl (h₂.symm.trans ?_) (hf := Sheaf.isMonHom_sheafCompose_map
      (J := coherentTopology Profinite.{u}) (continuousMapRingSheafToLowerStar X T))
    rw [h₃]
    exact congrArg (@Functor.monObjObj _ _ _ _ _ _ pointLowerStar _ _) h₁.symm
  exact (upperStarFromPointAdjunction X).isMonHom_homEquiv_symm _

/-- **Naturality of `ψ_X` in `T`**: for a continuous ring homomorphism `φ : T →+* T'`, the
comparisons commute with the morphisms `p_X^* T̲ ⟶ p_X^* T̲'` and `C(-, T)_X ⟶ C(-, T')_X` induced
by `φ`. -/
lemma continuousMapComparison_naturality {T' : Type} [TopologicalSpace T'] [Ring T']
    [IsTopologicalRing T'] (φ : T →+* T') (hφ : Continuous φ) :
    (upperStarFromPoint X).map
        ((sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (Profinite.continuousMapRingSheafMap φ hφ)) ≫ continuousMapComparison X T' =
      continuousMapComparison X T ≫
        (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (continuousMapRingSheafMap X φ hφ) := by
  rw [continuousMapComparison, continuousMapComparison, ← Adjunction.homEquiv_naturality_left_symm,
    ← Adjunction.homEquiv_naturality_right_symm]
  congr 1

end AlgebraicGeometry.ProEtale

/-! ### Naturality of the comparison in the scheme -/

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X X' : Scheme.{u}} (g : X' ⟶ X)

/-- The components of the inverse of the composition isomorphism `f_* ⋙ g_* ≅ (f ≫ g)_*` are the
restriction maps along the base change isomorphisms `MorphismProperty.Over.pullbackComp`. -/
lemma coefficient_lowerStarComp_inv_app_hom_app {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (G : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (V : R.ProEt) :
    ((lowerStarComp Ab.{u + 1} h₁ h₂).inv.app G).hom.app (op V) =
      G.obj.map ((MorphismProperty.Over.pullbackComp h₁ h₂).inv.app V).op := by
  simp [lowerStarComp]

/-- Base change along `g` of a morphism `f : V' ⟶ V` of the pro-étale site of `X` is compatible
with the first projections. -/
@[reassoc]
lemma overPullback_map_left_fst {V V' : X.ProEt} (f : V' ⟶ V) :
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map f).left ≫ pullback.fst V.hom g =
      pullback.fst V'.hom g ≫ f.left := by
  rw [MorphismProperty.Over.pullback_map_left, pullback.lift_fst]

/-- **A criterion for the compatibility of morphisms out of `p^* Λ` with pullback.** Let
`ψ : π_X^* F ⟶ C` and `ψ' : π_{X'}^* F ⟶ C'` for a sheaf `F` on `Spec ℤ`, and `b : C ⟶ g_* C'`.
If the adjoints `F ⟶ π_{X*} C ⟶ π_{X*} g_* C'` and `F ⟶ π_{X'*} C' ≅ π_{X*} g_* C'` agree, then
`g^* ψ` followed by the adjoint `g^* C ⟶ C'` of `b` is the composition isomorphism
`g^* π_X^* F ≅ π_{X'}^* F` followed by `ψ'`. -/
lemma upperStar_map_comp_homEquiv_symm_eq (F : Sheaf (ProEt.topology specZ.{u}) Ab.{u + 1})
    {C : Sheaf (ProEt.topology X) Ab.{u + 1}} {C' : Sheaf (ProEt.topology X') Ab.{u + 1}}
    (b : C ⟶ (g)_*[Ab.{u + 1}].obj C') (ψ : (toSpecZ X)^*[Ab.{u + 1}].obj F ⟶ C)
    (ψ' : (toSpecZ X')^*[Ab.{u + 1}].obj F ⟶ C')
    (h : (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X)).homEquiv _ _ ψ ≫
        (toSpecZ X)_*[Ab.{u + 1}].map b =
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X')).homEquiv _ _ ψ' ≫
        (eqToHom (congrArg (lowerStar Ab.{u + 1}) (comp_toSpecZ g).symm)).app C' ≫
          (lowerStarComp Ab.{u + 1} g (toSpecZ X)).inv.app C') :
    (g)^*[Ab.{u + 1}].map ψ ≫ ((upperStarLowerStarAdjunction Ab.{u + 1} g).homEquiv _ _).symm b =
      ((upperStarComp Ab.{u + 1} g (toSpecZ X)).inv.app F ≫
        (eqToHom (congrArg (upperStar Ab.{u + 1}) (comp_toSpecZ g))).app F) ≫ ψ' := by
  apply ((upperStarLowerStarAdjunction Ab.{u + 1} g).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit]
  apply ((upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, h, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have coh := unit_comp_lowerStar_map_unit_comp_upperStarComp Ab.{u + 1} g (toSpecZ X')
    (toSpecZ X) (comp_toSpecZ g) F
  rw [Functor.map_comp ((toSpecZ X)_*[Ab.{u + 1}]) _ ((g)_*[Ab.{u + 1}].map ψ'), reassoc_of% coh]
  simp only [Category.assoc]
  congr 1
  have n₁ := (lowerStarComp Ab.{u + 1} g (toSpecZ X)).inv.naturality ψ'
  have n₂ := (eqToHom (congrArg (lowerStar Ab.{u + 1}) (comp_toSpecZ g).symm)).naturality ψ'
  simp only [Functor.comp_map] at n₁
  rw [← n₁, ← reassoc_of% n₂]

variable (T : Type) [TopologicalSpace T] [Ring T] [IsTopologicalRing T]

/-- The morphism of sheaves of rings `C(-, T)_X ⟶ g_* C(-, T)_{X'}`: precomposition with the
projections `V ×_X X' → V`. -/
noncomputable def continuousMapRingSheafToPushforward :
    continuousMapRingSheaf X T ⟶
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).sheafPushforwardContinuous
        RingCat.{u + 1} (ProEt.topology X) (ProEt.topology X')).obj
        (continuousMapRingSheaf X' T) where
  hom :=
    { app V := RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        (((ContinuousMap.compRightAlgHom ℤ T (pullback.fst V.unop.hom g).base.hom).toRingHom).comp
          ULift.ringEquiv.toRingHom))
      naturality V V' f := by
        ext a
        refine ULift.ext _ _ (ContinuousMap.ext fun x ↦ ?_)
        have h := congrArg (fun k ↦ k.base x) (overPullback_map_left_fst g f.unop)
        simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
        change a.down (f.unop.left.base ((pullback.fst V'.unop.hom g).base x)) =
          a.down ((pullback.fst V.unop.hom g).base
            (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map f.unop).left.base x))
        exact congrArg a.down h.symm }

/-- The morphism of ring objects `C(-, T)_X ⟶ g_* C(-, T)_{X'}`: precomposition with the
projections `V ×_X X' → V`. -/
noncomputable abbrev continuousMapToPushforward :
    (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf X T) ⟶
      (g)_*[Ab.{u + 1}].obj ((sheafCompose (ProEt.topology X')
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X' T)) :=
  (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (continuousMapRingSheafToPushforward g T)

/-- The comparison `g^* C(-, T)_X ⟶ C(-, T)_{X'}`, adjoint to the precomposition with the
projections `V ×_X X' → V`. -/
noncomputable def continuousMapPullbackHom :
    (g)^*[Ab.{u + 1}].obj ((sheafCompose (ProEt.topology X)
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X T)) ⟶
      (sheafCompose (ProEt.topology X') (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf X' T) :=
  ((upperStarLowerStarAdjunction Ab.{u + 1} g).homEquiv _ _).symm (continuousMapToPushforward g T)

/-- The sections of `p_* G` over a profinite set `S` are those of `G` over `Spec LC(S, ℤ)`, also
on morphisms. -/
lemma pointLowerStar_map_hom_app_eq {G G' : Sheaf (ProEt.topology specZ.{u}) Ab.{u + 1}}
    (φ : G ⟶ G') (S : Profinite.{u}ᵒᵖ) :
    (pointLowerStar.map φ).hom.app S = φ.hom.app (op (profiniteToProEt.obj S.unop)) :=
  rfl

/-- `ψ_X` corresponds, under the two adjunctions `π_X^* ⊣ π_{X*}` and `p^* ⊣ p_*`, to the
precomposition with the projections `X[S] → S`. -/
lemma homEquiv_homEquiv_continuousMapComparison (X : Scheme.{u}) :
    pointUpperStarLowerStarAdjunction.homEquiv _ _
        ((upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X)).homEquiv _ _
          (continuousMapComparison X T)) =
      continuousMapToLowerStar X T := by
  rw [continuousMapComparison, Adjunction.comp_homEquiv]
  erw [Equiv.symm_trans_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The precompositions with the projections `X[S] → S` and `X'[S] → S` are compatible with the
projections `X[S] ×_X X' → X[S]` and the identification `X[S] ×_X X' ≅ X'[S]`. -/
lemma continuousMapToLowerStar_comp_map_continuousMapToPushforward :
    continuousMapToLowerStar X T ≫ pointLowerStar.map ((toSpecZ X)_*[Ab.{u + 1}].map
      (continuousMapToPushforward g T)) =
    continuousMapToLowerStar X' T ≫ pointLowerStar.map
      ((eqToHom (congrArg (lowerStar Ab.{u + 1}) (comp_toSpecZ g).symm)).app _ ≫
        (lowerStarComp Ab.{u + 1} g (toSpecZ X)).inv.app _) := by
  ext S : 3
  have h₁ := eqToHom_lowerStar_app_hom_app Ab.{u + 1} (comp_toSpecZ g).symm
    (congrArg (lowerStar Ab.{u + 1}) (comp_toSpecZ g).symm)
    ((sheafCompose (ProEt.topology X') (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (continuousMapRingSheaf X' T)) (profiniteToProEt.obj S.unop)
  have h₂ := coefficient_lowerStarComp_inv_app_hom_app g (toSpecZ X)
    ((sheafCompose (ProEt.topology X') (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (continuousMapRingSheaf X' T)) (profiniteToProEt.obj S.unop)
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, pointLowerStar_map_hom_app_eq,
    pointLowerStar_map_hom_app_eq, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, h₁,
    h₂, ← Functor.map_comp, ← op_comp]
  ext f
  refine ULift.ext _ _ (ContinuousMap.ext fun x ↦ ?_)
  change f.down (profiniteTestObjectProj X S.unop
      ((pullback.fst (profiniteTestObject X S.unop).hom g).base x)) =
    f.down (profiniteTestObjectProj X' S.unop
      (((MorphismProperty.Over.pullbackComp g (toSpecZ X)).inv.app (profiniteToProEt.obj S.unop) ≫
        (MorphismProperty.Over.pullbackCongr (comp_toSpecZ g)).hom.app
          (profiniteToProEt.obj S.unop)).left.base x))
  have e : ((MorphismProperty.Over.pullbackComp g (toSpecZ X)).inv.app
      (profiniteToProEt.obj S.unop) ≫ (MorphismProperty.Over.pullbackCongr (comp_toSpecZ g)).hom.app
        (profiniteToProEt.obj S.unop)).left ≫
        pullback.fst (profiniteToProEt.obj S.unop).hom (toSpecZ X') =
      pullback.fst (profiniteTestObject X S.unop).hom g ≫
        pullback.fst (profiniteToProEt.obj S.unop).hom (toSpecZ X) := by
    rw [MorphismProperty.Comma.comp_left, Category.assoc,
      MorphismProperty.Over.pullbackCongr_hom_app_left_fst,
      ← MorphismProperty.Over.pullbackComp_left_fst_fst g (toSpecZ X), ← Category.assoc,
      ← MorphismProperty.Comma.comp_left, Iso.inv_hom_id_app]
    rfl
  have e' := congrArg (fun k ↦ k.base x) e
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at e'
  rw [profiniteTestObjectProj, profiniteTestObjectProj, ContinuousMap.comp_apply,
    ContinuousMap.comp_apply]
  exact congrArg (fun y ↦ f.down (specLocallyConstantToProfinite S.unop y)) e'.symm

/-- **Naturality of `ψ` in the scheme**: for `g : X' ⟶ X`, the square
```
g^* p_X^* T̲ --g^* ψ_X--> g^* C(-, T)_X
    | α_g                     |
p_{X'}^* T̲ ----ψ_{X'}----> C(-, T)_{X'}
```
commutes, where the right vertical map is adjoint to the precomposition with the projections
`V ×_X X' → V`. -/
lemma upperStar_map_continuousMapComparison_comp_continuousMapPullbackHom :
    (g)^*[Ab.{u + 1}].map (continuousMapComparison X T) ≫ continuousMapPullbackHom g T =
      condensedPullbackHom (Profinite.continuousMapRingObj.{u} T) g ≫
        continuousMapComparison X' T := by
  rw [condensedPullbackHom_eq]
  refine upperStar_map_comp_homEquiv_symm_eq g (pointUpperStar.obj _)
    (continuousMapToPushforward g T) (continuousMapComparison X T) (continuousMapComparison X' T)
    ?_
  apply (pointUpperStarLowerStarAdjunction.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
    homEquiv_homEquiv_continuousMapComparison, homEquiv_homEquiv_continuousMapComparison]
  exact continuousMapToLowerStar_comp_map_continuousMapToPushforward g T

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

/-- **The pullback of `C(-, T)` from the point is the sheaf `U ↦ C(U, T)`** (sorried input), for a
locally compact, Hausdorff, totally disconnected topological ring `T`: the comparison
`ψ_X : p_X^* T̲ ⟶ C(-, T)_X` is an isomorphism.

This is Bhatt–Scholze, *The pro-étale topology for schemes*, Lemma 4.2.12. Proof sketch: `T̲` is
the filtered colimit of the condensed sets `K̲ = C(-, K)` over the compact subsets `K ⊆ T`, a
continuous map from a profinite set having compact image. Each such `K` is profinite, so `K̲` is
representable, and `p_X^*` (whose underlying functor on sets is computed by a filtered colimit,
`S ↦ X[S]` being representably flat, followed by sheafification) sends it to the representable
sheaf of `X[K] = Spec LC(K, ℤ) ×_{Spec ℤ} X`, whose sections over `U` are the continuous maps
`U → K` (`LocallyConstant.liftPrimeSpectrum`). Sections over quasi-compact quasi-separated
objects commute with filtered colimits (`Scheme.ProEt.isColimitSectionsOfIsColimit`), so over
such `U` the sections of `p_X^* T̲` are `colim_K C(U, K) = C(U, T)`, `U` being quasi-compact. As
the quasi-compact quasi-separated objects form a basis of `X_proét`, `ψ_X` is an isomorphism. -/
theorem isIso_continuousMapComparison (X : Scheme.{u}) (T : Type) [TopologicalSpace T] [Ring T]
    [IsTopologicalRing T] [LocallyCompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] :
    IsIso (continuousMapComparison X T) :=
  sorry

end AlgebraicGeometry.ProEtale
