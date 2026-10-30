import WeilConjectures.TraceFormula.WeilIdentityStructure
import WeilConjectures.Scratch.T3

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

lemma weilHomologyComparison_hom_app_comp_map_boundedConstructibleUpperStarId
    (C : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (n : ℤ) :
    (weilHomologyComparison ℓ (Iso.refl X) n).hom.app C ≫
        ((boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ n).map
          ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app C) =
      (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.app
        (((boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ n).obj C) := by
  rw [weilHomologyComparison_hom_app, Functor.comp_map, ObjectProperty.ι_map,
    boundedConstructibleUpperStarId_hom_app_hom, Category.assoc, ← Functor.map_comp]
  have h := leftDerivedUpperStarHomologyIso_hom_app_id _ X.left n C.obj
  simp only [leftDerivedUpperStarHomologyIso, Functor.leftDerivedFunctorHomologyFunctorIso,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, Category.assoc] at h
  rw [Functor.map_comp]
  exact h

theorem WeilBoundedConstructible.homologyFunctor_obj_str_hom_of_id_comp
    (K : WeilBoundedConstructible ℓ (Iso.refl X).hom) (β : K.carrier ⟶ K.carrier)
    (hK : K.str.hom =
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app K.carrier ≫ β)
    (n : ℤ) :
    ((WeilBoundedConstructible.homologyFunctor ℓ (Iso.refl X) n).obj K).str.hom =
      (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.app
        (((boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ n).obj K.carrier) ≫
        ((boundedConstructible _).ι ⋙ DerivedCategory.homologyFunctor _ n).map β := by
  rw [WeilBoundedConstructible.homologyFunctor_obj_str, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, hK, Functor.map_comp, ← Category.assoc,
    weilHomologyComparison_hom_app_comp_map_boundedConstructibleUpperStarId]

/-- Weil sheaves for the identity whose structures are `(𝟙)^* ≅ 𝟭` followed by endomorphisms
intertwined by an isomorphism of the underlying module objects are isomorphic. -/
noncomputable def WeilSheaf.isoOfUpperStarIdComp {F G : WeilSheaf ℓ (Iso.refl X)}
    (βF : F.carrier ⟶ F.carrier) (βG : G.carrier ⟶ G.carrier)
    (hF : F.str.hom = (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.app F.carrier ≫ βF)
    (hG : G.str.hom = (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.app G.carrier ≫ βG)
    (e : F.carrier ≅ G.carrier) (he : βF ≫ e.hom = e.hom ≫ βG) : F ≅ G :=
  IsoAlgebra.isoMk e (by
    have n := (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.naturality e.hom
    rw [Functor.id_map] at n
    rw [← IsoAlgebra.str_hom, ← IsoAlgebra.str_hom, hF, hG]
    erw [reassoc_of% n]
    rw [Category.assoc, he])

variable [Finite k]

theorem weilStalkTraceAlternatingSum_mk_single
    (A : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)
      ((DerivedCategory.singleFunctor _ 0).obj A)) (β : A ≅ A) (n : ℕ)
    (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
    (hx : x ≫ ((Iso.refl X).pow (n + 1)).hom.left =
      ((geometricFrobeniusField k).pow (n + 1)).hom ≫ x) :
    weilStalkTraceAlternatingSum ℓ (n + 1) x hx
        (IsoAlgebra.mk ⟨(DerivedCategory.singleFunctor _ 0).obj A, hA⟩
          ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).app _ ≪≫
            ObjectProperty.isoMk _ ((DerivedCategory.singleFunctor _ 0).mapIso β))) =
      traceOrZero (upperStarGaloisComp ℓ ((geometricFrobeniusField k).pow (n + 1)).hom x
        (hx.symm.trans ((congrArg (x ≫ ·) (pow_hom_left_eq_id
          (by rw [Iso.refl_hom, Over.id_left] : (Iso.refl X).hom.left = 𝟙 X.left) (n + 1))).trans
            (Category.comp_id x))) A
        ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
          (@HPow.hPow (End A) ℕ (End A) instHPow β.hom (n + 1)))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
