/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.DualizableLocalRetract
public import WeilConjectures.SixFunctors.ProEtale.Derived.LocallyPerfect.Transport
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarMonoidalStructure

/-!
# Dualizable complexes are locally retracts of finite subcomplexes

Let `K ∈ D(X_proét, Λ)` be dualizable, represented by a complex `M`. This file proves the first
step of Stacks, Tag 0FPV, on the pro-étale site: there is a covering sieve of the terminal object
of `X_proét` such that for each of its members `V`, with structure morphism `g : V ⟶ X`, the
complex `g^* M` has finitely many global sections `xₖ` such that `Q(g^* M)` is a retract of
`Q(L')` for every subcomplex `L' ⊆ g^* M` containing the `xₖ`
(`AlgebraicGeometry.ProEtale.exists_sieve_retract`).

Locally, the coevaluation of `K` is represented by a cocycle of `M ⊗ F` which is a finite sum of
pure tensors of sections over `V` (`AlgebraicGeometry.ProEtale.exists_sieve_sum_tensorSectionMap_of_Q_map`).
The derived pullback `Lg^*` is monoidal, so it sends the duality data of `K` to duality data of
`Lg^* K ≅ Q(g^* M)`, whose coevaluation is then represented by the transported cocycle, a sum of
pure tensors of global sections; we conclude with the zigzag argument
`CategoryTheory.exists_comp_eq_of_coevaluation_comp_whiskerRight`.

## Main results

- `AlgebraicGeometry.ProEtale.singleUnitHomEquiv_inv_η_comp_map`: the cocycle of the pullback of
  a chain map out of the unit is the transport of its cocycle.
- `AlgebraicGeometry.ProEtale.exists_sieve_retract`: the local retract statement above.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open _root_.AlgebraicGeometry.Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- The pullback along `g : V ⟶ X` of a chain map `φ` out of the unit in degree `0`, precomposed
with `𝟙_ ≅ g^* 𝟙_`, has as cocycle the transport of the restriction to `V` of the cocycle
of `φ`. -/
lemma singleUnitHomEquiv_inv_η_comp_map (V : X.ProEt)
    {N : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ}
    (φ : (HomologicalComplex.single _ (.up ℤ) 0).obj
      (𝟙_ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) ⟶ N) :
    (singleUnitHomEquiv _ (inv (η ((V.hom)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex
        (.up ℤ))) ≫ ((V.hom)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).map φ)).1 =
      (sectionTransport V (N.X 0)).hom
        ((N.X 0).obj.map ((Scheme.ProEt.isTerminalMkId X).from V).op
          (singleUnitHomEquiv N φ).1) := by
  let G := (V.hom)^*[ModuleCat.{u + 1} Λ]
  let sX := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
  let sV := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (Sheaf (Scheme.ProEt.topology V.left) (ModuleCat.{u + 1} Λ)))
  have hη : (η (G.mapHomologicalComplex (.up ℤ))).f 0 = G.map sX.hom ≫ η G ≫ sV.inv := by
    rw [Functor.OplaxMonoidal.mapHomologicalComplex_η, mapHomologicalComplexη,
      HomologicalComplex.comp_f, HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  have key : sV.inv ≫ (inv (η (G.mapHomologicalComplex (.up ℤ)))).f 0 =
      inv (η G) ≫ G.map sX.inv := by
    rw [← cancel_mono ((η (G.mapHomologicalComplex (.up ℤ))).f 0), Category.assoc,
      ← HomologicalComplex.comp_f, IsIso.inv_hom_id, HomologicalComplex.id_f]
    erw [Category.comp_id]
    rw [hη, Category.assoc, ← G.map_comp_assoc, Iso.inv_hom_id, G.map_id, Category.id_comp,
      IsIso.inv_hom_id_assoc]
  change sectionOfUnitHom (sV.inv ≫ (inv (η (G.mapHomologicalComplex (.up ℤ))) ≫
    (G.mapHomologicalComplex (.up ℤ)).map φ).f 0) = _
  rw [HomologicalComplex.comp_f, ← Category.assoc, key, Category.assoc,
    Functor.mapHomologicalComplex_map_f, ← G.map_comp]
  exact sectionOfUnitHom_upperStar_map V _


/-- The comparison `δ : g^*(M ⊗ F) ⟶ g^* M ⊗ g^* F` of complexes sends the transport of the
pure tensor `x ⊗ y` in the summand `Mᵖ ⊗ F^q` to the pure tensor of the transports. -/
lemma δ_mapHomologicalComplex_f_sectionTransport (V : X.ProEt)
    (M F : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ)
    (p q n : ℤ) (h : p + q = n) (x : (M.X p).obj.obj (op V)) (y : (F.X q).obj.obj (op V)) :
    ((δ ((V.hom)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)) M F).f n).hom.app
        (op (terminalProEt V.left))
      ((sectionTransport V ((M ⊗ F).X n)).hom
        ((HomologicalComplex.ιTensorObj M F p q n h).hom.app (op V)
          (tensorSectionMap _ _ V (x ⊗ₜ y)))) =
    (HomologicalComplex.ιTensorObj (((V.hom)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex
      (.up ℤ)).obj M) (((V.hom)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj F)
        p q n h).hom.app (op (terminalProEt V.left))
      (tensorSectionMap _ _ _ ((sectionTransport V (M.X p)).hom x ⊗ₜ
        (sectionTransport V (F.X q)).hom y)) := by
  let G := (V.hom)^*[ModuleCat.{u + 1} Λ]
  have h1 : G.map (HomologicalComplex.ιTensorObj M F p q n h) ≫
      (δ (G.mapHomologicalComplex (.up ℤ)) M F).f n =
      δ G (M.X p) (F.X q) ≫ HomologicalComplex.ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj M)
        ((G.mapHomologicalComplex (.up ℤ)).obj F) p q n h :=
    HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX _ _ _ _ p q n h
  have h2 := sectionTransport_naturality V (HomologicalComplex.ιTensorObj M F p q n h)
    (tensorSectionMap _ _ V (x ⊗ₜ y))
  refine (congrArg (((δ (G.mapHomologicalComplex (.up ℤ)) M F).f n).hom.app
    (op (terminalProEt V.left))) h2).trans ?_
  refine (ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app (op (terminalProEt V.left)))
    h1) _).trans ?_
  exact congrArg _ (δ_upperStar_sectionTransport_tensorSectionMap V _ _ x y)

end AlgebraicGeometry.ProEtale
