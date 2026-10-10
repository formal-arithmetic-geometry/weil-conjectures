/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.DualizableLocalRetract
public import WeilConjectures.SixFunctors.ProEtale.Derived.LocallyPerfect.Transport
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarCoevaluation

/-!
# Dualizable complexes are locally retracts of finite subcomplexes

Let `K ∈ D(X_proét, Λ)` be dualizable, represented by a complex `M`. This file proves the first
step of Stacks, Tag 0FPV, on the pro-étale site: there is a covering sieve of the terminal object
of `X_proét` such that for each of its members `V`, with structure morphism `g : V ⟶ X`, the
complex `g^* M` has finitely many global sections `xₖ` such that `Q(g^* M)` is a retract of
`Q(L')` for every subcomplex `L' ⊆ g^* M` containing the `xₖ`
(`AlgebraicGeometry.ProEtale.exists_sieve_retract`).

Locally, the coevaluation of `K` is represented by a cocycle of `M ⊗ F` which is a finite sum of
pure tensors of sections over `V`
(`AlgebraicGeometry.ProEtale.exists_sieve_sum_tensorSectionMap_of_Q_map`).
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



/-- A chain map `ψ` out of the unit in degree `0` into `M ⊗ F`, whose cocycle is a finite sum of
pure tensors `ι(xₖ) ⊗ yₖ` of global sections with `xₖ` in a subcomplex `ι : L ⟶ M`, lifts to
`L ⊗ F` if `F` has flat terms. -/
lemma exists_comp_whiskerRight_eq_of_singleUnitHomEquiv {Y : Scheme.{u}}
    {L M F : CochainComplex (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ℤ}
    (ι : L ⟶ M) [∀ n, Mono (ι.f n)] (hF : ∀ n, ObjectProperty.flat (F.X n))
    {m : ℕ} (p : Fin m → ℤ) (x : ∀ k, (L.X (p k)).obj.obj (op (terminalProEt Y)))
    (y : ∀ k, (F.X (-p k)).obj.obj (op (terminalProEt Y)))
    (ψ : (HomologicalComplex.single _ (.up ℤ) 0).obj
      (𝟙_ (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) ⟶ M ⊗ F)
    (hψ : (singleUnitHomEquiv _ ψ).1 =
      ∑ k, (HomologicalComplex.ιTensorObj M F (p k) (-p k) 0 (by simp)).hom.app _
        (tensorSectionMap _ _ _ ((ι.f (p k)).hom.app _ (x k) ⊗ₜ y k))) :
    ∃ τ, τ ≫ ι ▷ F = ψ := by
  let z : ((L ⊗ F).X 0).obj.obj (op (terminalProEt Y)) :=
    ∑ k, (HomologicalComplex.ιTensorObj L F (p k) (-p k) 0 (by simp)).hom.app _
      (tensorSectionMap _ _ _ (x k ⊗ₜ y k))
  have hz : ((ι ▷ F).f 0).hom.app _ z = (singleUnitHomEquiv _ ψ).1 := by
    rw [hψ, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    refine (Sheaf.congr_hom_app_apply (CochainComplex.ιTensorObj_comp_whiskerRight_f
      ι F (p k) (-p k) 0 (by simp)) _).trans ?_
    exact congrArg ((HomologicalComplex.ιTensorObj M F (p k) (-p k) 0 (by simp)).hom.app _)
      (whiskerRight_hom_app_tensorSectionMap _ _ _ _ _)
  have : Mono ((ι ▷ F).f 1) := CochainComplex.mono_whiskerRight_f ι F hF 1
  have hd : ((L ⊗ F).d 0 1).hom.app _ z = 0 := by
    apply injective_hom_app_of_mono ((ι ▷ F).f 1)
    rw [← Sheaf.comp_hom_app_apply, ← HomologicalComplex.Hom.comm, Sheaf.comp_hom_app_apply, hz,
      (singleUnitHomEquiv _ ψ).2, map_zero]
  refine ⟨(singleUnitHomEquiv (L ⊗ F)).symm ⟨z, hd⟩, ?_⟩
  apply (singleUnitHomEquiv (M ⊗ F)).injective
  refine Subtype.ext ?_
  refine (singleUnitHomEquiv_comp_coe _ (ι ▷ F)).trans ?_
  simp only [Equiv.apply_symm_apply]
  exact hz

open _root_.DerivedCategory in
/-- Two chain maps whose images in the derived category agree have equal images under
`Qh ∘ quotient`. -/
lemma Qh_map_quotient_map_eq {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {K L : CochainComplex C ℤ} {f g : K ⟶ L} (h : Q.map f = Q.map g) :
    Qh.map ((HomotopyCategory.quotient _ _).map f) =
      Qh.map ((HomotopyCategory.quotient _ _).map g) := by
  rw [← cancel_mono ((quotientCompQhIso C).hom.app L), quotientCompQhIso_hom_naturality,
    quotientCompQhIso_hom_naturality, h]

-- the elaboration of the chain-level computations on `V.left` is slow
set_option maxHeartbeats 1000000 in
open _root_.DerivedCategory in
/-- **Local retract, after pullback.** Let `K` have a right dual `D` in `D(X_proét)`, with
`K ≅ Q(M)` and `D ≅ Q(F)` for a complex `F` of flat sheaves whose pullback along `g : V ⟶ X` is
K-flat, and let the coevaluation be represented by `Q(φ) ≫ Q(s)⁻¹`. Suppose that over `V` the
cocycle of `φ` is cohomologous to `s(∑ₖ xₖ ⊗ yₖ)` for a cocycle `∑ₖ xₖ ⊗ yₖ` of `M ⊗ F`. Then
`Q(g^* M)` is a retract of `Q(L')` for every subcomplex `L' ⊆ g^* M` containing the transports of
the `xₖ`. -/
theorem exists_retract_upperStar (V : X.ProEt)
    (K D : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    [ExactPairing K D]
    (M F : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ)
    (e : K ≅ Q.obj M) (eD : D ≅ Q.obj F)
    (hF : ∀ n, ObjectProperty.flat (F.X n))
    (hF' : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((V.hom)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj F))
    (I : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ)
    (s : M ⊗ F ⟶ I) [QuasiIso s]
    (φ : 𝟙_ (CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ) ⟶ I)
    (hu : coevaluationQ K D M F e eD = Q.map φ ≫ inv (Q.map s))
    {m : ℕ} (p : Fin m → ℤ) (x : ∀ k, (M.X (p k)).obj.obj (op V))
    (y : ∀ k, (F.X (-p k)).obj.obj (op V)) (w : (I.X (-1)).obj.obj (op V))
    (hd : ((M ⊗ F).d 0 1).hom.app _ (∑ k, (HomologicalComplex.ιTensorObj M F (p k) (-p k) 0
      (by simp)).hom.app _ (tensorSectionMap _ _ _ (x k ⊗ₜ y k))) = 0)
    (hs : (s.f 0).hom.app _ (∑ k, (HomologicalComplex.ιTensorObj M F (p k) (-p k) 0
      (by simp)).hom.app _ (tensorSectionMap _ _ _ (x k ⊗ₜ y k))) =
      (I.X 0).obj.map ((Scheme.ProEt.isTerminalMkId X).from V).op (singleUnitHomEquiv I φ).1 +
        (I.d (-1) 0).hom.app _ w)
    {L' : CochainComplex (Sheaf (Scheme.ProEt.topology V.left) (ModuleCat.{u + 1} Λ)) ℤ}
    (ι : L' ⟶ ((V.hom)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj M)
    [∀ n, Mono (ι.f n)]
    (x' : ∀ k, (L'.X (p k)).obj.obj (op (terminalProEt V.left)))
    (hx' : ∀ k, (ι.f (p k)).hom.app _ (x' k) = (sectionTransport V (M.X (p k))).hom (x k)) :
    ∃ r : Q.obj (((V.hom)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj M) ⟶
      Q.obj L', r ≫ Q.map ι = 𝟙 _ := by
  have : WeaklyEtale V.hom := V.prop
  let G := L((V.hom)^*[ModuleCat.{u + 1} Λ])
  let GC := (V.hom)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)
  let qX := HomotopyCategory.quotient (Sheaf (Scheme.ProEt.topology X)
    (ModuleCat.{u + 1} Λ)) (.up ℤ)
  let qV := HomotopyCategory.quotient (Sheaf (Scheme.ProEt.topology V.left)
    (ModuleCat.{u + 1} Λ)) (.up ℤ)
  let c' := (V.hom)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctorCounit
  let _ := monoidalLeftDerivedUpperStar (ModuleCat.{u + 1} Λ) V.hom
  let _ := ExactPairing.map G K D
  let F' := GC.obj F
  let M' := GC.obj M
  have hF'flat (n : ℤ) : ObjectProperty.flat (F'.X n) :=
    Functor.PreservesFlat.flat_obj (F := (V.hom)^*[ModuleCat.{u + 1} Λ]) (hF n)
  have hF'k : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat (qV.obj F') :=
    (HomotopyCategory.kFlat_quotient_obj_iff _).2 hF'
  let t := ∑ k, (HomologicalComplex.ιTensorObj M F (p k) (-p k) 0 (by simp)).hom.app _
    (tensorSectionMap _ _ _ (x k ⊗ₜ y k))
  let t' := (sectionTransport V ((M ⊗ F).X 0)).hom t
  have ht' : ((GC.obj (M ⊗ F)).d 0 1).hom.app _ t' = 0 := by
    have := sectionTransport_naturality V ((M ⊗ F).d 0 1) t
    erw [← this]
    rw [hd, map_zero]
  let φt := (singleUnitHomEquiv (GC.obj (M ⊗ F))).symm ⟨t', ht'⟩
  have hφt : Q.map (inv (η GC) ≫ GC.map φ) = Q.map (φt ≫ GC.map s) := by
    refine Q_map_eq_of_singleUnitHomEquiv_eq_add _ _ (-(sectionTransport V (I.X (-1))).hom w) ?_
    rw [singleUnitHomEquiv_inv_η_comp_map, singleUnitHomEquiv_comp_coe]
    simp only [φt, Equiv.apply_symm_apply]
    have h1 := sectionTransport_naturality V (s.f 0) t
    have h2 := sectionTransport_naturality V (I.d (-1) 0) w
    rw [hs, map_add] at h1
    have h3 : ((GC.map s).f 0).hom.app (op (terminalProEt V.left)) t' =
        (show ((GC.obj I).X 0).obj.obj (op (terminalProEt V.left)) from
          (sectionTransport V (I.X 0)).hom ((I.X 0).obj.map
            ((Scheme.ProEt.isTerminalMkId X).from V).op (singleUnitHomEquiv I φ).1)) +
        ((GC.obj I).d (-1) 0).hom.app (op (terminalProEt V.left))
          ((sectionTransport V (I.X (-1))).hom w) := h1.symm.trans (congrArg _ h2)
    change _ = ((GC.obj I).d (-1) 0).hom.app (op (terminalProEt V.left))
      (-(sectionTransport V (I.X (-1))).hom w) +
        ((GC.map s).f 0).hom.app (op (terminalProEt V.left)) t'
    rw [h3, map_neg]
    abel
  obtain ⟨τ, hτ⟩ := exists_comp_whiskerRight_eq_of_singleUnitHomEquiv ι hF'flat p x'
    (fun k ↦ (sectionTransport V _).hom (y k)) (φt ≫ δ GC M F) (by
      rw [singleUnitHomEquiv_comp_coe]
      erw [Equiv.apply_symm_apply]
      simp only [t', t, map_sum, hx']
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      exact δ_mapHomologicalComplex_f_sectionTransport V M F (p k) (-p k) 0 (by simp) (x k) (y k))
  exact exists_retract_of_upperStar_of_coevaluationQ V.hom K D M F I e eD s φ hu hF' ι φt hφt τ hτ

end AlgebraicGeometry.ProEtale
