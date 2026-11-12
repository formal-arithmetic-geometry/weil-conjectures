/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateCube
public import WeilConjectures.SixFunctors.NearbyCycles.Exchange
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethCoefficientChangeSquares
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.RestrictScalarsMate

/-!

# Nearby cycles and restriction of scalars

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings, not necessarily flat, and write
`Res = D(Res_a)` for the levelwise restriction of scalars. For a model `M = (𝒳, j, i, ε)` of `X`,
the nearby cycles `Ψ = Li^* Rj_* Lε^*` commute with `Res`: the derived pullbacks and the derived
pushforwards do, for every coefficient change
(`ProEtale.CondensedRing.derivedComapLeftDerivedUpperStarIso`,
`ProEtale.CondensedRing.rightDerivedLowerStarComapIso`), which gives an isomorphism
`Res Ψ^{Λ'}(A) ≅ Ψ^Λ(Res A)` (`NearbyCyclesModel.comapComparison`).

These isomorphisms are compatible with the pullback exchanges `α_φ : Lf'^* Ψ_N ⟶ Ψ_M Lf^*` of a
morphism of models `φ` (`NearbyCyclesModel.Hom.comap_map_pullbackExchange_app`). Hence, if the
pullback exchange with coefficients `Λ'` is invertible at `A`, then the pullback exchange with
coefficients `Λ` is invertible at `Res A`
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_comap`). This transports results proved for
the unit with coefficients `Λ'` to the restriction of scalars of the unit with coefficients `Λ`,
for instance from the residue field `T ⧸ 𝔪` of a finite coefficient ring `T` to `T`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory

variable {DY' DX' DTN DTM DGN DGM DY DX : Type*} [Category* DY'] [Category* DX'] [Category* DTN]
  [Category* DTM] [Category* DGN] [Category* DGM] [Category* DY] [Category* DX]
  {EY' EX' ETN ETM EGN EGM EY EX : Type*} [Category* EY'] [Category* EX'] [Category* ETN]
  [Category* ETM] [Category* EGN] [Category* EGM] [Category* EY] [Category* EX]
  {Fp : DY' ⥤ DX'} {IN : DTN ⥤ DY'} {IM : DTM ⥤ DX'} {T : DTN ⥤ DTM}
  {JN : DGN ⥤ DTN} {JM : DGM ⥤ DTM} {G : DGN ⥤ DGM} {EN : DY ⥤ DGN} {EM : DX ⥤ DGM}
  {F : DY ⥤ DX}
  {Fp' : EY' ⥤ EX'} {IN' : ETN ⥤ EY'} {IM' : ETM ⥤ EX'} {T' : ETN ⥤ ETM}
  {JN' : EGN ⥤ ETN} {JM' : EGM ⥤ ETM} {G' : EGN ⥤ EGM} {EN' : EY ⥤ EGN} {EM' : EX ⥤ EGM}
  {F' : EY ⥤ EX}
  {cY' : DY' ⥤ EY'} {cX' : DX' ⥤ EX'} {cTN : DTN ⥤ ETN} {cTM : DTM ⥤ ETM} {cGN : DGN ⥤ EGN}
  {cGM : DGM ⥤ EGM} {cY : DY ⥤ EY} {cX : DX ⥤ EX}

/-- **Invertible pasted exchanges and a change of coefficients.** In the situation of
`CategoryTheory.map_exchange_comp_eq`, if the comparisons `ρ_N` and `ρ_M` of the right adjoints
are isomorphisms, then the pasted exchange `α'` is invertible at `c A` as soon as `α` is invertible
at `A`. -/
lemma isIso_app_of_map_exchange
    (θi : IN ⋙ Fp ⟶ T ⋙ IM) (β : JN ⋙ T ⟶ G ⋙ JM) (θε : EN ⋙ G ⟶ F ⋙ EM)
    (θi' : IN' ⋙ Fp' ⟶ T' ⋙ IM') (β' : JN' ⋙ T' ⟶ G' ⋙ JM') (θε' : EN' ⋙ G' ⟶ F' ⋙ EM')
    (PFp : Fp ⋙ cX' ≅ cY' ⋙ Fp') (PIN : IN ⋙ cY' ≅ cTN ⋙ IN') (PIM : IM ⋙ cX' ≅ cTM ⋙ IM')
    (PT : T ⋙ cTM ≅ cTN ⋙ T') (PG : G ⋙ cGM ≅ cGN ⋙ G') (PEN : EN ⋙ cGN ≅ cY ⋙ EN')
    (PEM : EM ⋙ cGM ≅ cX ⋙ EM') (PF : F ⋙ cX ≅ cY ⋙ F')
    (ρN : JN ⋙ cTN ⟶ cGN ⋙ JN') (ρM : JM ⋙ cTM ⟶ cGM ⋙ JM') [IsIso ρN] [IsIso ρM]
    (hθi : ∀ o, Fp'.map (PIN.inv.app o) ≫ PFp.inv.app (IN.obj o) ≫ cX'.map (θi.app o) =
      θi'.app (cTN.obj o) ≫ IM'.map (PT.inv.app o) ≫ PIM.inv.app (T.obj o))
    (hβ : ∀ o, PT.inv.app (JN.obj o) ≫ cTM.map (β.app o) ≫ ρM.app (G.obj o) =
      T'.map (ρN.app o) ≫ β'.app (cGN.obj o) ≫ JM'.map (PG.inv.app o))
    (hθε : ∀ o, G'.map (PEN.inv.app o) ≫ PG.inv.app (EN.obj o) ≫ cGM.map (θε.app o) =
      θε'.app (cY.obj o) ≫ EM'.map (PF.inv.app o) ≫ PEM.inv.app (F.obj o))
    (α : (EN ⋙ JN ⋙ IN) ⋙ Fp ⟶ F ⋙ EM ⋙ JM ⋙ IM)
    (hα : α = Functor.whiskerLeft (EN ⋙ JN) θi ≫
      Functor.whiskerRight (Functor.whiskerLeft EN β ≫ Functor.whiskerRight θε JM) IM)
    (α' : (EN' ⋙ JN' ⋙ IN') ⋙ Fp' ⟶ F' ⋙ EM' ⋙ JM' ⋙ IM')
    (hα' : α' = Functor.whiskerLeft (EN' ⋙ JN') θi' ≫
      Functor.whiskerRight (Functor.whiskerLeft EN' β' ≫ Functor.whiskerRight θε' JM') IM')
    (A : DY) (hA : IsIso (α.app A)) : IsIso (α'.app (cY.obj A)) := by
  have key := map_exchange_comp_eq θi β θε θi' β' θε' PFp PIN PIM PT PG PEN PEM PF ρN ρM hθi hβ
    hθε α hα α' hα' A
  have h : IsIso (cX'.map (α.app A) ≫ (PIM.hom.app _ ≫ IM'.map (ρM.app _ ≫
      JM'.map (PEM.hom.app (F.obj A)))) ≫ IM'.map (JM'.map (EM'.map (PF.hom.app A)))) :=
    inferInstance
  rw [key] at h
  exact (isIso_comp_left_iff _ _).1 ((isIso_comp_left_iff _ _).1 h)

end CategoryTheory

-- `Mod.comap_additive` and `Mod.instAdditiveComap_weilConjectures` are two instances for the same
-- fact; the commutations of restriction of scalars with the derived functors are stated with the
-- latter, and mixing the two makes unification very slow.
attribute [-instance] Mod.comap_additive

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {X X' : Scheme.{u}}

variable {Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

set_option maxHeartbeats 1000000 in
-- the pasted squares are matched against the pullback exchanges
/-- **Restriction of scalars of an invertible pullback exchange**: for a morphism of models
`φ : M ⟶ N`, if the pullback exchange `α_φ : Lf'^* Ψ_N ⟶ Ψ_M Lf^*` with coefficients `Λ'` is
invertible at `A`, then the pullback exchange with coefficients `Λ` is invertible at the
restriction of scalars `Res A`. Indeed, `Res` carries `α_φ` with coefficients `Λ'` to `α_φ` with
coefficients `Λ`, up to the commutations of `Res` with the derived pullbacks and pushforwards
(`CategoryTheory.map_exchange_comp_eq`); the cube conditions are
`ProEtale.CondensedRing.derivedComapLeftDerivedUpperStarIso_cube` and its mate, and the
commutation with `Rj_*` is invertible by
`ProEtale.CondensedRing.rightDerivedLowerStarComapIso_hom_eq_mateEquiv`. -/
theorem Hom.isIso_pullbackExchange_app_comap (φ : M.Hom N f f')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ' Y)))
    (h : IsIso ((φ.pullbackExchange Λ').app A)) :
    IsIso ((φ.pullbackExchange Λ).app (D(Mod.comap (coefficientMap a Y)).obj A)) := by
  have hβ := mateEquiv_app_cube (derivedUpperStarLowerStarAdjunction Λ' N.j)
    (derivedUpperStarLowerStarAdjunction Λ' M.j) (derivedUpperStarLowerStarAdjunction Λ N.j)
    (derivedUpperStarLowerStarAdjunction Λ M.j) (pullbackSquareComparison Λ' φ.commSq_j).hom
    (pullbackSquareComparison Λ φ.commSq_j).hom (derivedComapLeftDerivedUpperStarIso a N.j).hom
    (derivedComapLeftDerivedUpperStarIso a M.j).hom
    (derivedComapLeftDerivedUpperStarIso a φ.total).hom
    (derivedComapLeftDerivedUpperStarIso a φ.generic).hom
    (derivedComapLeftDerivedUpperStarIso_cube a φ.commSq_j)
  have := isIso_app_of_map_exchange (pullbackSquareComparison Λ' φ.commSq_i).hom
    (mateEquiv (derivedUpperStarLowerStarAdjunction Λ' N.j)
      (derivedUpperStarLowerStarAdjunction Λ' M.j)
      (pullbackSquareComparison Λ' φ.commSq_j).hom).natTrans
    (pullbackSquareComparison Λ' φ.commSq_ε).hom
    (pullbackSquareComparison Λ φ.commSq_i).hom
    (mateEquiv (derivedUpperStarLowerStarAdjunction Λ N.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j)
      (pullbackSquareComparison Λ φ.commSq_j).hom).natTrans
    (pullbackSquareComparison Λ φ.commSq_ε).hom
    (derivedComapLeftDerivedUpperStarIso a f').symm
    (derivedComapLeftDerivedUpperStarIso a N.i).symm
    (derivedComapLeftDerivedUpperStarIso a M.i).symm
    (derivedComapLeftDerivedUpperStarIso a φ.total).symm
    (derivedComapLeftDerivedUpperStarIso a φ.generic).symm
    (derivedComapLeftDerivedUpperStarIso a N.ε).symm
    (derivedComapLeftDerivedUpperStarIso a M.ε).symm
    (derivedComapLeftDerivedUpperStarIso a f).symm
    (mateEquiv (derivedUpperStarLowerStarAdjunction Λ' N.j)
      (derivedUpperStarLowerStarAdjunction Λ N.j)
      (derivedComapLeftDerivedUpperStarIso a N.j).hom).natTrans
    (mateEquiv (derivedUpperStarLowerStarAdjunction Λ' M.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j)
      (derivedComapLeftDerivedUpperStarIso a M.j).hom).natTrans
    (derivedComapLeftDerivedUpperStarIso_cube a φ.commSq_i) hβ
    (derivedComapLeftDerivedUpperStarIso_cube a φ.commSq_ε)
    (φ.pullbackExchange Λ') rfl (φ.pullbackExchange Λ) rfl A h
  exact this

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
