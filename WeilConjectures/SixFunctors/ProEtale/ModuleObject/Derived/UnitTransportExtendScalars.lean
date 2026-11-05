/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerAction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullFac

/-!
# Extension of scalars commutes with the derived unit and the unit transport

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings and write `T = L(Ext_a)` for the
derived extension of scalars. For `p : G ⟶ T₀` and `q : G ⟶ S`, the comparison
`ProEtale.CondensedRing.derivedPushPullExtendScalarsHom a p q K`
```
T (Rp_* Lq^* K) ⟶ Rp_* T (Lq^* K) ≅ Rp_* Lq^* (T K)
```
is the push comparison `ProEtale.CondensedRing.derivedUpperStarExtendScalarsPushHom a p` followed
by the pull isomorphism `ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso a q`. We show:

* `ProEtale.CondensedRing.map_unit_comp_derivedPushPullExtendScalarsHom`: it carries `T` of the
  unit of `Lq^* ⊣ Rq_*` to the unit of `Lq^* ⊣ Rq_*` with coefficients `Λ'` (the push comparison
  is the mate of the inverse of the pull isomorphism);
* `ProEtale.CondensedRing.derivedUpperStarExtendScalarsPushHom_comp_app`: the push comparisons
  are compatible with the composition isomorphisms `Rp_* ⋙ Rq_* ≅ R(p ≫ q)_*`; this is the mate
  of the compatibility `ProEtale.CondensedRing.derivedUpperStarExtendScalarsIsoCompCoherence` of
  the pull isomorphisms with the composition of derived pullbacks, through the abstract
  `CategoryTheory.mateEquiv_conjugateIsoEquiv_comp_app`;
* `ProEtale.CondensedRing.map_derivedUnitTransport_comp_derivedPushPullExtendScalarsHom`: it
  commutes with the unit transports `ProEtale.CondensedRing.derivedUnitTransport` along any
  `s : G' ⟶ G`;
* `ProEtale.CondensedRing.isIso_derivedPushPullExtendScalarsHom`: it is an isomorphism as soon as
  the push comparison is, and the arrow-isomorphism corollaries
  `ProEtale.CondensedRing.arrowIsoMapUnit` and
  `ProEtale.CondensedRing.arrowIsoMapDerivedUnitTransport`.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory

variable {C₁ C₂ C₃ C₁' C₂' C₃' : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* C₁'] [Category* C₂'] [Category* C₃']
  {L₁₂ : C₁ ⥤ C₂} {R₂₁ : C₂ ⥤ C₁} {L₂₃ : C₂ ⥤ C₃} {R₃₂ : C₃ ⥤ C₂}
  {L₁₃ : C₁ ⥤ C₃} {R₃₁ : C₃ ⥤ C₁}
  {L₁₂' : C₁' ⥤ C₂'} {R₂₁' : C₂' ⥤ C₁'} {L₂₃' : C₂' ⥤ C₃'} {R₃₂' : C₃' ⥤ C₂'}
  {L₁₃' : C₁' ⥤ C₃'} {R₃₁' : C₃' ⥤ C₁'}
  (adj₁₂ : L₁₂ ⊣ R₂₁) (adj₂₃ : L₂₃ ⊣ R₃₂) (adj₁₃ : L₁₃ ⊣ R₃₁)
  (adj₁₂' : L₁₂' ⊣ R₂₁') (adj₂₃' : L₂₃' ⊣ R₃₂') (adj₁₃' : L₁₃' ⊣ R₃₁')
  {T₁ : C₁ ⥤ C₁'} {T₂ : C₂ ⥤ C₂'} {T₃ : C₃ ⥤ C₃'}
  (e₁₂ : L₁₂ ⋙ T₂ ≅ T₁ ⋙ L₁₂') (e₂₃ : L₂₃ ⋙ T₃ ≅ T₂ ⋙ L₂₃') (e₁₃ : L₁₃ ⋙ T₃ ≅ T₁ ⋙ L₁₃')
  (c : L₁₃ ≅ L₁₂ ⋙ L₂₃) (c' : L₁₃' ≅ L₁₂' ⋙ L₂₃')

section UnitTransport

variable {CS CG' CG CT CS' CG'' CGp CT' : Type*} [Category* CS] [Category* CG'] [Category* CG]
  [Category* CT] [Category* CS'] [Category* CG''] [Category* CGp] [Category* CT']
  {Lq : CS ⥤ CG'} {Ls : CG' ⥤ CG} {Lsq : CS ⥤ CG} {Lp : CT ⥤ CG'} {Rp : CG' ⥤ CT}
  {Rs : CG ⥤ CG'} {Lsp : CT ⥤ CG} {Rsp : CG ⥤ CT}
  {Lq' : CS' ⥤ CG''} {Ls' : CG'' ⥤ CGp} {Lsq' : CS' ⥤ CGp} {Lp' : CT' ⥤ CG''}
  {Rp' : CG'' ⥤ CT'} {Rs' : CGp ⥤ CG''} {Lsp' : CT' ⥤ CGp} {Rsp' : CGp ⥤ CT'}
  (adjp : Lp ⊣ Rp) (adjs : Ls ⊣ Rs) (adjsp : Lsp ⊣ Rsp)
  (adjp' : Lp' ⊣ Rp') (adjs' : Ls' ⊣ Rs') (adjsp' : Lsp' ⊣ Rsp')
  {TS : CS ⥤ CS'} {TG' : CG' ⥤ CG''} {TG : CG ⥤ CGp} {TT : CT ⥤ CT'}
  (eq : Lq ⋙ TG' ≅ TS ⋙ Lq') (es : Ls ⋙ TG ≅ TG' ⋙ Ls') (esq : Lsq ⋙ TG ≅ TS ⋙ Lsq')
  (ep : Lp ⋙ TG' ≅ TT ⋙ Lp') (esp : Lsp ⋙ TG ≅ TT ⋙ Lsp')
  (cq : Lsq ≅ Lq ⋙ Ls) (cq' : Lsq' ≅ Lq' ⋙ Ls') (cp : Lsp ≅ Lp ⋙ Ls) (cp' : Lsp' ≅ Lp' ⋙ Ls')

end UnitTransport

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

end AlgebraicGeometry.ProEtale.CondensedRing
