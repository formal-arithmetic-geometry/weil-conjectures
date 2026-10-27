module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Equivalence

/-! # Normalized mates and transport through equivalences

Source: main-20261015, sk-lem-sp-reduction-exceptional.proof.md, Charts and
uniqueness of transposes (blueprint: lem-pur-normalized-mate-scalar-site-transport).

The right mate is Mathlib's `mateEquiv` applied to the inverse scalar square.
The transport below is a composite of the specified natural transformations.
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈

set_option autoImplicit false

namespace CategoryTheory

open CategoryTheory.Functor

/-- The five-factor transported arrow, as a natural transformation with explicit endpoints.
Source: main-20261015, sk-lem-sp-reduction-exceptional.proof.md, Charts and
uniqueness of transposes (blueprint: lem-pur-normalized-mate-scalar-site-transport).
-/
def normalizedMateTransport
    {CA : Type u₁} {DA : Type u₂} {CB : Type u₃} {DB : Type u₄}
    {CA' : Type u₅} {DA' : Type u₆} {CB' : Type u₇} {DB' : Type u₈}
    [Category.{v₁} CA] [Category.{v₂} DA] [Category.{v₃} CB] [Category.{v₄} DB]
    [Category.{v₅} CA'] [Category.{v₆} DA'] [Category.{v₇} CB'] [Category.{v₈} DB']
    {GA : DA ⥤ CA} {GB : DB ⥤ CB} {GA' : DA' ⥤ CA'} {GB' : DB' ⥤ CB'}
    {UA : CA ⥤ CA'} {VA : DA ⥤ DA'} {UB : CB ⥤ CB'} {VB : DB ⥤ DB'}
    {S : CA ⥤ CB} {T : DA ⥤ DB} {S' : CA' ⥤ CB'} {T' : DA' ⥤ DB'}
    (ρA : GA ⋙ UA ≅ VA ⋙ GA') (ρB : GB ⋙ UB ≅ VB ⋙ GB')
    (δX : UA ⋙ S' ≅ S ⋙ UB) (δY : VA ⋙ T' ≅ T ⋙ VB)
    (b : GA ⋙ S ⟶ T ⋙ GB) : VA ⋙ GA' ⋙ S' ⟶ VA ⋙ T' ⋙ GB' :=
  whiskerRight ρA.inv S' ≫ whiskerLeft GA δX.hom ≫ whiskerRight b UB ≫
    whiskerLeft T ρB.hom ≫ whiskerRight δY.inv GB'

/-- Normalization identifies the right mate with the conjugated model isomorphism.
Source: main-20261015, sk-lem-sp-reduction-exceptional.proof.md, Charts and
uniqueness of transposes (blueprint: lem-pur-normalized-mate-scalar-site-transport).

Proof: apply the inverse hom bijection for `adjB`, namely `v ↦ FB.map v ≫ εB`.
Expand the model counit at B, substitute `hnorm`, move the inverse of `γA` past
`q` by naturality, and cancel `γA` with its inverse. The result is
`q.inv.app (GA.obj K) ≫ T.map (adjA.counit.app K)`, the inverse transpose of
the specified mate. Injectivity of the hom bijection proves the formula.
The right-hand side is the composite of three whiskered natural isomorphisms;
its inverse reverses these factors. This proves naturality and invertibility.
These are Steps 1–2 of the node, using lem-weil-pbc-adjunction-of-natural-bijection
and def-weil-pbc-adjunction-mate.
-/
theorem normalizedRightMate
    {CA : Type u₁} {DA : Type u₂} {CB : Type u₃} {DB : Type u₄}
    [Category.{v₁} CA] [Category.{v₂} DA] [Category.{v₃} CB] [Category.{v₄} DB]
    (FA : CA ⥤ DA) (GA HA : DA ⥤ CA) (FB : CB ⥤ DB) (GB HB : DB ⥤ CB)
    (adjA : FA ⊣ GA) (adjB : FB ⊣ GB) (γA : HA ≅ GA) (γB : HB ≅ GB)
    (S : CA ⥤ CB) (T : DA ⥤ DB) (q : FA ⋙ T ≅ S ⋙ FB) (a : HA ⋙ S ≅ T ⋙ HB)
    (hnorm : ∀ K : DA,
      q.hom.app (HA.obj K) ≫ FB.map (a.hom.app K) ≫
          FB.map (γB.hom.app (T.obj K)) ≫ adjB.counit.app (T.obj K) =
        T.map (FA.map (γA.hom.app K) ≫ adjA.counit.app K)) :
    (∀ K : DA, (mateEquiv adjA adjB q.inv).app K =
      S.map (γA.inv.app K) ≫ a.hom.app K ≫ γB.hom.app (T.obj K)) ∧
    IsIso (mateEquiv adjA adjB q.inv).natTrans := by
  have hformula : ∀ K : DA, (mateEquiv adjA adjB q.inv).app K =
      S.map (γA.inv.app K) ≫ a.hom.app K ≫ γB.hom.app (T.obj K) := by
    intro K
    apply (adjB.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit]
    rw [mateEquiv_counit]
    apply (cancel_epi (FB.map (S.map (γA.hom.app K)))).1
    apply (cancel_epi (q.hom.app (HA.obj K))).1
    have hn := q.hom.naturality (γA.hom.app K)
    dsimp at hn
    simp only [FB.map_comp, Category.assoc]
    rw [← reassoc_of% hn]
    simp only [Iso.hom_inv_id_app_assoc]
    rw [← FB.map_comp_assoc, ← S.map_comp, Iso.hom_inv_id_app,
      S.map_id, FB.map_id, Category.id_comp]
    simpa only [T.map_comp] using (hnorm K).symm
  refine ⟨hformula, ?_⟩
  have : ∀ K, IsIso ((mateEquiv adjA adjB q.inv).natTrans.app K) := by
    intro K
    change IsIso ((mateEquiv adjA adjB q.inv).app K)
    rw [hformula]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- Counit-compatible equivalences carry the normalized mate to the specified new mate.
Source: main-20261015, sk-lem-sp-reduction-exceptional.proof.md, Charts and
uniqueness of transposes (blueprint: lem-pur-normalized-mate-scalar-site-transport).

Proof: first use `normalizedRightMate` (node Steps 1–2). For Step 3, expand the
five-factor transport and precompose its inverse transpose with `FB'S'(ρA)`.
Cancel `ρA.inv ≫ ρA`, move `δY.inv` through the B-prime counit by naturality,
substitute `hcB`, move the B comparison through the actual old mate by naturality,
and substitute the old mate's transpose equation. In Step 4 solve `hsquare` for
`VB(q.inv) ≫ cB.inv ≫ FB'(δX)`, substitute, and move the old A counit through
`δY` by naturality. Step 5 substitutes `hcA`, uses naturality of `q'` at `ρA`,
and cancels the isomorphism `FB'S'(ρA)`. This gives precisely the displayed new
counit equation. The injective inverse hom bijection for `adjB'` identifies the
transport with the restriction of `mateEquiv adjA' adjB' q'.inv`.
In Step 6 the transport is invertible because all five factors are whiskered
isomorphisms, including the old mate. Naturality of the specified new mate along
`j` gives the last formula. Essential surjectivity of `VA` supplies such a `j`
for every new object, so every component, hence the new mate, is invertible.
No geometric, additive, tensor, sheaf, or coefficient assumptions enter.
-/
theorem normalizedMateScalarSiteTransport
    {CA : Type u₁} {DA : Type u₂} {CB : Type u₃} {DB : Type u₄}
    [Category.{v₁} CA] [Category.{v₂} DA] [Category.{v₃} CB] [Category.{v₄} DB]
    (FA : CA ⥤ DA) (GA HA : DA ⥤ CA) (FB : CB ⥤ DB) (GB HB : DB ⥤ CB)
    (adjA : FA ⊣ GA) (adjB : FB ⊣ GB) (γA : HA ≅ GA) (γB : HB ≅ GB)
    (S : CA ⥤ CB) (T : DA ⥤ DB) (q : FA ⋙ T ≅ S ⋙ FB) (a : HA ⋙ S ≅ T ⋙ HB)
    (hnorm : ∀ K : DA,
      q.hom.app (HA.obj K) ≫ FB.map (a.hom.app K) ≫
          FB.map (γB.hom.app (T.obj K)) ≫ adjB.counit.app (T.obj K) =
        T.map (FA.map (γA.hom.app K) ≫ adjA.counit.app K))
    {CA' : Type u₅} {DA' : Type u₆} {CB' : Type u₇} {DB' : Type u₈}
    [Category.{v₅} CA'] [Category.{v₆} DA'] [Category.{v₇} CB'] [Category.{v₈} DB']
    (FA' : CA' ⥤ DA') (GA' : DA' ⥤ CA') (FB' : CB' ⥤ DB') (GB' : DB' ⥤ CB')
    (adjA' : FA' ⊣ GA') (adjB' : FB' ⊣ GB')
    (UA : CA ≌ CA') (VA : DA ≌ DA') (UB : CB ≌ CB') (VB : DB ≌ DB')
    (cA : FA ⋙ VA.functor ≅ UA.functor ⋙ FA')
    (cB : FB ⋙ VB.functor ≅ UB.functor ⋙ FB')
    (ρA : GA ⋙ UA.functor ≅ VA.functor ⋙ GA')
    (ρB : GB ⋙ UB.functor ≅ VB.functor ⋙ GB')
    (hcA : ∀ K : DA, cA.hom.app (GA.obj K) ≫ FA'.map (ρA.hom.app K) ≫
      adjA'.counit.app (VA.functor.obj K) = VA.functor.map (adjA.counit.app K))
    (hcB : ∀ K : DB, cB.hom.app (GB.obj K) ≫ FB'.map (ρB.hom.app K) ≫
      adjB'.counit.app (VB.functor.obj K) = VB.functor.map (adjB.counit.app K))
    (S' : CA' ⥤ CB') (T' : DA' ⥤ DB')
    (δX : UA.functor ⋙ S' ≅ S ⋙ UB.functor)
    (δY : VA.functor ⋙ T' ≅ T ⋙ VB.functor) (q' : FA' ⋙ T' ≅ S' ⋙ FB')
    (hsquare : ∀ M : CA,
      T'.map (cA.hom.app M) ≫ q'.hom.app (UA.functor.obj M) ≫
          FB'.map (δX.hom.app M) =
        δY.hom.app (FA.obj M) ≫ VB.functor.map (q.hom.app M) ≫ cB.hom.app (S.obj M)) :
    (∀ K : DA,
      FB'.map ((normalizedMateTransport ρA ρB δX δY
        (mateEquiv adjA adjB q.inv).natTrans).app K) ≫
          adjB'.counit.app (T'.obj (VA.functor.obj K)) =
        q'.inv.app (GA'.obj (VA.functor.obj K)) ≫
          T'.map (adjA'.counit.app (VA.functor.obj K))) ∧
    normalizedMateTransport ρA ρB δX δY (mateEquiv adjA adjB q.inv).natTrans =
      whiskerLeft VA.functor (mateEquiv adjA' adjB' q'.inv).natTrans ∧
    IsIso (normalizedMateTransport ρA ρB δX δY (mateEquiv adjA adjB q.inv).natTrans) ∧
    IsIso (mateEquiv adjA' adjB' q'.inv).natTrans ∧
    (∀ (K : DA) (K' : DA') (j : VA.functor.obj K ≅ K'),
      (mateEquiv adjA' adjB' q'.inv).app K' =
        S'.map (GA'.map j.inv) ≫
          (normalizedMateTransport ρA ρB δX δY
            (mateEquiv adjA adjB q.inv).natTrans).app K ≫ GB'.map (T'.map j.hom)) := by
  have hsq (M : CA) :
      FB'.map (δX.hom.app M) ≫ cB.inv.app (S.obj M) ≫
          VB.functor.map (q.inv.app M) =
        q'.inv.app (UA.functor.obj M) ≫ T'.map (cA.inv.app M) ≫
          δY.hom.app (FA.obj M) := by
    apply (cancel_epi (T'.map (cA.hom.app M) ≫
      q'.hom.app (UA.functor.obj M))).1
    simp only [Category.assoc]
    rw [reassoc_of% (hsquare M)]
    simp only [Iso.hom_inv_id_app_assoc]
    rw [← VB.functor.map_comp, Iso.hom_inv_id_app]
    erw [VB.functor.map_id, Category.comp_id, ← T'.map_comp_assoc,
      Iso.hom_inv_id_app]
    erw [T'.map_id, Category.id_comp]
  have htranspose (K : DA) :
      FB'.map ((normalizedMateTransport ρA ρB δX δY
        (mateEquiv adjA adjB q.inv).natTrans).app K) ≫
          adjB'.counit.app (T'.obj (VA.functor.obj K)) =
        q'.inv.app (GA'.obj (VA.functor.obj K)) ≫
          T'.map (adjA'.counit.app (VA.functor.obj K)) := by
    have hBc : FB'.map (ρB.hom.app (T.obj K)) ≫
        adjB'.counit.app (VB.functor.obj (T.obj K)) =
          cB.inv.app (GB.obj (T.obj K)) ≫
            VB.functor.map (adjB.counit.app (T.obj K)) := by
      apply (cancel_epi (cB.hom.app (GB.obj (T.obj K)))).1
      simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using hcB (T.obj K)
    have hAc : cA.inv.app (GA.obj K) ≫ VA.functor.map (adjA.counit.app K) =
        FA'.map (ρA.hom.app K) ≫ adjA'.counit.app (VA.functor.obj K) := by
      rw [← hcA K]
      simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    have hnB := adjB'.counit.naturality (δY.inv.app K)
    have hnC := cB.inv.naturality ((mateEquiv adjA adjB q.inv).app K)
    have hnY := δY.hom.naturality (adjA.counit.app K)
    have hnQ := q'.inv.naturality (ρA.hom.app K)
    dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_map] at hnB hnC hnY hnQ
    apply (cancel_epi (FB'.map (S'.map (ρA.hom.app K)))).1
    dsimp only [normalizedMateTransport, NatTrans.comp_app,
      whiskerRight_app, whiskerLeft_app]
    simp only [FB'.map_comp, Category.assoc]
    rw [← FB'.map_comp_assoc, ← S'.map_comp, Iso.hom_inv_id_app,
      S'.map_id, FB'.map_id, Category.id_comp]
    rw [hnB, reassoc_of% hBc, reassoc_of% hnC,
      ← VB.functor.map_comp_assoc, mateEquiv_counit, VB.functor.map_comp_assoc,
      reassoc_of% (hsq (GA.obj K)), ← reassoc_of% hnY]
    simp only [Iso.hom_inv_id_app]
    erw [Category.comp_id]
    rw [← T'.map_comp, hAc, T'.map_comp, ← reassoc_of% hnQ]
  have hident : normalizedMateTransport ρA ρB δX δY
      (mateEquiv adjA adjB q.inv).natTrans =
        whiskerLeft VA.functor (mateEquiv adjA' adjB' q'.inv).natTrans := by
    ext K
    apply (adjB'.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, whiskerLeft_app]
    rw [htranspose, mateEquiv_counit]
  have : IsIso (mateEquiv adjA adjB q.inv).natTrans :=
    (normalizedRightMate FA GA HA FB GB HB adjA adjB γA γB S T q a hnorm).2
  have htransport : IsIso (normalizedMateTransport ρA ρB δX δY
      (mateEquiv adjA adjB q.inv).natTrans) := by
    unfold normalizedMateTransport
    infer_instance
  have hreplace (K : DA) (K' : DA') (j : VA.functor.obj K ≅ K') :
      (mateEquiv adjA' adjB' q'.inv).app K' =
        S'.map (GA'.map j.inv) ≫
          (normalizedMateTransport ρA ρB δX δY
            (mateEquiv adjA adjB q.inv).natTrans).app K ≫ GB'.map (T'.map j.hom) := by
    rw [hident]
    dsimp only [whiskerLeft_app]
    have hn := (mateEquiv adjA' adjB' q'.inv).natTrans.naturality j.hom
    dsimp only [Functor.comp_map] at hn
    apply (cancel_epi (S'.map (GA'.map j.hom))).1
    simp only [← S'.map_comp_assoc, ← GA'.map_comp,
      Iso.hom_inv_id, GA'.map_id, S'.map_id, Category.id_comp]
    exact hn
  have : ∀ K' : DA', IsIso ((mateEquiv adjA' adjB' q'.inv).natTrans.app K') := by
    intro K'
    change IsIso ((mateEquiv adjA' adjB' q'.inv).app K')
    rw [hreplace (VA.inverse.obj K') K' (VA.counitIso.app K')]
    infer_instance
  exact ⟨htranspose, hident, htransport, NatIso.isIso_of_isIso_app _, hreplace⟩

end CategoryTheory
