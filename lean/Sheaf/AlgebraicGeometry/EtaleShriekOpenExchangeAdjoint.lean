module

public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import Sheaf.AlgebraicGeometry.OpenExchangeTower

/-!
# Open compact-support exchange and the extension-composition mate

Source: literature/stacks-project/more-etale.tex, Tags 0F7B, 0F7J and 0F7L
(blueprint: lem-amb-shriek-open-exchange-adjoint).
-/


open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Etale

@[expose] public section

namespace AlgebraicGeometry.Etale

-- Re-recorded by Q87 for the stage-2 delivery on 2026-10-18.

universe u

set_option autoImplicit false

/-- The extension/composition comparison `δ : Rf_! Dv_! ≅ Du_! Rf_{U!}` of the node, namely
`α_{u,f_U}⁻¹ ∘ α_{f,v}` with compact support along the opens `v` and `u` identified with
termwise extension by zero through the compactification `(w, 𝟙)`
(`rightDerivedLowerShriekIsoOfIsOpenImmersion`) and the refinement comparisons.
Source: Stacks Project, Tags 0F7B, 0F7J and 0F7L
(blueprint: lem-amb-shriek-open-exchange-adjoint).
-/
noncomputable def openExchangeIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U S : Scheme.{u}} {f : X ⟶ S} (u : U ⟶ S)
    [IsOpenImmersion u] [IsNoetherian X] [IsNoetherian U] [IsNoetherian S]
    [IsNoetherian (pullback f u)] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [HasCompactification f] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) (pullback.fst f u)).mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f u) ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) u).mapDerivedCategory :=
  Functor.isoWhiskerRight
      (rightDerivedLowerShriekIsoOfIsOpenImmersion A (pullback.fst f u)).symm
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) ≪≫
    unboundedEtaleLowerShriekCompIso A (pullback.fst f u) f ≪≫
    unboundedEtaleLowerShriekCongr A (pullback.condition) ≪≫
    (unboundedEtaleLowerShriekCompIso A (pullback.snd f u) u).symm ≪≫
    Functor.isoWhiskerLeft
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f u))
      (rightDerivedLowerShriekIsoOfIsOpenImmersion A u)

/-- The canonical compact-support exchange for the cartesian square of an open immersion.
Source: Stacks Project, Tag 0F7L (blueprint: lem-amb-shriek-open-exchange-adjoint).
-/
noncomputable def canonicalCompactSupportExchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U S : Scheme.{u}} {f : X ⟶ S} (u : U ⟶ S)
    [IsOpenImmersion u] [IsNoetherian X] [IsNoetherian U] [IsNoetherian S]
    [IsNoetherian (pullback f u)] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [HasCompactification f] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
        (upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst f u)).mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f u) := by
  let sq : IsPullback (pullback.fst f u) (pullback.snd f u) f u :=
    IsPullback.of_hasPullback f u
  letI : IsIso (unboundedEtaleCompactSupportBaseChange A sq) :=
    (unboundedEtaleCompactSupport_baseChange A sq).1
  exact asIso (unboundedEtaleCompactSupportBaseChange A sq)

private theorem conjugate_leftAdjointUniq {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (e : R₁ ≅ R₂) :
    (conjugateEquiv adj₁ adj₂).symm e.hom =
      (adj₁.leftAdjointUniq (adj₂.ofNatIsoRight e.symm)).inv := by
  apply NatTrans.ext
  funext X
  apply (adj₂.homEquiv X _).injective
  rw [Adjunction.homEquiv_unit, ← unit_conjugateEquiv_symm]
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (adj₂.ofNatIsoRight e.symm) adj₁ X
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  rw [Adjunction.leftAdjointUniq_inv_app]
  apply (cancel_mono (e.inv.app _)).1
  rw [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  simpa only [Category.comp_id, Category.comp_id, Iso.symm_hom] using h.symm

private theorem comp_conjugate (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (j : X ⟶ Y) (k : Y ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion k] (h : X ⟶ Z) [IsOpenImmersion h]
    (w : h = j ≫ k) :
    (conjugateEquiv
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) h)
      ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).comp
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) k))).symm
      (upperStarComp (ModuleCat.{u + 1} A) j k h w).hom =
    (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) j k).inv ≫
      eqToHom (by subst h; rfl) := by
  subst h
  rw [eqToHom_refl, Category.comp_id]
  exact conjugate_leftAdjointUniq _ _ _



private theorem open_square_comp (A : Type (u + 1)) [CommRing A]
    {U' U Z' Z : Scheme.{u}}
    {v : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {b : Z' ⟶ Z}
    [IsOpenImmersion v] [IsOpenImmersion b]
    [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : CommSq v j' j b) :
    let va := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v
    let ba := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b
    let ja := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
    let j'a := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j'
    ((conjugateIsoEquiv (va.comp ja) (j'a.comp ba)).symm
      (squareUpperStarIso (ModuleCat.{u + 1} A) sq.flip)).hom =
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) j' b).inv ≫
        eqToHom (by simp only [sq.w]) ≫
        (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) v j).hom := by
  dsimp only
  rw [conjugateIsoEquiv_symm_apply_hom]
  simp only [squareUpperStarIso, Iso.trans_hom, Iso.symm_hom]
  rw [← conjugateEquiv_symm_comp _
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (j' ≫ b))]
  rw [comp_conjugate A j' b (j' ≫ b) rfl]
  simp only [eqToHom_refl, Category.comp_id]
  congr 1
  have hc := comp_conjugate A v j (j' ≫ b) sq.w.symm
  have hi : (conjugateIsoEquiv
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (j' ≫ b))
      ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v).comp
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j))).symm
      (upperStarComp (ModuleCat.{u + 1} A) v j (j' ≫ b) sq.w.symm) =
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) v j).symm ≪≫
        eqToIso (by simp only [sq.w]) := Iso.ext hc
  exact congrArg Iso.inv hi

private theorem open_base_change_mate (A : Type (u + 1)) [CommRing A]
    {U' U Z' Z : Scheme.{u}}
    {v : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {b : Z' ⟶ Z}
    [IsOpenImmersion v] [IsOpenImmersion b]
    [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : CommSq v j' j b) :
    openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} A) sq =
      ((mateEquiv
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j')).symm
        (TwoSquare.mk _ _ _ _
          (squareUpperStarIso (ModuleCat.{u + 1} A) sq.flip).hom)).natTrans := by
  let ja := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  let j'a := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j'
  let va := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v
  let ba := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) b
  let tau := TwoSquare.mk _ _ _ _ (squareUpperStarIso (ModuleCat.{u + 1} A) sq.flip).hom
  let beta := (mateEquiv ja j'a).symm tau
  change (conjugateEquiv (ja.comp ba) (va.comp j'a)).symm
    (mateEquiv ba va tau).natTrans = beta.natTrans
  apply (conjugateEquiv (ja.comp ba) (va.comp j'a)).injective
  rw [Equiv.apply_symm_apply]
  have hi := iterated_mateEquiv_conjugateEquiv ja j'a va ba beta
  rw [Equiv.apply_symm_apply] at hi
  exact hi

private theorem open_square_mate (A : Type (u + 1)) [CommRing A]
    {U' U Z' Z : Scheme.{u}}
    {v : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {b : Z' ⟶ Z}
    [IsOpenImmersion v] [IsOpenImmersion b]
    [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback v j' j b) :
    let va := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v
    let ba := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b
    let ja := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
    let j'a := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j'
    let a := (conjugateIsoEquiv (va.comp ja) (j'a.comp ba)).symm
      (squareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq.flip)
    (mateEquiv va ba (TwoSquare.mk _ _ _ _ a.hom)).natTrans =
      openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq := by
  dsimp only
  let va := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v
  let ba := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b
  let ja := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  let j'a := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j'
  let a := (conjugateIsoEquiv (va.comp ja) (j'a.comp ba)).symm
    (squareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq.flip)
  change (mateEquiv va ba (TwoSquare.mk _ _ _ _ a.hom)).natTrans = _
  rw [open_base_change_mate A sq.toCommSq]
  apply congrArg TwoSquare.natTrans
  apply (mateEquiv ja j'a).injective
  rw [Equiv.apply_symm_apply]
  apply TwoSquare.ext
  intro M
  have hi := iterated_mateEquiv_conjugateEquiv va ba j'a ja
    (TwoSquare.mk _ _ _ _ a.hom)
  have hi' := congr_app hi M
  simpa [a] using hi'

private theorem derived_open_square_mate (A : Type (u + 1)) [CommRing A]
    {U' U Z' Z : Scheme.{u}}
    {v : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {b : Z' ⟶ Z}
    [IsOpenImmersion v] [IsOpenImmersion b]
    [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback v j' j b) :
    let va := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v
    let ba := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b
    let ja := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
    let j'a := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j'
    let a := (conjugateIsoEquiv (va.comp ja) (j'a.comp ba)).symm
      (squareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq.flip)
    (Functor.mapDerivedCategorySquareIso a).hom =
      ((mateEquiv
        (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v)
        (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b)).symm
        (TwoSquare.mk _ _ _ _
          (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
            (ModuleCat.{u + 1} A) sq).hom)).natTrans := by
  dsimp only
  let va := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v
  let ba := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b
  let ja := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  let j'a := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j'
  let a := (conjugateIsoEquiv (va.comp ja) (j'a.comp ba)).symm
    (squareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq.flip)
  let beta := @asIso _ _ _ _ _
    (isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} A) sq)
  have hm := open_square_mate A sq
  change (mateEquiv va ba (TwoSquare.mk _ _ _ _ a.hom)).natTrans = beta.hom at hm
  have hu (K : Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      ba.unit.app _ ≫ (upperStar (ModuleCat.{u + 1} A) b).map (a.hom.app K) =
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j').map (va.unit.app K)) ≫
          beta.hom.app _ := by
    rw [← hm]
    exact (unit_mateEquiv va ba (TwoSquare.mk _ _ _ _ a.hom) K).symm
  have hd (K : DerivedCategoryModule A U') :=
    Adjunction.mapDerivedCategoryAdjunction_mate va ba beta a hu K
  let ad := (Functor.mapDerivedCategorySquareIso a).hom
  let betad := (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
    (ModuleCat.{u + 1} A) sq).hom
  change ad = ((mateEquiv va.mapDerivedCategoryAdjunction
    ba.mapDerivedCategoryAdjunction).symm (.mk _ _ _ _ betad)).natTrans
  ext K
  apply (ba.mapDerivedCategoryAdjunction.homEquiv _ _).injective
  change ba.mapDerivedCategoryAdjunction.unit.app _ ≫
    (upperStar (ModuleCat.{u + 1} A) b).mapDerivedCategory.map (ad.app K) = _
  rw [ba.mapDerivedCategoryAdjunction.homEquiv_unit]
  exact (hd K).trans
    (unit_mateEquiv_symm va.mapDerivedCategoryAdjunction
      ba.mapDerivedCategoryAdjunction (.mk _ _ _ _ betad) K)

private theorem interchange_mate
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {B : C ⥤ D} {R : D ⥤ C} {L : E ⥤ F} {S : F ⥤ E}
    (b : B ⊣ R) (l : L ⊣ S) [IsIso b.unit]
    (P : D ⥤ F) (Q : C ⥤ E)
    (ex : P ⋙ S ⟶ R ⋙ Q) (gam : Q ⋙ L ⟶ B ⋙ P)
    (H : C) (K : D) (beta : H ≅ R.obj K)
    (hg : l.homEquiv _ _ (gam.app H) ≫ ex.app (B.obj H) ≫
      Q.map ((asIso b.unit).inv.app H) = 𝟙 (Q.obj H)) :
    l.homEquiv _ _ (gam.app H ≫ P.map (B.map beta.hom ≫ b.counit.app K)) ≫
      ex.app K ≫ Q.map beta.inv = 𝟙 (Q.obj H) := by
  have hg' : l.homEquiv _ _ (gam.app H) ≫ ex.app (B.obj H) =
      Q.map (b.unit.app H) := by
    apply (cancel_mono (Q.map ((asIso b.unit).inv.app H))).1
    rw [Category.assoc, hg]
    simp
  have hb : b.unit.app H ≫ R.map (B.map beta.hom ≫ b.counit.app K) = beta.hom := by
    rw [R.map_comp, ← Functor.comp_map, ← b.unit.naturality_assoc]
    simp [b.right_triangle_components]
  have hn := ex.naturality (B.map beta.hom ≫ b.counit.app K)
  dsimp only [Functor.comp_map, Functor.id_obj] at hn
  rw [l.homEquiv_naturality_right, Category.assoc, ← Category.assoc
    (S.map (P.map _)), hn, ← Category.assoc, ← Category.assoc, hg']
  rw [← Q.map_comp, hb, ← Q.map_comp]
  simp

private theorem mate_transport
    {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {S : D ⥤ C} (l : L ⊣ S)
    {H H' : C} {K K' : D} (s : H' ≅ H) (t : K ≅ K')
    (g : L.obj H ⟶ K) (e : S.obj K ⟶ H)
    (h : l.homEquiv _ _ g ≫ e = 𝟙 H) :
    l.homEquiv _ _ (L.map s.hom ≫ g ≫ t.hom) ≫
      S.map t.inv ≫ e ≫ s.inv = 𝟙 H' := by
  rw [l.homEquiv_naturality_left, l.homEquiv_naturality_right]
  simp only [Category.assoc]
  rw [← S.map_comp_assoc, t.hom_inv_id, S.map_id, Category.id_comp]
  rw [← Category.assoc (l.homEquiv _ _ g), h]
  simp

attribute [local irreducible] lowerStar openImmersionLowerShriek upperStar
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

set_option maxRecDepth 10000 in
/-- The extension/composition comparison mate is the canonical compact-support exchange: for
`f : X ⟶ S` separated, of finite type and compactifiable, an open immersion `u : U ⟶ S`,
`v = pullback.fst f u` and `f_U = pullback.snd f u`, the map
`κ_F = Rf_!(ε_{v,F}) ∘ δ_{v^*F}⁻¹ : Du_! Rf_{U!} v^*F ⟶ Rf_! F` has adjunct `C_{f,u,F}⁻¹`
under `Du_! ⊣ u^*`; equivalently `κ_F = ε_{u,Rf_!F} ∘ Du_!(C_{f,u,F}⁻¹)`. No boundedness
assumption on `F` is made.
Source: Stacks Project, Tags 0F7B, 0F7J and 0F7L; etale-cohomology Tags 03S3,
03S6 and 0F70 (blueprint: lem-amb-shriek-open-exchange-adjoint).

Proof:
1. Choose a compactification `f = r ∘ j` and its pullback along `u`: open
   `b : X̄_U ⟶ X̄`, `j_U : X_U ⟶ X̄_U` and proper `r_U : X̄_U ⟶ U`. Put `J = Dj_!`,
   `J' = Dj_{U!}`, `V = Dv_!`, `B = Db_!`, `L = Du_!`, `P = Rr_*`, `P' = Rr_{U*}`. Let
   `a : JV ≅ BJ'` be the adjunction-normalized open composition identification for
   `j v = b j_U` (lem-cbc-extension-zero-composition). Compact support along an open `w`
   is identified with `Dw_!` by the compactification `(w, 𝟙)`; the sheaf counit for an
   open is evaluation (lem-weil-pbc-extension-by-zero-adjunction), with its termwise derived
   adjunction (lem-amb-etale-adjoint-locality). Let `Γ : L P' ≅ P B` be the interchange for
   the cartesian square `(b, r_U, r, u)` (lem-amb-unbounded-proper-open-interchange). The
   tower formula for `α` (lem-amb-unbounded-compact-support-comparisons) gives
   `δ_M⁻¹ = P(a_M⁻¹) ∘ Γ_{J'M}`: for `α_{f,v}` the tower square has identity bottom open and
   gives the open composition identification, for `α_{u,f_U}` it is the square
   `(b, r_U, r, u)`. All schemes are Noetherian, so the opens are quasi-compact of finite
   type, and the comparisons and interchange apply on the unbounded categories.
2. Write `E : u^* P ⟶ P' b^*` for proper exchange and `e : b^* J ≅ J' v^*` for the inverse
   open base-change comparison, so `C_F = P'(e_F) ∘ E_{JF}`
   (lem-amb-unbounded-compact-support-comparisons); `e` has the unit normalization of
   lem-cbc-derived-extension-zero-base-change-underived-compatibility. For `H = J' v^* F` put
   `h = J(ε_{v,F}) ∘ a_{v^*F}⁻¹ : B H ⟶ J F`. On an etale test object over `X̄_U` both
   `b^* B H` and `H` are extensions by zero from `X_U`; restricting to `X_U` identifies `a`,
   the restricted evaluation counit and `e` with identities, so
   `e_F ∘ b^* h ∘ η_{b,H} = 1_H`, first for sheaves and then degreewise on complexes. The
   cartesian clause of lem-amb-unbounded-proper-open-interchange says the adjunct of `Γ_H` is
   `λ_H⁻¹` with `λ_H = P'(η_{b,H}⁻¹) ∘ E_{BH}`, hence
   `E_{BH} ∘ u^*(Γ_H) ∘ η_{u,P'H} = P'(η_{b,H})`. By step 1, `κ_F = P(h) ∘ Γ_H`. For its
   adjunct `m_F = u^* κ_F ∘ η_{u,P'H}`, naturality of `E` in `h` gives
   `C_F ∘ m_F = P'(e_F) ∘ E_{JF} ∘ u^*P(h) ∘ u^*(Γ_H) ∘ η_{u,P'H}`
   `= P'(e_F ∘ b^* h) ∘ E_{BH} ∘ u^*(Γ_H) ∘ η_{u,P'H} = P'(e_F ∘ b^* h ∘ η_{b,H}) = 1_{P'H}`.
   Since `C_F` is an isomorphism, `m_F = C_F⁻¹`, the first conjunct.
3. The adjunction bijection for `Du_! ⊣ u^*` is injective, so the equality of adjuncts in
   step 2 gives `κ_F = ε_{u,Rf_!F} ∘ Du_!(C_F⁻¹)`, the second conjunct. Every comparison and
   adjunction used is constructed on the whole unbounded derived category, so `F` is
   arbitrary.
-/
theorem openExchange_adjunct
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U S : Scheme.{u}} {f : X ⟶ S} (u : U ⟶ S)
    [IsOpenImmersion u] [IsNoetherian X] [IsNoetherian U] [IsNoetherian S]
    [IsNoetherian (pullback f u)] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [HasCompactification f]
    (F : DerivedCategoryModule A X) :
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) u).homEquiv
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f u)).obj
        ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f u)).mapDerivedCategory.obj F))
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj F)
      ((openExchangeIso A u).inv.app
          ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f u)).mapDerivedCategory.obj F) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) (pullback.fst f u)).counit.app F)) =
      (canonicalCompactSupportExchange A u).inv.app F) ∧
    ((openExchangeIso A u).inv.app
          ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f u)).mapDerivedCategory.obj F) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) (pullback.fst f u)).counit.app F)) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) u).mapDerivedCategory.map
        ((canonicalCompactSupportExchange A u).inv.app F) ≫
      (derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) u).counit.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj F) := by
  let c := HasCompactification.compactification f
  let sq := IsPullback.of_hasPullback f u
  let cs := c.ofIsPullback sq
  let psq := IsPullback.of_hasPullback c.g u
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
  let J' := (openImmersionLowerShriek (ModuleCat.{u + 1} A) cs.i).mapDerivedCategory
  let V := (upperStar (ModuleCat.{u + 1} A) (pullback.fst f u)).mapDerivedCategory
  let B := (openImmersionLowerShriek (ModuleCat.{u + 1} A)
    (pullback.fst c.g u)).mapDerivedCategory
  let R := (upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g u)).mapDerivedCategory
  let L := (openImmersionLowerShriek (ModuleCat.{u + 1} A) u).mapDerivedCategory
  let P := rightDerivedLowerStar (ModuleCat.{u + 1} A) c.g
  let Q := rightDerivedLowerStar (ModuleCat.{u + 1} A) cs.g
  let b := derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) (pullback.fst c.g u)
  let l := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) u
  let t := rightDerivedLowerShriekIso A c
  let t' := rightDerivedLowerShriekIso A cs
  let beta := (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
    (ModuleCat.{u + 1} A) (c.isPullback_i_ofIsPullback sq)).app F
  let ex := exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) psq.toCommSq
  let gam := openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A) psq.flip
  let H := J'.obj (V.obj F)
  let K := J.obj F
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have : IsLocallyNoetherian (pullback c.g u) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd c.g u)
  have : CompactSpace (pullback c.g u : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd c.g u)
  have : IsNoetherian (pullback c.g u) := ⟨⟩
  have hg := unboundedEtaleCompactSupport_tower_adjunct A psq H
  change l.homEquiv _ _ (gam.app H) ≫ ex.app (B.obj H) ≫
    Q.map ((asIso b.unit).inv.app H) = 𝟙 (Q.obj H) at hg
  have hm := interchange_mate b l P Q ex gam H K beta hg
  let v := derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) (pullback.fst f u)
  let betanat := (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
    (ModuleCat.{u + 1} A) (c.isPullback_i_ofIsPullback sq)).hom
  let a := ((mateEquiv v b).symm (.mk _ _ _ _ betanat)).natTrans
  have ha : a.app (V.obj F) ≫ J.map (v.counit.app F) =
      B.map beta.hom ≫ b.counit.app K :=
    (mateEquiv_counit_symm v b (.mk _ _ _ _ betanat) F).symm
  have hraw := openExchange_tower A u c (V.obj F)
  dsimp only at hraw
  have hi := open_square_comp A (c.isPullback_i_ofIsPullback sq).toCommSq
  have hi' :
      (conjugateIsoEquiv
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
          (pullback.fst f u)).comp
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c.i))
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) cs.i).comp
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
            (pullback.fst c.g u)))).symm
        (squareUpperStarIso (ModuleCat.{u + 1} A)
          (c.isPullback_i_ofIsPullback sq).toCommSq.flip) =
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} A)
        cs.i (pullback.fst c.g u)).symm ≪≫
        eqToIso (by
          simp only [cs, Compactification.ofIsPullback_i_fst]) ≪≫
        openImmersionLowerShriekComp (ModuleCat.{u + 1} A) (pullback.fst f u) c.i := by
    apply Iso.ext
    exact hi
  rw [← hi'] at hraw
  rw [derived_open_square_mate A (c.isPullback_i_ofIsPullback sq)] at hraw
  change (openExchangeIso A u).inv.app (V.obj F) =
    L.map (t'.inv.app (V.obj F)) ≫ gam.app H ≫
      P.map (a.app (V.obj F)) ≫ t.hom.app _ at hraw
  have ht : (openExchangeIso A u).inv.app (V.obj F) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map (v.counit.app F) =
      L.map (t'.inv.app (V.obj F)) ≫ gam.app H ≫
        P.map (B.map beta.hom ≫ b.counit.app K) ≫ t.hom.app F := by
    rw [hraw]
    simp only [Category.assoc]
    erw [← t.hom.naturality (v.counit.app F)]
    change L.map (t'.inv.app (V.obj F)) ≫ gam.app H ≫ P.map (a.app (V.obj F)) ≫
      P.map (J.map (v.counit.app F)) ≫ t.hom.app F = _
    rw [← P.map_comp_assoc, ha]
  have hc := congr_app ((unboundedEtaleCompactSupport_baseChange A sq).2 c) F
  rw [unboundedEtaleCompactSupport_exchange_normalization A sq c] at hc
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.assoc] at hc
  change (canonicalCompactSupportExchange A u).hom.app F =
    ((upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory).map (t.inv.app F) ≫
      ex.app K ≫ Q.map beta.inv ≫ t'.hom.app (V.obj F) at hc
  have h : l.homEquiv _ _
      ((openExchangeIso A u).inv.app (V.obj F) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) (pullback.fst f u)).counit.app F)) =
      (canonicalCompactSupportExchange A u).inv.app F := by
    apply (cancel_mono ((canonicalCompactSupportExchange A u).hom.app F)).1
    rw [Iso.inv_hom_id_app]
    rw [ht, hc]
    simpa only [Category.assoc, Functor.id_obj, Functor.comp_obj,
      Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, L, V] using
      mate_transport l (t'.app (V.obj F)).symm (t.app F)
        (gam.app H ≫ P.map (B.map beta.hom ≫ b.counit.app K))
        (ex.app K ≫ Q.map beta.inv) hm
  refine ⟨h, ?_⟩
  have hc' := l.homEquiv_counit
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f u)).obj (V.obj F))
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj F)
    ((canonicalCompactSupportExchange A u).inv.app F)
  rw [← hc', ← h]
  exact ((l.homEquiv _ _).symm_apply_apply _).symm

end AlgebraicGeometry.Etale

end
