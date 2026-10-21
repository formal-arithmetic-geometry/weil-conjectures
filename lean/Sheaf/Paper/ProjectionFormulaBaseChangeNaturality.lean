/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange
public import Sheaf.Paper.ProjectionMateExact
public import Sheaf.Paper.ProjectionFormulaArrows
import Sheaf.Paper.ProjectionMateSquareCoherence
import Sheaf.Paper.ProjectionFormulaTotalization
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.ProEtaleProjectionFormulaTensorCoherence

/-!
# Operator and base-change naturality of the projection formula

Source: blueprint, proper base change, order 1274; Stacks Tags 0B56, 0944 and 0E48
(blueprint: lemma-weil-pbc-projection-formula-base-change-naturality).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u w v u' v'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Naturality in the first variable of the specified counit mate for an arbitrary coefficient.
Source: Stacks 0B56 and blueprint order 1274, paragraph 1
(blueprint: lemma-weil-pbc-projection-formula-base-change-naturality).
Proof: transpose both composites under adj. Naturality of alpha identifies the second
transpose with counit tensor identity followed by u tensor identity. Naturality of the
counit identifies it with the first transpose. Injectivity of the Hom equivalence
proves equality. This applies to every u and in particular to endomorphisms. -/
theorem derivedProjectionFormulaMate_naturality
    {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]
    (L : A ⥤ B) (V : B ⥤ A) (adj : L ⊣ V)
    (TR : A × A ⥤ A) (TS : B × B ⥤ B)
    (alpha : TR ⋙ L ≅ (L.prod L) ⋙ TS)
    (E E' : B) (Q : A) (q : E ⟶ E') :
    derivedProjectionFormulaMate L V adj TR TS alpha E Q ≫
        V.map (TS.map (Prod.mkHom q (𝟙 (L.obj Q)))) =
      TR.map (Prod.mkHom (V.map q) (𝟙 Q)) ≫
        derivedProjectionFormulaMate L V adj TR TS alpha E' Q := by
  exact (congrArg (fun t ↦ t.app Q)
    ((adj.rightAdjointProjectionMap (T_C := Functor.curry.obj TS)
      (T_D := Functor.curry.obj TR)
      (Functor.curry.map alpha.hom ≫ (Functor.curryObjProdComp L L TS).hom)).naturality q)).symm

/-- Transport the two arrows along the specified coefficient isomorphism and its pullback.
These are the reduction identifications of blueprint order 1274, not new choices of maps.
Source: blueprint order 1274 (blueprint: lemma-weil-pbc-projection-formula-base-change-naturality).
-/
noncomputable def transportTensorProjectionArrows
    {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]
    (L : A ⥤ B) (V : B ⥤ A) (TR : A × A ⥤ A) (TS : B × B ⥤ B)
    (E : B) (F Q : A) (e : F ≅ Q)
    (arrows : (TR.obj (V.obj E, F) ⟶ V.obj (TS.obj (E, L.obj F))) ×
      (V.obj (TS.obj (E, L.obj F)) ⟶ TR.obj (V.obj E, F))) :
    (TR.obj (V.obj E, Q) ⟶ V.obj (TS.obj (E, L.obj Q))) ×
      (V.obj (TS.obj (E, L.obj Q)) ⟶ TR.obj (V.obj E, Q)) :=
  ⟨TR.map (Prod.mkHom (𝟙 (V.obj E)) e.inv) ≫ arrows.1 ≫
      V.map (TS.map (Prod.mkHom (𝟙 E) (L.map e.hom))),
    V.map (TS.map (Prod.mkHom (𝟙 E) (L.map e.inv))) ≫ arrows.2 ≫
      TR.map (Prod.mkHom (𝟙 (V.obj E)) e.hom)⟩

private theorem transportTensorProjectionArrows_mate
    {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]
    (L : A ⥤ B) (V : B ⥤ A) (adj : L ⊣ V)
    (TR : A × A ⥤ A) (TS : B × B ⥤ B)
    (alpha : TR ⋙ L ≅ (L.prod L) ⋙ TS)
    (E : B) (F Q : A) (e : F ≅ Q)
    (rho : V.obj (TS.obj (E, L.obj F)) ⟶ TR.obj (V.obj E, F)) :
    (transportTensorProjectionArrows L V TR TS E F Q e
      (derivedProjectionFormulaMate L V adj TR TS alpha E F, rho)).1 =
        derivedProjectionFormulaMate L V adj TR TS alpha E Q := by
  have hn := ((adj.rightAdjointProjectionMap (T_C := Functor.curry.obj TS)
    (T_D := Functor.curry.obj TR)
    (Functor.curry.map alpha.hom ≫ (Functor.curryObjProdComp L L TS).hom)).app E).naturality
      e.hom
  change TR.map (Prod.mkHom (𝟙 _) e.hom) ≫
      derivedProjectionFormulaMate L V adj TR TS alpha E Q =
    derivedProjectionFormulaMate L V adj TR TS alpha E F ≫
      V.map (TS.map (Prod.mkHom (𝟙 _) (L.map e.hom))) at hn
  dsimp only [transportTensorProjectionArrows]
  rw [← hn, ← Category.assoc, ← TR.map_comp]
  simp

private theorem transportTensorProjectionArrows_inverse
    {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]
    (L : A ⥤ B) (V : B ⥤ A) (TR : A × A ⥤ A) (TS : B × B ⥤ B)
    (E : B) (F Q : A) (e : F ≅ Q)
    (arrows : (TR.obj (V.obj E, F) ⟶ V.obj (TS.obj (E, L.obj F))) ×
      (V.obj (TS.obj (E, L.obj F)) ⟶ TR.obj (V.obj E, F)))
    (h : arrows.1 ≫ arrows.2 = 𝟙 _ ∧ arrows.2 ≫ arrows.1 = 𝟙 _) :
    let t := transportTensorProjectionArrows L V TR TS E F Q e arrows
    t.1 ≫ t.2 = 𝟙 _ ∧ t.2 ≫ t.1 = 𝟙 _ := by
  let p : TR.obj (V.obj E, F) ≅ V.obj (TS.obj (E, L.obj F)) :=
    ⟨arrows.1, arrows.2, h.1, h.2⟩
  let t := (TR.mapIso ((Iso.refl (V.obj E)).prod e)).symm ≪≫ p ≪≫
    V.mapIso (TS.mapIso ((Iso.refl E).prod (L.mapIso e)))
  dsimp only [transportTensorProjectionArrows]
  constructor
  · simpa only [t, p, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
      Functor.mapIso_inv, Iso.symm_hom, Iso.symm_inv, Iso.prod_hom, Iso.prod_inv,
      Iso.refl_hom, Iso.refl_inv, Category.assoc] using t.hom_inv_id
  · simpa only [t, p, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
      Functor.mapIso_inv, Iso.symm_hom, Iso.symm_inv, Iso.prod_hom, Iso.prod_inv,
      Iso.refl_hom, Iso.refl_inv, Category.assoc] using t.inv_hom_id

private theorem transportTensorProjectionArrows_naturality
    {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]
    (L : A ⥤ B) (V : B ⥤ A) (adj : L ⊣ V)
    (TR : A × A ⥤ A) (TS : B × B ⥤ B)
    (alpha : TR ⋙ L ≅ (L.prod L) ⋙ TS)
    (E E' : B) (F Q : A) (e : F ≅ Q) (q : E ⟶ E')
    (arrows : (TR.obj (V.obj E, F) ⟶ V.obj (TS.obj (E, L.obj F))) ×
      (V.obj (TS.obj (E, L.obj F)) ⟶ TR.obj (V.obj E, F)))
    (arrows' : (TR.obj (V.obj E', F) ⟶ V.obj (TS.obj (E', L.obj F))) ×
      (V.obj (TS.obj (E', L.obj F)) ⟶ TR.obj (V.obj E', F)))
    (hfst : arrows.1 = derivedProjectionFormulaMate L V adj TR TS alpha E F)
    (hfst' : arrows'.1 = derivedProjectionFormulaMate L V adj TR TS alpha E' F)
    (hi : arrows.1 ≫ arrows.2 = 𝟙 _ ∧ arrows.2 ≫ arrows.1 = 𝟙 _)
    (hi' : arrows'.1 ≫ arrows'.2 = 𝟙 _ ∧ arrows'.2 ≫ arrows'.1 = 𝟙 _) :
    let t := transportTensorProjectionArrows L V TR TS E F Q e arrows
    let t' := transportTensorProjectionArrows L V TR TS E' F Q e arrows'
    t.1 ≫ V.map (TS.map (Prod.mkHom q (𝟙 (L.obj Q)))) =
        TR.map (Prod.mkHom (V.map q) (𝟙 Q)) ≫ t'.1 ∧
      t.2 ≫ TR.map (Prod.mkHom (V.map q) (𝟙 Q)) =
        V.map (TS.map (Prod.mkHom q (𝟙 (L.obj Q)))) ≫ t'.2 := by
  let t := transportTensorProjectionArrows L V TR TS E F Q e arrows
  let t' := transportTensorProjectionArrows L V TR TS E' F Q e arrows'
  have ht : t.1 = derivedProjectionFormulaMate L V adj TR TS alpha E Q := by
    change TR.map (Prod.mkHom (𝟙 _) e.inv) ≫ arrows.1 ≫ _ = _
    rw [hfst]
    exact transportTensorProjectionArrows_mate L V adj TR TS alpha E F Q e arrows.2
  have ht' : t'.1 = derivedProjectionFormulaMate L V adj TR TS alpha E' Q := by
    change TR.map (Prod.mkHom (𝟙 _) e.inv) ≫ arrows'.1 ≫ _ = _
    rw [hfst']
    exact transportTensorProjectionArrows_mate L V adj TR TS alpha E' F Q e arrows'.2
  have hi := transportTensorProjectionArrows_inverse L V TR TS E F Q e arrows hi
  have hi' := transportTensorProjectionArrows_inverse L V TR TS E' F Q e arrows' hi'
  change t.1 ≫ t.2 = 𝟙 _ ∧ t.2 ≫ t.1 = 𝟙 _ at hi
  change t'.1 ≫ t'.2 = 𝟙 _ ∧ t'.2 ≫ t'.1 = 𝟙 _ at hi'
  change t.1 ≫ _ = _ ≫ t'.1 ∧ t.2 ≫ _ = _ ≫ t'.2
  have hn : t.1 ≫ V.map (TS.map (Prod.mkHom q (𝟙 (L.obj Q)))) =
      TR.map (Prod.mkHom (V.map q) (𝟙 Q)) ≫ t'.1 := by
    rw [ht, ht']
    exact derivedProjectionFormulaMate_naturality L V adj TR TS alpha E E' Q q
  refine ⟨hn, ?_⟩
  calc
    t.2 ≫ TR.map (Prod.mkHom (V.map q) (𝟙 Q)) =
        t.2 ≫ TR.map (Prod.mkHom (V.map q) (𝟙 Q)) ≫ t'.1 ≫ t'.2 := by
          simp only [hi'.1, Category.comp_id]
    _ = t.2 ≫ (t.1 ≫ V.map (TS.map (Prod.mkHom q (𝟙 (L.obj Q))))) ≫ t'.2 := by
      simp only [Category.assoc] at hn ⊢
      rw [← reassoc_of% hn]
    _ = V.map (TS.map (Prod.mkHom q (𝟙 (L.obj Q)))) ≫ t'.2 := by
      simp only [← Category.assoc, hi.2, Category.id_comp]

end CategoryTheory

namespace SheafOfModules

/-- Naturality in K of the actual mate and specified finite-total inverse. Taking E'=E
and phi an endomorphism gives exactly the two displayed operator equations.
All representative and adjunction arguments are those of the recorded arrows, so rho is
the image of the specified total chain map, rather than a separately assumed inverse.
The coefficient complex F represents any chosen Q_n, independently of its index n.
Qn and eQ implement an optional specified reduction representative; the identity
isomorphism includes the original untransported equations.
Source: Stacks 0B56, 0944 and blueprint order 1274, paragraphs 1 and 2
(blueprint: lemma-weil-pbc-projection-formula-base-change-naturality).
Proof: apply first-variable naturality to phi and the coefficient Q(F). The induced map
on E tensor LF(Q(F)) is precisely phi tensor identity. The totalization theorem gives
both inverse identities for the two components of ringedProjectionFormulaArrows.
Compose the first naturality equation with rho on both sides and cancel pi rho and
rho pi. This gives the second displayed equality. Specified coefficient isomorphisms
Q(F) to reduction objects, and their derived pullbacks, transport both equalities by
conjugation. No global strict-perfect representative is required of arbitrary perfect objects. -/
theorem ringedProjectionFormula_operator_naturality
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{u}} {S RI : Sheaf JD CommRingCat.{u}}
    (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (uPush : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R), uStar.obj M = changeOfRings
        c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (a : M ⟶ N), uStar.map a =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))]
    (LF : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ)))
    (PR : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ))
    (PS : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) ℤ))
    (hPR : ∀ P, PR P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (hPS : ∀ P, PS P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (TR : (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) × (DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
    (TS : (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) × (DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (rR : (PR.ι.prod PR.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) _
          (SheafOfModules.monoidalCategory R)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PR.ι ⋙ DerivedCategory.Q).prod (PR.ι ⋙ DerivedCategory.Q)) ⋙ TR)
    (rS : (PS.ι.prod PS.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) _
          (SheafOfModules.monoidalCategory S)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PS.ι ⋙ DerivedCategory.Q).prod (PS.ι ⋙ DerivedCategory.Q)) ⋙ TS)
    (k : CanonicalRingedTensorComparison R S RI uInv I c uStar hobj)
    (V : SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⥤
      SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (am :
      uStar ⊣ V)
    [V.Additive]
    (RF : DerivedCategory (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)) ⥤ DerivedCategory (SheafOfModules.{u} ((sheafCompose JC (forget₂
      CommRingCat.{u} RingCat.{u})).obj R)))
    (eta : V.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (hRF : ∀ G : DerivedCategory (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)) ⥤ DerivedCategory (SheafOfModules.{u} ((sheafCompose JC (forget₂
      CommRingCat.{u} RingCat.{u})).obj R)),
      Function.Bijective (fun b : RF ⟶ G ↦ eta ≫ Functor.whiskerLeft DerivedCategory.Qh b))
    (computeR : ∀ K : CochainComplex (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)) ℤ, K.IsKInjective →
      IsIso (derivedPushforwardComplexComparison V RF eta K))
    (computeL : ∀ P : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ,
      P.IsAcyclicTensorKFlat → (∀ n : ℤ, (P.X n).IsFlat) →
        IsIso (derivedPullbackComplexComparison uStar LF epsilon P))
    (adjD : LF ⊣ RF)
    (canonicalAdj : ∀ K : CochainComplex (SheafOfModules.{u} ((sheafCompose JD (forget₂
      CommRingCat.{u} RingCat.{u})).obj S)) ℤ, K.IsKInjective →
      LF.map (derivedPushforwardComplexComparison V RF eta K) ≫
          adjD.counit.app (DerivedCategory.Q.obj K) =
        derivedPullbackComplexComparison uStar LF epsilon
          ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
            DerivedCategory.Q.map ((am.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K))
    (E : DerivedCategory (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S))) (K : CochainComplex (SheafOfModules.{u} ((sheafCompose JD (forget₂
      CommRingCat.{u} RingCat.{u})).obj S)) ℤ) (hK : K.IsKInjective)
    (repE : E ≅ DerivedCategory.Q.obj K)
    (F : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ)
    (P : StrictPerfectCoefficientPackage ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R) F)
    (hbounded : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r))
    (E' : DerivedCategory (SheafOfModules.{u} ((sheafCompose JD
      (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (K' : CochainComplex (SheafOfModules.{u} ((sheafCompose JD
      (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) ℤ)
    (hK' : K'.IsKInjective) (repE' : E' ≅ DerivedCategory.Q.obj K') (phi : E ⟶ E')
    (Qn : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
    (eQ : DerivedCategory.Q.obj F ≅ Qn) :
    (transportTensorProjectionArrows LF RF TR TS E (DerivedCategory.Q.obj F) Qn eQ
      (ringedProjectionFormulaArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF
      PR PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj
      E K hK repE F P hbounded)).1 ≫
        RF.map (TS.map (Prod.mkHom phi (𝟙 (LF.obj Qn)))) =
      TR.map (Prod.mkHom (RF.map phi) (𝟙 Qn)) ≫
        (transportTensorProjectionArrows LF RF TR TS E' (DerivedCategory.Q.obj F) Qn eQ
      (ringedProjectionFormulaArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF
      PR PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj
      E' K' hK' repE' F P hbounded)).1 ∧
    (transportTensorProjectionArrows LF RF TR TS E (DerivedCategory.Q.obj F) Qn eQ
      (ringedProjectionFormulaArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF
      PR PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj
      E K hK repE F P hbounded)).2 ≫
        TR.map (Prod.mkHom (RF.map phi) (𝟙 Qn)) =
      RF.map (TS.map (Prod.mkHom phi (𝟙 (LF.obj Qn)))) ≫
        (transportTensorProjectionArrows LF RF TR TS E' (DerivedCategory.Q.obj F) Qn eQ
      (ringedProjectionFormulaArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF
      PR PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj
      E' K' hK' repE' F P hbounded)).2 := by
  let alpha := ringedTopoiCanonicalDerivedTensorComparison uInv uPush adj I c uStar
    hobj hmap LF epsilon hLF PR PS hPR hPS TR TS rR rS k V am
  let arrows := ringedProjectionFormulaArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF
    PR PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj
    E K hK repE F P hbounded
  let arrows' := ringedProjectionFormulaArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF
    PR PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj
    E' K' hK' repE' F P hbounded
  apply transportTensorProjectionArrows_naturality LF RF adjD TR TS alpha E E'
    (DerivedCategory.Q.obj F) Qn eQ phi arrows arrows'
  · unfold arrows ringedProjectionFormulaArrows
    rfl
  · unfold arrows' ringedProjectionFormulaArrows
    rfl
  · exact ringedProjectionFormula_totalization uInv uPush adj I c uStar hobj hmap LF epsilon hLF
      PR PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj
      E K hK repE F P hbounded
  · exact ringedProjectionFormula_totalization uInv uPush adj I c uStar hobj hmap LF epsilon hLF
      PR PS hPR hPS TR TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj
      E' K' hK' repE' F P hbounded

end SheafOfModules

namespace AlgebraicGeometry.Scheme

/-- The projection arrow for arbitrary coefficients on the small ringed pro-etale sites.
It is exactly the existing counit mate using the uniquely normalized tensor comparison.
Source: Stacks 0B56 (blueprint: lemma-weil-pbc-projection-formula-base-change-naturality). -/
noncomputable def proEtaleProjectionFormulaMate
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
    (K : DerivedCategory (proEtaleRingModules X S))
    (Q : DerivedCategory (proEtaleRingModules Y R)) :=
  derivedProjectionFormulaMate (proEtaleRingDerivedPullback f R S c)
    (proEtaleRingDerivedDirectImage f R S c) (proEtaleRingDerivedAdjunction f R S c)
    a.tensor b.tensor (proEtaleCanonicalTensorComparison f R S c a b) K Q

/-- The two routes agree with the stated target identification on the actual ringed
pro-etale square. All coefficient objects are arbitrary in the unbounded categories.
Source: Stacks 07A7, 0B56 and 0E48; blueprint order 1274, paragraphs 2 and 3
(blueprint: lemma-weil-pbc-projection-formula-base-change-naturality).
Proof: the four coefficient identifications and hcoeff give a commutative square of
ringed topoi. The ambient exchange is the mate of the canonical composition comparison.
The projection arrows are mates of tensor comparison followed by counit tensor identity.
Apply ringed exchange tensor coherence, with the same K and Q. Alternatively transpose
both routes under the f' adjunction, use tensor compatibility of the composition
comparison on flat K-flat representatives, and naturality of the two counits. Both
transposes become the g' pullback of the f counit tensor identity. The last map of the
first route applies the g' tensor comparison and theta inverse to its coefficient
factor. This is exactly the specified target identification. Injectivity of the
adjunction bijection proves equality, without assuming any map invertible beyond the
canonical tensor and composition identifications. -/
theorem proEtaleProjectionFormula_baseChange
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RX' : Sheaf (ProEt.topology X') CommRingCat.{u + 1})
    (RY' : Sheaf (ProEt.topology Y') CommRingCat.{u + 1})
    (cf : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX)
    (cg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RY ≅ RY')
    (cg' : (proEtaleSheafInverseImage g' CommRingCat.{u + 1}).obj RX ≅ RX')
    (cf' : (proEtaleSheafInverseImage f' CommRingCat.{u + 1}).obj RY' ≅ RX')
    (hcoeff : HEq
      (proEtaleRingCompositeCoefficients g' f RY RX RX' cf cg')
      (proEtaleRingCompositeCoefficients f' g RY RY' RX' cg cf'))
    (aY : ProEtaleTensorModel Y RY) (aX : ProEtaleTensorModel X RX)
    (aY' : ProEtaleTensorModel Y' RY') (aX' : ProEtaleTensorModel X' RX')
    (K : DerivedCategory (proEtaleRingModules X RX))
    (Q : DerivedCategory (proEtaleRingModules Y RY)) :
    (proEtaleRingDerivedPullback g RY RY' cg).map
        (proEtaleProjectionFormulaMate f RY RX cf aY aX K Q) ≫
      (proEtaleAmbientRingedExchange sq RX RY RX' RY' cf cg cg' cf' hcoeff).app
        (aX.tensor.obj (K, (proEtaleRingDerivedPullback f RY RX cf).obj Q)) ≫
      (proEtaleRingDerivedDirectImage f' RY' RX' cf').map
        ((proEtaleCanonicalTensorComparison g' RX RX' cg' aX aX').hom.app
          (K, (proEtaleRingDerivedPullback f RY RX cf).obj Q) ≫
          aX'.tensor.map (Prod.mkHom
            (𝟙 ((proEtaleRingDerivedPullback g' RX RX' cg').obj K))
            ((proEtaleAmbientRingedPullbackComparison sq RX RY RX' RY'
              cf cg cg' cf' hcoeff).inv.app Q))) =
    (proEtaleCanonicalTensorComparison g RY RY' cg aY aY').hom.app
        ((proEtaleRingDerivedDirectImage f RY RX cf).obj K, Q) ≫
      aY'.tensor.map (Prod.mkHom
        ((proEtaleAmbientRingedExchange sq RX RY RX' RY' cf cg cg' cf' hcoeff).app K)
        (𝟙 ((proEtaleRingDerivedPullback g RY RY' cg).obj Q))) ≫
      proEtaleProjectionFormulaMate f' RY' RX' cf' aY' aX'
        ((proEtaleRingDerivedPullback g' RX RX' cg').obj K)
        ((proEtaleRingDerivedPullback g RY RY' cg).obj Q)  := by
  let theta := proEtaleAmbientRingedPullbackComparison sq RX RY RX' RY' cf cg cg' cf' hcoeff
  have hc : ∀ P Q : DerivedCategory (proEtaleRingModules Y RY),
      theta.hom.app (aY.tensor.obj (P, Q)) ≫
          (proEtaleRingDerivedPullback g' RX RX' cg').map
            ((proEtaleCanonicalTensorComparison f RY RX cf aY aX).hom.app (P, Q)) ≫
          (proEtaleCanonicalTensorComparison g' RX RX' cg' aX aX').hom.app
            ((proEtaleRingDerivedPullback f RY RX cf).obj P,
              (proEtaleRingDerivedPullback f RY RX cf).obj Q) =
        (proEtaleRingDerivedPullback f' RY' RX' cf').map
            ((proEtaleCanonicalTensorComparison g RY RY' cg aY aY').hom.app (P, Q)) ≫
          (proEtaleCanonicalTensorComparison f' RY' RX' cf' aY' aX').hom.app
            ((proEtaleRingDerivedPullback g RY RY' cg).obj P,
              (proEtaleRingDerivedPullback g RY RY' cg).obj Q) ≫
          aX'.tensor.map (Prod.mkHom (theta.hom.app P) (theta.hom.app Q)) := by
    intro P Q
    exact proEtaleProjectionFormula_tensor_coherence sq RX RY RX' RY' cf cg cg' cf'
      hcoeff aY aX aY' aX' P Q
  let adjF := proEtaleRingDerivedAdjunction f RY RX cf
  let adjK := proEtaleRingDerivedAdjunction f' RY' RX' cf'
  let tF := proEtaleCanonicalTensorComparison f RY RX cf aY aX
  let tG := proEtaleCanonicalTensorComparison g RY RY' cg aY aY'
  let tH := proEtaleCanonicalTensorComparison g' RX RX' cg' aX aX'
  let tK := proEtaleCanonicalTensorComparison f' RY' RX' cf' aY' aX'
  have hmain := CategoryTheory.projectionMate_square_of_tensor_coherence_projection
    adjF adjK aY.tensor aX.tensor aY'.tensor aX'.tensor
    tF tG.hom tH.hom tK theta hc K Q
  rw [show proEtaleAmbientRingedExchange sq RX RY RX' RY' cf cg cg' cf' hcoeff =
      (mateEquiv (proEtaleRingDerivedAdjunction f RY RX cf)
        (proEtaleRingDerivedAdjunction f' RY' RX' cf')
        (TwoSquare.mk _ _ _ _ theta.hom)).natTrans from rfl]
  change (proEtaleRingDerivedPullback g RY RY' cg).map
      (derivedProjectionFormulaMate _ _ _ _ _ _ K Q) ≫ _ ≫ _ = _
  exact hmain

end AlgebraicGeometry.Scheme
