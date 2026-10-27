/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenSupportFactorModel
public import Sheaf.SixFunctors.OpenSupportCompactificationModel
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
import all Sheaf.AlgebraicGeometry.SfGraphCompactSupportCompositionBaseChange
import all Sheaf.SixFunctors.OpenSupportGraphExchange

/-! # The graph-free proper/open part of the support cube

Source: blueprint `prop-asd-smooth-base-change`, coherence (i).
(blueprint: lem-asd-open-support-tail-cube)
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor lowerStar upperStar openImmersionLowerShriek
  mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
  mapDerivedCategoryOpenImmersionLowerShriekComp openSupportTailIso
  compactificationExactExchange compactificationSupportBaseChangeIso
  derivedOpenImmersionLowerShriekBaseChangeIso
  rightDerivedLowerShriekOfCompactificationBaseChangeMap'
  rightDerivedLowerShriekOfCompactificationBaseChangeMap
  openImmersionLowerShriekLowerStarExchange exactDerivedBaseChangeMap

private theorem open_exchange_congr
    (Λ : Type (u + 1)) [CommRing Λ]
    {V V' Z Z' : Scheme.{u}} {b : V' ⟶ V} {z : Z' ⟶ Z}
    {r s : V ⟶ Z} {r' s' : V' ⟶ Z'}
    [IsOpenImmersion r] [IsOpenImmersion s]
    [IsOpenImmersion r'] [IsOpenImmersion s']
    (hr : r = s) (hr' : r' = s')
    (sq : IsPullback b r' r z) (sq' : IsPullback b s' s z)
    (K : DerivedCategoryModule Λ V) :
    D((z)^*[ModuleCat.{u + 1} Λ]).map
        ((mapDerivedCategoryOpenImmersionLowerShriekCongr
          (ModuleCat.{u + 1} Λ) hr).hom.app K) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} Λ) sq').inv.app K =
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} Λ) sq).inv.app K ≫
      (mapDerivedCategoryOpenImmersionLowerShriekCongr
        (ModuleCat.{u + 1} Λ) hr').hom.app
        (D((b)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  subst s s'
  simp only [mapDerivedCategoryOpenImmersionLowerShriekCongr,
    Iso.refl_hom, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]
  exact (Category.comp_id
    ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
      (ModuleCat.{u + 1} Λ) sq).inv.app K)).symm

private noncomputable def openWordIso
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {V P X Z : Scheme.{u}}
    (i : V ⟶ P) (k : P ⟶ Z) (a : V ⟶ X) (t : X ⟶ Z)
    [IsOpenImmersion i] [IsOpenImmersion k]
    [IsOpenImmersion a] [IsOpenImmersion t]
    (h : i ≫ k = a ≫ t) :
    D((i)_!open[A]) ⋙ D((k)_!open[A]) ≅ D((a)_!open[A]) ⋙ D((t)_!open[A]) :=
  (mapDerivedCategoryOpenImmersionLowerShriekComp A i k).symm ≪≫
    mapDerivedCategoryOpenImmersionLowerShriekCongr A h ≪≫
      mapDerivedCategoryOpenImmersionLowerShriekComp A a t

private theorem openWord_exchange
    (Λ : Type (u + 1)) [CommRing Λ]
    {V V' P P' X X' Z Z' : Scheme.{u}}
    {b : V' ⟶ V} {w : P' ⟶ P} {g' : X' ⟶ X} {z : Z' ⟶ Z}
    {i : V ⟶ P} {k : P ⟶ Z} {a : V ⟶ X} {t : X ⟶ Z}
    {i' : V' ⟶ P'} {k' : P' ⟶ Z'} {a' : V' ⟶ X'} {t' : X' ⟶ Z'}
    [IsOpenImmersion i] [IsOpenImmersion k]
    [IsOpenImmersion a] [IsOpenImmersion t]
    [IsOpenImmersion i'] [IsOpenImmersion k']
    [IsOpenImmersion a'] [IsOpenImmersion t']
    (sqI : IsPullback b i' i w) (sqK : IsPullback w k' k z)
    (sqA : IsPullback b a' a g') (sqT : IsPullback g' t' t z)
    (h : i ≫ k = a ≫ t) (h' : i' ≫ k' = a' ≫ t')
    (K : DerivedCategoryModule Λ V) :
    D((z)^*[ModuleCat.{u + 1} Λ]).map
        ((openWordIso (ModuleCat.{u + 1} Λ) i k a t h).hom.app K) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} Λ) sqT).inv.app (D((a)_!open[ModuleCat.{u + 1} Λ]).obj K) ≫
      D((t')_!open[ModuleCat.{u + 1} Λ]).map
        ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
          (ModuleCat.{u + 1} Λ) sqA).inv.app K) =
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} Λ) sqK).inv.app (D((i)_!open[ModuleCat.{u + 1} Λ]).obj K) ≫
      D((k')_!open[ModuleCat.{u + 1} Λ]).map
        ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
          (ModuleCat.{u + 1} Λ) sqI).inv.app K) ≫
      (openWordIso (ModuleCat.{u + 1} Λ) i' k' a' t' h').hom.app
        (D((b)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  let A := ModuleCat.{u + 1} Λ
  have hI := sfExactExchangePasting.2.2 Λ sqI sqK K
  have hA := sfExactExchangePasting.2.2 Λ sqA sqT K
  have hC := open_exchange_congr Λ h h' (sqI.paste_vert sqK) (sqA.paste_vert sqT) K
  simp only [openWordIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  apply (cancel_mono ((mapDerivedCategoryOpenImmersionLowerShriekComp A a' t').inv.app
    (D((b)^*[A]).obj K))).1
  dsimp only [A]
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [← hA]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [hC, reassoc_of% hI]


private theorem properOpen_cube_forward
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {P Z U Y P' Z' U' Y' : Scheme.{u}}
    {k : P ⟶ Z} {r : P ⟶ U} {p : Z ⟶ Y} {j : U ⟶ Y}
    {k' : P' ⟶ Z'} {r' : P' ⟶ U'} {p' : Z' ⟶ Y'} {j' : U' ⟶ Y'}
    {w : P' ⟶ P} {z : Z' ⟶ Z} {c : U' ⟶ U} {g : Y' ⟶ Y}
    [IsOpenImmersion k] [IsOpenImmersion j]
    [IsOpenImmersion k'] [IsOpenImmersion j']
    [IsProper r] [IsProper p] [IsProper r'] [IsProper p']
    (sq : IsPullback r k j p) (sq' : IsPullback r' k' j' p')
    (sqK : IsPullback w k' k z) (sqJ : IsPullback c j' j g)
    (sqP : IsPullback z p' p g) (sqR : IsPullback w r' r c)
    (M : DerivedCategoryModule Λ P) :
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} Λ) sqJ).hom.app (R((r)_*[ModuleCat.{u + 1} Λ]).obj M) ≫
      D((g)^*[ModuleCat.{u + 1} Λ]).map
        ((openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} Λ) sq).app M) ≫
      (exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sqP.toCommSq).app
        (D((k)_!open[ModuleCat.{u + 1} Λ]).obj M) =
    D((j')_!open[ModuleCat.{u + 1} Λ]).map
        ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sqR.toCommSq).app M) ≫
      (openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} Λ) sq').app
        (D((w)^*[ModuleCat.{u + 1} Λ]).obj M) ≫
      R((p')_*[ModuleCat.{u + 1} Λ]).map
        ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
          (ModuleCat.{u + 1} Λ) sqK).hom.app M) := by
  obtain ⟨_θ, _Γ, _hθ, _hΓ, hCart, _hVert, _hHoriz, _hIdV, _hIdH, hCube⟩ :=
    etaleProperOpenExchangeCube Λ
  have H := congr_app (hCube k r p j k' r' p' j' w z c g
    sq.toCommSq.flip sq'.toCommSq.flip sqK sqJ sqP sqR) M
  rw [hCart k r p j sq, hCart k' r' p' j' sq'] at H
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] at H
  have H' := congrArg (fun q =>
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
      (ModuleCat.{u + 1} Λ) sqJ).hom.app (R((r)_*[ModuleCat.{u + 1} Λ]).obj M) ≫
    q ≫ R((p')_*[ModuleCat.{u + 1} Λ]).map
      ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} Λ) sqK).hom.app M)) H
  simpa only [Functor.comp_obj, Category.assoc, ← Functor.map_comp, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, Iso.hom_inv_id_app_assoc, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.id_comp] using H'


private theorem tail_hom
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y} {j : U ⟶ Y} [IsOpenImmersion j]
    {a : V ⟶ X} [IsOpenImmersion a] {p : V ⟶ U}
    (sq : IsPullback a p f j) (cf : Compactification f)
    (K : DerivedCategoryModule Λ V) :
    (openSupportTailIso Λ sq cf).hom.app K =
      (openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} Λ)
        (IsPullback.of_hasPullback cf.g j).flip).app
        (D(((cf.ofIsPullback sq).i)_!open[ModuleCat.{u + 1} Λ]).obj K) ≫
      R((cf.g)_*[ModuleCat.{u + 1} Λ]).map
        ((openWordIso (ModuleCat.{u + 1} Λ) (cf.ofIsPullback sq).i
          (pullback.fst cf.g j) a cf.i (cf.ofIsPullback_i_fst sq)).hom.app K) := by
  simp only [openSupportTailIso, openWordIso,
    openImmersionLowerShriekLowerStarExchangeIso, asIso_hom,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_comp, Category.assoc, Category.id_comp, Category.comp_id]

private theorem tail_exact
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y X' Y' U V U' V' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g)
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} (sqU : IsPullback a p f j)
    {c : U' ⟶ U} {j' : U' ⟶ Y'} [IsOpenImmersion j']
    (sqj : IsPullback c j' j g)
    {b : V' ⟶ V} {p' : V' ⟶ U'} (_sq' : IsPullback b p' p c)
    {a' : V' ⟶ X'} [IsOpenImmersion a'] (sqV : IsPullback a' p' f' j')
    (sqA : IsPullback b a' a g') (cf : Compactification f)
    (w : ((cf.ofIsPullback sq).ofIsPullback sqV).Z ⟶ (cf.ofIsPullback sqU).Z)
    (hi : IsPullback b ((cf.ofIsPullback sq).ofIsPullback sqV).i
      (cf.ofIsPullback sqU).i w)
    (hp : IsPullback w ((cf.ofIsPullback sq).ofIsPullback sqV).g
      (cf.ofIsPullback sqU).g c)
    (hw : w ≫ pullback.fst cf.g j =
      pullback.fst (cf.ofIsPullback sq).g j' ≫ pullback.fst cf.g g)
    (K : DerivedCategoryModule Λ V) :
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} Λ) sqj).hom.app
        (Rf_!(cf.ofIsPullback sqU)[ModuleCat.{u + 1} Λ].obj K) ≫
      D((g)^*[ModuleCat.{u + 1} Λ]).map ((openSupportTailIso Λ sqU cf).hom.app K) ≫
      (compactificationExactExchange Λ cf (cf.ofIsPullback sq)
        (pullback.fst cf.g g) (cf.isPullback_i_ofIsPullback sq)
        (cf.isPullback_g_ofIsPullback sq).flip).app
        (D((a)_!open[ModuleCat.{u + 1} Λ]).obj K) =
    D((j')_!open[ModuleCat.{u + 1} Λ]).map
        ((compactificationExactExchange Λ (cf.ofIsPullback sqU)
          ((cf.ofIsPullback sq).ofIsPullback sqV) w hi hp).app K) ≫
      (openSupportTailIso Λ sqV (cf.ofIsPullback sq)).hom.app
        (D((b)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      Rf_!(cf.ofIsPullback sq)[ModuleCat.{u + 1} Λ].map
        ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
          (ModuleCat.{u + 1} Λ) sqA).hom.app K) := by
  let A := ModuleCat.{u + 1} Λ
  let df := cf.ofIsPullback sq
  let cq := cf.ofIsPullback sqU
  let dq := df.ofIsPullback sqV
  let k := pullback.fst cf.g j
  let k' := pullback.fst df.g j'
  let z := pullback.fst cf.g g
  let si := cf.isPullback_i_ofIsPullback sq
  let sp := (cf.isPullback_g_ofIsPullback sq).flip
  have hk : k ≫ cf.g = cq.g ≫ j := pullback.condition
  have hk' : k' ≫ df.g = dq.g ≫ j' := pullback.condition
  have sqK : IsPullback w k' k z := by
    apply IsPullback.of_bot (p := hw) (t := sp)
    rw [hk, hk']
    exact hp.paste_vert sqj
  let H := openWordIso A cq.i k a cf.i (cf.ofIsPullback_i_fst sqU)
  have hC := properOpen_cube_forward Λ
    (IsPullback.of_hasPullback cf.g j).flip
    (IsPullback.of_hasPullback df.g j').flip sqK sqj sp hp
    (D((cq.i)_!open[A]).obj K)
  have hP := (exactDerivedBaseChangeMap A sp.toCommSq).naturality (H.hom.app K)
  have hN := (openImmersionLowerShriekLowerStarExchange A
    (IsPullback.of_hasPullback df.g j').flip).naturality
      ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso A hi).inv.app K)
  have hO := openWord_exchange Λ hi sqK sqA si
    (cf.ofIsPullback_i_fst sqU) (df.ofIsPullback_i_fst sqV) K
  have hOmixed := congrArg (fun q =>
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso A sqK).hom.app
      (D((cq.i)_!open[A]).obj K) ≫ q ≫ D((df.i)_!open[A]).map
      ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso A sqA).hom.app K)) hO
  dsimp only [A, df, cq, dq] at hOmixed
  simp only [Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app, Iso.hom_inv_id_app_assoc, CategoryTheory.Functor.map_id,
    Functor.comp_obj, Category.id_comp, Category.comp_id] at hOmixed
  have hM := congrArg (R((df.g)_*[A]).map) hOmixed
  simp only [Functor.map_comp, Category.assoc] at hM
  simp only [Functor.comp_obj, Functor.comp_map] at hP hN
  rw [tail_hom, tail_hom]
  dsimp only [A, df, cq, dq, k, k', z, si, sp, H]
    at hP hN hC hM ⊢
  simp only [compactificationExactExchange, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_comp, Category.assoc, Category.id_comp, Category.comp_id]
  dsimp only [rightDerivedLowerShriekOfCompactification, rightDerivedLowerStar,
    Functor.comp_obj, Functor.comp_map] at hP hN hC hM ⊢
  erw [reassoc_of% hP, reassoc_of% hC, hM, ← reassoc_of% hN]
  rfl


/-- The proper/open interchange and open compositor commute with base change.
Source: blueprint `prop-asd-smooth-base-change`, coherence (i), applied to the two
base changes of the proper/open compactification diagram.

Proof: write k for the first projection of cf.g against j, k' for the corresponding
projection after base change, and z for the first projection of cf.g against g.
The hypothesis hw identifies the square (w,k',k,z), while hp is the square for
the proper parts. Apply the proper/open exchange cube to these squares and sqj.
Its proper exchanges are the mates of the commuting inverse-image squares;
proper mate pasting identifies the composite proper exchanges on the two paths.
Whisker this equality by the open extension along (cf.ofIsPullback sqU).i.
For the remaining factors, transpose the two paths under the composite open
adjunction. The unit equations of open base change, inverse-image composition
coherence, and the triangle identities give the same transpose. Exactness of
open extension descends this identity degreewise to the unbounded derived
category. The open compositor associativity and the equations defining the
base-changed open embeddings identify its two outer composites with a followed
by cf.i and a' followed by (cf.ofIsPullback sq).i. Substitute these identities
and reassociate. This first gives the equation for exact inverse image. Conjugate
by its canonical comparison with left derived inverse image; naturality cancels
the endpoint comparisons and gives the displayed equation. There is no graph
comparison in this calculation, no quasi-compactness assumption, and the same
unit equations cover empty opens and the zero coefficient ring.
(blueprint: lem-asd-open-support-tail-cube) -/
theorem openSupportTail_cube
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y X' Y' U V U' V' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g)
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} (sqU : IsPullback a p f j)
    {c : U' ⟶ U} {j' : U' ⟶ Y'} [IsOpenImmersion j']
    (sqj : IsPullback c j' j g)
    {b : V' ⟶ V} {p' : V' ⟶ U'} (sq' : IsPullback b p' p c)
    {a' : V' ⟶ X'} [IsOpenImmersion a'] (sqV : IsPullback a' p' f' j')
    (sqA : IsPullback b a' a g') (cf : Compactification f)
    (w : ((cf.ofIsPullback sq).ofIsPullback sqV).Z ⟶ (cf.ofIsPullback sqU).Z)
    (hi : IsPullback b ((cf.ofIsPullback sq).ofIsPullback sqV).i
      (cf.ofIsPullback sqU).i w)
    (hp : IsPullback w ((cf.ofIsPullback sq).ofIsPullback sqV).g
      (cf.ofIsPullback sqU).g c)
    (hw : w ≫ pullback.fst cf.g j =
      pullback.fst (cf.ofIsPullback sq).g j' ≫ pullback.fst cf.g g)
    (K : DerivedCategoryModule Λ V) :
    (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) sqj).hom.app
        (Rf_!(cf.ofIsPullback sqU)[ModuleCat.{u + 1} Λ].obj K) ≫
      L((g)^*[ModuleCat.{u + 1} Λ]).map ((openSupportTailIso Λ sqU cf).hom.app K) ≫
      (compactificationSupportBaseChangeIso Λ sq cf).hom.app
        (D((a)_!open[ModuleCat.{u + 1} Λ]).obj K) =
    D((j')_!open[ModuleCat.{u + 1} Λ]).map
        ((rightDerivedLowerShriekOfCompactificationBaseChangeMap'
          (ModuleCat.{u + 1} Λ) (cf.ofIsPullback sqU)
          ((cf.ofIsPullback sq).ofIsPullback sqV) w hi hp.toCommSq).app K) ≫
      (openSupportTailIso Λ sqV (cf.ofIsPullback sq)).hom.app
        (L((b)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      Rf_!(cf.ofIsPullback sq)[ModuleCat.{u + 1} Λ].map
        ((derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) sqA).hom.app K)
    := by
  let A := ModuleCat.{u + 1} Λ
  let df := cf.ofIsPullback sq
  let cq := cf.ofIsPullback sqU
  let dq := df.ofIsPullback sqV
  have Hd := tail_exact Λ sq sqU sqj sq' sqV sqA cf w hi hp hw K
  have hcf := congr_app (compactificationExactExchange_transport Λ cf sq)
    (D((a)_!open[A]).obj K)
  have hcq := congr_app (cartesian_exchange_transport Λ cq dq w hi hp) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    at hcf hcq
  have Hg := (leftDerivedUpperStarIsoMapDerivedCategory A g).inv.naturality
    ((openSupportTailIso Λ sqU cf).hom.app K)
  have HT := (openSupportTailIso Λ sqV df).hom.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory A b).hom.app K)
  apply (cancel_epi (D((j')_!open[A]).map
    ((leftDerivedUpperStarIsoMapDerivedCategory A c).inv.app (Rf_!(cq)[A].obj K)))).1
  apply (cancel_mono (Rf_!(df)[A].map
    ((leftDerivedUpperStarIsoMapDerivedCategory A g').hom.app
      (D((a)_!open[A]).obj K)))).1
  dsimp only [A, df, cq, dq] at Hg HT hcf hcq Hd ⊢
  simp only [derivedOpenImmersionLowerShriekBaseChangeIso,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [rightDerivedLowerShriekOfCompactification, rightDerivedLowerStar,
    Functor.comp_obj, Functor.comp_map] at Hg HT hcf hcq Hd ⊢
  rw [← reassoc_of% Hg, ← reassoc_of% HT]
  simp only [compactificationSupportBaseChangeIso, asIso_hom]
  rw [← hcf]
  have hcqJ := congrArg (D((j')_!open[A]).map) hcq
  simp only [Functor.map_comp, Category.assoc] at hcqJ
  rw [← reassoc_of% hcqJ]
  dsimp only [A]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  exact Hd

end AlgebraicGeometry.Etale
