module

public import Sheaf.AlgebraicGeometry.StandardSingleBaseChangeMap
public import Sheaf.AlgebraicGeometry.RelativeMVMaps
public import Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionData
import Sheaf.AlgebraicGeometry.DerivedSourceRestrictionUnitNaturality
import Sheaf.AlgebraicGeometry.TopRestrictionCoefficientCoherence

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry


private noncomputable def topRestriction_pullbackIso
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (g : A ⟶ B) :
    pullback ((⊤ : Y.Opens).ι ≫ p) g ≅ pullback p g := by
  let j := (⊤ : Y.Opens).ι
  let r := pullback.fst p g
  let s := pullback.snd p g
  let r' := pullback.fst (j ≫ p) g
  let s' := pullback.snd (j ≫ p) g
  let kh := pullback.lift (r' ≫ j) s' (by
    simpa only [r', s', j, Category.assoc] using
      (pullback.condition (f := j ≫ p) (g := g)))
  let ki : pullback p g ⟶ pullback (j ≫ p) g := pullback.lift (r ≫ Y.topIso.inv) s (by
    change r ≫ Y.topIso.inv ≫ Y.topIso.hom ≫ p = s ≫ g
    rw [Iso.inv_hom_id_assoc]
    exact pullback.condition)
  let k : pullback (j ≫ p) g ≅ pullback p g :=
    { hom := kh
      inv := ki
      hom_inv_id := by
        apply pullback.hom_ext
        · simp [kh, ki, r, r', j, Category.assoc]
        · simp [kh, ki, s, s', Category.assoc]
      inv_hom_id := by
        apply pullback.hom_ext
        · simp [kh, ki, r, r', j, Category.assoc]
        · simp [kh, ki, s, s', Category.assoc] }
  exact k

private theorem topRestriction_pullbackIso_fst
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (g : A ⟶ B) :
    (topRestriction_pullbackIso p g).hom ≫ pullback.fst p g =
      pullback.fst ((⊤ : Y.Opens).ι ≫ p) g ≫ (⊤ : Y.Opens).ι := by
  exact pullback.lift_fst _ _ _

private theorem topRestriction_pullbackIso_snd
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (g : A ⟶ B) :
    (topRestriction_pullbackIso p g).hom ≫ pullback.snd p g =
      pullback.snd ((⊤ : Y.Opens).ι ≫ p) g := by
  exact pullback.lift_snd _ _ _

attribute [local irreducible] topRestriction_pullbackIso

private theorem topRestriction_imageComp_eq
    [∀ Z : Scheme.{u}, HasDerivedCategory (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Z : Scheme.{u}} (j : X ⟶ Y) (f : Y ⟶ Z) :
    relativeMVImageComp j f =
      (conjugateIsoEquiv (relativeMVAdj (j ≫ f))
        ((relativeMVAdj f).comp (relativeMVAdj j)) (relativeMVComp j f)).symm := by
  ext E
  simp [relativeMVImageComp, Adjunction.rightAdjointUniq,
    conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_apply_inv,
    conjugateEquiv_apply_app, Adjunction.ofNatIsoLeft_counit, Functor.map_comp]


private theorem topRestriction_restriction_naturality
    [∀ Z : Scheme.{u}, HasDerivedCategory (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X X' S S' T T' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (t : T ⟶ X) (p : T' ⟶ X') (v : T' ⟶ T) (hv : v ≫ t = p ≫ g')
    (q : T' ⟶ S') (hq : p ≫ f' = q) :
    (derivedPullback g).map (relativeMVUnit t f K) ≫
        schemeDerivedBaseChangeMap (t ≫ f) q g v
          (by rw [← hq, ← Category.assoc, hv, Category.assoc, h, ← Category.assoc])
          ((derivedPullback t).obj K) ≫
        (schemeDerivedDirectImage q).map
          ((relativeMVComp v t).hom.app K ≫
            eqToHom (congrArg (fun s ↦ (derivedPullback s).obj K) hv) ≫
            (relativeMVComp p g').inv.app K ≫ (derivedPullback p).map φ) =
      (schemeDerivedBaseChangeMap f f' g g' h K ≫
        (schemeDerivedDirectImage f').map φ) ≫
        relativeMVUnit p f' K' ≫
        eqToHom (congrArg (fun s ↦ (schemeDerivedDirectImage s).obj
          ((derivedPullback p).obj K')) hq) := by
  subst q
  simpa only [relativeMVUnit, topRestriction_imageComp_eq, Iso.symm_hom,
    Functor.id_obj,
    eqToHom_refl, Category.comp_id, Category.assoc] using
    derivedSourceRestriction_unit_naturality f f' g g' h K K' φ t p v hv


private theorem topRestriction_finish
    {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {A B T T' : D} {X Y Z W : C}
    (β : A ⟶ B) (v : B ⟶ R.obj Y) (F : B ⟶ R.obj Z)
    (u : A ⟶ T) (a : T ⟶ T') (e : A ⟶ T')
    (β₀ : T ⟶ R.obj X) (β' : T' ⟶ R.obj W)
    (z : X ⟶ Y) (d : Y ⟶ Z) (c : X ⟶ W) (q : W ⟶ Z)
    (hm : u ≫ β₀ ≫ R.map z = β ≫ v)
    (hn : a ≫ β' = β₀ ≫ R.map c) (hc : z ≫ d = c ≫ q)
    (hF : F = v ≫ R.map d) (he : e = u ≫ a) :
    β ≫ F = e ≫ β' ≫ R.map q := by
  rw [hF, ← Category.assoc, ← hm]
  simp only [Category.assoc]
  rw [← R.map_comp, hc, R.map_comp, he]
  simp only [Category.assoc]
  rw [← reassoc_of% hn]


/-- The derived pullback unit for a scheme isomorphism is invertible.
Source: Stacks Project, Tag 0D5S.
(blueprint: lem-pc-standard-single-base-change-top-restriction-iso-pullback-unit) -/
theorem standardSingleBaseChange_topRestriction_iso_pullback_unit
    [∀ X : Scheme.{u},
      HasDerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {X Z : Scheme.{u}} (s : X ≅ Z) :
    IsIso (relativeMVAdj s.hom).unit := by
  obtain ⟨_, i, _, _, _⟩ := Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      exists_derivedPullbackComposition)))
  let b : derivedPullback s.hom ⋙ derivedPullback s.inv ≅ 𝟭 _ :=
    relativeMVComp s.inv s.hom ≪≫
      eqToIso (congrArg (fun t ↦ derivedPullback t) s.inv_hom_id) ≪≫ i Z
  let c : derivedPullback s.inv ⋙ derivedPullback s.hom ≅ 𝟭 _ :=
    relativeMVComp s.hom s.inv ≪≫
      eqToIso (congrArg (fun t ↦ derivedPullback t) s.hom_inv_id) ≪≫ i X
  have : (derivedPullback s.inv).Faithful := Functor.Faithful.of_comp_iso c
  have : (derivedPullback s.hom).Faithful := Functor.Faithful.of_comp_iso b
  have : (derivedPullback s.hom).Full := Functor.Full.of_comp_faithful_iso b
  infer_instance


set_option linter.unusedVariables false in

/-- Canonical source restriction comparison for the top open.
Source: Stacks Project, Tags 08HY and 0D5S.
(blueprint: def-pc-standard-single-base-change-top-restriction-source-iso) -/
noncomputable def standardSingleBaseChange_topRestriction_sourceIso
    {Y B : Scheme.{u}} (p : Y ⟶ B) (M : Y.Modules) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (schemeDerivedDirectImage p).obj
          ((DerivedCategory.singleFunctor _ 0).obj M) ≅
        (schemeDerivedDirectImage ((⊤ : Y.Opens).ι ≫ p)).obj
          ((DerivedCategory.singleFunctor _ 0).obj (M.restrict (⊤ : Y.Opens).ι)) := by
  classical
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let j := (⊤ : Y.Opens).ι
  let K := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M
  have : IsIso (relativeMVAdj j).unit :=
    standardSingleBaseChange_topRestriction_iso_pullback_unit Y.topIso
  let a : (derivedPullback j).obj K ≅
      (DerivedCategory.singleFunctor _ 0).obj (M.restrict j) :=
    (singleComplexOpenPullbackIso Y ⊤).app K ≪≫
      ((schemeOpenRestriction Y ⊤).mapDerivedCategorySingleFunctor 0).app M ≪≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings
          (⊤ : Y.Opens).toScheme.toRingedSpace)) 0).mapIso
        ((Scheme.Modules.overFunctorEquiv ⊤).app M)
  exact (schemeDerivedDirectImage p).mapIso
      (asIso ((relativeMVAdj j).unit.app K)) ≪≫
    (relativeMVImageComp j p).app ((derivedPullback j).obj K) ≪≫
    (schemeDerivedDirectImage (j ≫ p)).mapIso a

set_option linter.unusedVariables false in
/-- Source restriction comparison for the top open; see the two-step proof of
`standardSingleBaseChange_topRestriction_comparison`.
Source: Stacks Project, Tags 08HY and 0D5S.
(blueprint: lem-pc-standard-single-base-change-top-restriction-source) -/
theorem standardSingleBaseChange_topRestriction_source
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (M : Y.Modules) (g : A ⟶ B) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let j := (⊤ : Y.Opens).ι
    let N := M.restrict j
    Nonempty ((schemeDerivedDirectImage p).obj
          ((DerivedCategory.singleFunctor _ 0).obj M) ≅
        (schemeDerivedDirectImage (j ≫ p)).obj
          ((DerivedCategory.singleFunctor _ 0).obj N)) := by
  dsimp
  exact ⟨standardSingleBaseChange_topRestriction_sourceIso p M⟩

/-- Direct-image comparison along an isomorphism of the upper row. -/
private noncomputable def topRestriction_imageIso
    [∀ Z : Scheme.{u}, HasDerivedCategory (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {P P' A : Scheme.{u}} (k : P' ≅ P) (s : P ⟶ A) (s' : P' ⟶ A)
    (h : k.hom ≫ s = s') (T : schemeDerivedCategory P)
    {T' : schemeDerivedCategory P'} (d : (derivedPullback k.hom).obj T ≅ T') :
    (schemeDerivedDirectImage s).obj T ≅ (schemeDerivedDirectImage s').obj T' := by
  have : IsIso (relativeMVAdj k.hom).unit :=
    standardSingleBaseChange_topRestriction_iso_pullback_unit k
  exact (schemeDerivedDirectImage s).mapIso
      (asIso ((relativeMVAdj k.hom).unit.app T)) ≪≫
    (relativeMVImageComp k.hom s).app ((derivedPullback k.hom).obj T) ≪≫
    (eqToIso (congrArg schemeDerivedDirectImage h)).app
      ((derivedPullback k.hom).obj T) ≪≫
    (schemeDerivedDirectImage s').mapIso d

private theorem topRestriction_imageIso_hom
    [∀ Z : Scheme.{u}, HasDerivedCategory (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {P P' A : Scheme.{u}} (k : P' ≅ P) (s : P ⟶ A) (s' : P' ⟶ A)
    (h : k.hom ≫ s = s') (T : schemeDerivedCategory P)
    {T' : schemeDerivedCategory P'} (d : (derivedPullback k.hom).obj T ≅ T') :
    (topRestriction_imageIso k s s' h T d).hom =
      (relativeMVUnit k.hom s T ≫
        eqToHom (congrArg (fun q ↦ (schemeDerivedDirectImage q).obj
          ((derivedPullback k.hom).obj T)) h)) ≫
        (schemeDerivedDirectImage s').map d.hom := by
  simp only [topRestriction_imageIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, asIso_hom, eqToIso.hom, eqToHom_app, relativeMVUnit, Category.assoc]

attribute [local irreducible] topRestriction_imageIso

attribute [local irreducible] derivedPullback Scheme.Modules.tensorPullbackObj
  Scheme.picardTermwiseSingleMap Scheme.Modules.tensorPullbackCompositionIso
attribute [local irreducible] Adjunction.homEquiv relativeMVAdj relativeMVComp
  relativeMVImageComp singleComplexOpenPullbackIso Adjunction.leftAdjointUniq
  Scheme.Modules.restrictFunctorIsoPullback Scheme.Modules.overFunctorEquiv
  standardSingleBaseChangeMap standardSingleBaseChange_topRestriction_sourceIso relativeMVUnit
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] Scheme.Modules.Hom DerivedCategory
  Functor.mapHomologicalComplex HomotopyCategory Functor.mapHomotopyCategory
  HomotopyCategory.quotient DerivedCategory.Q DerivedCategory.Qh
  HomologicalComplexUpToQuasiIso.Qh


private theorem topRestriction_baseChange_naturality
    [∀ Z : Scheme.{u}, HasDerivedCategory (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) {E E' : schemeDerivedCategory X} (φ : E ⟶ E') :
    (derivedPullback g).map ((schemeDerivedDirectImage f).map φ) ≫
        schemeDerivedBaseChangeMap f f' g g' h E' =
      schemeDerivedBaseChangeMap f f' g g' h E ≫
        (schemeDerivedDirectImage f').map ((derivedPullback g').map φ) := by
  let c := relativeMVComp f' g ≪≫
    eqToIso (congrArg (fun t ↦ derivedPullback t) h.symm) ≪≫ (relativeMVComp g' f).symm
  have mate (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
      (a' : derivedPullback f' ⊣ schemeDerivedDirectImage f')
      (e : derivedPullback g ⋙ derivedPullback f' ≅
        derivedPullback f ⋙ derivedPullback g') :
      (derivedPullback g).map ((schemeDerivedDirectImage f).map φ) ≫
          a'.homEquiv _ _ (e.hom.app ((schemeDerivedDirectImage f).obj E') ≫
            (derivedPullback g').map (a.counit.app E')) =
        a'.homEquiv _ _ (e.hom.app ((schemeDerivedDirectImage f).obj E) ≫
          (derivedPullback g').map (a.counit.app E)) ≫
          (schemeDerivedDirectImage f').map ((derivedPullback g').map φ) := by
    rw [← a'.homEquiv_naturality_left, ← a'.homEquiv_naturality_right]
    congr 1
    have hn := e.hom.naturality ((schemeDerivedDirectImage f).map φ)
    dsimp only [Functor.comp_map] at hn
    rw [← Category.assoc, hn]
    simp only [Category.assoc, ← (derivedPullback g').map_comp]
    have hc := a.counit.naturality φ
    dsimp only [Functor.comp_map, Functor.id_map] at hc
    rw [hc]
  have hh := mate (relativeMVAdj f) (relativeMVAdj f') c
  simp only [c, Iso.symm_hom, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app, Category.assoc] at hh
  simp only [relativeMVAdj, relativeMVComp] at hh
  unfold schemeDerivedBaseChangeMap
  simpa only [Functor.id_obj] using hh

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 250000 in
-- The pinned adjunctions have large dependent types during the final comparison.
/-- Compatibility equation for the canonical source restriction comparison.
Source: Stacks Project, Tags 08HY and 0D5S.
(blueprint: lem-pc-standard-single-base-change-top-restriction-compatibility)

Proof: Substitute the hypothesis on `e`. Write L_f = derivedPullback f and
R_f = schemeDerivedDirectImage f; composition of arrows below is written `≫`.
Put j = (⊤ : Y.Opens).ι, N = M.restrict j, K = M[0], K' = N[0]. Let
P = pullback p g have projections r = pullback.fst p g and s = pullback.snd p g.
Let P' = pullback (j ≫ p) g have projections r' and s'. The universal property
constructs k : P' ≅ P with k.hom ≫ r = r' ≫ j and k.hom ≫ s = s': its forward
map is pullback.lift (r' ≫ j) s', and its inverse is pullback.lift (r ≫ j.inv) s.
Here j.inv denotes Y.topIso.inv. Pullback projection extensionality and the two
inverse identities for Y.topIso prove that these maps are inverse.

Let a : L_j K ≅ K' be precisely the single restriction comparison in sourceIso.
For any f write q_f(V) = Scheme.picardTermwiseSingleMap f V. Tensor pullback
along the isomorphism k.hom is exact, so q_k on any module is invertible.
The canonical module isomorphism b from tensorPullbackObj k.hom
(tensorPullbackObj r M) to tensorPullbackObj r' N is obtained by tensor-pullback
composition along k.hom,r, transport across k.hom ≫ r = r' ≫ j, inverse
composition along r',j, and tensorPullback r' of the canonical comparison
from tensorPullbackObj j M to N. More explicitly, put
δ(h,f) = Scheme.Modules.tensorPullbackCompositionIso h f (h ≫ f) rfl, directed from tensor pullback
of h ≫ f to tensor pullback
along f followed by h. If ρ : tensorPullbackObj j M ≅ N is the canonical
adjoint-uniqueness comparison to restriction used in a, then
  b = δ(k.hom,r).inv.app M ≫ transport ≫ δ(r',j).hom.app M
    ≫ (Scheme.Modules.tensorPullback r').map ρ.hom,
where transport is along k.hom ≫ r = r' ≫ j. Thus a.hom is q_j(M) followed
by single.map ρ.hom. All these comparisons are pinned to the
same tensor-pullback adjunctions. Define
  T = (tensorPullbackObj r M)[0], T' = (tensorPullbackObj r' N)[0],
  d : L_k T ≅ T' = asIso(q_k(tensorPullbackObj r M)) ≪≫ single.mapIso b.
Write C(h,f) for relativeMVComp h f, including equality transport when paths
are identified. The coefficient-composition identity is
  L_k(q_r(M)) ≫ d.hom =
    C(k,r).hom.app K ≫ C(r',j).inv.app K ≫ L_r'(a.hom) ≫ q_r'(N).
The equality transport between the two C components uses k.hom ≫ r = r' ≫ j.
To verify this identity, apply Scheme.picardTermwiseSingleMap_composition to
(k.hom,r) and (r',j). Its tensorPullbackCompositionIso and single-complex
comparison factors are exactly those defining b. Cancel the inverse factors,
and use naturality of the single comparison for the tensor-to-restriction map.
The defining leftDerivedLift factorization in exists_derivedPullbackComposition
ensures that these are the pinned C comparisons, rather than arbitrary ones.

Define F : R_s T ≅ R_s' T' by composing R_s of the invertible unit
T ≅ R_k L_k T, (relativeMVImageComp k.hom s).app (L_k T), transport across
k.hom ≫ s = s', and R_s'.mapIso d. Invertibility of the unit follows from
standardSingleBaseChange_topRestriction_iso_pullback_unit k. Set t = F.symm.

Here is the compatibility calculation before cancelling F. Put D = L_g R_p K.
Write B(r,s,p;K) for the transpose of schemeDerivedBaseChangeMap p s g r:
  B(r,s,p;K) = C(s,g).hom.app (R_p K) ≫ C(r,p).inv.app (R_p K)
    ≫ L_r((relativeMVAdj p).counit.app K),
with the pullback.condition transport between the two C components. Thus the
transpose of standardSingleBaseChangeMap p M g under relativeMVAdj s is
B(r,s,p;K) ≫ q_r(M). Under relativeMVAdj s', the transpose of that map followed
by F.hom is
  C(k,s).inv.app D ≫ L_k(B(r,s,p;K)) ≫ L_k(q_r(M)) ≫ d.hom.
This follows by expanding F and the right-adjoint mate relativeMVImageComp:
its mate formula converts the composite adjunction to relativeMVAdj s', and
L_k of the unit followed by the k counit cancels by the left triangle identity.

Substitute the coefficient identity. The remaining prefix satisfies
  C(k,s).inv.app D ≫ L_k(B(r,s,p;K)) ≫ C(k,r).hom.app K
    ≫ C(r',j).inv.app K ≫ L_r'(a.hom)
  = L_s'(L_g(e.hom)) ≫ B(r',s',j ≫ p;K').
For this equation, expand e as R_p(unit_j) followed by relativeMVImageComp j p
and R_(j≫p)(a). Move a through the counit by counit naturality. Expand the
composition counit using the right-adjoint mate defining relativeMVImageComp:
the counit for j ≫ p is C(j,p).inv followed by L_j of the p counit and then
the j counit (with the right-adjoint comparison on its source). Naturality moves
the inserted unit_j next to the j counit, where
  L_j(unit_j.app K) ≫ counit_j.app (L_j K) = 𝟙 (L_j K)
cancels it. The other mate cancellation is
  unit_j.app (R_j V) ≫ R_j(counit_j.app V) = 𝟙 (R_j V).
Associativity and the identity laws in exists_derivedPullbackComposition
identify the remaining C paths using r ≫ p = s ≫ g, r' ≫ j ≫ p = s' ≫ g,
and the two projection identities for k. These are the pinned composition
laws, the single-map composition identity, and the two adjunction triangle
identities; no comparison along g is inverted.

Appending q_r'(N) shows equality of the two transposes under relativeMVAdj s'.
The adjunction hom equivalence is injective, hence
  standardSingleBaseChangeMap p M g ≫ F.hom =
    L_g(e.hom) ≫ standardSingleBaseChangeMap (j ≫ p) N g.
Compose on the right with F.inv and cancel F.hom ≫ F.inv to get the claimed
equation with t = F.symm. All constructions are functorial and remain valid
for empty schemes and zero modules. -/
theorem standardSingleBaseChange_topRestriction_compatibility
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (M : Y.Modules) (g : A ⟶ B) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    ∀ (e : (schemeDerivedDirectImage p).obj
          ((DerivedCategory.singleFunctor _ 0).obj M) ≅
        (schemeDerivedDirectImage ((⊤ : Y.Opens).ι ≫ p)).obj
          ((DerivedCategory.singleFunctor _ 0).obj (M.restrict (⊤ : Y.Opens).ι))),
      e = standardSingleBaseChange_topRestriction_sourceIso p M → ∃ (t : (schemeDerivedDirectImage
          (pullback.snd ((⊤ : Y.Opens).ι ≫ p) g)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.Modules.tensorPullbackObj
              (pullback.fst ((⊤ : Y.Opens).ι ≫ p) g)
              (M.restrict (⊤ : Y.Opens).ι))) ≅
        (schemeDerivedDirectImage (pullback.snd p g)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M))),
      standardSingleBaseChangeMap p M g =
        (derivedPullback g).map e.hom ≫
          standardSingleBaseChangeMap ((⊤ : Y.Opens).ι ≫ p)
            (M.restrict (⊤ : Y.Opens).ι) g ≫ t.hom := by
  classical
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  intro e he
  rw [he]
  clear e he
  let j := (⊤ : Y.Opens).ι
  let N := M.restrict j
  let K := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M
  let K' := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings (⊤ : Y.Opens).toScheme.toRingedSpace)) 0).obj N
  let r := pullback.fst p g
  let s := pullback.snd p g
  let r' := pullback.fst (j ≫ p) g
  let s' := pullback.snd (j ≫ p) g
  let k := topRestriction_pullbackIso p g
  have hr : k.hom ≫ r = r' ≫ j := topRestriction_pullbackIso_fst p g
  have hs : k.hom ≫ s = s' := topRestriction_pullbackIso_snd p g
  let a : (derivedPullback j).obj K ≅ K' :=
    (singleComplexOpenPullbackIso Y ⊤).app K ≪≫
      ((schemeOpenRestriction Y ⊤).mapDerivedCategorySingleFunctor 0).app M ≪≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings
          (⊤ : Y.Opens).toScheme.toRingedSpace)) 0).mapIso
        ((Scheme.Modules.overFunctorEquiv ⊤).app M)
  let ρ : Scheme.Modules.tensorPullback j ≅ Scheme.Modules.restrictFunctor j :=
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j)).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction j) ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback j).symm
  let b : @Iso (SheafOfModules.{u} (moduleRings (pullback (j ≫ p) g).toRingedSpace))
      inferInstance ((Scheme.Modules.tensorPullback k.hom).obj
        (Scheme.Modules.tensorPullbackObj r M)) (Scheme.Modules.tensorPullbackObj r' N) :=
      (Scheme.Modules.tensorPullbackCompositionIso k.hom r
      (k.hom ≫ r) rfl).symm.app M ≪≫
    (eqToIso (congrArg Scheme.Modules.tensorPullback hr)).app M ≪≫
    (Scheme.Modules.tensorPullbackCompositionIso r' j (r' ≫ j) rfl).app M ≪≫
    (Scheme.Modules.tensorPullback r').mapIso (ρ.app M)
  have : IsIso (Scheme.picardTermwiseSingleMap k.hom
      (Scheme.Modules.tensorPullbackObj r M)) :=
    picardTermwiseSingleMap_isIso_of_iso k _
  let d := asIso (Scheme.picardTermwiseSingleMap k.hom
      (Scheme.Modules.tensorPullbackObj r M)) ≪≫
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings (pullback (j ≫ p) g).toRingedSpace)) 0).mapIso b
  let T := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings (pullback p g).toRingedSpace)) 0).obj
      (Scheme.Modules.tensorPullbackObj r M)
  let F := topRestriction_imageIso k s s' hs T d
  have hF := topRestriction_imageIso_hom k s s' hs T d
  have hc := topRestriction_coefficient_coherence M k r r' hr
  have hc' :
      ((relativeMVComp r' j).hom.app K ≫
        eqToHom (congrArg (fun s ↦ (derivedPullback s).obj K) hr.symm) ≫
        (relativeMVComp k.hom r).inv.app K ≫
        (derivedPullback k.hom).map (Scheme.picardTermwiseSingleMap r M)) ≫ d.hom =
      (derivedPullback r').map a.hom ≫ Scheme.picardTermwiseSingleMap r' N := hc
  have he : (standardSingleBaseChange_topRestriction_sourceIso p M).hom =
      relativeMVUnit j p K ≫ (schemeDerivedDirectImage (j ≫ p)).map a.hom := by
    unfold standardSingleBaseChange_topRestriction_sourceIso relativeMVUnit
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, asIso_hom]
    simp only [a, j, K, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      Category.assoc]
  refine ⟨F.symm, ?_⟩
  have hm := topRestriction_restriction_naturality p s g r
    (pullback.condition (f := p) (g := g)) K T
    (Scheme.picardTermwiseSingleMap r M) j k.hom r' hr.symm s' hs
  have hn : (derivedPullback g).map ((schemeDerivedDirectImage (j ≫ p)).map a.hom) ≫
      schemeDerivedBaseChangeMap (j ≫ p) s' g r'
        (pullback.condition (f := j ≫ p) (g := g)) K' =
    schemeDerivedBaseChangeMap (j ≫ p) s' g r'
        (pullback.condition (f := j ≫ p) (g := g)) ((derivedPullback j).obj K) ≫
      (schemeDerivedDirectImage s').map ((derivedPullback r').map a.hom) := by
    exact topRestriction_baseChange_naturality (j ≫ p) s' g r'
      (pullback.condition (f := j ≫ p) (g := g)) a.hom
  have hb : standardSingleBaseChangeMap p M g ≫ F.hom =
      (derivedPullback g).map (standardSingleBaseChange_topRestriction_sourceIso p M).hom ≫
        standardSingleBaseChangeMap (j ≫ p) N g := by
    have he' : (derivedPullback g).map
        (standardSingleBaseChange_topRestriction_sourceIso p M).hom =
        (derivedPullback g).map (relativeMVUnit j p K) ≫
          (derivedPullback g).map ((schemeDerivedDirectImage (j ≫ p)).map a.hom) := by
      rw [he, Functor.map_comp]
    have hb₀ := topRestriction_finish
      (C := schemeDerivedCategory (pullback (j ≫ p) g)) (D := schemeDerivedCategory A)
      (schemeDerivedDirectImage s')
      (schemeDerivedBaseChangeMap p s g r (pullback.condition (f := p) (g := g)) K ≫
        (schemeDerivedDirectImage s).map (Scheme.picardTermwiseSingleMap r M))
      (relativeMVUnit k.hom s T ≫
        eqToHom (congrArg (fun q ↦ (schemeDerivedDirectImage q).obj
          ((derivedPullback k.hom).obj T)) hs)) F.hom
      ((derivedPullback g).map (relativeMVUnit j p K))
      ((derivedPullback g).map ((schemeDerivedDirectImage (j ≫ p)).map a.hom))
      ((derivedPullback g).map (standardSingleBaseChange_topRestriction_sourceIso p M).hom)
      (schemeDerivedBaseChangeMap (j ≫ p) s' g r'
        (pullback.condition (f := j ≫ p) (g := g)) ((derivedPullback j).obj K))
      (schemeDerivedBaseChangeMap (j ≫ p) s' g r'
        (pullback.condition (f := j ≫ p) (g := g)) K')
      ((relativeMVComp r' j).hom.app K ≫
        eqToHom (congrArg (fun s ↦ (derivedPullback s).obj K) hr.symm) ≫
        (relativeMVComp k.hom r).inv.app K ≫
        (derivedPullback k.hom).map (Scheme.picardTermwiseSingleMap r M))
      d.hom ((derivedPullback r').map a.hom) (Scheme.picardTermwiseSingleMap r' N)
      hm hn hc' hF he'
    unfold standardSingleBaseChangeMap
    change (schemeDerivedBaseChangeMap p s g r
        (pullback.condition (f := p) (g := g)) K ≫
      (schemeDerivedDirectImage s).map (Scheme.picardTermwiseSingleMap r M)) ≫ F.hom =
        (derivedPullback g).map (standardSingleBaseChange_topRestriction_sourceIso p M).hom ≫
          (schemeDerivedBaseChangeMap (j ≫ p) s' g r'
            (pullback.condition (f := j ≫ p) (g := g)) K' ≫
            (schemeDerivedDirectImage s').map (Scheme.picardTermwiseSingleMap r' N))
    exact hb₀
  have hcancel : standardSingleBaseChangeMap p M g =
      ((derivedPullback g).map (standardSingleBaseChange_topRestriction_sourceIso p M).hom ≫
        standardSingleBaseChangeMap (j ≫ p) N g) ≫ F.inv :=
    (Iso.eq_comp_inv (C := schemeDerivedCategory A) F
      (f := (derivedPullback g).map
        (standardSingleBaseChange_topRestriction_sourceIso p M).hom ≫
          standardSingleBaseChangeMap (j ≫ p) N g)
      (g := standardSingleBaseChangeMap p M g)).mpr hb
  exact hcancel.trans (Category.assoc (obj := schemeDerivedCategory A)
    ((derivedPullback g).map (standardSingleBaseChange_topRestriction_sourceIso p M).hom)
    (standardSingleBaseChangeMap (j ≫ p) N g) F.inv)

end AlgebraicGeometry
