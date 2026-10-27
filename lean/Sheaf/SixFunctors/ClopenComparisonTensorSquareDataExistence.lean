/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.ClopenComparisonTensorSquareData
import all Sheaf.SixFunctors.OpenTensorNormalization
import all Sheaf.SixFunctors.OpenOperationModels
import Sheaf.SixFunctors.OpenTensorSupportAux
import Sheaf.SixFunctors.CanonicalPullTensor
import Sheaf.SixFunctors.ClopenReverseModuleAdjunction

/-! # Existence of normalized clopen tensor data -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization
namespace SheafOfModules.ClopenComparisonTensorSquare

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem open_tensor_exists {m : Mode} {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (R : Sheaf (topology m X) CommRingCat.{u + 1})
    (e : OpenExtension m j R) (a : TensorModel R)
    (b : TensorModel (restrictRing m j R)) : Nonempty (OpenTensor m j R e a b) := by
  let S : Sheaf (topology m X) CommRingCat.{u + 1} := ⊤_ _
  let P := (baseChange m (𝟙 X)).sheafPushforwardContinuous CommRingCat.{u + 1}
    (topology m X) (topology m X)
  have hp : IsTerminal (P.obj S) := isLimitOfHasTerminalOfPreservesLimit P
  let c : R ⟶ P.obj S := hp.from R
  let d := input m (𝟙 X) j R S c
  let t := normalizedSiteSquare d
  obtain ⟨a'⟩ := tensorModel_exists d.S
  obtain ⟨b'⟩ := tensorModel_exists (restrictRing m d.j' d.S)
  obtain ⟨o, ha, hb, _, _, _⟩ := normalizedOperations_exists d t a b a' b'
    (normalizedRightSquare t) (normalizedRightSquare_sections t)
  let o' : Operations d t := { o with opens := ⟨e, o.opens.extension'⟩ }
  have hmu : o'.tensorX = a := ha
  have hnu : o'.tensorU = b := hb
  have h : Nonempty (OpenTensor m j R e o'.tensorX o'.tensorU) := by
    have (Z : Der (restrictRing m j R) × Der R) :
        IsIso ((gammaInverse o').app Z) := by
      rcases Z with ⟨M,N⟩
      exact tensor_open_extension_comparison_isIso o' M N
    have : IsIso (gammaInverse o') := NatIso.isIso_of_isIso_app _
    let delta := (asIso (gammaInverse o')).symm
    refine ⟨{
      ordinary := o'.restrictionTensor
      pure_sections := o'.restrictionTensor_sections
      tensorComparison := o'.tensorComparison
      delta := delta
      inverse_transpose := ?_ }⟩
    intro M N
    exact (o'.opens.adj.homEquiv _ _).apply_symm_apply _
  simpa only [hmu, hnu] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem assemble_data {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    (o : Operations d t) {A : Scheme.{u}} (s : A ⟶ d.U') [IsOpenImmersion s]
    (tp : PullTensor m d.g d.R d.S d.coefficient o.gPull o.tensorX o.tensorX')
    (tq : PullTensor m d.gU (restrictRing m d.j d.R) (restrictRing m d.j' d.S)
      (cornerCoefficient t) o.gUPull o.tensorU o.tensorU')
    (e : OpenExtension m s (restrictRing m d.j' d.S))
    (ar : restrict m s (restrictRing m d.j' d.S) ⊣ e.ordinary)
    (har : ∀ M, e.adjunction.unit.app M ≫ ar.counit.app M = 𝟙 M)
    (ta : TensorModel (restrictRing m s (restrictRing m d.j' d.S)))
    (tb : OpenTensor m d.j' d.S o.opens.extension' o.tensorX' o.tensorU')
    (ts : OpenTensor m s (restrictRing m d.j' d.S) e o.tensorU' ta) :
    Nonempty (Data o s) := by
  let L := e.ordinary.mapDerivedCategory
  let S' := (restrict m s (restrictRing m d.j' d.S)).mapDerivedCategory
  let B := o.opens.jShriek'
  let RB := o.opens.jStar'
  let aS := exactDerivedAdjunction e.adjunction
  let aB := o.opens.adj'
  let U := ta.functor
  let dk : (L ⋙ B).prod (𝟭 _) ⋙ o.tensorX'.functor ≅
      (𝟭 _).prod (RB ⋙ S') ⋙ U ⋙ (L ⋙ B) :=
    NatIso.ofComponents
      (fun Z ↦ tb.delta.app (L.obj Z.1, Z.2) ≪≫
        B.mapIso (ts.delta.app (Z.1, RB.obj Z.2))) (by
      intro X Y f
      have hb := tb.delta.hom.naturality (Prod.mkHom (L.map f.1) f.2)
      have hs := ts.delta.hom.naturality (Prod.mkHom f.1 (RB.map f.2))
      dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map,
        Functor.comp_obj, Functor.prod_obj, Functor.id_obj] at hb hs ⊢
      simp only [Iso.trans_hom, Functor.mapIso_hom]
      erw [← Category.assoc, hb, Category.assoc, ← B.map_comp, hs, B.map_comp]
      exact (Category.assoc _ _ _).symm)
  refine ⟨{
    tensorP := tp
    tensorQ := tq
    tensorB := tb
    extensionS := e
    tensorA := ta
    tensorS := ts
    rightAdjunction := ar
    counit_normalization := har
    deltaK := dk
    inverse_transposeK := ?_ }⟩
  intro M N
  change (aS.comp aB).homEquiv _ _
    (B.map (ts.delta.inv.app (M, RB.obj N)) ≫ tb.delta.inv.app (L.obj M, N)) = _
  rw [Adjunction.comp_homEquiv]
  change aS.homEquiv _ _ ((aB.homEquiv _ _)
    (B.map (ts.delta.inv.app (M, RB.obj N)) ≫ tb.delta.inv.app (L.obj M, N))) = _
  erw [aB.homEquiv_naturality_left, tb.inverse_transpose]
  erw [aS.homEquiv_naturality_right, ts.inverse_transpose]
  dsimp only [restrictionModel, Functor.comp_obj, Functor.prod_obj,
    Functor.id_obj] at *
  have hn := ts.tensorComparison.comparison.inv.naturality
    (Prod.mkHom (aB.unit.app (L.obj M)) (𝟙 (RB.obj N)))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj,
    restrictionModel, Functor.id_obj] at hn
  rw [Functor.map_comp]
  simp only [Category.assoc]
  slice_lhs 2 3 => erw [← hn]
  simp only [← Category.assoc]
  rw [← U.map_comp]
  have hp :
      Prod.mkHom (aS.unit.app M) (𝟙 (S'.obj (RB.obj N))) ≫
        Prod.mkHom (S'.map (aB.unit.app (L.obj M))) (S'.map (𝟙 (RB.obj N))) =
      Prod.mkHom ((aS.comp aB).unit.app M) (𝟙 _) := by
    ext
    · exact (Adjunction.comp_unit_app aS aB M).symm
    · simp
  rw [hp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Construct compatible tensor and clopen adjunction data on the ringed site.
Source: Stacks 04TS, 07A4 and 0GL1.
(blueprint: lem-sf-clopen-comparison-tensor-data-existence).

Proof: the proper/open calculus makes the canonical lift clopen. Construct its
open extension and tensor model, and the canonical tensor pullback comparisons
for p and q, transported along the unique adjunction and derived-functor
isomorphisms to the supplied presentations. Restriction preserves pure tensors
and flat K-flat representatives, hence supplies tensor comparisons for both
opens. The localized open projection formula supplies their delta isomorphisms
with the displayed transpose. For the clopen lift, gluing along the image and
its complementary open identifies modules with pairs; restriction is the first
projection and extension is insertion with zero. Thus restriction also has that
extension as right adjoint, with counit inverse to the open unit. On the vertical
site the same constructions commute with every coefficient transition. Compose
the two open tensor maps for deltaK; naturality of the restriction tensor
comparison and the composite-unit formula verify its required transpose. -/
theorem data_nonempty (m : Mode) {A B C D : Scheme.{u}}
    (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (R : Sheaf (topology m D) CommRingCat.{u + 1})
    (S : Sheaf (topology m B) CommRingCat.{u + 1})
    (c : R ⟶ ((baseChange m p).sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology m D) (topology m B)).obj S)
    (t : SiteSquare (input m p i R S c))
    (o : Operations (input m p i R S c) t) (_a : Assertion o) :
    Nonempty (Data o (AlgebraicGeometry.ProEtale.StrictTower.squareLift k r p i h)) := by
  let s := AlgebraicGeometry.ProEtale.StrictTower.squareLift k r p i h
  have : IsClosedImmersion s := by dsimp only [s]; infer_instance
  obtain ⟨tp⟩ := canonical_pull_tensor m _ _ _ _ o.gPull o.tensorX o.tensorX'
  obtain ⟨tq⟩ := canonical_pull_tensor m _ _ _ _ o.gUPull o.tensorU o.tensorU'
  obtain ⟨e, ar, har⟩ := clopen_reverse_module_adjunction m s
    (restrictRing m (input m p i R S c).j' S)
  obtain ⟨ta⟩ := tensorModel_exists (restrictRing m s
    (restrictRing m (input m p i R S c).j' S))
  obtain ⟨tb⟩ := open_tensor_exists (input m p i R S c).j' S
    o.opens.extension' o.tensorX' o.tensorU'
  obtain ⟨ts⟩ := open_tensor_exists s (restrictRing m (input m p i R S c).j' S)
    e o.tensorU' ta
  exact assemble_data o s tp tq e ar har ta tb ts

end SheafOfModules.ClopenComparisonTensorSquare
