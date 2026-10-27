/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A7
-/
module

public import Sheaf.Paper.ConstantExtensionSheetHeartData
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Sheaf.Paper.ConstantExtensionSheetGeometry
import Sheaf.Paper.ConstantExtensionSheetCoefficientEquivalences
import Sheaf.Paper.ConstantExtensionSheetCommonStageEquivalences

/-! # Cyclic sheet coordinates and Weil hearts

Source: Deligne, Weil II, (1.1.7), (1.1.10), pp. 150--152.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v uC uB vC vB
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Endofunctor
open AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem fixedPairTransportEquivalence
    {C : Type uC} [Category.{vC} C] {B : Type uB} [Category.{vB} B]
    {F : C ⥤ C} {Q : B ⥤ B} {R : C ⥤ B} [R.IsEquivalence]
    (e : R ⋙ Q ≅ F ⋙ R) : (IsoAlgebra.mapOfNatIso e).IsEquivalence := by
  let T := IsoAlgebra.mapOfNatIso e
  let ff : T.FullyFaithful :=
    { preimage := fun {A A'} f ↦ ObjectProperty.homMk
        { f := R.preimage f.hom.f
          h := by
            apply R.map_injective
            apply (cancel_epi (e.hom.app A.carrier)).mp
            have hf := f.hom.h
            change Q.map f.hom.f ≫
                (e.hom.app A'.carrier ≫ R.map A'.obj.str) =
              (e.hom.app A.carrier ≫ R.map A.obj.str) ≫ f.hom.f at hf
            have hn := e.hom.naturality (R.preimage f.hom.f)
            dsimp only [Functor.comp_map] at hn
            rw [R.map_preimage] at hn
            simp only [Functor.map_comp, R.map_preimage]
            calc
              _ = (e.hom.app A.carrier ≫
                  R.map (F.map (R.preimage f.hom.f))) ≫ R.map A'.obj.str :=
                (Category.assoc _ _ _).symm
              _ = (Q.map f.hom.f ≫ e.hom.app A'.carrier) ≫ R.map A'.obj.str :=
                congrArg (fun g ↦ g ≫ R.map A'.obj.str) hn.symm
              _ = _ := by simpa only [Category.assoc] using hf }
      map_preimage := fun f ↦ by
        apply ObjectProperty.hom_ext
        apply Algebra.Hom.ext
        exact R.map_preimage f.hom.f
      preimage_map := fun f ↦ by
        apply ObjectProperty.hom_ext
        apply Algebra.Hom.ext
        exact R.preimage_map f.hom.f }
  let : T.Full := ff.full
  let : T.Faithful := ff.faithful
  let : T.EssSurj := ⟨fun A ↦ by
    let X := R.objPreimage A.carrier
    let b : R.obj X ≅ A.carrier := R.objObjPreimageIso A.carrier
    let a : F.obj X ≅ X := R.preimageIso
      ((e.app X).symm ≪≫ Q.mapIso b ≪≫ A.str ≪≫ b.symm)
    refine ⟨IsoAlgebra.mk X a, ⟨ObjectProperty.isoMk _ (Algebra.isoMk b ?_)⟩⟩
    change Q.map b.hom ≫ A.str.hom =
      (e.hom.app X ≫ R.map a.hom) ≫ b.hom
    simp [a, Category.assoc]⟩
  exact { }

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
variable (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
variable (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

private def sheetComponent (G : ZlSheetGeometry D m hm X₀) (i : Fin m) :
    (zlSheetRestriction D m hm X₀ l hl Ω ⋙
        zlSheetCycle m hm (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω)) ⋙ Pi.eval _ i ≅
      (sfCommonStageWeilFrobeniusPullback D l hl
        (constantExtensionOriginalModel D m hm X₀) Ω ⋙
          zlSheetRestriction D m hm X₀ l hl Ω) ⋙ Pi.eval _ i :=
  if h : i.val + 1 < m then
    eqToIso (by simp only [Functor.assoc, zlSheetCycle, Functor.pi'_eval,
      dif_pos h, zlSheetRestriction]) ≪≫
        zlSheetSuccessorComparison D m hm X₀ l hl Ω G i h
  else
    eqToIso (by simp only [Functor.assoc, zlSheetCycle, Functor.pi'_eval,
      dif_neg h, zlSheetRestriction]; rfl) ≪≫
        zlSheetReturnComparison D m hm X₀ l hl Ω G i h

private def sheetComparison (G : ZlSheetGeometry D m hm X₀) :
    zlSheetRestriction D m hm X₀ l hl Ω ⋙
        zlSheetCycle m hm (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω) ≅
      sfCommonStageWeilFrobeniusPullback D l hl
        (constantExtensionOriginalModel D m hm X₀) Ω ⋙
          zlSheetRestriction D m hm X₀ l hl Ω :=
  NatIso.pi' (fun i ↦ sheetComponent D m hm X₀ l hl Ω G i)

private theorem commonHeart_iso
    {Y : Scheme.{u}} {A B : generalAlgebraicallyClosedConstructibleCategory l Ω Y}
    (e : A ≅ B) (hA : sfCommonStageHeartProperty l Y Ω A) :
    sfCommonStageHeartProperty l Y Ω B := by
  constructor
  · obtain ⟨L, M, hM, ⟨d⟩⟩ := hA.1
    exact ⟨L, M, hM, ⟨e.symm ≪≫ d⟩⟩
  · obtain ⟨L, M, hM, ⟨d⟩⟩ := hA.2
    exact ⟨L, M, hM, ⟨e.symm ≪≫ d⟩⟩

private theorem sheetWeilCoordinates (G : ZlSheetGeometry D m hm X₀)
    (S : ZlSheetCommonClauses D m hm X₀ l hl Ω G) :
    Nonempty (ZlSheetWeilCoordinates D m hm X₀ l hl Ω G) := by
  let e := sheetComparison D m hm X₀ l hl Ω G
  let : (zlSheetRestriction D m hm X₀ l hl Ω).IsEquivalence := S.product.equivalence
  let := fixedPairTransportEquivalence e
  let Q := zlSheetCycleHeartProperty D m hm X₀ l hl Ω
  let : Q.IsClosedUnderIsomorphisms :=
    ⟨fun a hA i ↦ commonHeart_iso l Ω
      (Pi.isoApp ((IsoAlgebra.forget _).mapIso a) i) (hA i)⟩
  have h : Q.inverseImage (IsoAlgebra.mapOfNatIso e) =
      (sfCommonStageHeartProperty l
        (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left Ω).inverseImage
          (sfCommonStageWeilForget D l hl (constantExtensionOriginalModel D m hm X₀) Ω) := by
    funext A
    apply propext
    change (∀ i, sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω
      ((zlSheetRestriction D m hm X₀ l hl Ω).obj A.carrier i)) ↔ _
    constructor
    · intro ha
      exact ⟨(S.product.standard true 0 A.carrier).mpr (fun i ↦ (ha i).1),
        (S.product.standard false 0 A.carrier).mpr (fun i ↦ (ha i).2)⟩
    · intro ha i
      exact ⟨(S.product.standard true 0 A.carrier).mp ha.1 i,
        (S.product.standard false 0 A.carrier).mp ha.2 i⟩
  let E := (IsoAlgebra.mapOfNatIso e).asEquivalence.congrFullSubcategory h
  refine ⟨{
    comparison := e
    successor_normalization := ?_
    return_normalization := ?_
    equivalence := E
    identification := Iso.refl _
    exact_limits := inferInstance
    exact_colimits := inferInstance }⟩
  · intro N i hi
    change ((sheetComponent D m hm X₀ l hl Ω G i).hom.app N) ≍ _
    simp only [sheetComponent, dif_pos hi, Iso.trans_hom, NatTrans.comp_app,
      eqToIso.hom, eqToHom_app]
    exact eqToHom_comp_heq _ _
  · intro N i hi
    change ((sheetComponent D m hm X₀ l hl Ω G i).hom.app N) ≍ _
    simp only [sheetComponent, dif_neg hi, Iso.trans_hom, NatTrans.comp_app,
      eqToIso.hom, eqToHom_app]
    exact eqToHom_comp_heq _ _

/-- Cyclic geometric sheet coordinates at every coefficient stage and on Weil hearts.
Source: Deligne, Weil II, (1.1.7) and paragraph after (1.1.10), pp. 150--152
(blueprint: lem-zl-constant-extension-sheet-heart-coordinates).

Proof, following the seven DAG steps:
1. The degree-m finite field extension is Galois with cyclic q-power generator
(lem-sfb-finite-field-galois-frobenius). Split its tensor with the closure by all embeddings
(lem-exc-finite-galois-algebra-tensor-decomposition); the orthogonal idempotents give the
clopen sheets (lem-weil-pbc-spec-finite-product-fields). Base change along X₀ glues the
maps a tensor t tensor b to a tensor sigma(t)b on affine opens
(lem-weil-pbc-fibre-product-affine-spectra).
2. Write gamma for inverse q-power Frobenius. On affine tensors H fixes a,t and acts by
gamma on b, giving H j_sigma = j_(gamma^-1 sigma) g_X. Its m iterates visit every sheet,
and gamma^m fixes k_m. This gives the successor and return identities and identifies the
new-model Frobenius, with no assertion of k-linearity (def-weil-frobenius-detailed).
3. Reindex pro-etale sites by each coordinate isomorphism and its inverse
(lem-weil-proetale-isomorphism-inverse-image). The actual finite and integral derived
pullbacks are termwise exact inverse images (lem-weil-isomorphism-derived-pullback).
Their inverse and scalar identities persist through rationalization and common stages
(lem-pod-isomorphism-field-transport). Exact inverse images commute with cohomology,
preserve both standard halves, and restrict to exact heart equivalences.
4. Apply finite-clopen decomposition (lem-pur-finite-clopen-derived-decomposition), then
these coordinate equivalences. Pullback composition identifies that composite with the
actual h_i pullbacks (lem-weil-pbc-proetale-derived-pullback-composition and
lem-pod-integral-pullback-composition). The inverse first transports to each sheet and
then glues; reductions, scalar extension and cohomology are componentwise. Each h_i
is a projection after this equivalence, while its coordinate factor r_i is an equivalence.
5. Use those specified compositors to identify h_i*H*N with A_(i+1), and at the return
with P^m A_0. The displayed comparison is tau inverse, so the induced IsoAlgebra map
has structure a_i = h_i*(eta) tau_i^-1. Conversely glue the carriers and lift these
structure arrows by full faithfulness; lift their inverses to obtain a Weil sheaf
(def-weil-weil-sheaf-complex).
6. Naturality transforms the Weil morphism condition precisely into
u_i a_i = a'_i u_(i+1), including u_last a_last = a'_last P^m(u_0) at the return.
Full faithfulness lifts every such tuple uniquely; identities and composition are
componentwise. IsoAlgebra records exactly these equations, with no extra morphisms.
7. Integral composition is normalized on finite reductions and is associative
(lem-pod-integral-pullback-composition). Its scalar compatibility
(lem-pod-pullback-identities-scalar-extension) survives rationalization and representation
at any common coefficient field (def-weil-derived-pullback-tensor-hom). Thus every
successor and return comparison retains the normalization of def-zl-weil-ind-sheaf-category.
-/
theorem constantExtensionSheetHeartCoordinates :
    ∃ G : ZlSheetGeometry D m hm X₀,
      ZlSheetCoefficientClauses D m hm X₀ l hl ∧
      Nonempty (ZlSheetCommonClauses D m hm X₀ l hl Ω G) ∧
      Nonempty (ZlSheetWeilCoordinates D m hm X₀ l hl Ω G) := by
  obtain ⟨G⟩ := constantExtensionSheetGeometry D m hm X₀
  have hcoeff := constantExtensionSheetCoefficientEquivalences D m hm X₀ l hl G
  obtain ⟨S⟩ := constantExtensionSheetCommonStageEquivalences D m hm X₀ l hl Ω G hcoeff
  exact ⟨G, hcoeff, ⟨S⟩, sheetWeilCoordinates D m hm X₀ l hl Ω G S⟩

end WeilConjectures
