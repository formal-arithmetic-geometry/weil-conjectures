/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q85
-/
module

public import Sheaf.AlgebraicGeometry.ReducedCurveDualizingModule
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.CoherentSheafHom
import WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyAgree
import WeilConjectures.Topology.ClosedImmersionPushforwardCohomology

/-! # Dualizing adjunction for a reduced closed subcurve

Source: Stacks Project, curves.tex, Tag 0E33
(lemma-closed-immersion-dim-1-CM), part (2), with evaluation at 1.
(blueprint: lem-sfb-closed-subcurve-dualizing-adjunction).

The isomorphisms respect isomorphisms of the chosen representing pairs. The evaluation
map is specified on every open; its sections identify the sheaf Hom with the annihilator.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Closed-subcurve duality and its evaluation-at-one annihilator description.
Source: Stacks Project, curves.tex, Tag 0E33(2), using Tag 0BS2(5).
(blueprint: lem-sfb-closed-subcurve-dualizing-adjunction).

Proof (the node's five steps):
1. Properness over the field gives Noetherian schemes and coherent structure modules
   (lem-trf-proper-field-invertible-coherent, applied to the unit). The chosen dualizing
   modules are coherent by lem-sfb-reduced-curve-dualizing-module. Closed pushforward
   preserves coherence by lem-weil-pbc-closed-immersion-coherent-equivalence; hence the
   sheaf Hom is coherent by lem-weil-pbc-coherent-sheaf-hom-coherent.
2. The structure map identifies i_*O_Y with O_X/J (def-weil-closed-immersion and
   def-sbc-closed-immersion-ideal-sheaf). Evaluate a local linear map at 1. Its value is
   killed by J. Conversely a section killed locally by J sends a local quotient class
   of a to a times that section. Local lifts differ by J, so the values agree and glue.
   These inverse formulas commute with restrictions and scalars (def-pur-sheaf-hom).
3. The coherent closed-immersion equivalence supplies a coherent D on Y whose
   pushforward is this annihilator. Full faithfulness and unique factorization through
   the annihilator identify Hom_Y(G,D) with Hom_X(i_*G,omega_X), naturally and k-linearly.
4. lem-sc-zariski-module-abelian-cohomology-agree and
   lem-sc-cohomology-closed-immersion-pushforward identify H^1(X,i_*G) with H^1(Y,G).
   Naturality under scalar endomorphisms makes this comparison k-linear. Duality for X
   now identifies Hom_Y(G,D) with the k-linear dual of H^1(Y,G).
5. Uniqueness of the representing pair on Y identifies D with omega_Y: for a natural
   Hom bijection T, use T_D(id) and T^{-1}_{omega_Y}(id), whose composites are identities
   by naturality. Push forward and compose to obtain the displayed isomorphism.
   These constructions respect isomorphisms of both representing pairs, giving the
   stated commuting square. Step 2 supplies the evaluation map and its exact image.
   Neither connectedness nor invertibility of a dualizing module is used. -/
theorem exists_closedSubcurveDualizingAdjunction (k : Type u) [Field k]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [IsProper (Y ↘ Spec (.of k))]
    [IsReduced X] [IsReduced Y] [Nonempty X] [Nonempty Y]
    (hX : X.IsPureDimension 1) (hY : Y.IsPureDimension 1)
    (i : Y ⟶ X) [i.IsOver (Spec (.of k))] [IsClosedImmersion i] :
    ∃ e : ∀ (DX : ReducedCurveDualizingPair k X) (DY : ReducedCurveDualizingPair k Y),
        (Scheme.Modules.pushforward i).obj DY.omega ≅
          SheafOfModules.homObj (R := X.sheaf)
            ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Y.ringCatSheaf)) DX.omega,
      (∀ (DX DX' : ReducedCurveDualizingPair k X)
          (DY DY' : ReducedCurveDualizingPair k Y)
          (a : DX.omega ≅ DX'.omega) (b : DY.omega ≅ DY'.omega),
        (∀ (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
          (f : F ⟶ DX.omega), DX'.duality F hF (f ≫ a.hom) = DX.duality F hF f) →
        (∀ (G : Y.Modules) (hG : RingedSpace.IsCoherent Y.toRingedSpace G)
          (g : G ⟶ DY.omega), DY'.duality G hG (g ≫ b.hom) = DY.duality G hG g) →
        (Scheme.Modules.pushforward i).map b.hom ≫ (e DX' DY').hom =
          (e DX DY).hom ≫ SheafOfModules.homObjMap (R := X.sheaf)
            (𝟙 ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Y.ringCatSheaf)))
            a.hom) ∧
      (∀ DX : ReducedCurveDualizingPair k X,
        ∃ ev : SheafOfModules.homObj (R := X.sheaf)
            ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Y.ringCatSheaf))
            DX.omega ⟶ DX.omega,
          (∀ (U : X.Opens)
            (φ : Γ(SheafOfModules.homObj (R := X.sheaf)
              ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Y.ringCatSheaf))
              DX.omega, U)),
            ev.val.app (op U) φ = φ.app (op (Over.mk (𝟙 U))) (1 : Γ(Y, i ⁻¹ᵁ U))) ∧
          (∀ U : X.Opens, Function.Injective (ev.val.app (op U))) ∧
          (∀ (U : X.Opens) (w : Γ(DX.omega, U)),
            w ∈ Set.range (ev.val.app (op U)) ↔
              ∀ (V : X.Opens) (hVU : V ≤ U) (j : Γ(X, V)), j ∈ i.ker.idealOfOpens V →
                j • DX.omega.val.map (homOfLE hVU).op w = 0)) := by
  sorry

end AlgebraicGeometry
