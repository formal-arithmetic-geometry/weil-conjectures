/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction

/-! # The section formula for the canonical small-etale direct-image mate

Source: Stacks Project, Descent, Tag 03LC (3), and Cohomology, Tag 02N7.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- In normalized tensor-section coordinates the direct-image mate is module base change.

Source: Stacks Project, Descent, Tag 03LC (3); Cohomology, Tag 02N7 in degree zero.
(blueprint: lem-trf-zariski-etale-pushforward-section-formula).

Proof: transpose the defining counit mate by the extension/restriction adjunction.
The conjugate-iso unit equation identifies its transpose with pushforward of the
extension unit. On every open, the hypothesis on r identifies this with restriction
along the canonical preimage-open isomorphism. The open-unit normalization for e
then sends s to the tensor-pullback section 1 tensor s. Linearity gives the formula
b tensor s mapped to a_V-sharp(b) times v'-pullback(s). The defining adjunction for
moduleBaseChangeMap has this same transpose, by the normalized scheme pullback unit.
Restricting to opens of V and then using sheafification determines the maps from
these local tensor generators, so their maps on all global sections agree. Module
naturality of e supplies the identifications for the counit. The argument includes
empty opens and zero modules, and needs no flatness of maps between test objects. -/
theorem zariskiEtale_pushforward_section_formula
    (c : ∀ T : Scheme.{u}, ZariskiEtaleModuleContext T)
    (e : ∀ (T : Scheme.{u}) (F : T.Modules) [F.IsQuasicoherent],
          (SheafOfModules.toSheaf (smallEtaleModuleRing T)).obj ((c T).extension.obj F) ≅
            etaleTensorSectionsSheaf F)
    (hlinear : ∀ (T : Scheme.{u}) (F : T.Modules) [F.IsQuasicoherent]
            (V : T.Etale) (b : Γ(V.left, ⊤))
            (s : ((c T).extension.obj F).val.obj (op V)),
          (e T F).hom.hom.app (op V) (b • s) =
            b • (@id (Γ((tensorPullback V.hom).obj F, ⊤))
              ((e T F).hom.hom.app (op V) s)))
    (hnatural : ∀ (T : Scheme.{u}) (F K : T.Modules) [F.IsQuasicoherent] [K.IsQuasicoherent]
            (h : F ⟶ K) (V : T.Etale),
          ((SheafOfModules.toSheaf (smallEtaleModuleRing T)).map
            ((c T).extension.map h)).hom.app (op V) ≫ (e T K).hom.hom.app (op V) =
              (e T F).hom.hom.app (op V) ≫ ((tensorPullback V.hom).map h).app ⊤)
    (hopen : ∀ (T : Scheme.{u}) (F : T.Modules) [F.IsQuasicoherent] (W : T.Opens),
          ((c T).adjunction.unit.app F).app W ≫
              (e T F).hom.hom.app (op ((AlgebraicGeometry.gabberOpenEtale T).obj W)) ≫
                (tensorOpenSectionIso T F W).hom = 𝟙 _)
    {U T : Scheme.{u}} (a : U ⟶ T)
    (hp : (smallEtaleModulePushforward a).IsRightAdjoint)
    (r : smallEtaleModulePushforward a ⋙ (c T).restriction ≅
      (c U).restriction ⋙ pushforward a)
    (hr : ∀ (G : SmallEtaleModules U) (W : T.Opens),
      (r.hom.app G).app W =
        G.val.presheaf.map (AlgebraicGeometry.gabberPreimageEtaleIso a W).hom.op)
    (H : U.Modules) [H.IsQuasicoherent] [((pushforward a).obj H).IsQuasicoherent]
    (V : T.Etale) :
    (e T ((pushforward a).obj H)).inv.hom.app (op V) ≫
        ((SheafOfModules.toSheaf (smallEtaleModuleRing T)).map
          (zariskiEtalePushforwardComparison a (c U) (c T) hp r H)).hom.app (op V) ≫
        (e U H).hom.hom.app (op (a.Etale.obj V)) =
      (moduleBaseChangeMap a (pullback.fst V.hom a) V.hom
        (pullback.snd V.hom a) pullback.condition.symm H).app ⊤ := by
  sorry

end AlgebraicGeometry.Scheme.Modules
