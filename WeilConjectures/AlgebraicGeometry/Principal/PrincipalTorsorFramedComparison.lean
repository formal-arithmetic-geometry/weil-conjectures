/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PrincipalTorsorComparisons.PrincipalTorsorSignTypes
/-! Independent comparison result for the principal torsor sign calculation. -/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite HomologicalComplex
namespace AlgebraicGeometry.Etale
/-- A framed extension is the inverse-section localization pushout and its normalized
relative class is minus the class of (0,aug(g)).
Source: Stacks 03AJ, 06XU; framed-extension cocycle calculation of the principal-torsor node.
Proof: evaluate F at the global frame and extend it from the constant integer sheaf.
The equation F(s)=0 gives the left component adjoint to -g of a morphism from localization
to the given extension, proving the pushout-class equation by Ext-class naturality.
Extend the coefficient augmentation over E using injectivity. Factor its differential through
Q into cycles c. The first resolution extension-class formula gives beta=-extMk(c).
For u=hF(e), du=c(p1) and res(u)=-aug(g). Add the relative differential of u to the
normalized representative of beta to obtain (0,-aug(g)), proving the asserted negative class.
(blueprint: lem-pur-principal-torsor-framed-comparison). -/
theorem principalTorsorFramedComparison
    (C : PrincipalTorsorComparisons.{u}) (hC : C.Normalized) :
  ∀ (T Z : Scheme.{u}) (i : Z ⟶ T) [IsClosedImmersion i]
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (P : Sheaf.Torsor G)
    (e : P.sheaf.obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (s : P.sheaf.obj.obj (op (Scheme.Etale.mk W.ι)))
    (g : G.obj.obj (op (Scheme.Etale.mk W.ι)))
    (_hs : s = P.vadd (op (Scheme.Etale.mk W.ι)) g
      (P.sheaf.obj.map
        ((MorphismProperty.Over.mkIdTerminal @Etale T).from (Scheme.Etale.mk W.ι)).op e))
    (E : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : G ⟶ E) (b : E ⟶ (principalTorsorLocalization i W h).X₃)
    (hab : a ≫ b = 0) (hE : (ShortComplex.mk a b hab).ShortExact)
    (F : P.sheaf.obj ⟶ E.obj ⋙ forget AddCommGrpCat.{u + 1})
    (_hF : ∀ (U : T.Etaleᵒᵖ) (x : G.obj.obj U) (p : P.sheaf.obj.obj U),
      @id (E.obj.obj U) (F.app U (P.vadd U x p)) = F.app U p + a.hom.app U x)
    (_hbF : ∀ (U : T.Etaleᵒᵖ) (p : P.sheaf.obj.obj U),
      b.hom.app U (F.app U p) = (principalTorsorLocalization i W h).g.hom.app U
        (torsorExtensionOne T U.unop))
    (_hFs : @id (E.obj.obj (op (Scheme.Etale.mk W.ι)))
      (F.app (op (Scheme.Etale.mk W.ι)) s) = 0),
    (∃ hL : (principalTorsorLocalization i W h).ShortExact,
      hE.extClass = hL.extClass.comp
        (Ext.mk₀ ((C.openSection T Z i W h G).symm (-g))) (add_zero 1)) ∧
    ∀ (L : InjectiveResolution G)
      (y : relativeCohomology T (Scheme.Etale.mk W.ι) L 1),
      TorsorSignedRepresents T (Scheme.Etale.mk W.ι) L.cocomplex 0 0
        ((L.ι.f 0).hom.app (op (Scheme.Etale.mk W.ι)) g) y →
      C.relative T Z i W h G L 0 hE.extClass = -y := by sorry
end AlgebraicGeometry.Etale
