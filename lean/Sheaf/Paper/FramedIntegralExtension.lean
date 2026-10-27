module

public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import Sheaf.CategoryTheory.Sites.RelativeTorsorExtension
public import Sheaf.AlgebraicGeometry.RelativeExtensionCohomologyNormalization
public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary
import Sheaf.AlgebraicGeometry.OpenClosedIntegralSections

/-! # Supported Kummer realization of a framed line bundle

Source: Stacks Tags 03AJ, 03PL and 0A45; blueprint main-20261015,
lem-pur-divisor-class, first sentence and final paragraph
(blueprint: def-pur-framed-integral-extension).

The integral torsor extension remembers the frame on the complementary open.
Scalar extension is performed on roots of unity, never on Gm as a Z/m-module.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting
/-- The existing frame torsor, with the existing invertibility bridge made explicit.
Source: Stacks 03AJ and the framed-line refinement of lem-pur-divisor-class
(blueprint: def-pur-framed-integral-extension). -/
abbrev divisorFrameTorsor {T : Scheme.{u}} (L : T.Modules) [Scheme.Modules.IsInvertible L] :=
  @Scheme.Modules.etaleIsoTorsor T L
    (Scheme.Modules.IsInvertible.sheafOfModules_isInvertible L)

/-- The integral extension with its equivariant map and specified zero lift of the frame.
This exposes exactly the characterization in relative_extension_existsUnique.
Source: Stacks 03AJ, relative free-extension construction
(blueprint: def-pur-framed-integral-extension). -/
@[irreducible] def DivisorRelativeExtension {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (L : T.Modules) [Scheme.Modules.IsInvertible L]
    (s : (divisorFrameTorsor L).sheaf.obj.obj (op (Scheme.Etale.mk i.openComplement.ι)))
    (β : Ext.{u + 1} ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj
      (Etale.supportedIntegralConstant Z)) T.gmSheaf 1) : Prop :=
  Etale.RelativeExtensionRepresents i ⟨divisorFrameTorsor L, s⟩ β

/-- The framed torsor determines exactly one normalized integral extension.
Source: Stacks 03AJ, relative free-extension refinement
(blueprint: def-pur-framed-integral-extension).
Proof: the open-closed sequence at the constant integers is short exact. The open
adjunction identifies Hom(j_!Z_W,F) with F(W), taking the inclusion to one. Apply
relative_extension_existsUnique to the actual frame torsor. Its equivariant map
sends the specified section to zero. The characterization is unchanged when the
complement is empty or the support is empty. -/
theorem divisorRelativeExtension_existsUnique {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] (L : T.Modules) [Scheme.Modules.IsInvertible L]
    (s : (divisorFrameTorsor L).sheaf.obj.obj (op (Scheme.Etale.mk i.openComplement.ι))) :
    ∃! β : Ext.{u + 1} ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj
      (Etale.supportedIntegralConstant Z)) T.gmSheaf 1,
      DivisorRelativeExtension i L s β := by
  unfold DivisorRelativeExtension
  exact Etale.relativeExtension_existsUnique i ⟨divisorFrameTorsor L, s⟩

/-- The normalized integral extension of a framed line, selected from its unique
extension characterization. The section s is literally an isomorphism between the
pullbacks of O_T and L, encoded by the existing frame torsor.
Source: Stacks 03AJ, framed-line refinement
(blueprint: def-pur-framed-integral-extension). -/
@[irreducible] def divisorRelativeExtension {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (L : T.Modules) [Scheme.Modules.IsInvertible L]
    (s : (divisorFrameTorsor L).sheaf.obj.obj (op (Scheme.Etale.mk i.openComplement.ι))) :
    Ext.{u + 1} ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj
      (Etale.supportedIntegralConstant Z)) T.gmSheaf 1 :=
  Etale.relativeExtension i ⟨divisorFrameTorsor L, s⟩



attribute [local irreducible] Ext.comp Ext.mk₀ Ext.mapExactFunctor Ext.homEquiv
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors

private theorem integral_section (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (f : Etale.supportedIntegralConstant T ⟶ F) :
    (Sheaf.H.equiv₀ F (MorphismProperty.Over.mkIdTerminal @Etale T)).symm
      (f.hom.app (op (Scheme.Etale.mk (𝟙 T))) (Etale.supportedIntegralOne T)) =
      Ext.mk₀ f := by
  apply (Sheaf.H.equiv₀ F (MorphismProperty.Over.mkIdTerminal @Etale T)).injective
  rw [AddEquiv.apply_symm_apply]
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply]
  rw [show Ext.addEquiv₀ (Ext.mk₀ f) = f from Ext.addEquiv₀.apply_symm_apply _]
  rw [Adjunction.homAddEquiv_apply, constantSheafAdj_homEquiv_apply]
  rfl

private theorem integral_forget_generic {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (P : Sheaf.Torsor G)
    (s : P.sheaf.obj.obj (op (Scheme.Etale.mk i.openComplement.ι))) :
    (Ext.mk₀ (Etale.supportedIntegralUnit i)).comp (Etale.relativeExtension i ⟨P, s⟩)
      (zero_add 1) =
      Sheaf.Torsor.classH1 G (MorphismProperty.Over.mkIdTerminal @Etale T)
        (Quotient.mk _ P) := by
  have hone (V : T.Etaleᵒᵖ) :
      (Etale.supportedIntegralUnit i).hom.app V
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V ⟨1⟩) =
      ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj
        (Etale.supportedIntegralConstant Z)).obj.map
          ((MorphismProperty.Over.mkIdTerminal @Etale T).from V.unop).op
          ((Etale.supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
            (Etale.supportedIntegralOne T)) := by
    let k := ((MorphismProperty.Over.mkIdTerminal @Etale T).from V.unop).op
    have hn := ConcreteCategory.congr_hom
      ((Etale.supportedIntegralUnit i).hom.naturality k) (Etale.supportedIntegralOne T)
    have hu := ConcreteCategory.congr_hom
      ((toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).naturality k) (ULift.up 1)
    dsimp only [Etale.supportedIntegralOne] at hn
    simp only [ConcreteCategory.comp_apply] at hn hu
    change (toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V ⟨1⟩ =
        (Etale.supportedIntegralConstant T).obj.map k (Etale.supportedIntegralOne T) at hu
    exact (congrArg ((Etale.supportedIntegralUnit i).hom.app V) hu).trans hn
  have hβ : Etale.RelativeExtensionRepresents i ⟨P, s⟩ (Etale.relativeExtension i ⟨P, s⟩) := by
    unfold Etale.relativeExtension
    exact (Classical.choose_spec (Etale.relativeExtension_existsUnique i ⟨P, s⟩)).1
  unfold Etale.RelativeExtensionRepresents at hβ
  obtain ⟨E, f, g, hfg, hE, q, hq, hg, _, hβ⟩ := hβ
  let hT := MorphismProperty.Over.mkIdTerminal @Etale T
  let one := (Etale.supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
    (Etale.supportedIntegralOne T)
  let Q := Sheaf.Torsor.lifts hT hE one
  let σ (V : T.Etaleᵒᵖ) (p : P.sheaf.obj.obj V) :
      Q.sheaf.obj.obj V := ⟨q.app V p, (hg V p).trans (hone V)⟩
  have hclass := Sheaf.Torsor.classH1_eq_map_of_equivariant (G := G) hT
    (𝟙 G) P Q σ (by
      intro U V k p
      apply Subtype.ext
      change E.obj.map k (q.app U p) = q.app V (P.sheaf.obj.map k p)
      exact (ConcreteCategory.congr_hom (q.naturality k) p).symm) (by
      intro V x p
      apply Subtype.ext
      change q.app V (P.vadd V x p) =
        q.app V p + f.hom.app V x
      exact hq V x p)
  rw [Sheaf.Torsor.classH1_lifts] at hclass
  have hp : Sheaf.Torsor.classH1 G hT ⟦P⟧ =
      Sheaf.H.δ hE hT one := by
    simpa only [Sheaf.H.map_apply, Ext.comp_mk₀_id] using hclass.symm
  rw [Sheaf.H.δ_apply, integral_section T _ (Etale.supportedIntegralUnit i)] at hp
  rw [hβ]
  exact hp.symm


private theorem integral_iso_generic {Z T : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i] (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (P Q : Sheaf.Torsor G)
    (s : P.sheaf.obj.obj (op (Scheme.Etale.mk i.openComplement.ι)))
    (t : Q.sheaf.obj.obj (op (Scheme.Etale.mk i.openComplement.ι)))
    (e : Sheaf.Torsor.Iso P Q)
    (he : e.iso.hom.hom.app _ s = t) :
    Etale.relativeExtension i ⟨P, s⟩ = Etale.relativeExtension i ⟨Q, t⟩ := by
  have hM : Etale.RelativeExtensionRepresents i ⟨Q, t⟩ (Etale.relativeExtension i ⟨Q, t⟩) ∧
      ∀ β, Etale.RelativeExtensionRepresents i ⟨Q, t⟩ β → β = Etale.relativeExtension i ⟨Q, t⟩ := by
    simpa only [Etale.relativeExtension] using
      Classical.choose_spec (Etale.relativeExtension_existsUnique i ⟨Q, t⟩)
  have hL : Etale.RelativeExtensionRepresents i ⟨P, s⟩ (Etale.relativeExtension i ⟨P, s⟩) := by
    unfold Etale.relativeExtension
    exact (Classical.choose_spec (Etale.relativeExtension_existsUnique i ⟨P, s⟩)).1
  have h : Etale.relativeExtension i ⟨P, s⟩ = Etale.relativeExtension i ⟨Q, t⟩ := by
    apply hM.2
    unfold Etale.RelativeExtensionRepresents at hL ⊢
    obtain ⟨E, f, g, hfg, hE, q, hq, hg, hs, hβ⟩ := hL
    refine ⟨E, f, g, hfg, hE, e.iso.inv.hom ≫ q, ?_, ?_, ?_, hβ⟩
    · intro V x p
      change q.app V (e.iso.inv.hom.app V (Q.vadd V x p)) = _
      have hv := e.symm.map_vadd V x p
      change e.iso.inv.hom.app V (Q.vadd V x p) =
        P.vadd V x (e.iso.inv.hom.app V p) at hv
      exact (congrArg (q.app V) hv).trans (hq V x _)
    · intro V p
      exact hg V (e.iso.inv.hom.app V p)
    · change q.app _ (e.iso.inv.hom.app _ t) = 0
      rw [← he]
      let eV := ((sheafSections T.smallEtaleTopology (Type (u + 1))).obj
        (op (Scheme.Etale.mk i.openComplement.ι))).mapIso e.iso
      exact (congrArg (q.app _) (Iso.hom_inv_id_apply eV s)).trans hs
  exact h


/-- Framed torsor isomorphisms preserve the canonical integral extension.
Source: equivariant relative-extension characterization, Stacks 03AJ
(blueprint: def-pur-framed-integral-extension). -/
theorem divisorRelativeExtension_iso {Z T : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i] (L M : T.Modules)
    [Scheme.Modules.IsInvertible L] [Scheme.Modules.IsInvertible M]
    (s : (divisorFrameTorsor L).sheaf.obj.obj (op (Scheme.Etale.mk i.openComplement.ι)))
    (t : (divisorFrameTorsor M).sheaf.obj.obj (op (Scheme.Etale.mk i.openComplement.ι)))
    (e : Sheaf.Torsor.Iso (divisorFrameTorsor L) (divisorFrameTorsor M))
    (he : e.iso.hom.hom.app _ s = t) :
    divisorRelativeExtension i L s = divisorRelativeExtension i M t := by
  unfold divisorRelativeExtension
  exact integral_iso_generic i T.gmSheaf _ _ s t e he

/-- Forgetting the specified complementary lift gives the positive torsor class.
Source: Stacks 03AJ, equivariant lifting torsors and the extension boundary
(blueprint: def-pur-framed-integral-extension). -/
theorem divisorRelativeExtension_forget {Z T : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i] (L : T.Modules) [Scheme.Modules.IsInvertible L]
    (s : (divisorFrameTorsor L).sheaf.obj.obj (op (Scheme.Etale.mk i.openComplement.ι))) :
    (Ext.mk₀ (Etale.supportedIntegralUnit i)).comp (divisorRelativeExtension i L s)
      (zero_add 1) =
      Sheaf.Torsor.classH1 T.gmSheaf (MorphismProperty.Over.mkIdTerminal @Etale T)
        (Quotient.mk _ (divisorFrameTorsor L)) := by
  unfold divisorRelativeExtension
  exact integral_forget_generic i T.gmSheaf (divisorFrameTorsor L) s

end WeilConjectures.PurityFiniteSetting
