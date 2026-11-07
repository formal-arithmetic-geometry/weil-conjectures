/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerEtaleDescentData
import Submission.WeilConjectures.AlgebraicGeometry.Etale.EtaleLocalIsoCoverFromProEtaleSection
import Submission.WeilConjectures.ConstructibleSheaf.InternalHom

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Etale representatives of pro-etale derived Isom sections

Source: Stacks Project, proetale.tex, Tag 09B1; etale geometric-point lifting.
(blueprint: new-lem-weil-pbc-lisse-finite-level-etale-local-representative).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Pro-etale local sections of the derived Isom presheaf with bounded-below target admit
etale representatives at every geometric point.

Source: Stacks Project, proetale.tex, Tag 09B1; etale geometric-point lifting.
(blueprint: new-lem-weil-pbc-lisse-finite-level-etale-local-representative).

Proof: the bounded-below comparison lifts each supplied pro-etale Isom section to an
actual isomorphism on an etale cover, by
exists_etale_iso_cover_of_proetale_local_iso_section. Lift the given geometric point
through that cover using joint surjectivity. The isomorphism on that cover member is
the required pointed representative. This includes empty schemes and zero objects.
-/
theorem exists_etale_local_representative_of_proetale_local_iso_sections
    (X : Scheme.{u}) (U : X.ProEt)
    {B : Type (u + 1)} [CommRing B]
    (A D : DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (hD : DerivedCategory.TStructure.t.plus D)
    (hsections : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (x : Spec (.of Ω) ⟶ U.left),
      ∃ (V : U.left.Etale) (v : (pointSmallEtale x).fiber.obj V),
        Nonempty ((derivedLocalIsoPresheaf (ProEt.topology U.left) B
          ((derivedComparison U.left B).obj A)
          ((derivedComparison U.left B).obj D)).obj
            (op ((toProEt U.left).obj V)))) :
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (x : Spec (.of Ω) ⟶ U.left),
      ∃ (V : U.left.Etale) (v : (pointSmallEtale x).fiber.obj V),
        Nonempty ((localIsomorphismRestriction U.left B V).obj A ≅
          (localIsomorphismRestriction U.left B V).obj D) := by
  intro Ω instΩ instSep x
  obtain ⟨V, v, s⟩ := hsections Ω x
  obtain ⟨𝒰, h𝒰⟩ := exists_etale_iso_cover_of_proetale_local_iso_section
    U.left V A D hD (Classical.choice s)
  obtain ⟨i, t, ht⟩ := _root_.AlgebraicGeometry.Scheme.Cover.exists_comp_eq_of_isSepClosed 𝒰 v.left
  let W : U.left.Etale := Etale.mk (𝒰.f i ≫ V.hom)
  let w : (pointSmallEtale x).fiber.obj W :=
    Over.homMk t (by
      change t ≫ (𝒰.f i ≫ V.hom) = x
      rw [← Category.assoc, ht]
      exact v.w)
  exact ⟨W, w, h𝒰 i⟩

end AlgebraicGeometry.Scheme
