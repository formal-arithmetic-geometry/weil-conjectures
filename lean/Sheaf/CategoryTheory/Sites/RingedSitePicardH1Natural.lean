/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.CategoryTheory.Sites.RingedSitePicardData
import Sheaf.CategoryTheory.Sites.GeometricInverseImageExact
import Sheaf.CategoryTheory.Sites.InverseImageLocalFamilies
import Sheaf.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Picard classes and H1 of units, naturally in ringed-topos pullback

Source: Stacks Project, Cohomology on Sites, Tags 040E and 03AJ, with the
extension-of-scalars naturality argument
(blueprint: lem-sfb-ringed-site-picard-h1-natural).
-/

@[expose] public section

universe w h uC vC uD vD
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.RingedSitePicard
set_option autoImplicit false

/-- Picard classes are H1 of units, by their generator torsors, and scalar pullback
commutes with this identification. The module pullback is specified by its adjunction
to the supplied induced direct image: the tensor-Hom adjunction identifies it uniquely
with B tensor over inverse(A) inverse(M). Thus no flatness or arbitrary map is assumed.

Source: Stacks Project, Cohomology on Sites, Tags 040E and 03AJ
(blueprint: lem-sfb-ringed-site-picard-h1-natural).

Proof: (1) Glue frames and their inverse linear maps. Two frames differ by a unique unit,
so the generator sheaf is a units torsor. (2) For a torsor T sheafify the set quotient
(T times A)/((ut,a)=(t,ua)); in a local frame its sections are A. Glue the module
operations in those charts (lem-weil-pbc-site-sheafification-sections-local).
(3) Evaluation [t,a] to t(a) and t to (a to [t,a]) give inverse constructions.
(4) A pair of frames gives a tensor frame; multiplying one by u and the other by
u inverse fixes it. Torsor classification (lem-sfb-site-abelian-torsor-h1) gives
additivity and the group isomorphism, normalized by its extension class.
(5) Exact geometric inverse image and lem-sfb-topos-cohomology-pullback-delta give
the resolution comparison, including independence of every resolution and beta.
(6) Inverse image preserves locally inhabited sheaves and finite limits. Pull the
universal frame back and extend scalars; b tensor a maps to b f-sharp(a), with
inverse b to b tensor 1. This proves the pulled module is a line without flatness.
The module adjunction is the tensor-Hom adjunction, transported through the set
adjunction (lem-weil-pbc-geometric-module-construction).
(7) The integer sheaf is free abelian on the final sheaf; inverse image preserves
it and its section 1 by preservation of colimits and finite products.
(8) Map the pulled generator extension to the extension of the pulled line: in a
local frame v send h+n j(v) to rho(h)+n j'(s(v)). Replacing v by u+v replaces h
by h-nu, leaving this formula unchanged, so it glues.
(9) Compatibility of resolution pullback with boundaries and naturality for this
extension map give the displayed equality. All global sections are Hom from the
final sheaf; neither site is assumed to possess a final object. -/
theorem picard_h1_natural
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : D, HasWeakSheafify (K.over U) AddCommGrpCat.{w}]
    [∀ U : D, (K.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasExt.{h} (Sheaf J AddCommGrpCat.{w})]
    [HasExt.{h} (Sheaf K AddCommGrpCat.{w})]
    (A : Sheaf J CommRingCat.{w}) (B : Sheaf K CommRingCat.{w}) :
    ∃ (cA : Comparison A) (cB : Comparison B),
      ∀ f : RingedToposMorphismOfUniverses (ring B) (ring A),
        ∃ (P : CohomologyTransport f)
          (ρ : P.abelian.functor.obj (units A) ⟶ units B)
          (F : ringedSiteModules.{w} (ring A) ⥤ ringedSiteModules.{w} (ring B)),
          Nonempty (F ⊣ f.modules) ∧
          (∃ (AI : Sheaf K CommRingCat.{w})
            (I : SheafOfModules.AlgebraicInverseImage f.inverse A AI) (c : AI ⟶ B),
            I.ringUnderlying.hom ≫ (sheafCompose K (forget CommRingCat.{w})).map c =
              f.ringMap ∧
            ∀ M : ringedSiteModules.{w} (ring A),
              Nonempty (F.obj M ≅ SheafOfModules.changeOfRingsOfUniverses.{vD, uD, w, w} c
                (I.modules.obj M))) ∧
          ComputesByResolutions P (units A) ∧ IsStructuralUnitsMap P ρ ∧
          ∀ M : Line A, ∃ N : Line B,
            Nonempty (N.val ≅ F.obj M.val) ∧
            cB.comparison (lineClass N) =
              Sheaf.H.map ρ 1 (pullback P 1 (cA.comparison (lineClass M))) := by
  sorry

end CategoryTheory.RingedSitePicard
