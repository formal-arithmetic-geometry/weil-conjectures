/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs
public import Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.CategoryTheory.SiteConstantModuleIsomSheaf
import Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover

/-! # ProEtaleUniformModelEtaleCover

Source: Stacks Project, Tag 099Y, proof of lemma-compare-locally-constant.
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A fixed finite constant module model trivialized pro-etale locally is trivialized
etale locally. Source: Stacks Project, Tag 099Y, final paragraph of its proof, using
Modules on Sites, Tag 093T(2), and Bhatt--Scholze, Lemmas 5.1.1--5.1.4.

Proof: The finite module M over the finite ring Λ is finitely presented: its finite
underlying set generates it, and the kernel of the resulting map from a finite free
module is finite, hence finitely generated. On the slice over every pro-etale object,
form the set of isomorphisms from the restriction of constant M to the restriction
of F. Restriction defines a presheaf. Glue maps and their inverses sectionwise to prove
that this presheaf is a sheaf. This is the fixed-coefficient module-sheaf version of
the Isom sheaf in Tag 093T(2); one may also transport that construction through the
equivalence with modules over the constant ring sheaf.

On a given trivializing object W, the Isom sheaf becomes the sheaf of automorphisms
of constant M. Tag 093T(2), via the fixed-coefficient identification, identifies this
with the constant set sheaf Aut(M). Finite presentation is used here to commute Hom
with constant sheafification: use a finite presentation to express Hom as a kernel
of maps between finite powers, and express inverse pairs as a finite-limit diagram.
Thus the Isom sheaf is locally constant, hence locally classical. Each specified
trivialization supplies a section on W, so it is locally inhabited. Apply the
locally-classical etale-section comparison to obtain etale local sections. A section
is exactly an isomorphism of the restricted module sheaves with constant M. Refine
the resulting etale covering family to a universe-u family by choosing, for each
point of X, an object and a point above it; this yields the requested Cover.{u}.
Empty X has the empty cover. The zero module and the zero coefficient ring satisfy
the same inverse-pair construction and require no nonzero or free-module assumption.
(blueprint: lem-sf-proetale-uniform-finite-model-etale-cover) -/
theorem etale_cover_of_proetale_uniform_model
    (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (M : ModuleCat.{u + 1} Λ) [Finite M]
    (hF : ∃ (I : Type (u + 1)) (W : I → Scheme.{u}) (g : ∀ i, W i ⟶ X),
      Presieve.ofArrows W g ∈ proetalePrecoverage X ∧
        ∀ i, Nonempty ((AlgebraicGeometry.ProEtale.upperStar
          (ModuleCat.{u + 1} Λ) (g i)).obj F ≅
            (constantSheaf (ProEt.topology (W i)) (ModuleCat.{u + 1} Λ)).obj M)) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i : 𝒰.I₀,
      Nonempty ((AlgebraicGeometry.ProEtale.upperStar
        (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj F ≅
          (constantSheaf (ProEt.topology (𝒰.X i)) (ModuleCat.{u + 1} Λ)).obj M) := by
  sorry

end AlgebraicGeometry.Scheme
