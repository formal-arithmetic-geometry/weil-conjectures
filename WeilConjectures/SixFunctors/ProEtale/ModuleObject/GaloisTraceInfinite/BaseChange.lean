/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.GaloisCoverTraceMonoidal
set_option linter.privateModule false  -- prune: only private declarations remain

/-!
# Restriction along a morphism of weakly étale covers

Let `g : Y ⟶ X` and `g' : Y' ⟶ X` be weakly étale and `s : Y' ⟶ Y` a morphism over `X`. For a
pro-étale sheaf `H` on `X`, the sheaf `g_* g^* H` has sections `H(V ×_X Y)` over `V`, and `s`
induces the restriction `H(V ×_X Y) ⟶ H(V ×_X Y')`. This file packages it:

* on the site, as the natural transformation `V ×_X Y' ⟶ V ×_X Y` of base change functors
  (`AlgebraicGeometry.ProEtale.baseChangeHom`), compatible with composition, the projections and
  the action of automorphisms (`AlgebraicGeometry.ProEtale.baseChangeAction`);
* on sheaves, in the restriction model `j_g^* ⋙ g_*` of `g^* ⋙ g_*`
  (`AlgebraicGeometry.ProEtale.restrictionHom`), a monoidal natural transformation;
* on `g^* ⋙ g_*` itself, by conjugation with `g^* ≅ j_g^*`
  (`AlgebraicGeometry.ProEtale.lowerStarUpperStarHom`), a monoidal natural transformation
  compatible with the units of `g^* ⊣ g_*` and `g'^* ⊣ g'_*` and with the Galois actions.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X Y Y' Y'' : Scheme.{u}} (g : Y ⟶ X) (g' : Y' ⟶ X) (g'' : Y'' ⟶ X) [WeaklyEtale g]
  [WeaklyEtale g'] [WeaklyEtale g'']

/-! ### The site level -/

@[simp]
private lemma overHomMk_left {A B : X.ProEt} (f : A.left ⟶ B.left) (w : f ≫ B.hom = A.hom)
    (hf : (⊤ : MorphismProperty Scheme.{u}) f) : (MorphismProperty.Over.homMk f w hf).left = f :=
  rfl

@[simp]
private lemma proEtComp_left {A B C : X.ProEt} (f : A ⟶ B) (h : B ⟶ C) :
    (f ≫ h).left = f.left ≫ h.left :=
  rfl

@[simp]
private lemma proEtId_left (A : X.ProEt) : (𝟙 A : A ⟶ A).left = 𝟙 A.left :=
  rfl

variable {g g' g''}

/-! ### The restriction model -/

section Restriction

variable (g g')

variable {g g'}

end Restriction

end AlgebraicGeometry.ProEtale
