/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.NormalGeometricCoverComponents
import Sheaf.AlgebraicGeometry.ProEtaleLocalSystemRepresentability
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison

/-!
# Finite-cover sections of locally constant pro-étale sheaves on a normal scheme

Source: Bhatt--Scholze, *The pro-étale topology for schemes*, Lemma 7.3.9 (Loc_X = Cov_X),
pp. 67--68, and the proof of Lemma 7.4.10, p. 71 (blueprint:
lem-a1-normal-locally-constant-finite-section).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A locally nonempty locally constant pro-étale sheaf on a normal connected Noetherian scheme
has a section after a finite étale surjective cover.

Source: Bhatt--Scholze, *The pro-étale topology for schemes*, Lemma 7.3.9 and the proof of
Lemma 7.4.10 (blueprint: lem-a1-normal-locally-constant-finite-section).
Proof: represent the locally constant sheaf by an étale geometric covering using Lemma 7.3.9;
local nonemptiness gives a point of the covering. Normality and the valuation lifting property
make the connected component of that point finite étale and surjective by Lemma 7.4.10.
The inclusion of finite étale schemes into the pro-étale site and the representing bijection
then give a section over that component. -/
theorem exists_finiteEtale_section_of_normal_locallyConstant
    (X : Scheme.{u}) [Nonempty X] [ConnectedSpace X] [IsLocallyNoetherian X]
    [CompactSpace X]
    (hnormal : ∀ x : X,
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (hlocal : ∃ (𝒰 : Scheme.Cover Scheme.proetalePrecoverage X),
      ∀ i : 𝒰.I₀, ∃ (S : Type (u + 1)),
        Nonempty ((Functor.sheafPullbackConstruction.sheafPullback
          (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (𝒰.f i)) (Type (u + 1))
            (Scheme.ProEt.topology X) (Scheme.ProEt.topology (𝒰.X i))).obj F ≅
          (constantSheaf (Scheme.ProEt.topology (𝒰.X i)) (Type (u + 1))).obj S))
    (hnonempty : ∃ (𝒱 : Scheme.Cover Scheme.proetalePrecoverage X),
      ∀ j : 𝒱.I₀, Nonempty (F.obj.obj
        (op (MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme) (𝒱.f j)
          (Scheme.proetalePrecoverage_le_precoverage_weaklyEtale X 𝒱.mem₀ ⟨j⟩))))) :
    ∃ (Y : Scheme.ProEt X), IsFinite Y.hom ∧ Etale Y.hom ∧ Surjective Y.hom ∧
      Nonempty (F.obj.obj (op Y)) := by
  sorry

end AlgebraicGeometry
