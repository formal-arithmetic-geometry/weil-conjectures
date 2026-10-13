/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import Sheaf.AlgebraicGeometry.TheoremFormalFunctions
import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.FormalSystemsPullback

/-! # Lifting compatible maps through the formal-functions comparison

Source: Stacks Project, Lemma 088B, construction of alpha from the inverse limit of gamma.
(blueprint: lem-weil-pbc-formal-completion-pushforward-lift)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Any compatible map from a coherent adic system lifts through the canonical completed
proper pushforward comparison.

Source: Stacks Project, Lemma 088B, first half of the proof, paragraphs constructing
alpha from the inverse limit of gamma; https://stacks.math.columbia.edu/tag/088B.
(blueprint: lem-weil-pbc-formal-completion-pushforward-lift)

Proof: restrict to an affine open V = Spec A of Y. Write I = J(V), H = f_*F and
M = Gamma(V,H). The ideal-product and affine quotient formulas identify the sections of
H/J^(n+1)H with M/I^(n+1)M. The equations for kappa identify its section maps with the
canonical quotient maps of the degree-zero formal-functions theorem. Thus lim kappa
is the canonical isomorphism from the completion of M to lim Gamma(f^(-1)V,F/I^(n+1)F).
The coherent-formal-module equivalence identifies lim Gamma(V,G_n) with a finite
completed A-module N, whose projections are surjective with kernels I^(n+1)N. Compose
lim gamma with the inverse of lim kappa. This map is linear over the completed ring:
its projections are linear over A/I^(n+1), and those projections detect equality.
Consequently it induces compatible maps N/I^(n+1)N -> M/I^(n+1)M. Via the affine
sheaf equivalence these give alpha on V. The equation alpha_n kappa_n = gamma_n
follows after precomposition with the surjective projection N -> N/I^(n+1)N.
The same equation determines alpha uniquely, since on limits kappa is invertible,
and the projections of N are surjective. Restricting to a smaller affine open preserves
all quotient maps and equations, so uniqueness identifies the local alpha maps.
Glue their component sheaf maps on the affine basis. Transition compatibility and the
asserted equality hold on this basis, hence globally. The zero ideal gives ordinary
constant systems; the unit ideal gives zero systems; zero modules and empty affines
satisfy the construction as well. No isomorphism hypothesis on gamma is used. -/
theorem formalCompletion_pushforward_lift {X Y : Scheme.{u}} [IsNoetherian Y]
    (J : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]
    (G : CoherentFormalModule Y J) (F : CoherentModules X)
    (h : RingedSpace.IsCoherent Y.toRingedSpace
      ((Scheme.Modules.pushforward f).obj F.obj))
    (κ : formalCompletionSystem J ((Scheme.Modules.pushforward f).obj F.obj) ⟶
      formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f)
    (hκ : ∀ n : ℕ,
      formalModuleQuotientπ J (n + 1) ((Scheme.Modules.pushforward f).obj F.obj) ≫
        κ.app (op n) = (Scheme.Modules.pushforward f).map
          (formalModuleQuotientπ (J.comap f) (n + 1) F.obj))
    (γ : G.obj ⟶ formalCompletionSystem (J.comap f) F.obj ⋙
      Scheme.Modules.pushforward f) :
    ∃ α : G ⟶ (completion Y J).obj
        ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩,
      α.hom ≫ κ = γ := by sorry

end AlgebraicGeometry
