/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-! # Reflection of local finite presentations across a surjective closed immersion -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Surjective closed inverse image reflects pro-etale local finite presentation.
Source: Bhatt--Scholze, Lemma 5.4.2, Theorem 2.3.4 and Definition 6.8.10.
(blueprint: lem-weil-pbc-proetale-module-lfp-closed-reflection)

Proof: a surjective closed immersion is a universal homeomorphism. Topological
invariance is computed on the affine ind-etale basis of Theorem 2.3.4. On this basis
base change is an equivalence preserving the faithfully flat and Zariski covering
criteria. Refine the covering presentations of p^*M to basis objects and lift them
along this basis equivalence and its induced monoidal sheaf equivalence. The coefficient
ring identifies with p^*R, regular modules correspond,
and the equivalence preserves finite sums and cokernels. Thus the lifted finite matrices
present M on the corresponding covering of U. Compatibility with the adjunction unit
identifies the presented module with the original M, rather than an unspecified object.
For empty U, use the empty covering and rank-zero presentations. Neither reduction of U
nor a uniform nilpotence bound on the defining ideal is required. -/
theorem localFinitePresentation_of_surjective_closed_pullback
    {U V : Scheme.{u}} (p : V ⟶ U) [IsClosedImmersion p]
    (hp : Function.Surjective p)
    (R : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) [MonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) R)
    (hM : IsLocallyFinitelyPresented ((upperStar Ab.{u + 1} p).obj R)
      (((upperStar Ab.{u + 1} p).mapMod R).obj M)) :
    IsLocallyFinitelyPresented R M := by
  sorry

end AlgebraicGeometry.ProEtale
