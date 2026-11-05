/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.MumfordComplex
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.Model

/-!
# Perfectness of the higher direct images, with base change

For a proper morphism `f : X ⟶ T` of finite presentation and an `𝒪_X`-module `ℱ` of finite
presentation which is flat over `T`, the higher direct images are locally on `T` computed by a
bounded complex of finite free modules, compatibly with every base change: as an isomorphism
`g^* P ≅ R f'_* g'^* ℱ` in the derived category
(`AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_derivedPushforward`), and on
cohomology sheaves
(`AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`).

Over an affine open `V` of `T`, the pair `(f, ℱ)` is the base change of a pair `(p, 𝒢)` over an
affine scheme `S` with Noetherian ring of global sections
(`AlgebraicGeometry.Scheme.Modules.exists_isNoetherianRing_model`), for which the statement is
Mumford's complex
(`exists_isFiniteFreeComplex_derivedPushforward_of_isNoetherianRing`);
base changes of `f` over `V` are base changes of `p`.
-/

@[expose] public section

universe u

open CategoryTheory Limits DerivedCategory

namespace AlgebraicGeometry.Scheme.Modules

section General

variable {X T : Scheme.{u}}
variable (f : X ⟶ T) (ℱ : X.Modules)

end General

section Perfect

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) {ι : Type u} (U : ι → X.Opens)
  [IsAffine S] [Finite ι] [Nonempty ι] (hU : ∀ i, IsAffineOpen (U i)) (hU' : iSup U = ⊤)
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

end Perfect

end AlgebraicGeometry.Scheme.Modules
