/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
import Sheaf.CategoryTheory.SheafTensor

/-!
# Inverse image commutes with internal extension of scalars

Source: the current blueprint, sec-six-functors-basics,
sk-thm-sfb-qlbar-two-colimit/lem-sfb-extend-to-qlbar-constructible.proof.md,
final clause on tensoring local finite presentations on strata.
(blueprint: lem-sfb-internal-extension-inverse-image)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Inverse image commutes naturally with extension along an arbitrary morphism of
commutative internal ring objects. The rings on the target site are the actual inverse
images. Evaluating the natural isomorphism at `M` gives
`F_S (S ⊗_R M) ≅ F(S) ⊗_{F(R)} F_R(M)`.

Source: the current blueprint, sec-six-functors-basics,
sk-thm-sfb-qlbar-two-colimit/lem-sfb-extend-to-qlbar-constructible.proof.md,
final clause on restricting extended presentations to strata and pro-étale covers.
(blueprint: lem-sfb-internal-extension-inverse-image)

Proof:
1. By sk-def-sfb-change-of-scalars, extension is the balancing coequalizer of the
right R-action on S and the R-action on M, with the induced S-action. Transporting
rings and modules by def-sfb-modobj-transport gives precisely the balancing diagram
for the actual inverse-image rings. Commutativity follows from
lem-sfb-finite-upper-star-braided.
2. The adjunction def-sfb-finite-upper-lower-star-adjunction identifies maps from
F of this coequalizer to T with maps from S tensor M to g_* T that equalize the
balancing pair. Naturality of the adjunction identifies these with maps from
F(S tensor M) to T equalizing the image pair. Thus F preserves this coequalizer.
3. The tensorators of def-sfb-finite-upper-star-monoidal identify the image pair
with the transported balancing pair. The first-arrow identity follows from
naturality and the transported multiplication; the second follows from the
associativity coherence in def-sfb-strong-monoidal-functor and the transported
module action. The two coequalizer universal properties give inverse comparisons.
4. Both quotient maps respect multiplication on the first F(S) factor. After
precomposition with F(S) tensor the quotient map, the linearity equation is the
same on both sides. Tensor preserves this coequalizer by sk-def-sfb-sheaf-tensor,
so its quotient map is epic and cancels. The inverse comparison is linear too.
5. For a module morphism M to N, precompose the naturality equation with the
balancing quotient. The defining formula for extension on morphisms and
naturality of the tensorator make both sides equal. Cancel the quotient to get
naturality. Inverting this natural comparison gives the displayed orientation.
-/
theorem internal_extension_inverse_image
    {Z X : Scheme.{u}} (g : Z ⟶ X)
    (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] :
    Nonempty (Mod.extendScalars φ ⋙ (upperStar Ab.{u + 1} g).mapMod S ≅
      (upperStar Ab.{u + 1} g).mapMod R ⋙
        Mod.extendScalars ((upperStar Ab.{u + 1} g).map φ)) := by
  sorry

end AlgebraicGeometry.ProEtale
