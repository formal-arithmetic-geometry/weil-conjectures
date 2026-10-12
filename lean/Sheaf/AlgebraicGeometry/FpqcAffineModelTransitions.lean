/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Cover.Directed

/-!
# Transition maps between effective affine models

Source: Stacks Project, Descent, Tag 02W3, general-base proof (nested affine opens).
(blueprint: lem-galois-fpqc-affine-model-transitions)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Two effective affine models admit a Cartesian transition over an inclusion.
Source: Stacks Project, Descent, Tag 02W3, general-base proof; Tag 02W0.
(blueprint: lem-galois-fpqc-affine-model-transitions)

Proof: Restrict the model over B to U for an inclusion U into B. Its pullback
along X_U -> U and the U-model both identify with V_U. The compatibility with D
identifies their transports, so fpqc full faithfulness descends the comparison
isomorphism and its inverse. Compose with the projection to the B-model to get t.
The comparison isomorphism makes its square Cartesian. The equation with r is the
reconstruction equation of the descended morphism.
Base changes of the singleton fpqc covering are fpqc. This works also when U,
X_U or V_U is empty, and does not assume intersections of affine opens are affine. -/
theorem fpqc_affine_model_transition
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S)
    {V : Over X} (D : Over.DescentDatum f V)
    (E : ∀ U : S.affineOpens,
      Over.DescentDatum (pullback.snd f U.1.ι)
        (Over.mk (pullback.snd V.hom (pullback.fst f U.1.ι))))
    (hcompat : ∀ U : S.affineOpens,
        ∀ {T : Scheme.{u}} (a b : T ⟶ pullback f U.1.ι)
          (hab : a ≫ pullback.snd f U.1.ι = b ≫ pullback.snd f U.1.ι)
          (x : Over.mk a ⟶ Over.mk (pullback.snd V.hom (pullback.fst f U.1.ι))),
          (D.transport (a ≫ pullback.fst f U.1.ι) (b ≫ pullback.fst f U.1.ι)
            (by simp only [Category.assoc, pullback.condition]; rw [← Category.assoc,
              ← Category.assoc, hab])
            (Over.homMk (x.left ≫ pullback.fst V.hom (pullback.fst f U.1.ι))
              (by simpa [Category.assoc, pullback.condition] using
                  congrArg (fun z ↦ z ≫ pullback.fst f U.1.ι) (Over.w x)))).left =
            ((E U).transport a b hab x).left ≫ pullback.fst V.hom (pullback.fst f U.1.ι))
    (W : ∀ U : S.affineOpens, Over U.1.toScheme)
    (r : ∀ U : S.affineOpens,
      pullback V.hom (pullback.fst f U.1.ι) ⟶ (W U).left)
    (hp : ∀ U, IsPullback (r U) (pullback.snd V.hom (pullback.fst f U.1.ι))
      (W U).hom (pullback.snd f U.1.ι))
    (hinv : ∀ (U : S.affineOpens) {T : Scheme.{u}}
      (a b : T ⟶ pullback f U.1.ι)
      (hab : a ≫ pullback.snd f U.1.ι = b ≫ pullback.snd f U.1.ι)
      (x : Over.mk a ⟶ Over.mk (pullback.snd V.hom (pullback.fst f U.1.ι))),
      ((E U).transport a b hab x).left ≫ r U = x.left ≫ r U)
    {U B : S.affineOpens} (i : U ⟶ B) :
    ∃ t : (W U).left ⟶ (W B).left,
      IsPullback t (W U).hom (W B).hom (S.directedAffineCover.trans i) ∧
      Scheme.Cover.trans ((S.directedAffineCover.pullback₁ f).pullback₁ V.hom) i ≫ r B =
        r U ≫ t := by sorry

end AlgebraicGeometry
