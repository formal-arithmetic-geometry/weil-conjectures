/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.ActiveRootNormalizationData
public import WeilConjectures.RingTheory.ProEtale.IndEtale

/-! # Integral closedness of a punctured normal root stage after ind-etale base change

Source: Stacks, Tags 034M and 0CBF.
(blueprint: lem-sfb-root-stage-puncture-ind-etale-integral-closure).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace Algebra.ActiveRootNormalization

/-- A normal full root stage stays integrally closed in its puncture after the
specified ind-etale scalar extension; the puncture map is injective.
Source: Stacks, Tag 034M and Tag 0CBF, lemma-integral-closure-commutes-colim-smooth.
(blueprint: lem-sfb-root-stage-puncture-ind-etale-integral-closure).

Proof: put C = B[x_i]/(x_i^m-t_i) and g = image of the full product in C.
The regularity hypothesis embeds C[1/g] in the total fraction ring of C. An integral
element of C[1/g] maps to an integral total fraction, so 034M and injectivity of the
embedding put it in the structural image of C. Thus the actual integral closure of
C in C[1/g] is canonically C. Base change of B -> A gives C -> S = A tensor_B C
ind-etale: tensor the filtered etale presentation, whose stages remain etale by base
change, and use tensor-colimit compatibility. Apply 0CBF with ambient algebra C[1/g].
Its comparison identifies S tensor_C C = S with the actual integral closure of S in
S tensor_C C[1/g]. The latter ambient algebra is S[1/f] by localization's universal
property, through the structural maps used in strictPuncture. The comparison is an
isomorphism onto a subalgebra, so the map S -> S[1/f] is injective, and its image is
exactly the integral elements. Conversely structural elements are integral, using
X-a. Empty root families and the zero ring cause no change in these arguments. -/
theorem rootStage_puncture_indEtale_integralClosure
    {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {r : ℕ} (t : Fin r → B) (m : ℕ+)
    (hregular : Function.Injective
      (fun x : pthRootAlgebra m r B t ↦ algebraMap B _ (∏ i, t i) * x))
    (hnormal : ∀ (q : Ideal (pthRootAlgebra m r B t)) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (hA : (algebraMap B A).IndEtale) :
    Function.Injective (strictPuncture (A := A) t m).hom ∧
    ∀ x : asAlgebra (strictPuncture (A := A) t m),
      IsIntegral (strictStage (A := A) t m).right x ↔
        ∃ a : (strictStage (A := A) t m).right,
          (strictPuncture (A := A) t m).hom a = x := by sorry

end Algebra.ActiveRootNormalization
