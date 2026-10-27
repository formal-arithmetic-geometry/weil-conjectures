/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R6
-/
module

public import Sheaf.Paper.FiniteOpenProductSwap

/-! # Signed reversal of open-unit equations

Source: the symmetry paragraph of the latest blueprint proof of
`lem-sf-kunneth-coherence`, and Stacks Project Tags 03S6, 07A4, 0GL1.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open SheafOfModules.OpenTensorNormalization
namespace WeilConjectures.FiniteOpenProduct

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- Both Koszul symmetries preserve the actual open-unit equation.

Source: proof Step 6 of `lem-pur-supported-tensor-isomorphism-transport`,
expanding blueprint `lem-sf-kunneth-coherence`, symmetry paragraph; Stacks 07A4, 0GL1.
(blueprint: lem-pur-supported-tensor-signed-unit).

Proof: apply i* to the three factors and substitute hf. Naturality of eta moves
i*i!(sigma(P,Q)) to sigma(P,Q) followed by eta(Q tensor P). Naturality of the
signed braiding moves tensor(a,b) past sigma(P,Q), yielding the symmetry on
i*R, i*H followed by tensor(b,a). Braiding compatibility of the canonical
pullback tensor comparison moves i*(sigma(H,R)) past mu_i. The two adjacent
symmetries on i*H, i*R and i*R, i*H cancel. On total-complex degrees r,s their
product sign is (-1)^(rs+sr)=1, including odd degrees. These are equations on
the full coproduct total tensor of flat-term K-flat representatives; the derived
comparison and specified sigma are their localizations, so the equality holds
for arbitrary unbounded complexes. -/
theorem supportedTensor_signed_unit
    {W Y : Scheme.{u}} (i : W ⟶ Y) [IsOpenImmersion i]
    (R H : FiniteD A Y) (P Q : FiniteD A W)
    (a : (pull A i).obj R ≅ P) (b : (pull A i).obj H ≅ Q)
    (f : tensor A Y R H ⟶ (finiteShriek A i).obj (tensor A W P Q))
    (hf : (pull A i).map f = (tensorPullIso A i R H).hom ≫
      tensorMap A W a.hom b.hom ≫ (adj A i).unit.app (tensor A W P Q)) :
    (pull A i).map (sigma A Y H R ≫ f ≫ (finiteShriek A i).map (sigma A W P Q)) =
      (tensorPullIso A i H R).hom ≫ tensorMap A W b.hom a.hom ≫
        (adj A i).unit.app (tensor A W Q P) := by sorry

end WeilConjectures.FiniteOpenProduct
