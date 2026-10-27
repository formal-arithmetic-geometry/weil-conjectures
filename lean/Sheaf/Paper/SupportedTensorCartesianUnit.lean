/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R6
-/
module

public import Sheaf.Paper.FiniteOpenProductSwap

/-! # Cartesian transport of open-unit equations

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

/-- Restriction of the Cartesian tensor composite preserves the specified open unit.

Source: proof Steps 1, 3 and 4 of
`lem-pur-supported-tensor-isomorphism-transport`, expanding the symmetry paragraph
of blueprint `lem-sf-kunneth-coherence`; Stacks 03S6, 07A4 and 0GL1.
(blueprint: lem-pur-supported-tensor-cartesian-unit).

Proof: write U=i*, V=i'*, G=g*, T=h*, J=i!, J'=i'!, and theta for the
specified square. Naturality of theta rewrites UG(f') as theta at the source,
then T(V(f')), then theta inverse at the target. Substitute hf'. The
unit-normalized beta equation cancels T(eta') followed by theta inverse and
U(beta), leaving eta at T(P' tensor Q'). Move the final tensor comparison
past eta by unit naturality. Tensor-comparison composition coherence identifies
the remaining source composite with mu_i followed by tensor(theta at R', theta
at H') and tensor(T(a'), T(b')). Tensor naturality moves a', b' through mu_h;
the factors U(mu_g inverse) and U(mu_g) cancel. This is precisely the displayed
right side. All calculations take place on arbitrary unbounded objects; they
can be checked on flat-term K-flat representatives, where they are the ordinary
pullback tensor identities on each total-complex summand, and descend by the
localization universal property. -/
theorem supportedTensor_cartesian_unit
    {W Y W' Y' : Scheme.{u}} (i : W ⟶ Y) (i' : W' ⟶ Y')
    [IsOpenImmersion i] [IsOpenImmersion i']
    (g : Y ≅ Y') (h : W ≅ W') (s : IsPullback h.hom i i' g.hom)
    (R' H' : FiniteD A Y') (P' Q' : FiniteD A W')
    (a' : (pull A i').obj R' ≅ P') (b' : (pull A i').obj H' ≅ Q')
    (f' : tensor A Y' R' H' ⟶ (finiteShriek A i').obj (tensor A W' P' Q'))
    (hf' : (pull A i').map f' = (tensorPullIso A i' R' H').hom ≫
      tensorMap A W' a'.hom b'.hom ≫ (adj A i').unit.app (tensor A W' P' Q')) :
    (pull A i).map
      ((tensorPullIso A g.hom R' H').inv ≫ (pull A g.hom).map f' ≫
        (beta A h.hom i i' g.hom s).hom.app (tensor A W' P' Q') ≫
        (finiteShriek A i).map (tensorPullIso A h.hom P' Q').hom) =
      (tensorPullIso A i ((pull A g.hom).obj R') ((pull A g.hom).obj H')).hom ≫
        tensorMap A W
          (((square A i g.hom h.hom i' s.w.symm).app R' ≪≫
            (pull A h.hom).mapIso a').hom)
          (((square A i g.hom h.hom i' s.w.symm).app H' ≪≫
            (pull A h.hom).mapIso b').hom) ≫
        (adj A i).unit.app
          (tensor A W ((pull A h.hom).obj P') ((pull A h.hom).obj Q')) := by sorry

end WeilConjectures.FiniteOpenProduct
