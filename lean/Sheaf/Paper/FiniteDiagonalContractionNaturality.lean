/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.Paper.FiniteTraceDiagonalCanonicalMaps

/-! Canonical diagonal-unit naturality, isolated from the trace-diagonal datum. -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.FiniteTraceDiagonal

variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [QuasiCompact f]

/-- Naturality of the first canonical diagonal-unit isomorphism, in contraction direction.
Source: blueprint def-pur-td-datum, first unit isomorphism and canonical-map paragraph.
(blueprint: lem-pur-finite-diagonal-contraction-naturality).

Proof: write V = Lp1*, D = LDelta*, S = RDelta!, T = Rp2!, and U for the coefficient
unit. Put B = S(U). The contraction is T applied to the following four isomorphisms,
followed by canonical compact-support section contraction:
V(K) tensor B --signed symmetry--> B tensor V(K)
--projection--> S(U tensor D(V(K))) --unit multiplication--> S(D(V(K)))
--pullback section comparison--> S(K), then T(S(K)) --> K.
For a map a : K --> K', signed tensor symmetry commutes a tensor 1 with 1 tensor a.
The projection transformation is natural in its second input; its isomorphism
certificate changes no component. Left multiplication by U and the pullback
composition/identity comparisons are natural. Apply S, then T, to their squares.
The section contraction square is natural because both changes of compactification,
compact-support composition, and its identity normalization are natural isomorphisms
on the full etale-origin category. Compose these five squares, using functoriality
and associativity, to obtain precisely the displayed equation. The hypotheses supply
exactly the etale-origin and finite-Tor certificates needed by these canonical maps;
no invertibility or nonzero condition is used. In particular the argument applies to
the identity morphism and empty schemes. The remaining formal work is to assemble
these naturality squares while keeping the large native functors folded. -/
theorem contractionCore_naturality (c : Compactification f)
    (K K' : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K)
    (hK' : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K')
    (hU : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X
      (coefficientUnit (ModuleCat.{u + 1} A) X))
    (hP : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) (pullback f f)
      ((pullFor A (pullback.fst f f)).obj K))
    (hP' : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) (pullback f f)
      ((pullFor A (pullback.fst f f)).obj K')) (a : K ⟶ K') :
    (compactSupportFor A (c.ofIsPullback (IsPullback.of_hasPullback f f))).map
        (((tensorFor A (pullback f f)).map ((pullFor A (pullback.fst f f)).map a)).app
          ((compactSupportFor A (HasCompactification.compactification
            (Etale.TraceDiagonalDatum.diagonal f))).obj (coefficientUnit (ModuleCat A) X))) ≫
      (contractionCore A f c K' hK' hU hP').hom =
        (contractionCore A f c K hK hU hP).hom ≫ a := by sorry

end AlgebraicGeometry.ProEtale.FiniteTraceDiagonal
