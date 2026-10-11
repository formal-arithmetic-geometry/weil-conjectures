/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Topology.KrullDimension

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-!
# Saturated line subbundles on regular integral curves

Source: literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-rr/
lem-sc-riemann-roch.md, proof of (*) (blueprint: lem-sc-vector-bundle-line-subbundle).
-/

/-- The saturation of a prescribed nonzero generic section is an invertible subsheaf
with finite locally free quotient of rank one less. The stalk-image condition specifies
exactly the kernel of `E → j_*(E_η / Ks)`, without choosing a presentation of that
pushforward: its stalk at `x` is the inverse image of `Ks` under specialization.
The separate generic-point image equality states that its generic fibre is `Ks`.

Source: blueprint `lem-sc-riemann-roch.md`, proof of (*), rank-induction paragraph
(blueprint: lem-sc-vector-bundle-line-subbundle).

Proof:
1. By `lem-sc-integral-scheme-stalks-in-function-field`, each free stalk of `E`
embeds in the generic fibre. Thus the kernel stalk is `E_x ∩ Ks`, and at the generic
point it is `Ks` itself.
2. At each non-generic point, dimension one and regularity give a DVR by
`lem-sc-regular-dim1-dvr`. Apply `lem-sc-dvr-saturation-line` to obtain a free
rank-one intersection and a free quotient of rank `r - 1`. At the generic point these
claims are linear algebra over the function field.
3. The generic-point morphism is quasi-compact and quasi-separated since its source
has one point and `X` is Noetherian. By `pqf-lem-pushforward-qcoh` its pushforward
quotient is quasi-coherent; `lem-weil-pbc-quasi-coherent-module-kernel` makes the
kernel quasi-coherent. By `lem-weil-pbc-coherent-kernel-cokernel-locnoeth`, the kernel
and quotient are coherent. Their free stalks give finite local freeness with these
constant ranks by `lem-sc-regular-curve-torsionfree-free`; the kernel is invertible
by `def-sc-invertible-module`.
4. The kernel inclusion and quotient map give the short exact sequence. The stalk
identification in step 1 gives the prescribed saturation and generic fibre. -/
theorem exists_saturated_line_subbundle
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (hregular : ∀ x : X, IsRegularLocalRing (↑(X.presheaf.stalk x)))
    (hdim : topologicalKrullDim X = 1)
    (r : ℕ) (hr : 1 ≤ r)
    (E : X.Modules) [E.IsFiniteLocallyFreeOfRank r]
    (s : ↑(TopCat.Presheaf.stalk E.val.presheaf (genericPoint X))) (hs : s ≠ 0) :
    ∃ (L Q : X.Modules) (ι : L ⟶ E) (π : E ⟶ Q),
      ∃ hcomp : ι ≫ π = 0,
        L.IsInvertible ∧ Q.IsFiniteLocallyFreeOfRank (r - 1) ∧
          ShortComplex.ShortExact (ShortComplex.mk ι π hcomp) ∧
          (∀ x : X,
            Set.range (((TopCat.Presheaf.stalkFunctor _ x).map ι.mapPresheaf).hom) =
              (TopCat.Presheaf.stalkSpecializes E.val.presheaf
                (genericPoint_specializes x)) ⁻¹'
                (Submodule.span X.functionField {s} : Set ↑(TopCat.Presheaf.stalk E.val.presheaf
                  (genericPoint X)))) ∧
          Set.range (((TopCat.Presheaf.stalkFunctor _ (genericPoint X)).map
            ι.mapPresheaf).hom) =
              (Submodule.span X.functionField {s} : Set ↑(TopCat.Presheaf.stalk E.val.presheaf
                (genericPoint X))) :=
  by
  sorry

end AlgebraicGeometry
