/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.TraceFormula.SmoothGeometricallyNormal
import Sheaf.AlgebraicGeometry.NormalTopologicallyNoetherianComponents
import WeilConjectures.RingTheory.RegularLocalRing.UniqueFactorization
import WeilConjectures.AlgebraicGeometry.EffectiveCartier

/-!
# Divisorial indeterminacy of rational maps into group varieties

Source: Milne, Algebraic Groups (2017), 8.17, printed p.152; Abelian Varieties,
Chapter I, Lemma 3.3, printed pp.17–18
(blueprint: lem-sfb-group-rational-divisorial-indeterminacy).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The maximal extension domain of a rational map from a smooth integral variety to a
smooth connected group variety has empty or divisorial complement. The defining equation
for `D` is exactly the union of opens containing `U` on which `f` extends over the base.
Source: Milne, Algebraic Groups, 8.17, p.152; Abelian Varieties I, Lemma 3.3, pp.17–18
(blueprint: lem-sfb-group-rational-divisorial-indeterminacy).

Proof following the six steps of the node:
1. The product X ×_k X is smooth by the lifting criterion and tensor presentations.
   Finite type gives quasi-compactness. Apply lem-trf-smooth-geometrically-normal to X
   and its product: both are regular, normal and reduced, and locally Noetherian, hence
   Noetherian. Their stalks are UFDs by lem-trf-regular-local-regular-ring-ufd; prime
   localizations of stalks are generization stalks and satisfy its regular-ring hypothesis.
2. By lem-weil-pbc-noetherian-scheme-closed-subsets-minimal the product has Noetherian
   topology. Apply lem-trf-normal-topologically-noetherian-components and take its
   integral clopen component W containing the irreducible diagonal image. On U × U
   consider f(x)f(y)^{-1}. The lemma lem-sfb-group-difference-diagonal-domain gives
   its maximal domain B in W, with diagonal inverse image D and diagonal value e.
   By lem-weil-pbc-scheme-morphism-gluing, allowing domains not containing U gives
   the same union, since each such representative glues with f.
3. Choose a finite-type affine chart T around e in G. The difference map's inverse
   image H of T contains the diagonal of U and is dense in W. Apply
   lem-sfb-factorial-affine-rational-poles to H → T: its maximal T-valued extension
   domain E has complement the support of an effective Cartier divisor P on W.
4. The diagonal inverse image of E equals D. For the forward inclusion in E, restrict
   the B-valued representative to the inverse image of T near each diagonal point of D.
   Conversely a T-valued extension composed into G agrees with the difference map on
   its original domain by lem-sfb-relative-separated-dominant-ext (dense equality on a
   reduced source with separated target), so E is contained in B.
5. Pull back P along the diagonal to an effective Cartier divisor Q on X. A local
   equation pulls back to a nonzero element at the generic point, because U lies in D;
   it is therefore a non-zero-divisor at every stalk on its integral open domain.
   The support of Q is exactly X minus D, including the case of the empty divisor.
6. Apply lem-sfb-factorial-cartier-prime-decomposition to Q. Its finitely many integral
   components have nonempty irreducible closed supports and generic stalk dimension one.
   The supports cover X minus D. If Q is empty then D=X; otherwise there is at least
   one component, yielding the asserted positive finite family. -/
theorem group_rational_divisorial_indeterminacy
    (k : Type u) [Field k]
    (X : Over (Spec (.of k))) [IsIntegral X.left]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [Smooth X.hom]
    (G : Over (Spec (.of k))) [GrpObj G] [Smooth G.hom] [ConnectedSpace G.left]
    [IsSeparated G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (U : X.left.Opens) (hU : Dense (U : Set X.left))
    (f : U.toScheme ⟶ G.left) (hf : f ≫ G.hom = U.ι ≫ X.hom)
    (D : X.left.Opens)
    (hD : D = sSup {V : X.left.Opens | ∃ hUV : U ≤ V,
      ∃ F : V.toScheme ⟶ G.left,
        F ≫ G.hom = V.ι ≫ X.hom ∧ X.left.homOfLE hUV ≫ F = f}) :
    D = ⊤ ∨ ∃ r : ℕ, 1 ≤ r ∧ ∃ (Z : Fin r → Set X.left) (z : Fin r → X.left),
      (D : Set X.left)ᶜ = ⋃ i, Z i ∧
      ∀ i, (Z i).Nonempty ∧ IsIrreducible (Z i) ∧ IsClosed (Z i) ∧
        closure ({z i} : Set X.left) = Z i ∧ ringKrullDim (X.left.presheaf.stalk (z i)) = 1 := by
  sorry

end AlgebraicGeometry
