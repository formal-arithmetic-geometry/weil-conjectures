/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q147
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
import Sheaf.AlgebraicGeometry.GroupScheme.IdentityLocalDimension
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import WeilConjectures.AlgebraicGeometry.GlobalSectionsProper
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Projective
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Sheaf.AlgebraicGeometry.CoherentGroupBialgebra
import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Sheaf.AlgebraicGeometry.ProperFibreDimensionUpperSemicontinuous
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Algebra.Module.SpanRankOperations
import Sheaf.AlgebraicGeometry.FiniteTypeFibreImageDimensionBounds
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube

/-! # First structure-sheaf cohomology of an abelian variety

Source: Milne, Abelian Varieties, Chapter I, Remark 8.7(e), printed p.37;
Proposition 8.1 and the degree-one argument of Lemma 12.2.
(blueprint: lem-sfb-abelian-structure-h1-dimension)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsAbelianVariety

/-- The first Zariski cohomology of the structure sheaf of an abelian variety has dimension
its dimension. The field action is the one induced by the given structure morphism.

Source: Milne, Abelian Varieties I, Remark 8.7(e), printed p.37, with the finite-kernel
argument of Proposition 8.1 and the degree-one argument of Lemma 12.2.
(blueprint: lem-sfb-abelian-structure-h1-dimension)

Proof:
1. By lem-sc-abelian-variety-characterization and lem-sc-abelian-variety-projective,
   A is geometrically integral and projective. Proper coherent finiteness
   (lem-fin-proper-coherent-finite-dimensional) gives finite-dimensional H^q. Finite type
   over k makes A Noetherian, so lem-sc-noetherian-cohomology-above-dimension gives
   H^q = 0 for q > g. By lem-pc-h0-proper-variety, H^0 = k.
2. Put h = dim H^1. The coproduct of lem-sfb-coherent-group-bialgebra makes H^1 primitive.
   If h > g, choose g+1 independent degree-one classes. By lem-sfb-graded-primitive-product
   their ordered product is nonzero in H^(g+1), a contradiction. Thus h <= g. This works
   in characteristic two without factorial division or a square-zero assertion.
3. Apply lem-sfb-projective-picard-identity-representability to (A,0). Its proper connected
   identity component P represents rigidified algebraically trivial families and has
   tangent space H^1, without a smoothness or reducedness hypothesis on P.
4. Choose an ample L. On A_x times A_y normalize m^*L by tensoring with the inverses of
   both projection pullbacks and the constant identity fibre. The resulting N is trivial
   on both identity axes, and its fibres are algebraically trivial, since the smooth
   connected parameter A connects them to the identity fibre. Picard representability
   gives f : A -> P. By thm-sc-theorem-of-cube the normalized family is additive in y;
   uniqueness of rigidified representability makes f a group homomorphism.
5. Its kernel K is closed since P is separated. By
   lem-sfb-abelian-closed-subgroup-reduced-component, B = (K_red)^0 is an abelian subvariety
   of dimension dim K. The family N is trivial on A times B. Restrict to B times B and
   pull back along x |-> (x,-x). It follows that L|B tensor [-1]^*(L|B) is trivial, up to
   a constant one-dimensional factor, which is trivial over k.
6. To check ampleness of L|B in def-sc-ample's complete-system convention, restrict a
   very ample power's embedding to B. By coherent finiteness its complete section space V
   is finite dimensional. By lem-trf-projective-bundle-quotient-geometry its evaluation
   quotient defines j : B -> P(V dual). The restricted embedding factors as j followed
   by a linear projection, so j is a monomorphism. By lem-weil-pbc-proper-to-separated
   it is proper and by lem-pc-proper-monomorphism-closed it is a closed immersion.
   Thus L|B is ample; pullback by the inverse automorphism is ample as well.
7. By lem-sc-ample-tensor the trivial bundle on B is ample. If dim B > 0, geometric
   integrality and lem-pc-h0-proper-variety give H^0(B,O_B) = k, so every complete system
   of a power of the trivial bundle maps to P^0 and cannot embed B. Hence dim B = 0,
   and lem-sfb-abelian-closed-subgroup-reduced-component makes K finite, even if nonreduced.
8. The map f is proper by lem-weil-pbc-proper-to-separated. Over each closed point of P,
   lem-weil-pbc-closed-point-residue-field-base identifies the residue field with k.
   A nonempty fibre has a closed point by lem-sc-lft-over-field-jacobson-space; it is
   k-rational, and translation identifies the whole scheme-theoretic fibre with K.
   Thus closed fibres are finite or empty. By
   lem-weil-pbc-proper-fibre-dimension-upper-semicontinuous the positive-dimensional-fibre
   locus is closed; if nonempty it contains a closed point, a contradiction.
9. By lem-zl-finite-type-fibre-image-dimension-bounds, g <= dim P. By
   lem-ag-group-identity-local-dimension, dim P is the local dimension at the identity.
   The Noetherian cotangent inequality lem-weil-pbc-regular-local-cotangent-dimension
   bounds this by dim T_0 P = h. A finite-dimensional space and its dual have the same
   dimension. Therefore g <= dim P <= h <= g, proving h = g, also when g = 0. -/
theorem finrankH_one_structureSheaf_eq_dim {k : Type u} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A] :
    Scheme.Modules.finrankH k (SheafOfModules.unit A.left.ringCatSheaf) 1 =
      IsAbelianVariety.dim A := by
  sorry

end AlgebraicGeometry.IsAbelianVariety
