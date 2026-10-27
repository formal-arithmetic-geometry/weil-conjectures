/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q128
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Monoidal.Grp
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import Sheaf.AlgebraicGeometry.TranslatedCartierParameterFamily
import Sheaf.TraceFormula.SmoothGeometricallyNormal
import Sheaf.AlgebraicGeometry.ExistsAmpleOfReductionCharP
import WeilConjectures.AlgebraicGeometry.GroupScheme.Cartier
import Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates
import Sheaf.AlgebraicGeometry.AmpleExistenceFieldExtension
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor

/-! # An ample invertible module on a finite-type group scheme

Source: Stacks Project, Groupoids, Tag 0BF7, lemma-algebraic-quasi-projective;
Morphisms, Definition 01VW and Lemma 01VK (ampleness over an affine base).
(blueprint: lem-sfb-finite-type-group-ample-line).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A separated finite-type group scheme over any field admits an absolutely ample
invertible module.

Source: Stacks Project, Groupoids, Tag 0BF7, lemma-algebraic-quasi-projective;
Morphisms, Definition 01VW and Lemma 01VK.
(blueprint: lem-sfb-finite-type-group-ample-line).

Proof, following the five steps of the node:
1. First suppose k is algebraically closed. Set C = G^0 and H = C_red.
   By lem-sfb-locally-algebraic-group-identity-component, C is an open and closed
   finite-type subgroup and H is smooth, integral, separated and of finite type.
   Apply lem-sfb-translated-cartier-parameter-family to H, obtaining V, M and
   sections s_v. Its covering assertion at the identity gives v_0 in V(k).
   Set L = M_(v_0), invertible by lem-weil-pbc-invertible-pullback-tensor.
2. By lem-trf-smooth-geometrically-normal, H is normal. Apply
   lem-sfb-normal-variety-affine-parameter-picard to identify every M_v with L.
   Transfer s_v to a section t_v of L. Fibrewise linear isomorphisms preserve
   nonvanishing, so H_(t_v) = H_(s_v) is affine. Every closed point is rational
   by lem-weil-pbc-closed-point-residue-field-base and lies in one of these opens.
   Their closed complement is empty by lem-sc-lft-over-field-jacobson-space.
   Finite type gives quasi-compactness; these sections with exponent one give
   IsAmple H L, exactly def-weil-pbc-ample-invertible-module.
3. In characteristic p > 0, C is Noetherian by
   lem-weil-pbc-finite-type-over-noetherian, since a field is Noetherian. Apply
   lem-sfb-ample-existence-characteristic-p-reduction to get an ample invertible
   module N on C. In characteristic zero, lem-sfb-cartier-characteristic-zero-smooth
   makes C reduced, so C = H and the module from step 2 already suffices.
4. By lem-sfb-group-neutral-component-translates, G is the disjoint union of
   finitely many clopen components D_i, each isomorphic to C. Transfer N to each
   component and glue the modules to an invertible module on G. At a point of D_i,
   transfer an affine nonvanishing section locus for a positive power of N and
   extend the section by zero on the other components. Its nonvanishing locus
   on G is the same affine open. Quasi-compactness follows from finite type,
   giving absolute ampleness by def-weil-pbc-ample-invertible-module.
5. For arbitrary k, use def-weil-algebraic-closure and base change the group
   structure to its algebraic closure. The group identities follow from the
   fibre-product universal property. By lem-pod-separated-finite-type-base-change,
   the hypotheses survive. Steps 1--4 give an ample invertible module upstairs.
   Apply lem-sfb-ample-existence-field-extension to descend existence to G;
   no descent datum for the chosen module is required. -/
theorem exists_isAmple_of_finiteType_group
    (k : Type u) [Field k] (G : Over (Spec (.of k))) [GrpObj G]
    [IsSeparated G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    ∃ (M : G.left.Modules) (hM : M.IsInvertible), @IsAmple G.left M hM := by
  sorry

end AlgebraicGeometry.Scheme.Modules
