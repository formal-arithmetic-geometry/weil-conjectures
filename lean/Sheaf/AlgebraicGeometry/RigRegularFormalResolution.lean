/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q87
-/
module

public import Sheaf.AlgebraicGeometry.FormalResolutionRule
import Sheaf.RingTheory.FieldsExcellent
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.FlatUnderRegular
import WeilConjectures.RingTheory.GRingCompletionRegular
import WeilConjectures.RingTheory.RegularMapAscent

/-! # Strong resolution of rig-regular locally principal formal varieties

Source: Temkin, Non-embedded Desingularization, Theorem 3.1.5 and §3.4.1;
ILO VIII Remark 2.3.11 for original-singular-locus support
(blueprint: lem-per-rig-regular-formal-resolution).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace AlgebraicGeometry

/-- A single strong resolution rule on all the stated formal pairs.
Source: Temkin Theorem 3.1.5 (strong clause), proof §3.4.1; ILO VIII Remark 2.3.11
(blueprint: lem-per-rig-regular-formal-resolution).

Proof:
1. Choose a strong variety resolution compatible with all regular morphisms across
   coefficient fields, including finite disjoint unions, with every center supported
   over the original singular locus: lem-per-rig-variety-strong-resolution.
2. Algebraize every principal affine formal pair by
   lem-per-rig-principal-formal-algebraization. Its Cartier closed fibre contains the
   algebraic singular locus, so every retained algebraic center is open after completion.
3. Complete the ordered algebraic tower. Formal blowups are these completed blowups,
   and coherent center ideals remain coherent and open. Fields and finite type algebras
   are excellent (lem-exc-fields-excellent, lem-exc-finite-type-localization-excellent),
   hence G-rings by def-exc-excellent-ring. Completion maps are regular by
   lem-weil-pbc-g-ring-completion-regular. Flat local regularity descent
   (lem-weil-pbc-flat-under-regular) puts all centers over the formal singular locus.
4. At the terminal algebraic level every affine ring is excellent and regular. Its
   completion is Noetherian by lem-weil-pbc-adic-completion-noetherian and the completion
   map is regular by lem-weil-pbc-g-ring-completion-regular. Regularity ascent
   (lem-weil-pbc-regular-map-ascent) makes the final complete chart regular.
5. Apply lem-per-rig-formal-resolution-intrinsic: the identity on a fixed completion
   identifies towers obtained from different algebraizations, and regular thick-fibre
   comparison gives compatibility with all regular completed-pair morphisms. No common
   coefficient field or algebraization of the morphism is needed. Delete exactly empty
   centers, retaining all other extended ideals in their original order.
6. Refine a finite affine cover by principal charts and apply
   lem-per-rig-formal-resolution-gluing. Finite disjoint unions synchronize the stages;
   agreement on refinements and overlaps glues coherent centers, towers and pullback
   comparisons. Regularity and support are local. The empty input has length zero.
-/
theorem exists_rigRegularFormalResolutionRule :
    Nonempty RigRegularFormalResolutionRule.{u} := by
  sorry

end AlgebraicGeometry
