/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Constructible
public import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.GeometricallyReducedAlgebraicClosureTest
import Sheaf.AlgebraicGeometry.GeometricallyReducedFibreLocus

/-!
# Constructibility of the geometrically reduced fibre locus

Source: literature/stacks-project/more-morphisms.tex, Tag 0579 (lemma-geometrically-
reduced-constructible), with topology.tex Tag 053W and varieties.tex Tags 035X and 020I
(blueprint: lem-trf-geometric-reduced-fibre-locus-constructible).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Let `f : X ⟶ T` be quasi-compact and locally of finite presentation, with `T` qcqs.
Then the set of points of `T` whose geometric fibre, formed using the chosen algebraic closure
of the residue field, is reduced is constructible. Empty geometric fibres are included.

Source: literature/stacks-project/more-morphisms.tex, Tag 0579 (lemma-geometrically-reduced-
constructible), with topology.tex Tag 053W and varieties.tex Tags 035X and 020I.
Proof (following the node's four steps):
1. For each point choose an affine base neighbourhood `V` using
   [lem-weil-pbc-affine-opens-basis]. Quasi-compactness of `f` gives a finite affine
   cover `Uᵢ` of its inverse image by [lem-weil-pbc-qcqs-finite-affine-open-cover].
   By [lem-weil-pbc-lfp-affine-opens-finite-presentation], local finite presentation
   of `f` makes each chart ring map finitely presented. Apply
   [lem-trf-geometrically-reduced-fibre-locus] to each chart, then use
   [lem-trf-geometric-reducedness-algebraic-closure-test] to identify its locus with
   reducedness of the chosen algebraic-closure fibre. This includes every characteristic
   and empty chart fibres.
2. The base changes of the `Uᵢ` cover the geometric fibre. Reducedness is local on an
   open cover ([def-pc-reduced-scheme]), so the locus over `V` is the intersection of
   the finitely many chart loci. It is constructible by the Boolean-algebra definition
   [def-weil-constructible-subset].
3. These affine neighbourhoods establish local constructibility, in the sense used by
   [lem-trf-locally-constructible-qcqs-global].
4. Apply [lem-trf-locally-constructible-qcqs-global] on the qcqs base to obtain global
   constructibility. Empty sources and empty geometric fibres are included: reducedness
   is vacuous there. Neither flatness nor a Noetherian hypothesis is used.
(blueprint: lem-trf-geometric-reduced-fibre-locus-constructible). -/
theorem geometricReduced_fibre_locus_constructible
    {X T : Scheme.{u}} (f : X ⟶ T) [QuasiCompact f]
    [LocallyOfFinitePresentation f] [CompactSpace T] [QuasiSeparatedSpace T] :
    Topology.IsConstructible
      {t : T |
        IsReduced
          (Limits.pullback f (Scheme.fromSpecAlgebraicClosureResidueField T t))} := by
  sorry

end AlgebraicGeometry
