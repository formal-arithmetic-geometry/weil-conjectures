/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q148
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import WeilConjectures.AlgebraicGeometry.SectionComponentPullback
import WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.AlgebraicGeometry.FlatReducedSectionComponentOpen
import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates

/-!
# The relative neutral open subgroup of a smooth group over a trait

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §6.4, paragraph following
Proposition 2, printed p. 154; Stacks Project, Tags 055M, 055R and 057I
(blueprint: lem-sfb-smooth-group-relative-neutral-open).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj MonObj

namespace AlgebraicGeometry

/-- The relative identity component is an open subgroup, has geometrically connected fibres,
and commutes with arbitrary base change. On geometric fibres its left-multiplication orbits
are exactly the connected components. The orbit through a rational point g is the right
translate G⁰g of the neutral open. Equality of the families of these open subsets records
all the orbit components, including their open-subscheme structures.

Source: BLR, Néron Models, §6.4, after Proposition 2, printed p. 154; EGA IV₃, 15.6.5;
Stacks Project, Tags 055M, 055R, 057I and 0B7R
(blueprint: lem-sfb-smooth-group-relative-neutral-open).

Proof:
1. Smoothness gives flatness, local finite presentation and geometrically reduced fibres
(sbc-lem-smooth-criterion, sbc-lem-smooth-geometrically-reduced). Finite type gives
quasi-compactness; separatedness gives quasi-separatedness (lem-pc-separated-quasi-separated).
Thus the structure morphism is of finite presentation.
2. Apply lem-trf-flat-reduced-section-component-open to its identity section. The union U
of the fibre components through that section is open. Since the base is affine,
lem-trf-section-component-quasi-compact makes U quasi-compact.
3. By lem-sbc-section-component-cartesian the inverse image of U after any base change
is the section-component locus of the pulled-back identity. The pullback of an open is
its inverse-image open subscheme (def-pc-base-change). In particular its ordinary fibres
are the components through the identity; their rational identity points make them
geometrically connected (lem-sbc-connected-rational-point-geometrically-connected).
This gives the geometric-fibre characterization and arbitrary-base-change compatibility.
4. Check multiplication and inversion at every geometric point of their sources.
By lem-sfb-locally-algebraic-group-identity-component they preserve the geometric identity
components, hence their images lie in U. The identity section does too. Factor these maps
uniquely through U (def-weil-open-immersion); their group diagrams descend since the open
immersion is a monomorphism. This makes U an open subgroup, compatibly with base change.
5. The restriction is smooth by lem-pc-open-immersion-smooth-composition. Its diagonal is
a base change of the original closed diagonal, hence closed by
lem-weil-pbc-closed-immersion-base-change. It is locally of finite type as an open
restriction, and quasi-compact by step 2, hence of finite type.
6. Over each algebraically closed field, lem-sfb-group-neutral-component-translates
identifies every component with a translate of the identity component. Right translation
by g identifies G⁰g with the component of g, by the same connectedness and maximality
argument as for left translation. These are precisely the orbits for left multiplication
by G⁰. This uses no commutativity or connectedness hypothesis on G. -/
theorem GrpObj.smoothGroup_relativeNeutralOpen
    (C : Type u) [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (G : Over (Spec (.of C))) [GrpObj G]
    [Smooth G.hom] [IsSeparated G.hom]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    ∃ U : G.left.Opens,
      Smooth (U.ι ≫ G.hom) ∧ IsSeparated (U.ι ≫ G.hom) ∧
      LocallyOfFiniteType (U.ι ≫ G.hom) ∧ QuasiCompact (U.ι ≫ G.hom) ∧
      GeometricallyConnected (U.ι ≫ G.hom) ∧
      (∀ (T : Scheme.{u}) (t : T ⟶ Spec (.of C)),
        (pullback.fst G.hom t) ⁻¹' (U : Set G.left) =
          {x : ↥(pullback G.hom t) |
            x ∈ connectedComponentIn
              ((pullback.snd G.hom t) ⁻¹' {(pullback.snd G.hom t) x})
              (η[(Over.pullback t).obj G].left ((pullback.snd G.hom t) x))}) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of C)),
        (pullback.fst G.hom s) ⁻¹' (U : Set G.left) =
          connectedComponent (GrpObj.onePoint ((Over.pullback s).obj G)) ∧
        Set.range (fun g : 𝟙_ (Over (Spec (.of Ω))) ⟶ (Over.pullback s).obj G =>
          (GrpObj.mulRight ((Over.pullback s).obj G) g).left ''
            ((pullback.fst G.hom s) ⁻¹' (U : Set G.left))) =
          Set.range (fun x : ↥(pullback G.hom s) => connectedComponent x)) ∧
      ∃ gU : GrpObj (Over.mk (U.ι ≫ G.hom)),
        @IsMonHom _ _ _ _ _ gU.toMonObj _ (Over.homMk (V := G) U.ι) := by
  sorry

end AlgebraicGeometry
