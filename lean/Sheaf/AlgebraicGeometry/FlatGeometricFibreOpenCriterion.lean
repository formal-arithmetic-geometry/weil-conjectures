/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q99
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.FieldExtensionFpqcCover
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.Morphisms.FpqcOpenImmersionDescent
import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Sheaf.AlgebraicGeometry.GeometricFibreUnramifiedCriterion
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Gluing

/-!
# Recognizing open immersions and isomorphisms on geometric fibres

Source: Stacks Project, More on Morphisms, Tag 039E; Morphisms, Tag 02GM;
Étale Morphisms of Schemes, Tag 025G
(blueprint: lem-sfb-flat-geometric-fibre-open-criterion).

The underlying arrow of `(Over.pullback s).map (Over.homMk f hcomm)` is the canonical
map `X ×[S] Spec Ω ⟶ Y ×[S] Spec Ω`. The over-category objects are explicitly given
in each statement so that the two structure morphisms are fixed.

## Main statements

- `isOpenImmersion_isIso_of_geometric_fibres_of_flat`: both tests with flat source.
- `isOpenImmersion_isIso_of_geometric_fibres_of_smooth`: both tests between smooth schemes.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The geometric-fibre tests for open immersions and isomorphisms, with flat source.
Source: Stacks Project, Tags 039E, 02GM and 025G
(blueprint: lem-sfb-flat-geometric-fibre-open-criterion).

Proof:
1. For each point of `S`, extend its residue field to an algebraic closure.
   By `lem-pc-field-extension-fpqc-cover` and `lem-weil-pbc-fpqc-covering-axioms`,
   this gives an fpqc cover of the ordinary target fibre. The universal property
   `def-pc-fibre-product` identifies the pulled-back ordinary fibre map with the
   assumed geometric fibre map. Descend its open-immersion property by
   `lem-galois-fpqc-descend-open-immersion`, including when the fibre is empty.
2. Open immersions induce isomorphisms of local rings and are therefore flat.
   Apply `lem-sfb-relative-flat-fibre-test` at every source point, using flatness
   and local finite presentation of `p` and local finite type of `q`, to obtain
   flatness of `f`.
3. For a geometric point of `Y`, compose with `q`. The fibre of `f` there is a
   base change of the corresponding map in the hypothesis, by the fibre-product
   universal property. By `lem-weil-pbc-open-immersion-base-change`, it is open
   in the one-point spectrum of an algebraically closed field. It is thus empty
   or that spectrum, and in either case unramified. Local finite presentation
   implies local finite type, so `lem-trf-geometric-fibre-unramified-criterion`
   makes `f` unramified.
4. Two field-valued points of `X` with the same image in `Y` become equal after
   extension to an algebraic closure: they lie in one geometric fibre, whose
   map is an open immersion and hence a monomorphism. Descend equality along
   the fpqc field-extension cover using `lem-weil-pbc-fpqc-representable-descent`.
   The field-point criterion `def-weil-radicial-morphism` makes `f` radicial.
5. Flatness, unramifiedness and local finite presentation make `f` étale by
   `def-weil-etale-morphism`. Now `lem-weil-pbc-radicial-etale-open` gives the
   open-immersion conclusion.
6. If all geometric fibre maps are isomorphisms, they are open immersions, so
   the first conclusion applies. For each point `y` of `Y`, choose an algebraic
   closure of its residue field. The corresponding point of the target fibre
   lifts through the inverse fibre map. Its projection to `X` maps to `y`.
   Hence `f` is surjective, and a surjective open immersion is an isomorphism.
No step assumes nonempty fibres, reducedness, or Noetherianity of the base. -/
theorem isOpenImmersion_isIso_of_geometric_fibres_of_flat
    {S X Y : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y)
    (hcomm : f ≫ q = p) [Flat p] [LocallyOfFinitePresentation p]
    [LocallyOfFiniteType q] [LocallyOfFinitePresentation f] :
    ((∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
        IsOpenImmersion
          (((Over.pullback s).map
            (Over.homMk (U := Over.mk p) (V := Over.mk q) f hcomm)).left)) →
      IsOpenImmersion f) ∧
    ((∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
        IsIso
          (((Over.pullback s).map
            (Over.homMk (U := Over.mk p) (V := Over.mk q) f hcomm)).left)) →
      IsIso f) := by
  sorry

/-- Both geometric-fibre tests apply to locally finitely presented maps between smooth
schemes over an arbitrary base, with empty schemes and empty fibres allowed.
Source: Stacks Project, Tags 039E, 02GM, 025G, 01VE and 01VF
(blueprint: lem-sfb-flat-geometric-fibre-open-criterion).

Proof (step 7 of the node): `lem-pc-smooth-flat` gives flatness and local finite
presentation of both structure morphisms. Local finite presentation implies local
finite type, because a finite polynomial presentation supplies a finite generating
set. Thus the hypotheses of `isOpenImmersion_isIso_of_geometric_fibres_of_flat`
hold. Apply its two conclusions. No reducedness or Noetherian assumption is needed. -/
theorem isOpenImmersion_isIso_of_geometric_fibres_of_smooth
    {S X Y : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y)
    (hcomm : f ≫ q = p) [Smooth p] [Smooth q] [LocallyOfFinitePresentation f] :
    ((∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
        IsOpenImmersion
          (((Over.pullback s).map
            (Over.homMk (U := Over.mk p) (V := Over.mk q) f hcomm)).left)) →
      IsOpenImmersion f) ∧
    ((∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
        IsIso
          (((Over.pullback s).map
            (Over.homMk (U := Over.mk p) (V := Over.mk q) f hcomm)).left)) →
      IsIso f) := by
  sorry

end AlgebraicGeometry
