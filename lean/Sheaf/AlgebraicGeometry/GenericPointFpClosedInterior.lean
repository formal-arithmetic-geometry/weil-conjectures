/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q83
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Constructible
import Mathlib.Topology.Spectral.Basic
import WeilConjectures.Topology.ProconstructibleClosureSpecialization

/-! # Generic points in finitely presented closed subschemes

Source: Stacks Project, Properties, Tag 0AAW, part (1), applied to the image of a
finitely presented closed immersion, as in More on Groupoids, Tag 0ABB.
(blueprint: lem-sfb-generic-point-fp-closed-interior)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsClosedImmersion

/-- A component generic point in the image of a finitely presented closed immersion has an
open neighbourhood contained in that image as a set. No factorization through the closed
subscheme is asserted. Source: Stacks Project, Properties, Tag 0AAW, part (1), and More on
Groupoids, Tag 0ABB. (blueprint: lem-sfb-generic-point-fp-closed-interior)

Proof:
1. Choose an affine open `U` containing `ξ`. Its inverse image `W` under `i` is affine
   by `def-weil-closed-immersion`. The induced `W ⟶ U` is locally of finite presentation
   by `lem-weil-pbc-lfp-affine-opens-finite-presentation` and
   `def-sbc-locally-finite-presentation`. Its inverse images of affine opens are affine,
   hence quasi-compact by `lem-weil-pbc-affine-scheme-qcqs`. The latter also makes `U`
   quasi-compact and quasi-separated, hence spectral by `lem-weil-pbc-qcqs-scheme-spectral`.
2. Chevalley (`lem-weil-pbc-chevalley-constructible-image`) makes the image `E` of `W`
   constructible in `U`. Its complement `F` is constructible by
   `def-weil-constructible-subset`, and `ξ` does not belong to `F`.
3. If `e` in `U` specializes to `ξ`, the component `C = closure {ξ}` in `X` is contained
   in the irreducible closed set `closure {e}`. Maximality of `C` forces equality.
   Intersecting with `U` and using sobriety of the spectral space `U` gives `e = ξ`.
   This uses `def-sc-generic-point`, `def-weil-irreducible-components`, and
   `def-weil-spectral-space`.
4. If `ξ` lay in the closure of `F` in `U`, apply
   `lem-weil-pbc-spectral-proconstructible-closure-specialization` to the singleton family
   consisting of `F`. It gives `e` in `F` specializing to `ξ`, contradicting step 3.
5. Take `N` to be `U` minus the closure of `F` in `U`, with its open subscheme structure
   (`def-pc-scheme`, `def-weil-open-immersion`). It is open in `X`, contains `ξ`, and is
   contained in `E`, hence in the image of `i`, since `F` is contained in its closure. -/
theorem exists_open_subset_range_of_isGenericPoint
    {X Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]
    [AlgebraicGeometry.LocallyOfFinitePresentation i] [AlgebraicGeometry.QuasiCompact i]
    [AlgebraicGeometry.QuasiSeparated i] {C : Set X} (hC : C ∈ irreducibleComponents X)
    {ξ : X} (hξ : IsGenericPoint ξ C) (hξi : ξ ∈ Set.range i) :
    ∃ N : X.Opens, ξ ∈ N ∧ (N : Set X) ⊆ Set.range i := by
  sorry

end AlgebraicGeometry.IsClosedImmersion
