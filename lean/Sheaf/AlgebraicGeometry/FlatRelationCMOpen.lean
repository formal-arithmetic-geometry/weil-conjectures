/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.RestrictedFibreLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FibreCohenMacaulayLocus
import Sheaf.AlgebraicGeometry.CohenMacaulayFieldExtension
import Sheaf.TraceFormula.FlatLFPCMLocusFibreDense
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties

/-! # Cohen--Macaulay open restriction of a flat equivalence relation

Source: Stacks Project, More on Groupoids, Tag 0460 (lemma-make-CM), clauses (4), (5),
and More on Morphisms, Tag 045R (definition-CM)
(blueprint: lem-sfb-flat-relation-cm-open).

The relation is expressed on sections in `Over S`. Its restriction to `W` is the
iterated scheme pullback `(W ×[V] R) ×[V] W`, with the first pullback along `t`
and the second along `s`. The two displayed projections are exactly its maps to `W`.
The Cohen--Macaulay condition is written using the existing fibre, stalk, depth,
Noetherian-ring and Krull-dimension declarations.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A flat locally finitely presented scheme equivalence relation has an open
restriction with Cohen--Macaulay, locally finitely presented projections, whose
saturation maps surjectively, flatly and locally finitely presentedly to the objects.

Source: Stacks Project, More on Groupoids, Tag 0460, clauses (4), (5), specialized to
an equivalence relation; More on Morphisms, Tag 045R
(blueprint: lem-sfb-flat-relation-cm-open).

Proof:
1. For a flat locally finitely presented map `f`, let `C_f` be the fibre depth-equals-
   dimension locus. The fibres are locally Noetherian by
   `lem-sbc-restricted-fibre-locally-noetherian` with the whole base open, and this
   locus is open by `lem-sbc-fibre-cohen-macaulay-locus-open`.
2. A cartesian square identifies the new fibre with the old fibre extended along
   residue fields (`lem-weil-pbc-fibre-of-base-change`). The old fibre is locally
   of finite type over its residue field: tensor a finite presentation with that
   field. The first assertion of `lem-pur-cohen-macaulay-field-extension` therefore
   gives exact inverse-image compatibility of `C_f`, without a Noetherian base
   assumption. Isomorphisms preserve fibre local rings, regular sequences, prime
   chains, depth and dimension, so the assignment is invariant under isomorphisms.
3. Reflexivity on sections gives the unique identity `e : V → R`; symmetry gives
   an involution `i : R → R` interchanging `s` and `t`, with involutivity following
   from injectivity on sections. Apply `lem-sfb-relation-open-locus-descent` to
   `C_f`, obtaining `W = e⁻¹(C_s)` and `t⁻¹(W) = C_s`. The involution identifies
   the fibre local rings and gives `s⁻¹(W) = C_t`.
4. The source `W ×[V,t] R` is the open `t⁻¹(W)`. By
   `lem-trf-flat-lfp-cm-locus-fibre-dense`, `C_s` meets every nonempty open of
   every `s`-fibre. Each such fibre is nonempty by `e`, so this open maps
   surjectively to `V`. If `V` is empty, surjectivity is vacuous.
5. Open inclusions are etale (`lem-weil-pbc-open-immersion-etale`). Source-open
   restriction preserves flatness and local finite presentation by clause (i)
   of `lem-sfb-scheme-etale-source-target-properties`. Thus the saturation map
   has both properties. The iterated pullback is the open intersection
   `t⁻¹(W) ∩ s⁻¹(W)` by the pullback universal properties.
6. The two projections from this intersection factor through `W`. Their squares
   with `s` and `t` have open, hence etale, horizontal maps, so the square clause
   of `lem-sfb-scheme-etale-source-target-properties` gives flatness and local
   finite presentation. An open immersion identifies target local rings and
   residue fields; the fibre of each projection is an open restriction of the
   corresponding original fibre. Its local rings are unchanged, Noetherian,
   and have depth equal to dimension since the intersection lies in `C_s ∩ C_t`.
   These are exactly the Cohen--Macaulay assertions for both projections.
-/
theorem exists_flat_relation_cm_open
    {S : Scheme.{u}} {V R : Over S} (s t : R ⟶ V)
    (hinj : ∀ T : Over S,
      Function.Injective (fun r : T ⟶ R ↦ (r ≫ s, r ≫ t)))
    (hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ V ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b))
    [Flat s.left] [Flat t.left]
    [LocallyOfFinitePresentation s.left] [LocallyOfFinitePresentation t.left] :
    ∃ W : V.left.Opens,
      (∀ p : pullback (pullback.snd W.ι t.left ≫ s.left) W.ι ⟶ W.toScheme,
        (p = pullback.fst (pullback.snd W.ι t.left ≫ s.left) W.ι ≫
            pullback.fst W.ι t.left ∨
          p = pullback.snd (pullback.snd W.ι t.left ≫ s.left) W.ι) →
        Flat p ∧ LocallyOfFinitePresentation p ∧
          ∀ (w : W.toScheme) (x : p.fiber w),
            IsNoetherianRing ((p.fiber w).presheaf.stalk x) ∧
              (IsLocalRing.depth (R := (p.fiber w).presheaf.stalk x)
                ((p.fiber w).presheaf.stalk x) : WithBot ℕ∞) =
                ringKrullDim ((p.fiber w).presheaf.stalk x)) ∧
      Surjective (pullback.snd W.ι t.left ≫ s.left) ∧
      Flat (pullback.snd W.ι t.left ≫ s.left) ∧
      LocallyOfFinitePresentation (pullback.snd W.ι t.left ≫ s.left) := by
  sorry

end AlgebraicGeometry
