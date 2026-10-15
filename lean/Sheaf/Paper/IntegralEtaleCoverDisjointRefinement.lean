/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale
import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.PieceSection
import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber

/-! # Disjoint refinement of an étale cover over an integral morphism

Source: Stacks Project, Tags 04DR, 04DQ and 04DP
(blueprint: lem-sbc-integral-etale-cover-disjoint-refinement)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w

namespace AlgebraicGeometry

/-- An étale cover after an étale pointed neighbourhood of the base admits a disjoint
open refinement over an integral morphism.

Source: Stacks Project, Tag 04DR (lemma-integral-B), using Tag 04DQ (lemma-finite-B)
and the explicit refinement formulation of Tag 04DP (lemma-simplify-B).
(blueprint: lem-sbc-integral-etale-cover-disjoint-refinement)

Proof:
1. Choose an affine open `V₀` containing `v` (lem-weil-pbc-affine-opens-basis).
   Base change preserves integrality (lem-sbc-integral-morphism-base-change), so
   `T = X ×_Y V₀` is affine with integral coordinate algebra `B` over `A = Γ(V₀)`.
   Pull back the cover (lem-weil-pbc-etale-covering-base-change), retaining its maps
   to the original members. For empty `T`, use the empty decomposition.
2. Refine by affine standard étale members (lem-weil-pbc-affine-opens-basis and
   lem-weil-pbc-etale-locally-standard). Their images are open
   (lem-weil-pbc-etale-morphism-open-map); quasi-compactness of `Spec B`
   (lem-weil-pbc-affine-scheme-qcqs) gives a finite subcover `Eₖ`, still with maps
   to selected original members.
3. Descend these algebras to a finite `A`-subalgebra `B₀` of `B`
   (lem-sbc-standard-etale-finite-subalgebra). Set `Z = Spec B₀` and let `Fₖ`
   be the descended standard étale schemes. The tensor-product universal property
   identifies `Eₖ` with `T ×_Z Fₖ` (def-pc-fibre-product). The inclusion `B₀ → B`
   is integral and injective; lying over (lem-weil-pbc-integral-injective-lying-over)
   makes `T → Z` surjective. Thus the descended `Fₖ` cover `Z`.
4. Choose an algebraic closure `Ω` of the residue field at `v`. The geometric fibre
   of finite `Z → V₀` is finite (lem-weil-pbc-finite-closed-map-finite-fibres).
   Each of its residue fields is `Ω`: a finite-dimensional domain over a field is
   a field, and `Ω` is algebraically closed. For each geometric fibre point choose
   a lift into some `Fₖ` (lem-weil-pbc-etale-cover-geometric-point-lift). Apply
   lem-sbc-finite-pointed-piece-refinement to obtain a pointed neighbourhood and
   a clopen piece mapping to that `Fₖ`, containing just that marked fibre point.
5. Take the finite fibre product of these pointed neighbourhoods; for an empty
   fibre use the identity. Finite limits in the small étale site keep it étale
   (def-weil-pbc-etale-site). Pull back the pieces and subtract earlier pieces
   in a finite ordering. These clopen differences are disjoint, preserve their
   marked points and maps, and have the same union.
6. Every ordinary point over the marked base point lifts to an `Ω`-point
   (lem-weil-pbc-finite-geometric-point-lift), so the pieces cover that fibre.
   The clopen complement has closed image under the finite projection
   (lem-weil-pbc-finite-closed-map-finite-fibres). Remove this image from the base;
   the resulting pointed neighbourhood has a disjoint covering by the pieces.
   This also handles the empty geometric fibre.
7. Pull back these pieces along `T → Z`. Inverse images preserve disjointness
   and unions. Their maps to `T` and the selected `Fₖ` induce maps to `Eₖ` by
   the fibre-product universal property (def-pc-fibre-product), and then to the
   original cover members. Both structural maps agree, giving the final
   compatibility with `id_X × a`. The pieces are open subschemes
   (def-weil-open-immersion); an empty total pullback permits the empty index set.
-/
theorem integral_etale_cover_disjoint_refinement
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]
    (V : Y.Etale) (v : V.left)
    (I : Type w) (U : I → (CategoryTheory.Limits.pullback f V.hom : Scheme).Etale)
    (hU : ∀ x : (CategoryTheory.Limits.pullback f V.hom : Scheme),
      ∃ i : I, ∃ y : (U i).left,
      ((Scheme.Hom.toLRSHom' (U i).hom).base : TopCat.Hom _ _).hom y = x) :
    ∃ (V' : Y.Etale) (a : V' ⟶ V) (v' : V'.left),
      (Scheme.Hom.toLRSHom' a.left).base v' = v ∧
      ∃ (J : Type u) (W : J → Scheme) (w : ∀ j, W j ⟶ pullback f V'.hom)
        (_ : ∀ j, IsOpenImmersion (w j)) (α : J → I)
        (b : ∀ j, W j ⟶ (U (α j)).left),
        Set.Pairwise Set.univ (fun j k =>
          Disjoint
            (Set.range (((Scheme.Hom.toLRSHom' (w j)).base : TopCat.Hom _ _).hom))
            (Set.range (((Scheme.Hom.toLRSHom' (w k)).base : TopCat.Hom _ _).hom))) ∧
        (⋃ j, Set.range (((Scheme.Hom.toLRSHom' (w j)).base : TopCat.Hom _ _).hom)) = Set.univ ∧
        (∀ j, b j ≫ (U (α j)).hom =
          w j ≫ CategoryTheory.Limits.pullback.map f V'.hom f V.hom (𝟙 X) a.left (𝟙 Y)
            (by simp) (by simp only [Category.comp_id]; exact a.w.symm)) := by
  sorry

end AlgebraicGeometry
