module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Flat comparison square of residue fibres

Source: Stacks Project, Tag 05VJ, proof of
`lemma-base-change-criterion-flatness-fibre`, final cartesian diagram and the following
sentence (blueprint: lem-sfb-flat-residue-fibre-square).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Residue fibres commute with parameter base change, naturally in an `S`-morphism;
the residue-field map and the two comparison projections are flat. The isomorphisms
are specified by both projections, and the comparison maps by their composites with
the fibre inclusions, so these are the canonical comparisons.

Source: Stacks Project, Tag 05VJ, proof of
`lemma-base-change-criterion-flatness-fibre`, final diagram and following sentence
(blueprint: lem-sfb-flat-residue-fibre-square).

Proof: apply `lem-weil-pbc-fibre-of-base-change`, that is Mathlib's
`isPullback_fiberToSpecResidueField_of_isPullback`, to the pullback squares for
`(p,h)` and `(q,h)`. Their universal properties give the two isomorphisms with the
specified projections and the two identities with the fibre inclusions.
For commutativity, the two composites to the fibre of `q` have equal projections
to `Y` and to `Spec κ(h(t))`, hence agree by pullback extensionality.
For cartesianness, given compatible maps `v : D ⟶ p.fiber (h t)` and
`w : D ⟶ (pullback.snd q h).fiber t`, use the residue-field projection of `w`
and `v` to obtain a unique map to `(pullback.snd p h).fiber t`. Compatibility
ensures the required equation over `Spec κ(h(t))`. The two projections of its
composite to the fibre of `pullback.snd q h` agree with those of `w`, and thus
the composite equals `w`; uniqueness follows from the two projections of the
first comparison isomorphism (`def-pc-fibre-product`, `def-pc-scheme-fibre`).
Finally the residue-field homomorphism is a homomorphism of fields, so its
spectrum map is flat (`lem-pc-field-extension-flat`). Its base changes are the
two comparison maps, which are flat by `lem-weil-pbc-flat-morphism-base-change`.
None of these arguments uses any finiteness, flatness or Noetherian hypothesis
on `p`, `q`, `f` or `h`. -/
theorem flat_residue_fibre_square {S X Y T : Scheme.{u}}
    (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y) (h : T ⟶ S)
    (hf : f ≫ q = p) (t : T) :
    ∃ (a : (pullback.snd p h).fiber t ⟶ p.fiber (h t))
      (b : (pullback.snd q h).fiber t ⟶ q.fiber (h t)),
      (∃ α : (pullback.snd p h).fiber t ≅
          pullback (p.fiberToSpecResidueField (h t)) (Spec.map (h.residueFieldMap t)),
        α.hom ≫ pullback.fst _ _ = a ∧
        α.hom ≫ pullback.snd _ _ = (pullback.snd p h).fiberToSpecResidueField t) ∧
      (∃ β : (pullback.snd q h).fiber t ≅
          pullback (q.fiberToSpecResidueField (h t)) (Spec.map (h.residueFieldMap t)),
        β.hom ≫ pullback.fst _ _ = b ∧
        β.hom ≫ pullback.snd _ _ = (pullback.snd q h).fiberToSpecResidueField t) ∧
      a ≫ ((Over.pullback (S.fromSpecResidueField (h t))).map
        (Over.homMk f hf : Over.mk p ⟶ Over.mk q)).left =
        ((Over.pullback (T.fromSpecResidueField t)).map
          ((Over.pullback h).map (Over.homMk f hf : Over.mk p ⟶ Over.mk q))).left ≫ b ∧
      IsPullback a
        (((Over.pullback (T.fromSpecResidueField t)).map
          ((Over.pullback h).map (Over.homMk f hf : Over.mk p ⟶ Over.mk q))).left)
        (((Over.pullback (S.fromSpecResidueField (h t))).map
          (Over.homMk f hf : Over.mk p ⟶ Over.mk q)).left) b ∧
      a ≫ p.fiberι (h t) = (pullback.snd p h).fiberι t ≫ pullback.fst p h ∧
      b ≫ q.fiberι (h t) = (pullback.snd q h).fiberι t ≫ pullback.fst q h ∧
      Flat (Spec.map (h.residueFieldMap t)) ∧ Flat a ∧ Flat b := sorry

end AlgebraicGeometry
