/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Morphisms with geometrically reduced fibres

Three facts about morphisms whose geometric fibres are reduced.

The first is that a smooth morphism has geometrically reduced fibres: its geometric fibres
are smooth varieties, hence regular, hence reduced. Together with the instances
`Smooth → Flat` and `Smooth → LocallyOfFinitePresentation` of
`Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`, this is what makes a smooth morphism
satisfy the hypotheses of the statements below and of degree-zero flat base change.

The second is that precomposing with an étale morphism preserves geometrically reduced fibres,
an étale scheme over a reduced scheme being reduced. It makes the hypotheses of the third
statement stable under passing to the objects of the small étale site of the source.

The third is the étale-local slicing of such a morphism: a flat morphism, locally of
finite presentation, with geometrically reduced fibres admits an étale covering of its
source along which it factors through an étale morphism to the base, the remaining leg
being flat, locally of finite presentation, affine, with geometrically connected fibres
and admitting a section. The covering is recorded as an index type together with a jointly
surjective family of étale morphisms rather than as a bundled `Scheme.OpenCover`, since
the members of an étale cover are not open subschemes of the source.

## Main statements

- `AlgebraicGeometry.Smooth.geometricallyReduced`: a smooth morphism has geometrically
  reduced fibres.
- `AlgebraicGeometry.GeometricallyReduced.comp_of_etale`: an étale morphism followed by a
  morphism with geometrically reduced fibres has geometrically reduced fibres.
- `AlgebraicGeometry.exists_etaleCover_factorization`: the étale-local slicing of a flat,
  locally finitely presented morphism with geometrically reduced fibres.
- `AlgebraicGeometry.Smooth.exists_etaleCover_factorization`: the étale-local slicing of a
  smooth morphism, through smooth morphisms of affine schemes.

## References

- Stacks Project, More on Morphisms, Lemma 37.46.3,
  <https://stacks.math.columbia.edu/tag/0EY5>
- Stacks Project, Tag `0EY4`, <https://stacks.math.columbia.edu/tag/0EY4>
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth morphism has geometrically reduced fibres: the geometric fibres of a smooth
morphism are smooth varieties over an algebraically closed field, hence regular, hence
reduced. -/
instance Smooth.geometricallyReduced {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] :
    GeometricallyReduced f :=
  sorry

/-- An étale morphism followed by a morphism with geometrically reduced fibres has
geometrically reduced fibres: for a field `K` and `Spec K ⟶ Z`, the scheme `X ×_Z Spec K` is
étale over the reduced scheme `Y ×_Z Spec K`, and a scheme étale over a reduced scheme is
reduced. -/
theorem GeometricallyReduced.comp_of_etale {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Etale f] [GeometricallyReduced g] : GeometricallyReduced (f ≫ g) :=
  sorry

/-- Let `f : X ⟶ S` be flat, locally of finite presentation and with geometrically reduced
fibres. Then there is an étale covering `p i : U i ⟶ X` of `X`, that is, a family of étale
morphisms whose images cover `X`, such that each composite `p i ≫ f` factors as `q i ≫ r i`
with `r i : V i ⟶ S` étale and `q i : U i ⟶ V i` flat, locally of finite presentation and
affine, with geometrically connected fibres, and admitting a section:

```
U i --q i--> V i
 |            |
p i          r i
 v            v
 X ----f----> S
```

A smooth morphism satisfies the hypotheses, by `AlgebraicGeometry.Smooth.geometricallyReduced`
and the instances `Smooth → Flat` and `Smooth → LocallyOfFinitePresentation`; that special
case is Stacks `0EY4`, in which the first leg `q i` is moreover smooth. -/
@[stacks 0EY5]
theorem exists_etaleCover_factorization {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [GeometricallyReduced f] :
    ∃ (ι : Type u) (U : ι → Scheme.{u}) (p : ∀ i, U i ⟶ X) (V : ι → Scheme.{u})
      (q : ∀ i, U i ⟶ V i) (r : ∀ i, V i ⟶ S),
      (∀ i, Etale (p i)) ∧ (∀ x : X, ∃ (i : ι) (y : U i), (p i).base y = x) ∧
      (∀ i, Etale (r i)) ∧ (∀ i, Flat (q i)) ∧ (∀ i, LocallyOfFinitePresentation (q i)) ∧
      (∀ i, IsAffineHom (q i)) ∧ (∀ i, GeometricallyConnected (q i)) ∧
      (∀ i, ∃ s : V i ⟶ U i, s ≫ q i = 𝟙 (V i)) ∧ (∀ i, q i ≫ r i = p i ≫ f) :=
  sorry

/-- **Slicing a smooth morphism** (blueprint `sbc-lem-slicing`). Let `f : X ⟶ S` be smooth.
Then there is an étale covering `p i : U i ⟶ X` of `X` such that each composite `p i ≫ f`
factors as `q i ≫ r i` with `r i : V i ⟶ S` étale and `q i : U i ⟶ V i` a smooth morphism of
affine schemes with geometrically connected fibres admitting a section.

This is deduced from `AlgebraicGeometry.exists_etaleCover_factorization`: the first leg `q i`
given there is smooth since `q i ≫ r i = p i ≫ f` is smooth and `r i` is étale, and the
factorisations are restricted to the affine opens of `V i` and their preimages under the
affine morphism `q i`. -/
@[stacks 0EY4]
theorem Smooth.exists_etaleCover_factorization {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] :
    ∃ (ι : Type u) (U : ι → Scheme.{u}) (p : ∀ i, U i ⟶ X) (V : ι → Scheme.{u})
      (q : ∀ i, U i ⟶ V i) (r : ∀ i, V i ⟶ S),
      (∀ i, Etale (p i)) ∧ (∀ x : X, ∃ (i : ι) (y : U i), (p i).base y = x) ∧
      (∀ i, Etale (r i)) ∧ (∀ i, Smooth (q i)) ∧ (∀ i, IsAffine (U i)) ∧
      (∀ i, IsAffine (V i)) ∧ (∀ i, GeometricallyConnected (q i)) ∧
      (∀ i, ∃ s : V i ⟶ U i, s ≫ q i = 𝟙 (V i)) ∧ (∀ i, q i ≫ r i = p i ≫ f) := by
  obtain ⟨ι, U, p, V, q, r, hp, hcov, hr, -, -, hq, hgc, hs, hfac⟩ :=
    AlgebraicGeometry.exists_etaleCover_factorization f
  have hsm (i : ι) : Smooth (q i) := by
    have := hr i
    have : Smooth (q i ≫ r i) := by rw [hfac i]; infer_instance
    exact Smooth.of_comp_of_etale (q i) (r i)
  refine ⟨Σ i, (V i).affineOpens, fun j ↦ q j.1 ⁻¹ᵁ j.2.1, fun j ↦ (q j.1 ⁻¹ᵁ j.2.1).ι ≫ p j.1,
    fun j ↦ j.2.1, fun j ↦ q j.1 ∣_ j.2.1, fun j ↦ j.2.1.ι ≫ r j.1, fun j ↦ ?_, fun x ↦ ?_,
    fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_, fun j ↦ j.2.2, fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_⟩
  · have := hp j.1
    infer_instance
  · obtain ⟨i, y, rfl⟩ := hcov x
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ := (V i).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ ((q i).base y)) isOpen_univ
    exact ⟨⟨i, ⟨W, hW⟩⟩, ⟨y, hyW⟩, rfl⟩
  · have := hr j.1
    infer_instance
  · have := hsm j.1
    infer_instance
  · have := hq j.1
    exact j.2.2.preimage (q j.1)
  · have := hgc j.1
    infer_instance
  · obtain ⟨s, hs⟩ := hs j.1
    have hle : j.2.1 ≤ s ⁻¹ᵁ q j.1 ⁻¹ᵁ j.2.1 := fun v hv ↦ by
      simpa [← Scheme.Hom.comp_apply, hs] using hv
    refine ⟨s.resLE _ _ hle, ?_⟩
    rw [← cancel_mono j.2.1.ι, Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc,
      hs, Category.comp_id, Category.id_comp]
  · rw [morphismRestrict_ι_assoc, hfac, Category.assoc]

end AlgebraicGeometry
