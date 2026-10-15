/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import WeilConjectures.Compactification.CategoryBaseChange
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.BaseChange
import WeilConjectures.Compactification.Constructions
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.Compactification.Defs

/-!
# The compactification category and base change

Source: blueprint, sec-nagata-compactification/sk-prop-nagata-sketch-comp-category,
prop-nagata-compactification-category (blueprint: prop-nagata-compactification-category).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Compactification

/-- Source: blueprint sec-nagata-compactification/sk-prop-nagata-sketch-comp-category,
prop-nagata-compactification-category (blueprint: prop-nagata-compactification-category).

Proof plan (the eleven steps of the node). Refinements are proper by
lemma-nagata-proper-to-separated-target and compose by proper composition. Nagata's theorem
(thm-nagata-compactification) supplies an object. For two objects use the image of their graph
in the fibre product: the ambient product is proper, and the graph is a quasi-compact
immersion by separatedness and open-immersion base change. The immersion-compactification
lemmas make its image a compactification with dense open, and its two projections are
refinements. Iterate for a finite family, including the empty family by nonemptiness.
For parallel maps take the inverse image of the target's relative diagonal. This is closed;
it contains X, and its inverse image over X is X, so the induced map from X is the base
change of the original quasi-compact open immersion. This compactification equalizes the
maps. These properties give cofilteredness.
Base change preserves the open and proper maps and refinement equations, and the universal
property of fibre products gives preservation of identities, composites and equalities.
The image universal property (lemma-nagata-scheme-image-universal) gives the comparison
closed immersion from the image formed after base change to the pulled-back image, over
both projections. If the base change is flat, lemma-nagata-dense-flat-pullback preserves
density of the quasi-compact, quasi-separated open immersion; its zero kernel forces the
comparison closed immersion to be an isomorphism. The same argument preserves density for
any dense compactification under flat base change. Finally, density fails for arbitrary
base change: take X = D(t) in S = Spec K[t], ambient S, and base change t = 0 to Spec K.
Localization K[t] → K[t,t⁻¹] is injective on principal opens, whereas after this base change
the source is empty and the ambient scheme is Spec K, so the structural map K → 0 is not
injective. This supplies the existential counterexample, with a qcqs base and separated
finite-type source map. -/
theorem compactificationCategory_properties {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    Nonempty (Compactification f) ∧
    (∀ c : Compactification f, QuasiCompact c.i) ∧
    (∀ c d : Compactification f,
      (inf c d).Z = (graph c d).image ∧
      IsSchemeTheoreticallyDominant (inf c d).i ∧
      Nonempty ((inf c d) ⟶ c) ∧ Nonempty ((inf c d) ⟶ d)) ∧
    (∀ (I : Type v) [Finite I] (c : I → Compactification f),
      ∃ e : Compactification f, ∀ i : I, Nonempty (e ⟶ c i)) ∧
    (∀ (c d : Compactification f) (r s : c ⟶ d),
      ∃ (e : Compactification f) (h : e ⟶ c), h ≫ r = h ≫ s) ∧
    IsCofiltered (Compactification f) ∧
    (∀ (T : Scheme.{u}) (t : T ⟶ S),
      (∀ c : Compactification f, QuasiCompact (c.baseChange t).i) ∧
      (∀ (c d : Compactification f) (r : c ⟶ d),
        IsProper (r.baseChange t).hom) ∧
      (∀ (c d : Compactification f) (e : Compactification f)
          (r : e ⟶ c) (s : e ⟶ d),
        Nonempty ((baseChangeFunctor t).obj e ⟶ (baseChangeFunctor t).obj c) ∧
        Nonempty ((baseChangeFunctor t).obj e ⟶ (baseChangeFunctor t).obj d)) ∧
      (∀ (c d e : Compactification f) (r s : c ⟶ d) (h : e ⟶ c),
        h ≫ r = h ≫ s →
          (baseChangeFunctor t).map h ≫ (baseChangeFunctor t).map r =
            (baseChangeFunctor t).map h ≫ (baseChangeFunctor t).map s) ∧
      (∀ c d : Compactification f,
        IsClosedImmersion (infBaseChange c d t).hom ∧
        (infBaseChange c d t).comp ((infFst c d).baseChange t) =
          infFst (c.baseChange t) (d.baseChange t) ∧
        (infBaseChange c d t).comp ((infSnd c d).baseChange t) =
          infSnd (c.baseChange t) (d.baseChange t) ∧
        (Flat t → IsIso (infBaseChange c d t).hom)) ∧
      (Flat t → ∀ c : Compactification f,
        IsSchemeTheoreticallyDominant c.i →
          IsSchemeTheoreticallyDominant (c.baseChange t).i)) ∧
    (∃ (X₀ S₀ T₀ : Scheme.{u}) (f₀ : X₀ ⟶ S₀) (t₀ : T₀ ⟶ S₀)
        (c₀ : Compactification f₀),
      CompactSpace S₀ ∧ QuasiSeparatedSpace S₀ ∧ IsSeparated f₀ ∧
      LocallyOfFiniteType f₀ ∧ QuasiCompact f₀ ∧ QuasiCompact c₀.i ∧
      IsSchemeTheoreticallyDominant c₀.i ∧
      ¬ IsSchemeTheoreticallyDominant (c₀.baseChange t₀).i) := by
  sorry

end AlgebraicGeometry.Compactification
