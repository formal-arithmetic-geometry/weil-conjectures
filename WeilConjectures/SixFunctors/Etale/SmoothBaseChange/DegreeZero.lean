/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs

/-!
# Degree-zero flat base change

The base-change map is an isomorphism in degree zero for a morphism `p : X ⟶ S` which is
flat, locally of finite presentation and has geometrically reduced fibres, with *no* torsion
hypothesis on the coefficient sheaf. Smooth morphisms satisfy these hypotheses, so this is
the starting point of the induction proving smooth base change.

The proof is étale-local on `X`: by `AlgebraicGeometry.exists_etaleCover_factorization` one
may assume `p` factors as `U ⟶ V ⟶ S` with `V ⟶ S` étale and `U ⟶ V` quasi-compact flat
with geometrically connected fibres, and then both sides evaluate to `F(V ×_S T)` because for
such a morphism the global sections of an inverse image agree with the global sections
downstairs [Stacks 0A3H].

## Main statements

- `AlgebraicGeometry.Etale.baseChangeProperty_zero`: degree-zero base change for a flat,
  locally finitely presented morphism with geometrically reduced fibres.
- `AlgebraicGeometry.Etale.baseChangeProperty_zero_of_smooth`: the smooth case, a corollary
  of the previous statement and the instance
  `AlgebraicGeometry.Smooth.geometricallyReduced`.
- `AlgebraicGeometry.Etale.universalBaseChangeProperty_zero` and
  `AlgebraicGeometry.Etale.universalBaseChangeProperty_zero_of_smooth`: the same statements
  after every base change of `p`.

## References

- Stacks Project, Lemma 59.87.2, <https://stacks.math.columbia.edu/tag/0EYS>
- Stacks Project, Lemma 59.87.1, <https://stacks.math.columbia.edu/tag/0EZX>
- Stacks Project, More on Morphisms, Lemma 37.46.3, <https://stacks.math.columbia.edu/tag/0EY5>
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} (p : X ⟶ S)

/-- Blueprint `sk-prop-deg0`: Degree-zero flat base change.

For a Cartesian square

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

with `g` quasi-compact quasi-separated and `p` flat, locally of finite presentation and with
geometrically reduced fibres, the degree-zero base-change map `p⁻¹ g_* F ⟶ h_* e⁻¹ F` is an
isomorphism for *every* sheaf `F` of `Λ`-modules on `T_ét`: no torsion hypothesis is needed in
degree zero. -/
@[stacks 0EYS]
theorem Etale.baseChangeProperty_zero [Flat p] [LocallyOfFinitePresentation p]
    [GeometricallyReduced p] :
    Etale.BaseChangeProperty Λ p 0 :=
  sorry

/-- The smooth case of `AlgebraicGeometry.Etale.baseChangeProperty_zero`: a smooth morphism
is flat and locally of finite presentation and its geometric fibres are smooth varieties,
hence reduced, so `BC(p, Λ, 0)` holds for `p` smooth. This is the degree-zero start of the
induction in the smooth base change theorem. -/
theorem Etale.baseChangeProperty_zero_of_smooth [Smooth p] :
    Etale.BaseChangeProperty Λ p 0 :=
  Etale.baseChangeProperty_zero Λ p

/-- `AlgebraicGeometry.Etale.baseChangeProperty_zero` holds universally: flatness, local finite
presentation and geometric reducedness of the fibres are stable under base change. -/
theorem Etale.universalBaseChangeProperty_zero [Flat p] [LocallyOfFinitePresentation p]
    [GeometricallyReduced p] :
    Etale.UniversalBaseChangeProperty Λ p 0 := by
  intro _ _ _ _ p' hp
  have : Flat p' := CategoryTheory.MorphismProperty.of_isPullback hp ‹_›
  have : LocallyOfFinitePresentation p' := CategoryTheory.MorphismProperty.of_isPullback hp ‹_›
  have : GeometricallyReduced p' := CategoryTheory.MorphismProperty.of_isPullback hp ‹_›
  intro _ _ g e h _ _ sq F
  exact Etale.baseChangeProperty_zero Λ p' g e h sq F

/-- The smooth case of `AlgebraicGeometry.Etale.universalBaseChangeProperty_zero`: the base case
of the induction on `q` in the smooth base change theorem. -/
theorem Etale.universalBaseChangeProperty_zero_of_smooth [Smooth p] :
    Etale.UniversalBaseChangeProperty Λ p 0 :=
  Etale.universalBaseChangeProperty_zero Λ p

end AlgebraicGeometry
