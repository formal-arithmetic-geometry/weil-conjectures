## Worker report

The module defines and states `AlgebraicGeometry.exists_projective_galois_alteration_envelope`,
with proof `sorry`. It follows ILO Exposé X, Definition 3.3.1 and Theorem 3.4 proof Step 4.

The hypotheses are rendered as follows. `S` and `V` are schemes in the same universe; both are
integral, and `S` is Noetherian. Excellence is the explicit predicate
`∀ A : S.affineOpens, IsExcellent Γ(S, A)`. The alteration map is `r : V ⟶ S`, with Mathlib
classes `[IsProper r]` and `[Surjective r]`; generic finiteness is the explicit dense-open
existence `∃ U, Dense U ∧ IsFinite (r ∣_ U)`. The finite separable generic extension is
rendered by the pinned algebra map `algebraMap S.functionField V.functionField =
(r.functionFieldMap r.apply_genericPoint_of_isDominant).hom`, together with
`[FiniteDimensional ...]` and `[Algebra.IsSeparable ...]`.

The conclusion introduces `W`, its integral and Noetherian instances, `c : W ⟶ S`, its
surjectivity, and `t : W ⟶ V`. It requires `IsNormalScheme W`, excellence on all affine
opens, `IsProjectiveBundle c`, and `t ≫ r = c`. The generic-point binders and algebra map
pin the field `W.functionField` to the actual generic stalk map of `c`; the field extension is
finite dimensional and `IsGalois`, with fixed field `⊥` and finite automorphism group. The
map `i` is the actual generic map induced by `t`, and the monoid action `a` is over `S`; its
inverse-pullback generic action is the specified ring automorphism. Finally a dense open `U`
has finite, étale, surjective restriction, and the final `∀ Ω x y` clause states simple
transitivity on geometric fibres by existence and uniqueness of a field automorphism.

Dependency declarations used: `AlgebraicGeometry.Scheme` and `Scheme.Hom` (Mathlib),
`AlgebraicGeometry.IsIntegral` (Mathlib), `IsExcellent` from
`Sheaf.RingTheory.ExcellentRing`, `IsNoetherianRing`/`AlgebraicGeometry.IsNoetherian`
(Mathlib), `AlgebraicGeometry.IsProper`, `LocallyOfFiniteType`, `IsFinite`, `Etale`,
`CategoryTheory.Limits.pullback` (Mathlib), `Scheme.functionField` and
`Scheme.Hom.functionFieldMap` (WeilConjectures), `AlgebraicGeometry.IsProjectiveBundle`
from `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`, and `IsNormalScheme` from
`Sheaf.AlgebraicGeometry.NormalScheme`.

Edge cases checked: arbitrary index-free finite Galois extensions, empty geometric fibres
(the implication has no witnesses), the generic open required to be dense, and the identity
case for the action. No characteristic or prime-to-ell restriction is introduced.

Searches made: `msearch.py ... leanfinder` for a proper generically separable alteration
with normal projective Galois domination (returned normalization and properness declarations,
no match); `msearch.py ... leansearch` for a normal projective Galois alteration (returned
`IsGalois` and normalization declarations, no match); `msearch.py ... loogle` for
`IsGalois, AlgebraicGeometry.Scheme.functionField` (0 hits); `msearch.py ... grep` for
`galois.*alteration|alteration.*galois` (0 hits); `rg` over Mathlib, WeilConjectures and
`lean/Sheaf` found no existing theorem with this statement. Existing notions were imported
rather than redefined.

No `STATEMENT-DISPUTED` or node fault found.

## Second reading by Q11

I reread the node, its ILO source pages 158 and 160--161, every dependency record, and the
module. Each input hypothesis and each output clause listed in the node is represented in the
signature. The projective requirement uses the recorded projective-bundle predicate, the
normality clause uses the recorded stalk predicate, and the generic field action is tied to
actual function-field maps. No additional prime-to-ell condition, special characteristic, or
unmentioned geometric hypothesis was added.
