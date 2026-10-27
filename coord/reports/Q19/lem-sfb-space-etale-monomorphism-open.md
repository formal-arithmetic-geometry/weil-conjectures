## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleMonomorphismOpen` states
`AlgebraicGeometry.AlgebraicSpace.etale_monomorphism_is_open_immersion` for the
Stacks Project spaces-morphisms.tex Tag 05W5 monomorphism specialization.  It has
no proof beyond the required `sorry`.

The Lean statement is:

```lean
theorem etale_monomorphism_is_open_immersion
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : IsChartwiseEtale f)
    (hmono : ∀ (T : Over S),
      Function.Injective (fun x : yoneda.obj T ⟶ X.obj.obj => x ≫ f.hom.hom)) :
    ∀ (T : Over S) (y : yoneda.obj T ⟶ Y.obj.obj),
      IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left)
        (Limits.pullback.snd f.hom.hom y) := by
  sorry
```

The first hypothesis `S` is the base scheme and `X`, `Y` are algebraic spaces over
it, rendered by `{S : Scheme.{u}}` and `{X Y : AlgebraicSpace S}`.  The morphism
`f : X ⟶ Y` is the node's map.  The étale-on-charts hypothesis is rendered by the
recorded declaration `AlgebraicGeometry.AlgebraicSpace.IsChartwiseEtale f`; this
expands to every representable étale scheme chart `a : yoneda.obj T ⟶ X.obj.obj`
remaining representable étale after composition with `f.hom.hom`.  The sheaf
monomorphism clause is rendered by
`∀ T, Function.Injective (fun x : yoneda.obj T ⟶ X.obj.obj => x ≫ f.hom.hom)`,
which is injectivity of `X(T) → Y(T)` for every `S`-scheme `T` (Yoneda form).

For the conclusion, `T : Over S` and `y : yoneda.obj T ⟶ Y.obj.obj` are an
arbitrary scheme test and map to `Y`.  The sheaf base change is the actual
`Limits.pullback f.hom.hom y`, with projection
`Limits.pullback.snd f.hom.hom y`.  The predicate
`IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left)` says that this projection
is represented on every scheme test by a scheme morphism `p` satisfying Mathlib's
`AlgebraicGeometry.IsOpenImmersion`; this is exactly the node's meaning that every
scheme base change of `f` is an open immersion.

The statement dependencies and declarations used are:

- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`, including
  `AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith` and the actual sheaf
  pullback framework.
- `def-weil-etale-morphism`: Mathlib `AlgebraicGeometry.Etale`, used by the
  chartwise étale predicate.
- `def-sfb-space-chartwise-etale-morphism`: the existing definition
  `AlgebraicGeometry.AlgebraicSpace.IsChartwiseEtale` in
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite` (line 47), used by `hf`.
  This definition node owns the plain chartwise predicate; the enlarged-site
  comparison theorem is not a statement dependency.
- `def-weil-open-immersion`: Mathlib `AlgebraicGeometry.IsOpenImmersion`, used in
  the representing predicate.

The proof-plan imports are the recorded modules for
`lem-trf-space-fibre-products-etale-covers`
(`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`),
`lem-trf-space-chartwise-etale-permanence`
(`Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence`),
`lem-a1-etale-space-locally-quasi-finite`
(`Sheaf.AlgebraicGeometry.EtaleSpaceLocallyQuasiFinite`),
`lem-a1-separated-locally-qf-space-representable`
(`Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable`), and
Mathlib's `AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono` from
`Mathlib.AlgebraicGeometry.Morphisms.FlatMono`.  The closed-immersion definition
is available from Mathlib's `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.

Edge cases checked against the statement and Tag 05W5 are the empty source, the
identity map, an ordinary open subspace, a two-sheet étale cover (excluded by the
injectivity hypothesis), nonreduced test schemes, and non-quasi-compact opens.
No quasi-compactness, Noetherian, or surjectivity hypothesis is present.  The
arbitrary scheme test `T` includes the empty scheme.

Searches made:

- `msearch.py ... leanfinder "etale monomorphism of algebraic spaces is open immersion"`:
  only scheme-level `IsOpenImmersion.of_flat_of_mono` and unrelated scheme
  declarations; no algebraic-space statement.
- `msearch.py ... loogle "AlgebraicSpace.IsRepresentableWith, IsChartwiseEtale, IsOpenImmersion"`:
  zero hits because the algebraic-space names are project declarations.
- `msearch.py ... grep "etale.*monomorphism.*open" AlgebraicGeometry`: zero hits.
- Repository `rg` searches for `etale_monomorphism`, `etale.*monomorphism`, and
  `monomorphism.*etale` found no existing declaration of this statement.  The
  existing scheme theorem is only the proof leaf, not a duplicate.

No new nodes, dependency modules, statement correction, or
`STATEMENT-DISPUTED` flag are needed.

## Returned delivery repair

Addressed H2 of the independent review of immutable head `f986efa53158`.
Compared the retained delivery with current main: only its `lean` attachment
differed before this repair, and the current main still had the same three
statement dependencies. Rebased the node copy on current main while retaining
that attachment, then added the existing definition owner
`def-sfb-space-chartwise-etale-morphism` to `stmt_deps`, as explicitly requested
by the maintainer. Read that owner's statement and Lean record: it owns exactly
`AlgebraicGeometry.AlgebraicSpace.IsChartwiseEtale` from line 47 of
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`.

The Lean module is byte-identical to the retained returned delivery, with SHA-256
`03b5e0e15ea75cb55fffb3cca5a71e240d681ae8efab4c5015c83ee872c7a4d0`.
No theorem node was added to the statement dependencies; in particular,
`lem-trf-space-enlarged-etale-ringed-site-model` is not cited. The mathematical
statement and its signature, imports, proof docstring, and `sorry` are unchanged.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
