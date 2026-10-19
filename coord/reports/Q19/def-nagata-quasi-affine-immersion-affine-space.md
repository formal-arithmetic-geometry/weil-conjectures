## Worker report

Record the existing upstream definitions; no Lean module is added. The current
blueprint main-20261015 definition asks to choose one witness of
`lemma-nagata-quasi-affine-immersion-affine-space-exists`, naming its dimension
and morphism. This is exactly the existing pair
`AlgebraicGeometry.Scheme.Hom.affineSpaceImmersionDim` and
`AlgebraicGeometry.Scheme.Hom.affineSpaceImmersion` in
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace`.

The older local slopmaster2 source does not contain these definitions, although
the node's upstream audit already names them. I read their actual current
published source, signatures, bodies and docstrings using
`scompile.py --source WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace`.
The declarations are in section `QuasiAffineImmersion`, with `universe u` and
`variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsQuasiAffine]
[LocallyOfFiniteType π]`. The recorded statement is verbatim from the morphism
definition; these section variables are its elaborated arguments.

Clause-by-clause correspondence:

- The schemes and morphism under the hypotheses of the existence lemma are
  `{X S : Scheme.{u}} (π : X ⟶ S)`.
- Quasi-affineness of X is `[X.IsQuasiAffine]`; local finite type of the given
  morphism is `[LocallyOfFiniteType π]`. There is no affine-base, separated-base,
  Noetherian, characteristic, nonempty, or positive-dimension restriction.
- The chosen dimension is the natural number `π.affineSpaceImmersionDim`,
  defined by `(exists_immersion_affineSpace_of_quasiAffine π).choose`.
- The chosen morphism is `π.affineSpaceImmersion`, of type
  `X ⟶ 𝔸(ULift.{u} (Fin π.affineSpaceImmersionDim); S)`, defined by
  `(exists_immersion_affineSpace_of_quasiAffine π).choose_spec.choose`.
  Both projections therefore come from the same existential witness.
- The witness is an immersion over S, as required by the cited existence
  statement: the existing theorem `π.affineSpaceImmersion_spec` states both
  the equality of the composite with the projection to S and
  `IsImmersion π.affineSpaceImmersion`. This specification theorem is inspected
  as evidence; this definition node records only its two definitions.

Dependency declarations read in full:

- `lemma-nagata-quasi-affine-immersion-affine-space-exists` records
  `AlgebraicGeometry.exists_immersion_affineSpace_of_quasiAffine` in the same
  upstream module. Its conclusion is
  `∃ (n : ℕ) (i : X ⟶ 𝔸(ULift.{u} (Fin n); S)),
  i ≫ 𝔸(ULift.{u} (Fin n); S) ↘ S = π ∧ IsImmersion i`.
  The existing definitions call this very declaration. The source contains its
  proof, not a sorry; the arbitrary witness selection is therefore not a
  choice from a postponed existence theorem.
- `def-nagata-relative-affine-space` records `AlgebraicGeometry.AffineSpace`
  in `Mathlib.AlgebraicGeometry.AffineSpace`, publicly imported upstream.
  Its definition is the pullback of S and the spectrum of the integer
  polynomial ring over the terminal scheme. This matches the current
  blueprint's index-set definition. `ULift.{u} (Fin n)` supplies exactly n
  coordinates in universe u.

Edge cases checked: n = 0 is permitted by Fin and ULift, with no positivity
binder; the empty scheme is not excluded; S is arbitrary, including a
nonaffine base; no characteristic is assumed. The single explicit universe u
is the dependency's scheme universe, and lifting Fin only changes the size
of the coordinate index, not its elements. The arbitrary choice is precisely
what this definition node requests, rather than a purported canonical choice.
There is no node correction, missing notion, dependency repair, or dispute.
The blueprint update changes punctuation only for this item and is respected.

Searches for an existing declaration:

- `msearch.py ... leanfinder "Choose the dimension and an immersion of a
  quasi-affine scheme of finite type over an affine base into relative affine
  space"`: eight Mathlib hits, including IsQuasiAffine and toSpecΓ immersions;
  no selected finite-dimensional relative affine-space witness.
- `msearch.py ... loogle
  "AlgebraicGeometry.Scheme.Hom.affineSpaceImmersion,
  AlgebraicGeometry.Scheme.Hom.affineSpaceImmersionDim"`: zero hits, unknown
  identifier in Mathlib's search index.
- `msearch.py ... grep
  "affineSpaceImmersion|exists_immersion_affineSpace|quasiAffine"
  AlgebraicGeometry`: ten Mathlib hits about quasi-affine schemes and limits;
  none gives the selected pair.
- `rg -n 'affineSpaceImmersion|quasi.affine.*[Ii]mmersion'` in the upstream
  WeilConjectures source and project lean/Sheaf: upstream existence lemma and
  related material; no selected pair in those older local source files.
- `grep -rn 'def-nagata-quasi-affine-immersion-affine-space'` in upstream
  WeilConjectures: no local hit.
- `rg -n 'affineSpaceImmersionDim|affineSpaceImmersion'` in
  dag/lean_names_upstream.json and lean/Sheaf: the upstream names table lists
  both definitions and their specification; no project duplicate.
- The current published source retrieved by `scompile.py --source` contains
  exactly these definitions and their specification. Reuse them with
  `existing: true`; do not restate them in the side library.

Validation: deliver2.py compiles a probe checking both fully qualified existing
declarations through scompile.py, then runs the server's stage-2 preflight.
No standalone delivered Lean file exists for an existing-declaration binding.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
