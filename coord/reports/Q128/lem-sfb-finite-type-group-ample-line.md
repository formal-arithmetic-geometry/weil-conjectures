## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteTypeGroupAmpleLine` states
`AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_finiteType_group`.
Its only theorem has proof `by sorry`; there are no new definitions or helpers.
The node's statement, dependencies and proof plan are unchanged.

Clause-by-clause rendering:

| Node hypothesis or conclusion | Lean |
| --- | --- |
| k is an arbitrary field | `(k : Type u) [Field k]` |
| G is a scheme over k with group multiplication, identity and inverse satisfying the group diagrams | `(G : Over (Spec (.of k))) [GrpObj G]` |
| Its structure morphism is separated | `[IsSeparated G.hom]` |
| Separated means that its diagonal is a closed immersion | The field of Mathlib's `IsSeparated G.hom` is `IsClosedImmersion (Limits.pullback.diagonal G.hom)` |
| Its structure morphism is of finite type | `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, exactly the conjunction recorded in `def-weil-finite-type-morphism` |
| There exists an O_G-module M | `∃ (M : G.left.Modules)` |
| M is invertible | `(hM : M.IsInvertible)` in the existential telescope |
| M is ample in the absolute sense | `@IsAmple G.left M hM` |
| No properness, smoothness, connectedness or commutativity is required | There is no binder for any such condition; in particular no `IsCommMonObj G`, `Smooth G.hom`, or algebraically closed field assumption |

The invertibility witness is supplied explicitly to `IsAmple`, so the conclusion uses
one and the same M. Expanding the existing `IsAmple` gives quasi-compactness of G and,
for every point, a global section of a strictly positive tensor power with affine
nonvanishing locus containing the point. It is not a relative ampleness predicate.
There is no supplied line bundle to which the existential line must be related.

Dependency declarations read and used:

- `def-weil-field`: `Field`, in `Mathlib.Algebra.Field.Defs` (the node is a Mathlib leaf).
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, in
  `Mathlib.CategoryTheory.Monoidal.Grp`, specialized to `Over (Spec (.of k))`.
  Its inherited `MonObj` has unit, multiplication and the associativity/unit laws;
  `GrpObj` adds inverse and the two inverse identities. The specialization is documented
  in the imported `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`, in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and
  `AlgebraicGeometry.QuasiCompact`, in `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
  The latter module is publicly imported by the former.
- `def-sc-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsInvertible`, in
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: local isomorphism to the
  structure module, hence locally free of rank one and quasi-coherent.
- `def-weil-pbc-ample-invertible-module`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple`, in
  `WeilConjectures.AlgebraicGeometry.Ample`, with exactly the absolute definition above.
- Separatedness uses `AlgebraicGeometry.IsSeparated`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`, whose full definition was checked.

All recorded proof-dependency modules are imported without `public`, including the
Mathlib matches for algebraic closure, reduction, finite-type base change,
Jacobsonness, closed-point residue fields and Noetherianness; the characteristic-zero
Cartier module was resolved from its closed `lean_audit` declarations. The one
unstated proof dependency, `lem-sfb-normal-variety-affine-parameter-picard`, has neither
a module nor a Mathlib match, so no import can yet be written for it. Its use is retained
in step 2 of the docstring. It supplies no notion needed to state the present theorem.
The docstring includes each of the node's five proof steps and their named inputs.

Source check: read `literature/stacks-project/groupoids.tex`,
`lemma-algebraic-quasi-projective` (Tag 0BF7), including its reduction and disconnected
component arguments and its final construction of an ample line. Also read
`morphisms.tex`, `definition-quasi-projective` (01VW) and `lemma-ample-over-affine`
(01VK). These identify its quasi-projectivity conclusion with the present existence
statement. No correction or statement dispute was necessary.

Edge cases checked before writing:

- An empty scheme cannot be a group scheme over a field: its unit would give a
  morphism from the nonempty Spec(k). No extra nonemptiness assumption was added.
- The trivial group and zero-dimensional finite group schemes remain included.
- Nonreduced groups in positive characteristic (for example alpha_p), disconnected
  finite groups and noncommutative groups are included by the unrestricted binders.
- Both characteristic zero and positive characteristic, including imperfect fields,
  are covered. There is no smoothness, reducedness or algebraic closure assumption.
- Positive-dimensional nonproper groups, such as the additive group, remain included.
- Ampleness uses positive tensor exponents through the dependency definition;
  exponent zero is not silently substituted for them.
- The field and scheme live in the standard common ambient universe u, exactly as
  in the existing group-scheme interface. Arbitrary size examples can be placed in
  a common universe; there is no independent lower test-object universe making a
  hypothesis vacuous.

Searches for an existing statement (2026-10-24):

1. `msearch.py ... leanfinder "Every separated finite type group scheme over a field admits an ample invertible module"`:
   eight unrelated affine/separatedness results; no match.
2. `msearch.py ... leansearch "Every algebraic group scheme of finite type over a field has an ample line bundle"`:
   eight generic scheme, affine and finite morphism results; no match.
3. `msearch.py ... loogle '"IsAmple"'`: zero hits.
4. `msearch.py ... grep "group.*ample|ample.*group|quasiProjective.*[Gg]roup|[Gg]roup.*quasiProjective" AlgebraicGeometry`:
   zero Mathlib hits.
5. `rg -n -i "group.*ample|ample.*group|quasiprojective.*group|group.*quasiprojective|lem-sfb-finite-type-group-ample-line" lean/WeilConjectures lean/Sheaf`:
   found the upstream `GroupScheme.QuasiProjective` and the related project modules.
   Read its complete signatures and docstrings: the ample-section-family theorem
   assumes `IsAlgClosed k`; its arbitrary-field theorem
   `GrpObj.exists_isImmersion_projectiveSpace` concludes an immersion into projective
   space rather than existence of an `IsAmple` module. Neither is the exact statement
   here. `AlgebraicGroupAmpleDifference` concludes a tensor-dual decomposition for a
   supplied line, and is a consumer of this node. The normal-base local existence
   results require smoothness and connected fibres. No declaration is duplicated.
6. `rg` for `exists_isAmple_of_finiteType_group|FiniteTypeGroupAmpleLine` in Mathlib,
   `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`: no collisions.

## Second reading by Q128

A separate rereading of the node, source definitions and completed file matched all
binders and the existential conclusion against the table above. In particular,
`G.hom` is the structure morphism, `G.left.Modules` is the category of modules on G,
and `hM` is passed to the absolute `IsAmple` predicate. The finite-type condition is
both locally finite type and quasi-compact. Separatedness is explicitly retained as
the node requests. No algebraically closed-field restriction from the proof is in
the signature. No mismatches or definition changes were found. This is a worker
self-check; independent maintainer review remains part of the delivery protocol.

Validation: `scompile.py Q128 lem-sfb-finite-type-group-ample-line` compiled the
sandbox and final library module successfully, with no reported errors or warnings.
`deliver2.py Q128 lem-sfb-finite-type-group-ample-line --no-push` returned
`OK (dry run): commit 9baf13a0087 passes the preflight and compiles; nothing pushed`.
A JSON comparison confirms that `lean` is the only changed field of the item.
