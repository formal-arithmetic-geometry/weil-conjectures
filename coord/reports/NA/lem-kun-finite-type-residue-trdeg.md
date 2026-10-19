## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteTypeResidueTrdeg` states
`AlgebraicGeometry.finite_trdeg_residueField` with a single `sorry` proof. It introduces no
definitions, new nodes, dependency modules, or statement corrections.

Hypothesis and conclusion correspondence:

- “K is a field”: `{K : Type u} [Field K]`.
- “X is a scheme over K”: `{X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]`.
  Its structure morphism is `X ↘ Spec (CommRingCat.of K)`.
- “finite type over K”: both `[LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]`
  and `[QuasiCompact (X ↘ Spec (CommRingCat.of K))]`, precisely the dependency's
  conjunction. The quasi-compact hypothesis is retained even though the conclusion is
  also true for schemes merely locally of finite type.
- “x ∈ X”: `(x : X)`, without any closedness or genericity requirement.
- “the residue field κ(x)”: `X.residueField x`, literally the residue field of the stalk.
- “over K”: the algebra argument is explicitly
  `((X ↘ Spec (CommRingCat.of K)).residueFieldAlgebraMap x).toAlgebra`.
  The upstream definition in `WeilConjectures.ZetaSeries` composes the canonical map from K
  to the prime's residue field on Spec K, the inverse of `Spec.residueFieldIso`, and the
  structure morphism's `Scheme.Hom.residueFieldMap`. This is exactly the field extension
  through the structure morphism specified by `def-weil-residue-field`, with no additional
  arbitrary `Algebra K (X.residueField x)` hypothesis. Explicit `@Algebra.trdeg` supplies this
  argument without a statement-level `let`.
- “transcendence degree is finite”: `@Algebra.trdeg K (X.residueField x) _ _ ... <
  Cardinal.aleph0`. The underscores are the inferred commutative-ring instances of the two
  fields. The cardinal less than aleph zero condition means finite cardinality, including zero.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-scheme-over-base`: `Scheme.Over`, `Mathlib.AlgebraicGeometry.Over`.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`; `QuasiCompact`,
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-weil-residue-field`: `Scheme.residueField`, `Scheme.Hom.residueFieldMap`, and
  `Spec.residueFieldIso`, `Mathlib.AlgebraicGeometry.ResidueField`.
- `def-kun-transcendence-degree`: `Algebra.trdeg`,
  `Mathlib.RingTheory.AlgebraicIndependent.Basic` (Stacks 030G).
- The existing `Scheme.Hom.residueFieldAlgebraMap` in `WeilConjectures.ZetaSeries`
  packages the above residue-field extension; its full definition and docstring were read.

The proof dependencies are imported as a plan for stage 3: `Mathlib.FieldTheory.FinTrdeg`
(`exists_finset_isTranscendenceBasis`), `Mathlib.RingTheory.Localization.AtPrime.Basic`
(`Localization.AtPrime`), `Sheaf.Topology.PresheafModuleStalkFunctor`
(`PresheafOfModules.moduleStalkFunctor`); the affine-spectrum, residue-field, finite-type,
and transcendence-degree dependencies are already public imports. The declaration docstring
carries both proof steps, including the affine fraction-field identification and the finite
transcendence basis argument. No theorem is proved in this delivery.

Sources checked: algebra.tex, `lemma-dimension-prime-polynomial-ring` (Stacks 00P0), finite-type
domain and its fraction field; fields.tex/Mathlib finite-basis statement as recorded by
`lem-weil-pbc-finitely-generated-field-finite-transcendence-basis`. All statement dependency
records and their declaration source signatures/docstrings were opened. The CompactObject
example and its `lean` record supplied the module/record conventions.

Edge cases: the empty scheme has no x, so the universally quantified statement is vacuous.
A zero-dimensional/algebraic residue extension has transcendence degree zero, which satisfies
the conclusion. Nonclosed points are allowed (e.g. the generic point of affine n-space has
degree n, not necessarily an algebraic residue extension). Both positive and zero characteristic
are allowed. The scheme and base field use the same arbitrary universe u, as required by
Mathlib schemes and their morphisms; enlarging u accommodates any such pair. No nonemptiness,
separatedness, reducedness, integrality, perfection, or algebraic-closedness is assumed.
No statement dispute or node fault was found.

Searches on 2026-10-15:

- `msearch.py` LeanFinder, query “residue field of a finite type scheme over a field has finite
  transcendence degree”: 8 hits, including `RingHom.EssFiniteType.residueFieldMap`, the
  finite-type-algebra transcendence-degree lemma, and quasi-finite residue-field results.
  None is the exact scheme-level statement with the canonical structure-morphism algebra.
- `msearch.py` Loogle, `Algebra.trdeg, AlgebraicGeometry.Scheme.residueField`: 0 hits.
  An earlier query using the short name `Scheme.residueField` returned an unknown-identifier
  note, so it was repeated with the qualified name.
- `msearch.py` grep, `residueField.*[Ff]inTrdeg|trdeg.*residueField|residueField.*trdeg`:
  0 hits in Mathlib.
- `msearch.py` LeanSearch, query “The residue field at any point of a finite type scheme over
  a field has finite transcendence degree”: unavailable, Internal Server Error; no verdict.
- `rg` in project Lean sources and `lean/Sheaf` for `trdeg`, `residueField`, and finite
  transcendence-degree wording: no exact statement. It found the existing canonical
  `Scheme.Hom.residueFieldAlgebraMap`, which is reused instead of reconstructed.
- `grep -rn lem-kun-finite-type-residue-trdeg` in upstream `WeilConjectures`: no hits.
- `rg finite_trdeg_residueField` in Mathlib, upstream, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no name clash.

Validation: server-only `scompile.py` succeeds cleanly (nice 19, two threads, 60 seconds per
file); the final compile took 1.4 seconds. Every universe/variable is explicitly bound.

## Second reading by NA

I independently read the node statement, its Stacks source place, all statement dependencies, and the submitted module. The source (algebra.tex, Lemma `lemma-dimension-prime-polynomial-ring`, Tag 00P0) starts with a field `k`, a finite type `k`-algebra domain, and identifies the fraction-field transcendence degree as finite; applied to `A/𝔭` on an affine finite-type chart, this gives the residue-field claim in the node. The node's objects and clauses, matched to Lean, are:

- A field `K`: `{K : Type u} [Field K]`, with no characteristic or algebraic-closedness assumption.
- A scheme `X` over `K`: `{X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]`; its structure morphism is `X ↘ Spec (CommRingCat.of K)`.
- Finite type over `K`: `[LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]` and `[QuasiCompact (X ↘ Spec (CommRingCat.of K))]`, exactly Mathlib's conjunction for the dependency node's finite-type notion.
- A point `x ∈ X`: `(x : X)` is the explicit argument, with no closedness or genericity requirement.
- Its residue field `κ(x)`: `X.residueField x`, Mathlib's residue field of the stalk; the base-field map is the canonical `(...).residueFieldAlgebraMap x` supplied by the structure morphism and converted with `.toAlgebra`.
- Finiteness of the transcendence degree: `@Algebra.trdeg K (X.residueField x) _ _ (((X ↘ Spec (CommRingCat.of K)).residueFieldAlgebraMap x).toAlgebra) < Cardinal.aleph0`, which is precisely finite cardinality (including zero).

Every introduced object, hypothesis, and conclusion clause is present once and in the same order. No extra Noetherian, separated, reduced, integral, nonempty, characteristic, or universe restriction occurs. The same universe `u` is used for `K` and `X`, as required by the scheme-over-base structure and covering all such pairs; no independent test universe is introduced. The empty scheme is covered vacuously because it has no `x`; an empty transcendence basis gives degree zero; generic and nonclosed points are included; both characteristic zero and positive characteristic are included.

I checked the dependency declarations: `Scheme.Over`/`X ↘ ...`, `Scheme`, `LocallyOfFiniteType` and `QuasiCompact`, `Scheme.residueField`, `Algebra.trdeg`, and the upstream `Scheme.Hom.residueFieldAlgebraMap` all have the recorded meanings. Searches (LeanFinder, Loogle, LeanSearch, and grep over Mathlib, `WeilConjectures/`, and `lean/Sheaf`) found no existing exact scheme-level theorem or duplicate project declaration; only algebra-level finite-type residue-field ingredients and the canonical residue-field map were found. The canonical map is therefore reused rather than redefined. The submitted file compiled with the required server command and no errors.

No mismatch was found, so no statement, dependency, definition, or source field was changed. I added the `lean` record to the sandbox node copy with the signature verbatim from the module.
