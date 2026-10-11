## Worker report

Module: `Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne`; declaration:
`AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_dim_le_one`.
This states precisely the existence assertion of the node. Its only proof is `sorry`.
The declaration docstring records all six steps of the node's proof and their dependencies.
No definitions, extra nodes, dependency replacements, or statement corrections were needed.

Hypothesis and conclusion correspondence:

- Field k: `(k : Type u) [Field k]`, with no restriction on characteristic or algebraic closure.
- Scheme X: `(X : Scheme.{u})`, using the recorded scheme definition.
- Scheme over k: `[X.Over (Spec (CommRingCat.of k))]`; its structure morphism is
  `X ↘ Spec (CommRingCat.of k)`.
- Separated structure morphism: `[IsSeparated (X ↘ Spec (CommRingCat.of k))]`.
  This is the diagonal closed-immersion condition from the proper-morphism dependency;
  no properness or universal closedness is assumed.
- Finite type: `[LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]` and
  `[QuasiCompact (X ↘ Spec (CommRingCat.of k))]`, exactly the two conditions recorded by
  the finite-type dependency.
- Topological dimension at most one: `(hdim : topologicalKrullDim X ≤ 1)`;
  the coercion of X is its underlying topological space, with dimension in `WithBot ℕ∞`.
- Existence of an invertible O_X-module: `∃ L : X.Modules, ∃ hL : L.IsInvertible`.
  The local structure-sheaf trivializations are precisely local freeness of rank one;
  hence the module is quasi-coherent, as required by the dependency's equivalent definition.
- Ampleness of that same module: `@IsAmple X L hL`, supplying the existential witness
  of invertibility to the recorded absolute ampleness definition. This includes quasi-compactness
  and, at every point, an affine nonvanishing locus of a section of a positive tensor power.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Over`: `AlgebraicGeometry.Scheme.Over`, the structure morphism notation.
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `AlgebraicGeometry.IsSeparated`.
  The proper-morphism node records `IsProper`; its separatedness clause is exactly this
  Mathlib class, not a replacement notion.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`,
  available through the finite-type import.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, available through the ampleness import.
- `Sheaf.AlgebraicGeometry.Ample`: `AlgebraicGeometry.Scheme.Modules.IsAmple`.

Edge cases checked: the empty scheme has dimension bottom, which satisfies the inequality;
no `Nonempty` binder excludes it and ampleness's pointwise condition is vacuous there.
Dimension zero and dimension one both satisfy the same bound, while infinite dimension does not.
Nonreduced schemes and disconnected schemes are allowed. There are no hypotheses of integrality,
properness, smoothness, perfectness, or algebraic closure. The universe is arbitrary; scheme,
field, and spectrum use the same universe, as in Mathlib's category of schemes, without fixing
it to any particular level. No additional mathematical condition comes from this universe choice.

Searches (actual searches are logged in `searches.jsonl`):

- `msearch.py leansearch`: “A separated finite type scheme over a field of topological dimension
  at most one admits an ample invertible sheaf”. Service unavailable: Internal Server Error.
- `msearch.py leanfinder`: “A separated scheme of finite type over a field of dimension at most
  one has an ample line bundle”. Eight results, concerning quasi-affine separatedness,
  affine/integral schemes, and affine spaces; none states the existence assertion.
- `msearch.py loogle`: `AlgebraicGeometry.IsSeparated, topologicalKrullDim`: zero results.
- `msearch.py grep`: `IsAmple|ample invertible|ample sheaf`, Mathlib/AlgebraicGeometry:
  zero results.
- `rg` with the same ampleness patterns over `WeilConjectures` and `lean/Sheaf` found
  the recorded absolute definition and upstream relative ampleness, but no matching theorem.
  Upstream `AlgebraicGeometry.IsAmple` requires a very ample positive power and thus projectivity;
  its docstring explicitly excludes O on affine one-space, so it is not the dependency notion.
- `grep -rn lem-sc-dim-one-ample-invertible` in `WeilConjectures`: no result.
- `rg exists_isAmple_of_dim_le_one` in Mathlib, `WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no declaration-name collision.

Source inspected online because the local Stacks TeX was absent:
[Stacks 09NZ](https://stacks.math.columbia.edu/tag/09NZ) and
[Stacks 0A25](https://stacks.math.columbia.edu/tag/0A25).
The former states dimension one; the latter applies it with dimension at most one, as explicitly
recorded and justified by the node's stage-1 review. No new statement fault was found.

Validation: server single-file compile succeeded, exit code 0, no warnings (1.6 seconds).


## Second reading by H1

Independently opened the item node, its module, all seven statement-dependency nodes,
and the recorded declaration sources. Downloaded Stacks `varieties.tex` into the sandbox
scratchpad because the repository has no local Stacks TeX. Read lines 8163–8178 (09NZ)
and 9201–9215 (0A25), and the surrounding section context. The first proposition states
dimension one; 0A25 explicitly uses its ample-sheaf conclusion for dimension at most one.
Neither source adds perfectness, algebraic closure, reducedness, or properness. The node's
stage-1 extension to dimension zero is valid: a zero-dimensional Noetherian scheme is a
finite disjoint union of spectra of Artinian local rings, hence affine, with ample O.
Sources: https://stacks.math.columbia.edu/tag/09NZ and
https://stacks.math.columbia.edu/tag/0A25.

Object, hypothesis, and conclusion checklist (each verdict: exact):

- Field k: `(k : Type u) [Field k]`. Arbitrary field, all characteristics.
- Scheme X: `(X : Scheme.{u})`; Mathlib's `Scheme` extends a locally ringed space
  with affine neighbourhoods, matching `def-pc-scheme`.
- Spec(k)-structure: `[X.Over (Spec (CommRingCat.of k))]`. Opened `Scheme.Over`:
  it is `OverClass X S`, recording an actual structure morphism `X ↘ S`.
- Separated structure morphism: `[IsSeparated (X ↘ Spec (CommRingCat.of k))]`.
  Opened Mathlib's class: its diagonal is a closed immersion, exactly the separated
  clause in `def-weil-proper-morphism`; no other clause of properness is assumed.
- Finite-type structure morphism: the two binders `LocallyOfFiniteType` and
  `QuasiCompact` on that same morphism. Opened their definitions: finite-type maps
  on affine pairs and compact preimages of compact opens, respectively. These are
  the two recorded declarations of `def-weil-finite-type-morphism`, with the
  affine-cover equivalence recorded there; there is no additional finiteness premise.
- Dimension bound: `(hdim : topologicalKrullDim X ≤ 1)`. Opened the definition:
  `krullDim (IrreducibleCloseds X) : WithBot ℕ∞`, the chain dimension of the
  underlying space from `def-kun-topological-krull-dimension`.
- Invertible O_X-module exists: `∃ L : X.Modules, ∃ hL : L.IsInvertible`.
  Opened `X.Modules` (sheaves of modules over `X.ringCatSheaf`) and upstream
  `IsInvertible.exists_isoUnit`: local isomorphisms to the structure sheaf on
  open neighbourhoods, precisely locally free rank one. Such sheaves are
  quasi-coherent, so no quasi-coherence clause is lost.
- That same L is ample: `@IsAmple X L hL`. Opened the recorded
  `Sheaf.AlgebraicGeometry.Ample` declaration: `CompactSpace X` and, for each x,
  a positive tensor exponent, global section, and affine open whose points are
  exactly those where the germ is outside the maximal ideal times the stalk.
  Its existential open is the nonvanishing locus, not an arbitrary smaller open.
  This matches every clause of `def-weil-pbc-ample-invertible-module`.
  The existential order is L, its invertibility proof, and ampleness of L;
  the proof binder supplies a Prop-valued instance, not extra mathematical data.

Edge cases: empty X has bottom dimension and is compact; the pointwise
invertibility and ampleness conditions are vacuous, and the structure sheaf supplies
an object. On nonempty X the zero module is not locally rank one, so it cannot be a
spurious witness. Dimensions zero and one are both admitted; infinite dimension is
excluded by the stated bound. Positive tensor powers are required in ampleness;
`tensorPow 0` is the structure sheaf but cannot serve as its exponent witness.
There is no index set in this statement. Nonreduced and disconnected schemes are
included. The arbitrary universe u is bound explicitly; both Scheme and its Over
category use a common ambient universe, allowing any field and scheme to be placed
in a common larger universe, with no small-universe restriction. No free variable
or extra typeclass hypothesis was found.

Independent searches, using queries different from the first reader's:

- `msearch.py leanfinder`: “Every algebraic curve that is separated admits an ample
  line bundle, including zero dimensional schemes”: eight results, all separatedness,
  projective spectra, or affine-space facts; no matching existence theorem.
- `msearch.py loogle`: `topologicalKrullDim, AlgebraicGeometry.Scheme`: one result,
  `IsLocallyArtinian.of_topologicalKrullDim_le_zero`, not this statement.
- `msearch.py leansearch`: “Existence of an ample line bundle on a separated algebraic
  curve”: unavailable with Internal Server Error; no absence verdict inferred.
- `msearch.py grep`: `line bundle|quasi-projective|ample`: broad hits were unrelated
  occurrences of “example”, so followed with targeted `rg` searches rather than
  treating the capped output as an absence result.
- Targeted `rg` over Mathlib/AlgebraicGeometry, all WeilConjectures sources,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`, using
  `exists.*[Aa]mple|[Aa]mple.*dim|dim.*[Aa]mple` and `line bundle|quasi.projective`:
  no equivalent existence theorem. Upstream abelian-variety existence requires
  an abelian variety, and dimension-one degree results already assume ampleness.
  Opened upstream `AlgebraicGeometry.IsAmple` at Modules/Ample.lean:185:
  its positive power must come from a closed immersion into projective space;
  its own docstring excludes O on affine one-space. It cannot replace the
  project's absolute `Scheme.Modules.IsAmple`. No duplicate notion is introduced.

No new definition node or replacement dependency module is present or needed.
No statement correction is present or needed. No mismatch was found and no Lean or
node field changed. The sole theorem proof is `sorry`; there are no definitions or
hidden proof holes in this module. Header, namespace, imports, line lengths, both
source docstrings and the blueprint identifier are correct. All six proof steps
of the node, including the dependency names and the transfer of ampleness across
the lifted isomorphism, are present in the theorem docstring. The node's
`lean.statement` was checked byte-for-byte against the theorem signature.

Second-reader validation: `scompile.py` succeeded on the server in 1.7 seconds,
exit code 0, with no errors or warnings.

## Reviewer fix (R-dai1106)

The structure-morphism binders were rewritten to the project's family form (as the landed
consumer lem-sc-dim-one-quasi-projective, G1 3a25d3a0c): `{k : Type u} [Field k] {X : Scheme.{u}}
(f : X ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]` in place of
`[X.Over (Spec (CommRingCat.of k))]` with the classes on `X ↘ Spec (CommRingCat.of k)`; the
`Mathlib.AlgebraicGeometry.Over` import was dropped. Mathematically the same statement (a scheme
over k is a scheme with a morphism to Spec k), now directly applicable by the consumer.
Everything else unchanged; `IsAmple` was checked with `pp.fullNames` to elaborate to the landed
`AlgebraicGeometry.Scheme.Modules.IsAmple` (f0debf313), not upstream `AlgebraicGeometry.IsAmple`.
Fixed file compiled clean (SHEAF_GROUP=L, 1.7 s).
