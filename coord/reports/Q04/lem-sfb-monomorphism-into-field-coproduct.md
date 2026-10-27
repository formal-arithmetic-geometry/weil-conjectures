## Worker report

The module `Sheaf.AlgebraicGeometry.MonomorphismIntoFieldCoproduct` states
`AlgebraicGeometry.monomorphism_into_field_coproduct`, with exactly one postponed theorem
and no new definitions. Source read: `literature/stacks-project/schemes.tex`, lines
4680–4705, Tag 03DP, `lemma-mono-towards-spec-field`. Its final assertion explicitly
allows an arbitrary disjoint union, rather than the spectrum of an infinite product.
The node statement and all existing dependency records are unchanged.

Hypothesis and conclusion correspondence:

- The set I is `(I : Type u)`; its family of fields is `(k : I → Type u)` with
  `[∀ i : I, Field (k i)]`. Mathlib's `Field` supplies nontriviality and inverses.
- The specified scheme D is literally `∐ (fun i : I ↦ Spec (CommRingCat.of (k i)))`.
  These are the original fields, with no extensions or replacement fields.
- An arbitrary source scheme and morphism are `(T : Scheme.{u})` and the binder
  `m : T ⟶ ∐ (fun i : I ↦ Spec (CommRingCat.of (k i)))`.
- `[Mono m]` is precisely injectivity of postcomposition on every scheme-valued Hom set:
  `Mono.right_cancellation` quantifies over every test scheme and every pair of arrows.
- A subset of I is the witness `J : Set I`; its associated index type is the subtype J.
- The isomorphism is `e : T ≅ ∐ (fun j : J ↦ Spec (CommRingCat.of (k j.val)))`.
- The map from this selected coproduct to D is exactly
  `Sigma.desc (fun j : J ↦ Sigma.ι (fun i : I ↦ Spec (CommRingCat.of (k i))) j.val)`.
  Its restriction to the j-th component is the original coprojection at j.val.
- The equality `e.hom ≫ Sigma.desc (...) = m` makes the isomorphism an isomorphism over
  D and identifies m with that component inclusion. This also implies the inverse
  compatibility, so no extra condition is omitted.
- There is no finite, nonempty, compactness, reducedness, or dimension assumption.
  A common arbitrary universe u accommodates any set and family of fields after choosing
  a universe containing them; the coproduct is taken in Scheme.{u} as in the recorded
  coproduct dependency. No further universe equality is imposed on an existing interface.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs` (line 180).
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme` (lines 42 and 75).
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`, same module
  (lines 470 and 479). Only Spec is needed in the signature.
- `lem-weil-pbc-scheme-coproduct-family`: the recorded Mathlib coproduct instance,
  `AlgebraicGeometry.sigmaOpenCover`, and `AlgebraicGeometry.disjoint_opensRange_sigmaι`,
  `Mathlib.AlgebraicGeometry.Limits` (lines 187, 241 and 202). The existing coproduct
  construction, `Sigma.ι`, and `Sigma.desc` supply the signature's canonical objects/maps.
- `CategoryTheory.Mono`, `Mathlib.CategoryTheory.Category.Basic` (lines 325–330), supplies
  exactly the node's spelled-out monomorphism definition.

Proof dependencies are represented by plain imports of
`Mathlib.AlgebraicGeometry.AffineScheme`, `Mathlib.AlgebraicGeometry.OpenImmersion`,
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective`, and
`Sheaf.AlgebraicGeometry.ProEtaleFiniteLocalSystemsType`. The latter's recorded
`AlgebraicGeometry.Scheme.finiteLocalSystemsType_coproduct` was read at lines 135–142;
its arbitrary clopen decomposition interface matches the proof. The coproduct and Spec
proof inputs are already public statement imports. The proof-only node
`lem-sfb-field-ring-epimorphism-trivial-or-iso` currently has neither a Lean record nor a
Mathlib match, so it has no module to import yet. It is not needed to type the statement;
its ID and its use are retained in the complete theorem proof docstring.

Edge cases checked before writing: I empty forces D and T empty, and J empty gives the
empty coproduct. T empty for nonempty I is represented by J empty. A singleton I allows
only the empty source or that exact field spectrum. The identity of D is represented by
J = Set.univ. An infinite proper subset is allowed: no Finite or HasFiniteCoproducts
restriction occurs. Every characteristic is allowed. No node fault or statement dispute
was found, and no new node or dependency repair was necessary.

Searches actually run with the prescribed `msearch.py Q04
lem-sfb-monomorphism-into-field-coproduct` wrapper:

- LeanFinder: `A monomorphism of schemes into a disjoint union of spectra of fields is
  isomorphic over the target to the inclusion of a subset of components` — eight hits,
  including `isIso_of_comp_eq_sigmaSpec`, `instMonoCoprodScheme`, and `ι_sigmaSpec`.
  None states the node: the first needs an immersion, compactness and a factorization
  involving the spectrum of a product; the others concern coproduct maps themselves.
- Loogle: `"Mono", "Spec"` — twelve unrelated localization/monoid hits; no match.
- LeanSearch: `Every monomorphism of schemes into a coproduct of spectra of fields is
  isomorphic over the target to a subcoproduct` — eight hits, including `coprodSpec`,
  finite coproduct instances and `IsPreimmersion.instMonoScheme`; no classification of
  arbitrary monomorphisms into the stated target.
- Mathlib grep: `mono.*(spec|Spec)|monomorphism.*field|03DP` in `AlgebraicGeometry` —
  twenty-five hits concerning cancellation, spectra and unrelated maps; no exact match.
- Project rg in `lean/WeilConjectures` and `lean/Sheaf`:
  `mono.*(field|coproduct)|monomorphism.*(field|coproduct)|monomorphismIntoFieldCoproduct`,
  then the narrower `(mono|monomorphism).*(disjoint union|field spectra|spectrum of a
  field)|03DP|monomorphism_into_field_coproduct` in their AlgebraicGeometry directories.
  `FlatMonomorphismLocalStructure.lean` mentions this node as a future singleton-case
  proof dependency, but states a different flat quasi-compact result; no exact match.
- `grep -rn 'lem-sfb-monomorphism-into-field-coproduct' lean/WeilConjectures` returned
  no hit. A search of `dag/lean_names_upstream.json` for the proposed camel-case name
  also returned no hit. The final snake-case name was searched in both project trees.

Validation: the initial module compiled cleanly in both sandbox and library module modes
through scompile.py (1.6 seconds each). Final imports and delivery are checked again by
the prescribed compile and deliver2.py dry run below.

## Second reading by Q04

I reread the node and the final signature myself; no separate agent was started, as the
worker brief forbids that. The maintainer supplies the independent review. The field and
scheme binders render exactly the source's objects. Mono is categorical cancellation,
not pointwise injectivity. The selected index is a subset, and its summands are Spec of
the same k_i. The displayed equality has the correct direction for e : T ≅ subcoproduct:
first e.hom, then the canonical inclusion, equals m. Thus the isomorphism is over the
original D, without an arbitrary target automorphism. Empty I, empty J and infinite I
remain admitted. No mismatch or correction was found. Explicit public imports were added
for the statement dependencies, and plain imports for the already stated proof inputs.
