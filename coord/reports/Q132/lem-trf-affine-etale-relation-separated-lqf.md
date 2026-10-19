## Worker report

The module `Sheaf.AlgebraicGeometry.AffineEtaleRelationSeparatedQuasiFinite` states
`AlgebraicGeometry.affine_etale_relation_separated_locally_quasi_finite` with one
`sorry` and no new definitions. The DAG statement is unchanged. Its proof docstring
contains all five steps of the node, including the absolute affine product argument
that avoids imposing separatedness on the base.

Hypotheses and conclusions, checked against the base node:

- An arbitrary scheme S: `{S : Scheme.{u}}`, with the universe explicitly declared.
- The S-schemes R and U: `(R U : Over S)`. Their underlying schemes are `R.left`
  and `U.left`, their structure maps are `R.hom` and `U.hom`.
- U is an affine scheme, rather than merely affine over S: `[IsAffine U.left]`.
  Mathlib's `Scheme.isoSpec` identifies it with the spectrum of its global ring;
  `isAffine_Spec` and `IsAffine.of_isIso` give the converse characterization.
- The two S-morphisms: `(s t : R ⟶ U)`. The equations `s.w` and `t.w` say
  `s.left ≫ U.hom = R.hom` and `t.left ≫ U.hom = R.hom`.
- The morphism j=(s,t) into the actual scheme fibre product is
  `pullback.lift s.left t.left (s.w.trans t.w.symm)`. Its two composites with
  `pullback.fst U.hom U.hom` and `pullback.snd U.hom U.hom` are exactly s and t.
  `[Mono (pullback.lift ...)]` is the node's monomorphism hypothesis, in schemes.
- For every S-scheme T, R(T) is an equivalence relation on U(T):
  `hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ U ↦
  ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b)`.
  Every map here is over S, so these are exactly relative functor-of-points sets.
  Monicity of j identifies R(T) with this image relation; `Equivalence` supplies
  reflexivity, symmetry, and transitivity. This uses the existing core notion and
  the encoding already used by `etale_relation_quotient`, without defining a copy.
- The two étaleness assumptions: `[Etale s.left] [Etale t.left]`.
- Separatedness and local quasi-finiteness of s: the first conjunct
  `IsSeparated s.left ∧ Scheme.Hom.IsLocallyQuasiFinite s.left`.
- The corresponding two clauses for t: the second conjunct with `t.left`.
- The corresponding two clauses for j: the last conjunct uses the very same
  `pullback.lift` as the monomorphism hypothesis, for both properties.
- No separatedness hypothesis is made on S. No quasi-compactness hypothesis or
  finite-fibres conclusion is imposed on R. The pointwise predicate is precisely
  the recorded Stacks 01TD predicate, including its finite-type requirement.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-affine-spectrum`: that same module, `AlgebraicGeometry.Spec` and
  `Spec.map`; affineness uses `IsAffine` and `Scheme.isoSpec` from
  `Mathlib.AlgebraicGeometry.AffineScheme`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, its projections and `pullback.lift`;
  scheme pullback existence comes from `Mathlib.AlgebraicGeometry.Pullbacks`.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale` (the nondeprecated current recorded name).
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`
  and its import `Mathlib.AlgebraicGeometry.Morphisms.Separated`,
  `AlgebraicGeometry.IsSeparated`, closed immersion of the diagonal.
- `pqf-def-quasifinite`: `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`,
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite`, unfolding to
  `∀ x, IsQuasiFiniteAtPoint f x`. Its full affine finite-type definition was read.

The public imports expose all statement dependencies through these modules.
For the proof plan, the module imports
`Sheaf.AlgebraicGeometry.UnramifiedMorphism` (`AlgebraicGeometry.IsUnramified`)
and `Sheaf.AlgebraicGeometry.UnramifiedQuasiFinite`
(`AlgebraicGeometry.Scheme.Hom.isLocallyQuasiFinite_of_unramified`). The latter
already has a complete proof; it is only imported, not rewritten. Other proof
interfaces are supplied by the Mathlib imports: `pullbackSpecIso` with its projection
identities; `IsSeparated.hasAffineProperty` (and the affine-scheme separatedness
instance); `IsSeparated.of_comp`, `IsSeparated.isSeparated_of_mono`; open and closed
immersions; and `locallyOfFiniteType_of_comp`, the permanence lemma's clause (f).
Their source signatures and docstrings were inspected. The individual permanence
clauses' remaining modules were inspected, but the proof only needs clause (f).
No dependency interface required repair.

Edge cases checked before writing and again after elaboration: the empty affine
scheme (Spec of the zero ring) is allowed; when U is empty, R is necessarily empty
and all six properties hold. Empty R with nonempty U correctly fails reflexivity
on relative points, so it is not accidentally admitted as an equivalence relation.
The diagonal relation R=U, s=t=id is admitted. An arbitrary, possibly nonseparated
base remains admitted. No characteristic, noetherian, nonempty, compactness, or
finite-presentation assumption beyond étaleness was added. Local quasi-finiteness
remains pointwise, without silently strengthening it to quasi-finiteness. A single
explicit arbitrary universe u bounds the schemes and their relative test schemes,
as in the existing quotient interface; it introduces no equality of distinct
site/coefficient universes.

Searches for an existing statement (all via the prescribed wrappers or read-only rg):

- `msearch.py ... leansearch "An etale equivalence relation on an affine scheme has
  separated locally quasi finite projections and relation map"`: eight component
  hits, including `LocallyQuasiFinite.mk`, `Scheme.Etale`, `IsSeparated.of_isAffineHom`,
  `locallyQuasiFinite_iff`; no complete matching theorem.
- `msearch.py ... leanfinder` with the same query: eight hits, chiefly étale
  morphisms, formal unramifiedness, and composition; no complete matching theorem.
- `msearch.py ... loogle "AlgebraicGeometry.IsSeparated,
  AlgebraicGeometry.LocallyQuasiFinite"`: one normalization open-immersion instance,
  with extra finite-type and separatedness assumptions; not the node.
- `msearch.py ... grep
  "of_mono|of_comp|IsSeparated.*mono|LocallyQuasiFinite.*[Mm]ono"
  AlgebraicGeometry/Morphisms`: 25 hits, including separatedness of monomorphisms,
  cancellation, and local quasi-finiteness cancellation; none states all clauses.
- `rg` over Mathlib algebraic geometry, upstream `WeilConjectures/AlgebraicGeometry`,
  and side `lean/Sheaf/AlgebraicGeometry` for equivalence-relation terminology found
  `EtaleRelationQuotient.lean`; read it and reused its ordinary `Equivalence`
  hypothesis form. It concludes an algebraic-space quotient, not this theorem.
- `rg` over all side Lean, upstream Lean, and Mathlib algebraic geometry for
  `affine_etale_relation_separated|affineEtaleRelationSeparated|separated.*relation|
  relation.*separated` found no matching declaration.
- `rg` for the exact item id in upstream Lean and `dag/lean_names_upstream.json`
  found no recorded declaration. No repair note for this item was present.

Source checked directly in `literature/stacks-project/spaces.tex`,
`lemma-presentation-quasi-compact` (Tag 0265), opening two proof paragraphs and the
first representability step. These establish the same hypotheses and six clauses.
No node fault or STATEMENT-DISPUTED issue was found. No additional nodes or
modules are needed.

## Second reading by Q132

A separate second pass through the base JSON and completed Lean module was performed
in this same worker session; no other agents were started, as the dispatcher brief
requires. The maintainer supplies the independent delivery review.

The binders `{S}`, `(R U : Over S)`, `[IsAffine U.left]`, `(s t : R ⟶ U)`,
`[Mono (pullback.lift ...)]`, `hrel`, and the two `Etale` instances match, respectively,
the arbitrary base, both S-schemes, absolute affineness, both S-morphisms, the
canonical monic relation map, its equivalence-relation property on every test
scheme, and both étaleness assumptions. The first, second and third result pairs
supply exactly separatedness and Stacks local quasi-finiteness for s, t and j.
The equations supplied by Over morphisms make the lift canonical and typed without
introducing any extra compatibility hypothesis. In particular the map in both
conclusion predicates is identical to the monic map in the hypothesis. No stronger
conclusion about absolute separatedness of R or finite fibres is appended.
The unused-in-the-mathematical-proof equivalence-relation hypothesis is retained
because the node includes it. No mismatch was found and no correction was needed.

Validation: the prescribed `scompile.py Q132 lem-trf-affine-etale-relation-separated-lqf`
compiled this delivered file successfully, first as the sandbox module and then
under its final library module name, with no diagnostics. It also compiled the
required side-only unramified dependency in its private overlay. No global build
or direct compiler command was used. The node's `lean.statement` was extracted
verbatim from the theorem signature and its date uses UTC.
