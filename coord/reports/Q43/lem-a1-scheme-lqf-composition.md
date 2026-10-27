## Worker report

Item: `lem-a1-scheme-lqf-composition`. New module:
`Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteComposition`.
It states `AlgebraicGeometry.Scheme.Hom.isLocallyQuasiFinite_comp` with proof
`sorry`, and introduces no definitions or other theorems. The node changes only
in `lean`. No statement correction, missing dependency, or disputed statement.

The source was read in `literature/stacks-project/morphisms.tex`,
`lemma-composition-quasi-finite` (Stacks 01TL), lines 3894 onward. Its first
assertion is precisely the composition statement here; its additional assertion
about quasi-finite morphisms is not part of this DAG node.

Clause-by-clause correspondence:

- Arbitrary schemes X, Y, S: `{X Y S : Scheme.{u}}`, with explicit universe `u`.
  The universe is arbitrary, and no property classes are imposed on the schemes.
- Morphisms f : X → Y and h : Y → S: `(f : X ⟶ Y) (h : Y ⟶ S)`.
- Both morphisms locally quasi-finite in the scheme sense:
  `(hf : f.IsLocallyQuasiFinite) (hh : h.IsLocallyQuasiFinite)`.
- The composite h ∘ f has that same property:
  `(f ≫ h).IsLocallyQuasiFinite`; categorical composition is written in diagram order.
- The finite-type affine-neighbourhood condition is included by the existing
  `Scheme.Hom.IsLocallyQuasiFinite`, defined as pointwise `IsQuasiFiniteAtPoint`.
  The latter requires affine neighbourhoods U,V and an `Algebra.FiniteType`
  witness for the section map before applying `Algebra.IsQuasiFiniteAtPrime`.
  This is exactly the predicate recorded by `pqf-def-quasifinite`, not the
  weaker Mathlib class with the similar name.
- No quasi-compactness, separatedness, or Noetherian hypothesis is present.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom` (definitions and
  docstrings read at Scheme.lean:36–75). Imported publicly.
- `pqf-def-quasifinite`:
  `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`, declarations
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite` and
  `AlgebraicGeometry.Scheme.Hom.IsQuasiFiniteAtPoint`. The entire module,
  including all four recorded predicates and docstrings, was read. Imported publicly.
- Proof dependency `lem-a1-scheme-lqf-affine-criterion`:
  `Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteAffineCriterion`,
  `AlgebraicGeometry.Scheme.Hom.isLocallyQuasiFinite_affine_criterion`.
  Its complete signature and proof docstring were read; imported privately.
- Proof dependency `lem-trf-quasi-finite-composition`:
  `Sheaf.RingTheory.QuasiFiniteComposition`,
  `RingHom.finiteType_and_isQuasiFiniteAtPrime_comp`.
  Its complete signature and proof docstring were read; imported privately.
- Proof dependency `lem-weil-pbc-affine-opens-basis` has no Lean record but
  does have a usable `mathlib_match`: `AlgebraicGeometry.Scheme.isBasis_affineOpens`
  in `Mathlib.AlgebraicGeometry.AffineScheme`. Read its signature and basis
  neighbourhood interpretation; imported privately. No replacement record is needed.

The theorem docstring reproduces all four DAG proof steps: choose nested affine
neighbourhoods using the affine basis; apply the affine criterion to both maps;
compose their finite-type, every-prime quasi-finite section maps; evaluate at
the prime corresponding to x and use the pointwise definition. It explicitly
identifies the composite section map and covers empty X.

Edge cases checked before writing:

- Empty X: both the source predicate and conclusion are pointwise universal
  assertions with no points. No nonemptiness binder excludes this case.
- Empty Y or S: existence of the displayed morphisms forces the corresponding
  sources empty where necessary; the assertion remains well typed and vacuous.
- Either morphism an identity: composition gives the other locally quasi-finite map.
- Non-quasi-compact example: an infinite disjoint union of copies of Spec k mapping
  to Spec k is locally quasi-finite; the statement permits it and its identity
  composite. Nothing silently turns local quasi-finiteness into quasi-finiteness.
- The structural map A¹_k → Spec k fails the local quasi-finiteness hypothesis;
  dropping either map's hypothesis would fail on composing this map with an identity.
- No characteristic, reducedness, separation, or Noetherian condition enters the
  affine proof or the displayed signature.

Searches made (2026-10-24; wrapper logs are in `searches.jsonl`):

- `msearch.py ... leanfinder`, query "Composition of locally quasi-finite morphisms
  of schemes including locally of finite type is locally quasi-finite": eight hits,
  notably `AlgebraicGeometry.instLocallyQuasiFiniteCompScheme` and
  `AlgebraicGeometry.locallyOfFiniteType_comp`.
- `msearch.py ... loogle`, query `"LocallyQuasiFinite", "comp"`: seven hits,
  including the composition instance, stability instance, and cancellation results.
- `msearch.py ... grep`, query
  `LocallyQuasiFinite.*[Cc]omp|[Cc]omp.*LocallyQuasiFinite|LocallyOfFiniteType.*[Cc]omp`
  in `AlgebraicGeometry/Morphisms`: eight hits, including QuasiFinite.lean:82 and
  FiniteType.lean:68.
- `msearch.py ... leansearch`, query "Composition of locally quasi-finite scheme
  morphisms locally of finite type is locally quasi-finite": eight hits including
  the separate Mathlib composition results for local quasi-finiteness and finite type.
- Read Mathlib `AlgebraicGeometry/Morphisms/QuasiFinite.lean` definitions and
  composition instances, and `FiniteType.lean` composition. Mathlib explicitly
  omits finite type from `LocallyQuasiFinite`; its composition declaration alone
  therefore does not state the node. Converting would require the project theorem
  `Scheme.Hom.isLocallyQuasiFinite_iff`, whose declaration and docstring were also read.
- `rg -n 'isLocallyQuasiFinite.*[Cc]omp|[Cc]omp.*isLocallyQuasiFinite|IsLocallyQuasiFinite.*[Cc]omp'`
  in the project's `lean/WeilConjectures` and `lean/Sheaf`: comparisons and
  algebraic-stack composition appear, but no composition theorem for this predicate
  on arbitrary scheme morphisms.
- `grep -rn 'lem-a1-scheme-lqf-composition' lean/WeilConjectures`: no match.
- `rg` for `isLocallyQuasiFinite_comp|IsLocallyQuasiFiniteComposition` in
  `dag/lean_names_upstream.json`, `lean/WeilConjectures`, and `lean/Sheaf`: no match.

Validation: `scompile.py Q43 lem-a1-scheme-lqf-composition` compiled both its
sandbox form and library module form successfully (3.9 s and 2.4 s respectively),
with no errors or warnings. The only postponed proof is the named item theorem.

## Second reading by Q43

This is a separate self-check by the dispatched worker, not an independent agent
review: the dispatcher explicitly forbids starting other agents. Independent
review is supplied by the maintainer as specified in the brief.

Reopened the node and the generated module and compared the signature again.
The three schemes and the two maps have exactly the required domains and
codomains. Both hypotheses use the recorded Stacks predicate, including finite
type; the conclusion applies it to f followed by h. There are no extra property
instances, hidden nonemptiness assumptions, or altered definitions. The universe
and every variable are explicitly bound and `autoImplicit` is false. The proof
imports match all stated proof dependencies. The four-step docstring follows the
accepted split, and the only proof body is `sorry`. No mismatch found and no
change to the DAG statement or split was needed.
