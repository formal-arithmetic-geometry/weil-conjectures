## Worker report

The module `Sheaf.AlgebraicGeometry.AffinePrincipalRelativePseudoCoherenceLocalization`
states `AlgebraicGeometry.affine_principal_relative_pseudoCoherence_localization`.
Its only theorem has proof `sorry`; there are no new definitions or auxiliary theorems.
The node is unchanged except for its `lean` record.

Source read: `literature/stacks-project/more-morphisms.tex`, Tag 09VD,
`lemma-localize-relative-pseudo-coherent`, statement and both inverse-adjoining
paragraphs of the proof (lines 16737–16786). The node is explicitly its
principal-source-open case. The eight proof steps of the node are transcribed into
the theorem docstring, including the two coefficient arguments and the arbitrary
module-sheaf open restriction comparison.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* An affine base scheme is `S : Scheme.{u}` with `[IsAffine S]`. This is the
  invariant form of `S = Spec R`: take `R = Γ(S, ⊤)` and the canonical `S.isoSpec`.
  Conversely every `Spec R` has this instance. No extra ring or chosen chart is
  mathematical data used by the statement. The element `a : Γ(S, ⊤)` is its
  global section; on a prescribed spectrum, `Scheme.ΓSpecIso` identifies this
  with the node's element of R. The open `V = D_S(a)` is `S.basicOpen a`, and its
  scheme is `(S.basicOpen a).toScheme`.
* The affine source is `X : Scheme.{u}` with `[IsAffine X]`. The morphism is
  `f : X ⟶ (S.basicOpen a).toScheme`. Its finite type condition is the recorded
  conjunction encoded by `[LocallyOfFiniteType f] [QuasiCompact f]`.
* `b : Γ(X, ⊤)` gives `U = X.basicOpen b`; `(X.basicOpen b).ι` is its inclusion.
* `E : schemeDerivedCategory X` and `m : ℤ` are arbitrary. There is no boundedness,
  quasi-coherence, perfectness, Noetherian, or nonzero assumption on E or the schemes.
* The hypothesis `h` is the whole existential: `∃ n : ℕ, ∃ i : X ⟶ ...` expresses
  the dimension and chart; `IsClosedImmersion i` is the closed immersion clause.
  Its equation with f after composing with the affine-space structure morphism
  expresses that the immersion is over V. The last conjunct is precisely
  `Scheme.IsMPseudoCoherent ... m ((schemeDerivedDirectImage i).obj E)`.
* The conclusion gives `∃ r : ℕ` and `j` from the actual principal open subscheme
  to `AffineSpace (ULift.{u} (Fin r)) S`, with `IsClosedImmersion j`. The equation
  `j ≫ (... ↘ S) = (X.basicOpen b).ι ≫ f ≫ (S.basicOpen a).ι` states that j is
  over S with the specified composite structure map, rather than any map to S.
* The final conjunct uses the same m and the exact object
  `(schemeDerivedDirectImage j).obj ((derivedPullback (X.basicOpen b).ι).obj E)`.
  Thus `E|_U` is the recorded derived pullback, and the conclusion concerns Rj_*.
* `ULift.{u} (Fin n)` (and r) has precisely n (respectively r) coordinates in
  the universe required by Mathlib's `AffineSpace`. Dimensions zero are included.
* The single explicit family of `HasDerivedCategory.{w}` instances for schemes
  supplies D(O) for X, U, every affine space quantified over, and their open
  subschemes needed by `IsMPseudoCoherent`. It is the standard derived-category
  size/localization infrastructure, not a geometric restriction; u and w are
  explicitly declared, and `autoImplicit` is disabled.

Recorded statement dependencies read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, and `Scheme.basicOpen`; the spectrum declaration and
  its contravariant map have the signatures recorded by def-weil-affine-spectrum.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, together with
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`'s `AlgebraicGeometry.QuasiCompact`.
  The finite-type module publicly imports the latter.
* `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
* `Mathlib.AlgebraicGeometry.AffineSpace`: `AlgebraicGeometry.AffineSpace` and its
  canonical structure morphism, with finite index type `ULift (Fin n)`.
* `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory`, on the shared `SheafOfModules`
  carrier with its explicit derived-category instance.
* `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `AlgebraicGeometry.schemeDerivedDirectImage`, the unbounded derived direct image.
* `WeilConjectures.AlgebraicGeometry.DerivedPullback`:
  `AlgebraicGeometry.derivedPullback`, the canonical transported derived tensor pullback.
* `Sheaf.AlgebraicGeometry.MPseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsMPseudoCoherent`, with its pointwise open covering,
  strictly perfect approximations, homology isomorphisms above m, and epi in degree m.

All recorded proof dependency modules are imported as plain imports unless already
needed publicly by the statement. These include the polynomial localization quotient,
affine quotient sheafification, tilde sections, absolute pseudo-coherence, exactness of
closed-subset pushforward, principal localization open immersion, and module restriction.
`lem-sfb-closed-pushforward-pseudocoherence` currently has no recorded Lean declaration
or Mathlib match, so it contributes no import yet; its use remains in the proof docstring.
It is solely a proof dependency and no missing notion in the signature is supplied by it.

Edge cases checked before writing:

* a = 0, or a nilpotent, makes V empty and forces X empty; the node allows this.
* b = 0, or nilpotent, makes U empty, which admits a closed immersion in affine
  space and has zero restricted derived object. No nonemptiness condition was added.
* a or b a unit gives the whole corresponding scheme, also allowed.
* Zero rings and the empty affine scheme are included by `IsAffine`, without any
  nontriviality hypothesis. The coefficient argument for cT-1 works over zero
  rings and with zero divisors, so none was introduced.
* n = 0 and r = 0 are included by ℕ and Fin; the proof may choose r = n+2 but
  the statement only requires the node's existential dimension.
* Negative, zero, and positive m are all included by ℤ; the same m occurs at both ends.
* E is an arbitrary unbounded derived module object throughout.

Searches actually run for duplicate declarations:

* `msearch.py`, leanfinder, query
  "A complex with m pseudo coherent pushforward to affine space retains this property
  after principal source localization and enlarging a principal open affine base":
  eight hits, on ordinary affine-local morphism properties and small affine
  Zariski localization; none states this derived pseudo-coherence assertion.
* `msearch.py`, loogle, query `"IsMPseudoCoherent"`: zero hits.
* `msearch.py`, grep, query `pseudo.?coher|IsMPseudoCoherent`: zero Mathlib hits.
* `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for principal/pseudo-coherence
  combinations and `IsMPseudoCoherent` found the ring-level notions, the existing
  scheme definition, and `Scheme.IsMPseudoCoherentRelativeTo`, which is the general
  relative definition rather than this localization theorem. None is this statement.
* Literal node-id search in `lean/WeilConjectures` returned no match. Searching the
  chosen full declaration name and principal/relative variants in both source trees
  and `dag/lean_names_upstream.json` returned no match.

No statement fault or disputed assertion was found. No new nodes, dependency repairs,
or statement correction were needed. The source's fixed-m proof matches the node.

Validation: `scompile.py Q83 lem-sfb-affine-principal-relative-pseudocoherence-localization`
compiled the file as both a sandbox module (28.0 s) and its library module (3.1 s),
with no errors or warnings. The expected theorem proof remains `sorry` for stage 3.

## Second reading by Q83

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
