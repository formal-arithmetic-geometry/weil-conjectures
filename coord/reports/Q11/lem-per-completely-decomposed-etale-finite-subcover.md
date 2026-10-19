# Q11 stage 2: completely decomposed étale finite subcover

## Worker report

The module `Sheaf.AlgebraicGeometry.CompletelyDecomposedEtaleFiniteSubcover` states
`AlgebraicGeometry.completelyDecomposed_etale_finite_subcover`, with `sorry` as its
whole proof. No definitions or additional nodes are introduced. Only the item's
`lean` field changes. The previous reported PASS concerned its stage-1 split, not
a Lean statement: the current node had no `lean` record and the sandbox contained
no module or report. This delivery supplies that missing stage-2 statement.

I read the node's full statement and five proof steps, all four statement
dependencies and their recorded declarations/docstrings, and ILO Exposé II,
2.1.1 and 2.2.1--2.2.4, printed pp. 26--27 (PDF pp. 32--33). Corollary 2.2.4
at ell=infinity is exactly this finite completely decomposed subfamily assertion.
It does not require the individual source schemes to be quasi-compact or separated.
No statement correction or dispute is needed.

Clause-by-clause correspondence:

- The base scheme is `(X : Scheme.{u})`.
- The finite affine Noetherian-cover hypothesis is `[IsNoetherian X]`.
  Mathlib `AlgebraicGeometry.IsNoetherian` is locally Noetherian plus compact;
  `isNoetherian_iff_of_finite_affine_openCover` and
  `isNoetherian_iff_of_finite_iSup_eq_top` identify it with the node's finite
  affine-cover formulation. The section rings are `IsNoetherianRing`, meaning
  all ideals are finitely generated, exactly the recorded dependency.
- The set of indices is `{I : Type w}`, with `w` independent of the scheme
  universe. No finiteness or nonemptiness is imposed on it.
- The original source schemes and maps are `(U : I → Scheme.{u})` and
  `(f : ∀ i : I, U i ⟶ X)`.
- Every map is étale by `(het : ∀ i : I, Etale (f i))`.
- The pointwise covering condition is `hcover : ∀ x : X, ∃ (i : I) (z : U i),
  f i z = x ∧ IsIso ((f i).residueFieldMap z)`.
  The equality is the specified image condition. The `IsIso` condition is on
  the actual induced map, not an unspecified isomorphism of the two fields:
  `residueFieldMap` has domain `X.residueField (f i z)` and codomain
  `(U i).residueField z`. The image equality identifies its domain with κ(x).
  Thus no dependent cast or extra hypothesis is needed.
- The finite subset of the original index set is `∃ I₀ : Set I, I₀.Finite ∧ ...`.
- The rest of the conclusion repeats the exact lift condition for every `x`,
  using `∃ i ∈ I₀, ∃ z : U i, f i z = x ∧ IsIso ((f i).residueFieldMap z)`.
- There is no quasi-compactness, separation, or finiteness condition on `U i`.

Statement dependency declarations used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`; its ideal-finite-generation characterization is read
  at `isNoetherianRing_iff_ideal_fg`. The standard scheme packaging is
  `AlgebraicGeometry.IsNoetherian` in `Mathlib.AlgebraicGeometry.Noetherian`.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`. Its affine ring-map definition and
  `Etale.iff_flat_and_formallyUnramified` match the recorded dependency.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField` and
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap`.

The proof-only imports cover the recorded finite-presentation, finite-type,
closed/open-immersion, Noetherian-space, spectral-space and constructible-topology
nodes. `Mathlib.AlgebraicGeometry.Noetherian` supplies the locally-Noetherian,
minimal-closed-subset and quasi-separatedness ingredients; the topology imports
supply compactness of the constructible topology. The pointwise section lemma
`lem-per-rational-lift-locally-closed-section` currently has no `lean`,
`mathlib_match` or closed upstream declaration recorded, so it has no module to
import yet. It is a proof dependency only and is not needed to type this statement;
its later module import remains for the maintainer to add when it is stated.

Edge cases checked: empty `X` permits `I₀ = ∅`, even for empty `I`. If `X` is
nonempty and `I` empty, `hcover` cannot hold. An empty individual `U i` contributes
no lifts and can be discarded. A field target with a rational lift can select
one index; a field extension with no rational lift cannot satisfy `hcover` alone.
Disconnected, nonreduced and nonseparated schemes are not excluded. There are no
independent test-scheme universes or dimension/characteristic restrictions.

Searches for duplicates (actual `msearch.py` calls, recorded in searches.jsonl):

- LeanFinder: "Noetherian scheme completely decomposed etale covering finite
  subfamily with residue field isomorphisms" returned eight hits: ordinary
  étale pretopologies, open-cover finite subcovers, finite irreducible components,
  polynomial lifting and the Noetherian finite-affine-cover equivalences.
  None retains the pointwise residue-field-isomorphism condition for an
  arbitrary family while selecting finitely many original indices.
- Loogle: "AlgebraicGeometry.Etale,
  AlgebraicGeometry.Scheme.Hom.residueFieldMap" returned zero hits.
- Mathlib grep: "Nisnevich|completely.decomposed|rational.*subcover" returned
  only two documentation lines in `CategoryTheory/Sites/MayerVietorisSquare`.
- Source and side-library `rg` for completely decomposed/Nisnevich and finite
  subcovers found ordinary compactness uses and the existing finite-flat
  exchange consumer, not this theorem. Searches for
  `rational_lift|completelyDecomposed|completely_decomposed|finite.*decomposed`
  in upstream, `lean/Sheaf`, and `dag/lean_names_upstream.json` found no match
  to the theorem. The exact proposed declaration name is absent in Mathlib,
  upstream, the side library and the upstream name index. The requested item-id
  grep of upstream also found no match.

The prescribed `scompile.py` compiled both the sandbox and library-facing module
successfully (1.9 s and 2.0 s); no errors or warnings. All variables and universes
are explicit, with `autoImplicit false`. The only postponed proof is the named
item theorem, whose docstring carries all five natural-language proof steps.

Additional LeanSearch query: "A completely decomposed etale covering family of a
Noetherian scheme admits a finite completely decomposed subfamily" returned eight
hits: ordinary open-cover finite subcovers, locally Noetherian affine covers,
Noetherian finite-cover equivalences, ordinary étale topologies and the scheme
affine cover. None is the asserted completely decomposed finite selection.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
