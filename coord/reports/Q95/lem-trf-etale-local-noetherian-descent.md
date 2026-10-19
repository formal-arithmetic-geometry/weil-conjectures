## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleLocalNoetherianDescent` states
`AlgebraicGeometry.isLocallyNoetherian_of_etale_cover`. Its proof is `sorry`, as required
in stage 2. No definitions, additional nodes, dependency repairs, or statement corrections
are needed. The original node is changed only in `lean`.

Clause-by-clause correspondence:

- The scheme `T` is `{T : Scheme.{u}}`.
- An arbitrary index set is `{A : Type v}`, with no finiteness or nonemptiness hypothesis;
  the schemes of the covering family are `(Tₐ : A → Scheme.{u})`.
- The family of morphisms to `T` is `(t : ∀ a, Tₐ a ⟶ T)`.
- Every covering morphism is etale: `[∀ a, Etale (t a)]`.
- Joint surjectivity is exactly
  `(hcover : ∀ x : T, ∃ a : A, ∃ y : Tₐ a, t a y = x)`.
  This is the pointwise form of the union-of-ranges covering condition in Mathlib's
  `Scheme.ofArrows_mem_smallEtaleTopology_iff`; it requires no individual morphism to
  be surjective.
- Local Noetherianity of every member is `[∀ a, IsLocallyNoetherian (Tₐ a)]`.
- The sole conclusion is `IsLocallyNoetherian T`.

The three statement-dependency interfaces were read in their recorded Mathlib modules:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `AlgebraicGeometry.Scheme.smallEtaleTopology` and
  `AlgebraicGeometry.Scheme.ofArrows_mem_smallEtaleTopology_iff`; its object category
  `AlgebraicGeometry.Scheme.Etale` and morphism property `AlgebraicGeometry.Etale`
  are in `Mathlib.AlgebraicGeometry.Morphisms.Etale`. The explicit family presentation
  uses that same etale property and precisely the jointly-surjective covering clause;
  no replacement site or private predicate is introduced.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`, whose affine-open characterization agrees
  with the node by `AlgebraicGeometry.isLocallyNoetherian_of_affine_cover` and
  `AlgebraicGeometry.isLocallyNoetherian_iff_of_affine_openCover`.

All recorded proof-dependency modules are imported without `public` when they are not
already statement imports. These give `QuasiCompactCover.exists_hom` in
`Mathlib.AlgebraicGeometry.Cover.QuasiCompact`, covering base change in
`Mathlib.AlgebraicGeometry.Sites.MorphismProperty`, `Etale` in
`Mathlib.AlgebraicGeometry.Morphisms.Etale`, `flat_iff` in
`Mathlib.AlgebraicGeometry.Morphisms.Flat`, `isPullback_morphismRestrict` in
`Mathlib.AlgebraicGeometry.Restrict`, `Module.Flat.directSum` and
`Module.Flat.of_linearEquiv` in `Mathlib.RingTheory.Flat.Basic`,
`DirectSum.linearEquivFunOnFintype` in `Mathlib.Algebra.DirectSum.Module`,
`Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat` in
`Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`, and
`Module.FaithfullyFlat.of_comap_surjective` in
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`. The spectrum and affine-open
Noetherianity dependencies are supplied by the public Scheme and Noetherian imports.
The declaration docstring reproduces all three steps of the node's proof plan,
including the open-preimage identification added in its stage-1 review.

Sources checked directly: `descent.tex`, lemma-Noetherian-local-fppf (Tag 034C),
lines 4761–4781, states fppf locality of locally Noetherian schemes; `topologies.tex`,
lemma-zariski-etale-smooth-syntomic-fppf (Tag 021N), states that etale coverings
are fppf coverings. No extra standing assumption occurs in this source argument.

Edge cases checked: the empty target is locally Noetherian and can have an empty
cover; if the index type is empty the covering hypothesis forces the target to be
empty. Empty members of a nonempty covering do not matter. The singleton identity
cover gives exactly the assumed local Noetherianity. No affine, quasi-compact,
separated, connected, nonempty, or field assumption has been added. Index and scheme
universes are explicitly bound and independent, allowing arbitrary covering families.

Searches for an existing exact statement:

- `msearch.py leanfinder`, query “A scheme with a jointly surjective etale covering by
  locally Noetherian schemes is locally Noetherian”: eight hits, the locally
  Noetherian and Noetherian classes and their open-cover/locally-finite-type results;
  none is etale-cover descent.
- `msearch.py loogle`, query
  `AlgebraicGeometry.IsLocallyNoetherian, AlgebraicGeometry.Etale`: zero hits.
- `msearch.py grep`, query
  `(Noetherian.*[Ee]tale|[Ee]tale.*Noetherian|[Nn]oetherian.*[Dd]escent|[Nn]oetherian.*[Ff]ppf)`
  in `AlgebraicGeometry`: zero hits.
- Direct `rg` over upstream `WeilConjectures`, project `lean/Sheaf`, and the upstream
  name index for Noetherian/etale/descent combinations found unrelated results about
  constructible sheaves, Noetherian approximation, and permanence under locally
  finite type morphisms. A targeted search for
  `isLocallyNoetherian_of_etale_cover|etale_cover.*[Nn]oetherian|[Nn]oetherian.*etale_cover`
  across upstream, project, and Mathlib found no declaration. The literal node-id
  search in upstream also found no attachment.

No statement dispute or node fault was found. Compilation and delivery preflight
are run with the prescribed `scompile.py` and `deliver2.py` wrappers.

## Second reading by Q95

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
