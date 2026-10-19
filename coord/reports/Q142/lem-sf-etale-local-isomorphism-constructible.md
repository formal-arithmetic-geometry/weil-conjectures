## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleLocalIsomorphismConstructible` states
`AlgebraicGeometry.Scheme.etaleLocalIsomorphismConstructible`, with its sole proof
`sorry`. It transfers the finite-constant-module trivializations on the supplied
stratification, retaining the original schemes and immersions. No new definitions,
new nodes, statement correction, or disputed statement are needed.

Hypothesis and conclusion correspondence:

- `X : Scheme.{u}` is the arbitrary scheme. `Λ : Type (u + 1)`, `[CommRing Λ]`
  and `[Finite Λ]` give exactly the finite commutative coefficient ring. The
  standard constructible-material universe convention is used, without imposing
  Noetherian, quasi-compact, separated or nonempty hypotheses.
- `F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)` are the module sheaves
  over the constant ring sheaf. This is the coefficient encoding prescribed by
  def-weil-pbc-etale-sheaves for constructibility and inverse image. Morphisms and
  isomorphisms in this category are module-linear, rather than set isomorphisms.
- `S : LocallyClosedStratification X` is the supplied finite partition: `S.n` is
  its number of strata, `S.stratum` its parts, `S.domain` its stratum schemes,
  and `S.immersion` its immersions. The structure includes local closedness,
  pairwise disjointness, covering, immersion properties and range equalities.
- `hSc` explicitly requires constructibility of each part. No closure-incidence
  condition or Noetherian shortcut is added.
- `hG` is precisely clause (b) of `IsConstructibleEtaleModuleSheaf G`, with its
  existential stratification opened and fixed to `S`. For every `k : Fin S.n`,
  inverse image is `(Etale.upperStar (ModuleCat Λ) (S.immersion k)).obj G`.
  `d : LocallyConstantDatum ...` supplies a jointly surjective etale covering
  with constant restrictions. For each covering member `b`, the existential
  `M : ModuleCat Λ`, `Finite M`, and the displayed `Nonempty (... ≅ ... )`
  require a finite constant module model. The restriction is `.over` on the
  localized small site, exactly as in the dependency definition. The constant
  sheaf is `constantSheaf` on that localized site. Requiring the datum's
  constancy proofs adds no assumption: the explicit isomorphisms already
  witness constancy.
- `J : Type v`, `U : J → Scheme.{u}`, and `uMap` specify the supplied family.
  Its indexing universe is independent of the scheme universe; there is no
  `Finite`, `Fintype`, smallness, nonemptiness, or finite-subcover assumption.
  `hEt` requires every arrow etale. `hcover` is literal joint surjectivity:
  each point of `X` belongs to the image of one of those arrows.
- `hiso` gives each inverse-image isomorphism in the module-sheaf category,
  using the recorded `Etale.upperStar`. No equation between these isomorphisms
  is assumed on intersections.
- The conclusion repeats the exact finite-constant-value clause with `F` in
  place of `G`, for every `k : Fin S.n`. It still uses `S.immersion k` and
  `S.domain k`; it does not merely produce another existential stratification.
  Together with the existing `S` and `hSc`, this is exactly a witness to
  `IsConstructibleEtaleModuleSheaf F`. It does not assert equality with `G`'s
  particular chosen trivializations or add gluing data.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `AlgebraicGeometry.Scheme.smallEtaleTopology` (the site).
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the sheaf categories and
  coefficient conventions in its module documentation; the set-sheaf predicates
  are not substituted for the required module-sheaf notions.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`:
  `CategoryTheory.constantSheaf` (sheafification of a constant presheaf).
- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`:
  `AlgebraicGeometry.Scheme.LocallyClosedStratification` (given partition).
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf` (its exact fixed-S
  defining witness is written in `hG` and the conclusion).
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.upperStar` (module inverse image).
- `WeilConjectures.ConstructibleSheaf.Defs`:
  `AlgebraicGeometry.Scheme.LocallyConstantDatum`,
  `Cover.etalePrecoverageToEtale`, and `upperStarConstantSheafIso`.

The proof docstring includes all four node proof steps, with their node citations:
restriction/inverse-image identification and module linearity, arbitrary-cover
base change and composition, the full chain of module isomorphisms, and return
to restriction on each unchanged stratum. The modules of the stated proof tools
are imported, including the module-linear composition core. The Mathlib cover
base-change/composition tools are already in the imported site API.

Sources checked: the module-sheaf clause of Stacks 03RU in
`literature/stacks-project/etale-cohomology.tex`, lines 9917–9957; the recorded
inverse-image and localization-restriction signatures; the full live source of
both constructible-module definitions, fetched with `scompile.py --source`.
The current source of EtaleSheaves was also fetched through that wrapper because
it is absent from the older local upstream checkout.

Edge cases checked before writing:

- Empty `X` and zero strata: the point-covering and stratum conclusions are
  vacuous. An empty covering index is allowed precisely when it covers `X`.
- Empty strata or empty chart schemes: empty charts create no unwanted nonempty
  hypothesis; the existing definition permits the empty trivializing cover.
- The zero module, zero sheaf, and zero coefficient ring remain included.
- A singleton identity cover gives invariance under a global module isomorphism.
- Infinite and disconnected covers, including indexing types in larger universes,
  are included explicitly. The refinement argument needs no finite subcover.
- Local twists over a field need not glue to a global isomorphism. The conclusion
  only asserts finite local constancy on the original strata, as required.
- On non-Noetherian schemes constructibility of the parts is retained by `hSc`;
  local closedness is not silently treated as sufficient.

Searches made with `msearch.py` for this item:

- LeanFinder: “A fixed constructible stratification transfers between sheaves of
  modules isomorphic on an arbitrary etale covering”. Eight hits, concerning
  generators and quasicoherent data of module sheaves; no matching theorem.
- Loogle: `"IsConstructibleEtaleModuleSheaf"`. No hits.
- Mathlib grep: `constructible.*(local|iso)|IsConstructibleEtaleModuleSheaf`.
  Ten reported hits concern constructible subsets and finite-presentation
  geometry, not fixed-stratification transfer of module sheaves.
- LeanSearch: “A constructible stratification for a sheaf of modules also works
  for another sheaf isomorphic to it on each member of a jointly surjective etale
  covering”. Eight hits, including `Sheaf.isConstant_congr` and generic sheaf
  constructors. Constant-sheaf invariance under one global isomorphism is not
  the supplied theorem with arbitrary local covers and fixed scheme strata.
- `rg` of upstream `WeilConjectures` and project `lean/Sheaf` for the item id,
  proposed declaration, and local-isomorphism/constructible patterns found no
  exact theorem. Upstream `ConstructibleSheaf/Pullback.lean` contains global
  isomorphism invariance and pullback preservation only. Its signatures and the
  definitions in `ConstructibleSheaf/Defs.lean` were read.
- `dag/lean_names_upstream.json` contains neither the proposed declaration nor
  this blueprint id. No private duplicate of a notion was introduced.

Validation: `scompile.py Q142 lem-sf-etale-local-isomorphism-constructible` compiled
this single module in sandbox and library modes with no diagnostics. Every
universe and binder is explicit. The only postponed proof is the item's theorem.

## Dependency modules

`def-weil-pbc-etale-constructible-sheaf`: lean-only existing-interface repair under
brief-stage2 §1(B). Its old note says to rebind to the published `Sheaf` definition
with `LocallyClosedStratification` and explicit constructible parts, but its module
field still points to the upstream version using `Scheme.Stratification`. Their
shared declaration name prevents importing both definitions. The repaired record
points to `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`, whose source
was read using `scompile.py --source` and whose exact fixed-stratum clause appears
in this theorem. No definition is copied or changed; no dependency node field
outside `lean` changes. The consumer compiles against this existing interface.

## Second reading by Q142

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
