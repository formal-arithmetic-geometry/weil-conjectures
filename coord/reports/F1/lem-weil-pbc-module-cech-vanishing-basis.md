## Worker report

The module `Sheaf.AlgebraicGeometry.ModuleCechVanishingBasis` states
`AlgebraicGeometry.Scheme.Modules.isZero_moduleCohomology_restrict_of_cech_basis`.
Its only theorem has proof `sorry`; there are no new definitions or proofs.
The node statement is unchanged. There are no new nodes or dependency modules.

Source checked: Stacks Project, Tag 01EW, Lemma 20.11.9,
https://stacks.math.columbia.edu/tag/01EW, including both paragraphs of its proof.
The local literature file named in the node is absent on this machine, so the
published source was opened instead. Its three conditions and conclusion agree
with the node. Tag 01E1 supplies the stated restriction interpretation.

Clause-by-clause correspondence:

- Scheme X: `(X : Scheme.{u})`.
- Sheaf of O_X-modules F: `(F : X.Modules)`, the recorded Mathlib
  `AlgebraicGeometry.Scheme.Modules`, not an abelian sheaf substituted for a module.
- Basis B: `(B : Set X.Opens)` and `hB : IsTopologicalBasis
  ((fun W : X.Opens => (W : Set X)) '' B)`. This is exactly a set of open
  subsets which is a basis for the underlying topology.
- Set Cov of open coverings: `K` indexes its members; `U c` is the covered open,
  `J c` its index set, `V c j` its members, `hom c j` their inclusion arrows,
  and `hcover c : iSup (V c) = U c` is their union being the target.
  A collection may be indexed rather than stored as a set: repetition does not
  affect membership conditions or cofinality. Every set of coverings has such
  an indexing. The arrows are data specifying the inclusions, not an extra
  geometric condition; morphisms in the opens category are precisely inclusions.
- The Zariski site is the recorded opens category with
  `TopologicalSpace.Opens.grothendieckTopology`; `hcover` says this family covers.
  No separate topology or alternative site is introduced.
- The chosen iterated fibre products are `S c : SiteCechComplex (V c) (hom c)`.
  This is the dependency's recorded definition. On the opens category, its
  universal property identifies each `S.W p t` with `⨅ k, V c (t k)`.
  This is arbitrary chosen product data, as in the dependency node, not an
  additional restriction on the covering; every open family admits it. Its
  comparison theorem ensures independence of these choices.
- Condition (1): `hbase` says separately `U c ∈ B`, `∀ j, V c j ∈ B`, and
  `∀ p t, (⨅ k, V c (t k)) ∈ B`. The tuples have length p+1, including
  p=0. Thus precisely all nonempty finite tuple intersections are included.
- Condition (2): `hcofinal` quantifies over every `W ∈ B`, every open family
  `Z : A → X.Opens` with `iSup Z = W`, and supplies a member `c` with
  `U c = W` and `∀ j, ∃ a, V c j ≤ Z a`. This is exactly refinement, without
  imposing a chosen refinement function or surjectivity on that function.
- Condition (3): `hvanish` is `∀ c p, 0 < p →
  IsZero (((S c).cohomologyFunctor p).obj F.val.presheaf)`.
  The presheaf `F.val.presheaf` is the recorded underlying abelian-group
  presheaf. The dependency's cohomology functor takes homology of its product
  complex with the alternating sum of restrictions, exactly as in the node.
  `IsZero` is on an actual bundled abelian group, hence expresses vanishing.
- Conclusion: every positive natural degree p and every `W ∈ B` has
  `IsZero ((RingedSpace.moduleCohomology W.toScheme.toRingedSpace p).obj
  ((restrictFunctor W.ι).obj F))`. `W.toScheme` is the open subscheme;
  `restrictFunctor W.ι` is the recorded O_W-module restriction, and
  `moduleCohomology` is right derived global sections in O_W-modules.
  Thus this is H^p(W,F|_W)=0, not Ext cohomology of a bare abelian sheaf.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its
  scheme-morphism category (def-pc-scheme).
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`: `Scheme.Modules`,
  `Scheme.Modules.restrictFunctor` and its `restrictAppIso`/`restrictAdjunction`
  (def-weil-sheaf-of-modules-category and
  lem-weil-pbc-module-restriction-open-immersion-colimits).
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules`, its `val`,
  and the underlying `PresheafOfModules.presheaf`.
- `Mathlib.CategoryTheory.Sites.Spaces`:
  `TopologicalSpace.Opens.grothendieckTopology`; `Mathlib.Topology.Sheaves.Sheaf`:
  `TopCat.Sheaf` (def-sc-zariski-site, a Mathlib leaf with no lean record).
- `Sheaf.CategoryTheory.SiteCechComplex`: `CategoryTheory.SiteCechComplex`
  and `CategoryTheory.SiteCechComplex.cohomologyFunctor`
  (def-weil-pbc-site-cech-complex). Read its complete structure, construction,
  complex, homology functor, and choice comparison declarations.
- `Sheaf.Paper.PQFCohomology`: read
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages` and its full signature
  and docstring (pqf-def-cohomology). Its degree functors are exactly
  `AlgebraicGeometry.RingedSpace.moduleCohomology`, defined in
  `Sheaf.Topology.RingedSpaceModuleCohomology`, which the statement imports
  directly. The theorem packaging long exact sequences and higher direct
  images is not used in this signature, so its larger module is not imported.
  `moduleRings` is the shared ring-sheaf abbreviation, definitionally the same
  as `ringCatSheaf` on a scheme; no carrier conversion or copied definition.

Edge cases checked before writing:

- Empty scheme and empty basis: conclusion is vacuous; no nonempty hypothesis.
- A basis containing the empty open: cofinality includes its empty covering;
  a refining family must then be empty. Positive Čech and module cohomology
  both vanish. No bottom-open exclusion is imposed.
- Empty covering index sets are allowed. Tuples in positive-length powers of
  an empty type are absent, so the degree products are zero groups.
- Finite and infinite families and repeated indices are all allowed; there is
  no Fintype or finite-cover assumption and no pairwise-distinctness condition.
- Degrees start at p>0; no claim that H^0 vanishes. Intersections include p=0.
- Zero module is allowed. No quasi-coherence, quasi-compactness, separatedness,
  characteristic, or Noetherian condition is introduced.
- All universes are explicit. Both selected and test coverings have arbitrary
  index types in `Type (max u v)`, with v arbitrary; this covers arbitrary
  sizes and is never below the scheme universe. The collection's indexing
  universe w is independent. No auto-bound implicits or file-local notation.

Searches performed (the msearch calls are recorded in searches.jsonl):

- LeanFinder: `Cech cohomology vanishing on cofinal coverings of basis opens
  implies higher cohomology of a sheaf of modules vanishes on each basis open`.
  Eight results, including Sheaf.H, cohomologyPresheaf, and injective derived
  vanishing; no exact criterion for O_X-modules.
- Loogle: `"cech", "vanish"`. Zero hits.
- LeanSearch: `Higher cohomology of a sheaf of modules vanishes on basis opens
  if Cech cohomology vanishes for cofinal basis coverings`.
  Service unavailable (Internal Server Error); no result claimed.
- Mathlib grep through msearch: `cech.*(vanish|basis)|vanish.*cech|cohomologyFunctor`
  in CategoryTheory. One hit: a deprecated alias in SheafCohomology.Basic,
  not this criterion.
- Source grep/rg in WeilConjectures: the exact node id has no hits. Concept
  search and full-signature reading found
  `TopCat.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex` in
  `WeilConjectures.Topology.Sheaves.CechCriterion`. It concerns abelian sheaves,
  finite families and the whole space with B ⊤, not this module-valued statement
  for arbitrary coverings on every basis open.
- Project rg in lean/Sheaf found the related étale-site
  `isZero_rightDerived_etale_of_cech_vanishing`, the module Čech comparison,
  and open/module cohomology definitions; none states this node.
- Exact chosen declaration-name search in the source/project and
  dag/lean_names_upstream.json found no collision.

Validation: lcompile.py compiled the module cleanly (2.0 seconds, exit 0).
The delivery dry run provides the final server compile and preflight.
No statement dispute or correction is needed. The independent second reader
has not yet read this delivery and must supply their own section.

## Second reading by F1

The node was read before the module. Its objects and hypotheses match the Lean
signature item by item: `X : Scheme.{u}` is the scheme; `F : X.Modules` is the
sheaf of O_X-modules; `B : Set X.Opens` and `hB` say that the corresponding
underlying opens form a topological basis; `K`, `J`, `U`, and `V` index the
collection of coverings and their members; `hom` supplies the inclusion arrows;
and `S c : SiteCechComplex (V c) (hom c)` supplies the chosen iterated fibre
products. `hcover` says each family covers its target by `iSup (V c) = U c`.

The first conclusion hypothesis, `hbase`, separately puts each target, member,
and every finite nonempty intersection (`Fin (p + 1)`) in `B`, including degree
zero. The second, `hcofinal`, quantifies over every basis open and every open
covering indexed by `A : Type (max u v)`, then supplies a selected covering whose
members refine it. The third, `hvanish`, is exactly positive-degree vanishing of
the recorded Čech cohomology functor on `F.val.presheaf`. The conclusion has the
same quantifier order `p`, positivity, `W`, and basis membership, and states
`IsZero` for `RingedSpace.moduleCohomology W.toScheme.toRingedSpace p` applied to
the recorded `restrictFunctor W.ι` restriction. No clause is added, dropped,
strengthened, or weakened.

Edge cases remain represented: empty `K` or `J c`, empty scheme or basis, the
empty open, zero module, repeated or infinite index families, `p = 0` excluded
only from the conclusion and vanishing hypothesis, and arbitrary explicit
universes. No finiteness, quasi-compactness, separatedness, characteristic, or
nonemptiness assumption is present. An arrow in `X.Opens` already enforces the
required inclusion, so `hom` is not an extra geometric hypothesis.

I searched the project, source checkout, Mathlib, and DAG by declaration name
and by Čech/cohomology concepts (LeanFinder, Loogle, LeanSearch, and grep).
The only close source declaration is the abelian-sheaf whole-space criterion
`TopCat.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex`, which has different
coefficients, finite-family assumptions, and conclusion; it is not this node.
No existing declaration states this module-valued basis criterion.

No mismatch was found and no file or node field was changed. The module has one
statement theorem with `sorry`, imports only the recorded definitions, has the
required source and blueprint docstrings, and compiled successfully with
`lcompile.py`.
