## Worker report

Item: `lem-kun-tor-cokernel-flat`. The module
`Sheaf.AlgebraicGeometry.EtaleTensorCokernelFlat` states
`AlgebraicGeometry.Etale.isFlat_opcycles_of_tensor_cohomology_vanishing`.
Its sole proof is `sorry`. No definition, instance, axiom, extra theorem, new node,
or dependency repair is introduced. The natural statement is unchanged.

Hypothesis and conclusion correspondence:

- A commutative ring is `(Λ : Type (u + 1)) [CommRing Λ]`; the arbitrary scheme is
  `(T : Scheme.{u})`. This is the standing size convention: site objects have
  universe `u + 1`, morphisms universe `u`, and coefficients and module sections
  universe `u + 1`. The site universes are not identified. Small coefficient
  rings, including integers and finite rings, can be lifted into this universe.
- The small etale site is exactly `T.smallEtaleTopology` on `T.Etale`.
- The constant commutative ring sheaf is the explicit expression
  `(constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of Λ)`.
  It is sheafification of the constant ring presheaf. `sheafCompose` along
  `forget₂ CommRingCat RingCat` supplies the underlying sheaf of rings needed
  by module sheaves, without changing the coefficient action.
- The complex is `K : CochainComplex (ringedSiteModules.{u + 1} ...) ℤ`.
  The recorded abbreviation is transparently Mathlib `SheafOfModules` over
  that ring sheaf, not a separately defined module category. The module
  universe is explicit for both `K` and the test sheaf `M`.
- Every term is flat: `hflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite ... (K.X i)`.
  This uses the currently recorded flatness predicate, exactness of the
  sheafified sectionwise functor `G ↦ G ⊗ F`, with no stalkwise replacement.
- The arbitrary integer is `(a : ℤ)`.
- The vanishing hypothesis quantifies over **every** module sheaf in precisely
  the same category, `∀ M : ringedSiteModules.{u + 1} ...`, with no flatness,
  finiteness, constructibility, constancy, or boundedness assumption on `M`.
- Degree-zero placement is `(CochainComplex.singleFunctor _ 0).obj M`.
- Ordinary tensor, in the stated order `K` then `M`, is
  `CochainComplex.mapBifunctor K ((CochainComplex.singleFunctor _ 0).obj M)
  (@curriedTensor _ _ (SheafOfModules.monoidalCategory ...))`.
  This is the canonical sheaf tensor product, followed by direct-sum totalization;
  its sign convention is `d_K ⊗ 1 + (-1)^p 1 ⊗ d_M`. In particular it is not
  the derived tensor of `K` with `M`, which would require resolving `K`.
- All degrees below `a` are retained verbatim as `∀ n : ℤ, n < a → ...`.
  Cohomology sheaf vanishing is `IsZero (... .homology n)` in the abelian
  category of module sheaves, not vanishing only of global sections.
- The conclusion is `SheafOfModules.IsFlatOnSite ... (K.opcycles a)`.
  Mathlib's `HomologicalComplex.opcycles` is the categorical cokernel of the
  incoming differential (`ShortComplex.opcycles` of `K.sc a`); for the cochain
  shape its previous degree is `a - 1`. Thus this object is exactly the stated
  `coker(K^(a-1) → K^a)`. No conclusion concerning `H^a(K)` is substituted.

Dependency declarations read and used:

- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `AlgebraicGeometry.Scheme.smallEtaleTopology` and `Scheme.Etale`.
- `def-kun-constant-sheaf`: the recorded
  `Mathlib.Algebra.Homology.Additive` /
  `CategoryTheory.Functor.mapHomologicalComplex` is the generic termwise
  constant-complex interface; its note specializes the existing
  `CategoryTheory.constantSheaf` from `Mathlib.CategoryTheory.Sites.ConstantSheaf`.
  This item only needs the ring sheaf, so it uses `constantSheaf` directly;
  no termwise constant complex is needed.
- `def-pc-cochain-complex-modules`: `CochainComplex` from
  `Mathlib.Algebra.Homology.HomologicalComplex`.
- `def-weil-sheaf-of-modules-category`: `CategoryTheory.ringedSiteModules`
  from `Sheaf.CategoryTheory.RingedSiteModules`; the inherited category and
  abelian structure are Mathlib's.
- `def-pc-flat-sheaf-modules`: `SheafOfModules.IsFlatOnSite` from
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`, read in full together
  with its independent-universe `siteSheafTensorRight` construction.
- `def-kun-derived-tensor`: the recorded module
  `WeilConjectures.SixFunctors.Etale.Derived.Tensor` is publicly imported.
  Its primary `AlgebraicGeometry.Etale.derivedTensor` is not applied, because
  the hypothesis explicitly uses ordinary tensor. The record's ordinary
  tensor interface `HomologicalComplex.tensorObj` is the generic abbreviation
  for `mapBifunctor` with `curriedTensor`; the statement writes this underlying
  totalization explicitly over the recorded ringed-site module category.
- `def-pc-acyclic-complex-modules` is a Mathlib leaf; its `mathlib_match`
  supplies `HomologicalComplex.homology` and the vanishing/exactness criterion
  in `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`. No missing
  Lean record is invented for this Mathlib leaf.
- Proof dependency `lem-weil-pbc-site-flat-opcycles-tor-criterion`:
  `Sheaf.Algebra.Homology.SiteFlatOpcyclesTorCriterion` /
  `SheafOfModules.isFlat_opcycles_of_universal_tensor_exactAt`, imported
  without `public`. Its complete source was also checked through
  `scompile.py --source`. It is stated on a small representative; the proof
  docstring explains the small-site transport and tensor symmetry. The
  specialized monoidal `IsFlat` in that proof interface and the recorded
  `IsFlatOnSite` both concern the sheafification of the sectionwise tensor.
- `def-weil-size-convention` is explicitly a metatheoretic convention with
  no module/declaration. The universes above implement it. The existing
  generalized tensor infrastructure is publicly imported from
  `Sheaf.Algebra.Homology.KFlat`; its server source was read, including
  `SheafOfModules.isMonoidal_W_separateHomUniverse` and the two
  zero-morphism-preservation instances. No new size hypothesis is added.

Source and proof plan: read the full DAG statement and its two proof steps.
The blueprint file is absent in this read-only clone's `literature/` directory;
read the available upstream blueprint source at the same relative blueprint
path in the launcher's upstream blueprint snapshot. It states the same
commutative-ring, arbitrary-scheme, ordinary-tensor theorem. The declaration's
source docstring includes both DAG proof steps: vanishing at `a - 1`, then the
small-site flat-opcycles criterion with the sign-one symmetry for `M[0]`.
The theorem is a statement only; proving the transport and tensor comparisons
belongs to stage 3.

Edge cases checked before writing: the zero ring, empty scheme, zero complex,
zero test sheaf, arbitrary positive/zero/negative `a`, and unbounded complexes.
None is excluded by a binder. On an empty site the category is trivial and
flatness holds; the zero test sheaf contributes its expected automatic case,
while all nonzero test sheaves are still quantified. No boundedness of `K`,
Noetherian condition on `T`, restriction on characteristic, or finiteness of
coefficients is introduced. A nonflat sheaf placed in degree `a` is excluded
by `hflat`, so the hypothesis is not a hollow predicate. Neither termwise
flatness nor universal cohomology vanishing is replaced by a stronger condition.

Searches for an existing identical statement:

- `msearch.py ... leanfinder`, query
  `A complex of flat module sheaves whose tensor with every module has vanishing cohomology below a has flat cokernel in degree a`,
  and the refined query
  `Flat cokernel of a differential of flat sheaves from universal ordinary tensor cohomology vanishing`:
  eight ordinary-module flatness/exactness results, including
  `Module.Flat.iff_lTensor_preserves_shortComplex_exact`,
  `Module.Flat.iff_rTensor_preserves_shortComplex_exact`, and
  `Module.Flat.iff_rTensor_exact`; none is this etale sheaf statement.
- `msearch.py ... loogle`, `Module.Flat.iff_rTensor_exact`: one hit, the
  ordinary-module criterion, not this cochain/module-sheaf statement.
- `msearch.py ... grep`, `flat_opcycles|opcycles_of_exactAt|cokernel.*flat`:
  zero Mathlib hits. The separate search of the upstream project and
  `lean/Sheaf` found generic module and monoidal-category opcycle criteria,
  the existing general site criterion, and other applications; none states
  this exact constant-coefficient small-etale theorem. In particular the
  generic site criterion assumes only exactness at `a - 1`, unlike the
  item's full below-`a` hypothesis, so it is a proof dependency, not an exact
  existing-statement replacement.
- `msearch.py ... leansearch`,
  `Flat cokernel of differential in complex of flat module sheaves from vanishing of tensor cohomology`:
  service unavailable, Internal Server Error. This is recorded as unavailable,
  not as absence evidence. LeanFinder, Loogle, and direct source searches
  supplied the available independent searches.
- Direct `rg` of the upstream `WeilConjectures/`, Mathlib, this project's
  `lean/Sheaf`, and `dag/lean_names_upstream.json` found no occurrence of the
  chosen full theorem name. Searching the upstream project for
  `lem-kun-tor-cokernel-flat` found no existing matching declaration.

No `STATEMENT-DISPUTED` issue or correction is required.

## Second reading by NH

Independent second reader, 2026-10-16. I opened the sandbox node and module,
all seven statement-dependency records, the size-convention and flat-opcycles
proof-dependency records, and their source declarations. I also read the actual
blueprint item and its enclosing section at
`/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/`.
The lemma introduces its own arbitrary commutative ring and arbitrary scheme;
the section's separably closed field and invertible integer belong to the
Kunneth proposition, not to this general homological-algebra lemma. Stacks
`sites-modules.tex`, Definition 03ER(3), defines flatness by exactness of
`G ↦ G ⊗ F`. I read `sites-cohomology.tex`, Tag 08G0, including its surrounding
Tor-amplitude definition: boundedness there serves to identify ordinary and
derived tensor. The present node assumes ordinary tensor vanishing directly
and correctly does not add boundedness or a K-flatness hypothesis.

Object/hypothesis/conclusion checklist, in the order of the natural statement:

1. Arbitrary commutative ring Lambda: `(Λ : Type (u + 1)) [CommRing Λ]`.
   Correct; there is no field, nonzero, torsion, characteristic, finiteness,
   or Noetherian hypothesis.
2. Arbitrary scheme T and its small etale site: `(T : Scheme.{u})` and
   `T.smallEtaleTopology`. Correct. I read Mathlib's `Scheme.Etale` definition
   as the category of etale schemes over T and `smallEtaleTopology` as the
   induced jointly surjective etale topology.
3. Constant ring sheaf Lambda_T: each repeated
   `(constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of Λ)`.
   Correct. I read `CategoryTheory.constantSheaf`, whose body is the constant
   presheaf functor followed by `presheafToSheaf`. `sheafCompose` along
   `forget₂ CommRingCat RingCat` supplies exactly its underlying ring sheaf.
   The constant-complex prolongation recorded by `def-kun-constant-sheaf`
   is not needed here; its record explicitly cites this same constant sheaf.
4. Category of Lambda_T-module sheaves: the repeated
   `ringedSiteModules.{u + 1} ((sheafCompose ...).obj ...)`.
   Correct. The recorded `CategoryTheory.ringedSiteModules` is transparently
   `SheafOfModules`; I read its definition and Mathlib's sheaf-module interface.
   In particular these are arbitrary module sheaves, not merely locally
   constant sheaves or sheaves of abstract modules without the coefficient
   ring-sheaf action. Cokernels and homology use the inherited abelian category.
5. Integer-indexed cochain complex: `(K : CochainComplex (...) ℤ)`.
   Correct. Mathlib defines this as `HomologicalComplex` of shape `up ℤ`,
   whose differential goes from degree i to i+1 and squares to zero.
6. All terms flat: `hflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite ... (K.X i)`.
   Correct. The recorded independent-universe definition is `exactFunctor`
   of `siteSheafTensorRight`; I read that functor's actual construction as
   forgetting to presheaves, taking sectionwise balanced tensor, and sheafifying.
   This is exactly Definition 03ER(3), rather than sectionwise flatness.
7. Arbitrary integer a: `(a : ℤ)`. Correct; no lower or upper bound is added.
8. Every test module sheaf M in degree zero: `hvanish : ∀ M : ringedSiteModules ...`
   and `((CochainComplex.singleFunctor _ 0).obj M)`. Correct. The category
   and its explicit module universe agree with K's; no flatness,
   constructibility, constancy or other condition is imposed on M.
9. Ordinary total tensor K tensor M[0]:
   `CochainComplex.mapBifunctor K ((CochainComplex.singleFunctor _ 0).obj M)
   (@curriedTensor _ _ (SheafOfModules.monoidalCategory ...))`.
   Correct, in the stated factor order. I read `mapBifunctor` as the total
   complex of the bifunctor bicomplex, with the direct-sum totalization and
   differential `d_K ⊗ 1 + (-1)^p 1 ⊗ d_M`. I also read the source
   `SheafOfModules.monoidalCategory` and `tensorObjIsoSheafification`:
   its tensor is the sheafification of presheaf tensor, the same sheaf tensor
   used by `IsFlatOnSite`. The recorded derived-tensor module is imported,
   but no derived tensor is substituted into this ordinary-tensor hypothesis.
10. Cohomology sheaf vanishes for every n<a:
    `∀ n : ℤ, n < a → IsZero ((...).homology n)`.
    Correct. I read `HomologicalComplex.homology` as the homology of its
    degree-n short complex. Thus this is zero cohomology as a module sheaf,
    not just zero global-section cohomology. All n<a are retained.
11. Conclusion N=coker(K^(a-1) -> K^a) is flat:
    `SheafOfModules.IsFlatOnSite ... (K.opcycles a)`.
    Correct. Mathlib's `HomologicalComplex.opcyclesIsCokernel` identifies
    `K.opcycles a` as the cokernel of `K.d (a-1) a` since the predecessor
    for `up ℤ` is a-1. The node names N by this definition; no independent
    existential, extra conclusion, or substitution of H^a(K) is needed.

Edge cases: the zero ring, empty scheme, zero complex, zero test sheaf,
positive/zero/negative a, and complexes unbounded in either direction are
all admitted by the displayed binders. There is no external index family
whose empty case is excluded. Characteristic is arbitrary. Universe u is
explicitly bound; scheme/site morphisms have size u, site objects size u+1,
and coefficient/module sections size u+1, in the recorded standing convention.
This does not identify site object and morphism universes or restrict the
universal test to a smaller module universe. Smaller coefficient rings can
be represented by their usual universe lift. No extra essential-smallness,
sheafification, monoidal or abelian structure is assumed as a theorem binder;
the existing small-etale infrastructure supplies them.

Independent searches, using words beyond the first reader's query:

- `msearch.py NH lem-kun-tor-cokernel-flat leanfinder` with
  `Exact tensor testing detects flatness of the quotient by boundaries in a cochain complex of flat sheaves`:
  eight ordinary-module flatness/exactness lemmas, no identical sheaf theorem.
- `msearch.py ... loogle '"opcycles"'`: twelve opcycle-construction results,
  including `ShortComplex.opcyclesIsoCokernel`; no identical flatness theorem.
- `msearch.py ... grep
  '(opcycles|coimage|cokernel).*(flat|Flat)|(flat|Flat).*(opcycles|coimage)'`:
  no Mathlib match. Direct `rg` with the same notions in the upstream
  `WeilConjectures/` and this project's `lean/Sheaf` found the general
  site criterion, module/affine results, and
  `CategoryTheory.ObjectProperty.flat_opcycles_of_exactAt`.
  I opened that last signature: it uses categorical flatness of two terms
  and universal exactness at a-1, not this node's all-term flatness and
  below-a vanishing. None is an exact existing-statement replacement.
- `msearch.py ... leansearch` with
  `Universal vanishing of cohomology after tensoring a complex of flat sheaves implies that its cokernel of boundaries is flat`:
  service unavailable (Internal Server Error); not absence evidence.
- Direct name and blueprint-id searches in upstream, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` found no existing declaration of this item.

The recorded proof dependency
`SheafOfModules.isFlat_opcycles_of_universal_tensor_exactAt` was read in
`SiteFlatOpcyclesTorCriterion.lean`: it puts the test sheaf first and uses
`IsFlat`, so its application requires tensor symmetry, the small-site
transport, and identification of the two sheafified-tensor flatness predicates.
These are mathematically equivalent presentations, not extra hypotheses;
the item's proof docstring already explains the transport and the
`(-1)^(j*0)=1` differential calculation. Both DAG proof steps are present.
There are no new definition nodes or dependency modules to review, no hollow
definitions, and no proved declarations in this delivery. The sole named
statement has its source and blueprint marker, and its entire proof is `sorry`.
All variables/universes are bound, no private notation or local instance is
introduced, and the node's `lean.statement` was checked verbatim against the
signature in the file.

Mismatch/repair verdict: none found. I retained the correct Lean module and
node unchanged and appended this independent audit. No statement correction
or citer audit is needed. `scompile.py NH lem-kun-tor-cokernel-flat
lean/Sheaf/AlgebraicGeometry/EtaleTensorCokernelFlat.lean` passed for both
sandbox and library paths with no errors or warnings, under the normal
60-second per-file limit (9.9 s and 8.3 s).
