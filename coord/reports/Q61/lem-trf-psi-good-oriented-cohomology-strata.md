## Worker report

Item: lem-trf-psi-good-oriented-cohomology-strata. The delivered module is
`Sheaf.Paper.PsiGoodOrientedCohomologyStrata`; its namespace is
`AlgebraicGeometry.OrientedNearbyCycles.PsiGoodStrata`. Its primary declaration is
`exists_constructible_cohomology_strata`. This is a stage-2 statement, with a `sorry`
proof. There are three additional postponed transport properties: `upContinuous`,
`restrictSite_properties`, and `vanishing_finiteLimits`. Each has a source and a
natural-language proof in its docstring. All definitions have actual data and all
15 declarations are listed in lean.declarations. The helpers specify the site/scalar
transports and the canonical restriction already requested in the item's statement;
they impose no extra hypothesis on the theorem.

I read the node, all seven original statement dependencies and their recorded Lean
interfaces, including the full nearby-cycle and oriented-product interfaces. I read
Lu--Zheng's v7 author PDF online at the URL in the source field: Theorem 4.27(2),
the following definition of constructibility, and the proof using Orgogozo's Lemma
10.5 and Theorem 8.1. The theorem assumes finitely many irreducible components,
finite presentation, Noetherian torsion coefficients with invertible annihilator,
and Psi-goodness; the node is the stated Noetherian-base, finite-ring, degree-zero
specialization. No modification or vanishing-bound conclusion is included.

Clause-by-clause correspondence:

- Schemes X,S are bound explicitly in universe u. Locally Noetherian and
  quasi-compact S are `[IsLocallyNoetherian S] [CompactSpace S]`.
- Finite presentation of `f : X ⟶ S` is exactly the recorded convention:
  `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]`.
- `Λ : Type (u + 1)`, `[CommRing Λ] [Finite Λ]` give the finite commutative ring.
  `m : ℕ`, `_hm : 1 ≤ m`, and `_hΛ : (m : Λ) = 0` express the positive integral
  annihilator (equivalent to mΛ=0 because the ring is unital). `_hS : IsUnit
  (m : Γ(S, ⊤))` means m is invertible on S. Invertibility in the global section
  ring is equivalent to invertibility locally or at every stalk, also on the empty
  scheme, since local inverses glue uniquely.
- `L` is an actual sheaf of modules over the constant ring on the transported small
  etale site. The recorded nearby-cycle interface uses `Coeff Λ = ULift Λ`;
  this is the canonical coefficient transport, not an arbitrary coefficient algebra.
  ULift's ring equivalence transports every Λ-module in either direction and
  preserves finite underlying sets and constant sheaves. The ring universe is the
  recorded constructible-sheaf convention u+1, which accommodates every finite
  coefficient ring by this canonical universe transport.
- `fixedSheaf` uses `realizationRingIso` and `constantRingModuleRestriction` to
  express those very modules as fixed-ring module-valued sheaves. It does not
  postulate an equivalence or choose a new action. `etaleFixed` then applies the
  inverse of the AsSmall site equivalence. `_hc` applies the dependency's exact
  `Scheme.IsConstructibleEtaleModuleSheaf` to this transported L. Thus the original
  finite-constant-values constructibility is used, not the upstream geometric-stalk
  predicate or its alternative stratification structure.
- `degreeZero X Λ L` is `DerivedCategory.singleFunctor ... 0`, with the exact
  `HasDerivedCategory.standard` instance used by nearbyCycles. `_hgood` is the
  existing `IsPsiGood f Λ (degreeZero X Λ L)`. Its definition tests the canonical
  comparison for every scheme base change; no properness restriction is substituted.
- `(q : ℤ) (_hq : 0 ≤ q)` is precisely the nonnegative integer degree. `cohomology`
  applies the existing derived `homologyFunctor` at q to `nearbyCycles f Λ` on L[0].
- `∃ (A : Scheme.LocallyClosedStratification X)
  (B : Scheme.LocallyClosedStratification S)` gives the two finite partitions. This
  dependency structure includes finite indexing, locally closed disjoint parts,
  coverage, domain schemes, immersions, and equality of their images with the parts.
  The first two conjuncts require `Topology.IsConstructible` of every part.
- For every `a : Fin A.n` and `b : Fin B.n`, `productSite (A.immersion a ≫ f)
  (B.immersion b)` is the existing two-map oriented product `datum`. Its maps are
  exactly X_a→X→S and S_b→S. It uses the existing triples and generated topology.
- `restrictBeta` uses the recorded fibre-product associativity and the identity on
  the second pulled-back entry. `restrictSite` applies `Comma.map`: it pulls back
  both outer etale schemes along the immersions and fixes the middle S-etale scheme.
  Therefore its two projections and oriented 2-morphism are the prescribed ones.
  The finite-limit, cover-preserving construction gives precisely the universal
  lift of lem-trf-oriented-product-universal. `restrictionModules.modulePull`
  is the existing canonical constant-ring module inverse image of that morphism;
  it is not an arbitrary morphism supplied as a hypothesis.
- `R : topology.Cover (⊤_ ...)` is a covering sieve of the terminal triple.
  Its arrows form a covering family of the final object. For every member `r :
  Z ⟶ ⊤_ ...`, the conclusion chooses `M : ModuleCat (Coeff Λ)` with `Finite M`
  and an isomorphism after `.over Z` to the `constantSheaf` on `topology.over Z`.
  This is exactly local constancy with finite module values on the slice topos.
  Conversely a trivializing family generates such a sieve; further pullbacks of a
  constant sheaf are constant, so the covering-sieve form is equivalent to the
  family form, not a stronger uniformity or site-representability requirement.
- q is bound before the existential partitions; thus the partitions may depend on
  q. There is no zero-object or vanishing assertion in any degree.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (available through scheme imports).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` and `.QuasiSeparated`:
  `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated`, as the convention
  node specifies.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `Scheme.IsConstructibleEtaleModuleSheaf`, read in full including its finite-values
  clause and LocallyClosedStratification (the upstream namesake is not imported).
- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`:
  `Scheme.LocallyClosedStratification`, with every field read.
- `Sheaf.Paper.OrientedNearbyCycles`: `etaleDatum`, `etaleTopology`, `Coeff`,
  `etaleBaseChange`, `etaleBaseChangeComp`, `vanishingDatum`, `moduleMorphism`,
  `siteMorphism`, `nearbyCycles`, `IsPsiGood`, and their actual module/derived APIs.
- `Sheaf.CategoryTheory.Sites.OrientedProductLargeSites` and its public small-site
  interface: `universalWithLargeSites`, `OrientedProduct.Triples`, `topology`.
  AsSmall gives a small presentation in u+1, so the published small interface is
  the relevant specialization of the general universal property.
- `Sheaf.TraceFormula.OrientedPointCohomology`: existing `datum` and
  `triples_finiteLimits`, reused verbatim for the product strata. This avoids
  defining the two-map oriented product a second time.
- `Sheaf.CategoryTheory.ConstantRingModuleSheaves`:
  `constantRingModuleRestriction`, the exact fixed-ring module restriction.
- `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`:
  `realizationRingIso`, the existing canonical CommRingCat-to-RingCat transport.

The last three owning nodes were added to stmt_deps, using the authorization to add
already published definitions/interfaces. There are no new nodes and no dependency
record repairs. The theorem's mathematical statement is unchanged.

Proof imports: def-trf-oriented-nearby-cycles is public because it is needed in the
statement. The oriented-constructible-sheaf, proper-surjective constructibility and
descent proof nodes have no recorded Lean modules, so none can be imported yet.
I read the current server source of
`WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes` with
`scompile.py --source`. Its import of the upstream
`WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf` conflicts with
this item's required published Sheaf definition of that same name (different
stratification interface). I therefore omit this proof-only import, as instructed
for duplicate declarations; the proof plan still names the node. Replacing the
statement dependency by that upstream predicate would violate its explicit record.

Edge cases checked before finalizing: q=0 is included; q can be arbitrarily large
and there is no assertion of vanishing. Zero L, zero coefficient ring and m=1 are
allowed. Empty schemes and zero-stratum finite partitions have no nonemptiness
binder. Empty covering sieves are allowed precisely when the topology covers the
final object by the empty family. Disconnected schemes, strata with nilpotent
scheme structure, and arbitrary scheme base changes remain included. No
Noetherian-dimension or reducedness hypothesis is added. Module values are finite
as sets, not merely finitely generated over an unspecified ring. All universes and
variables are explicit and autoImplicit is false.

Searches actually run:

1. `msearch.py Q61 ... leanfinder "Psi-good oriented nearby cycle cohomology has
   finite constructible locally constant strata"`: 8 unrelated profinite/locally
   constant-function hits (GoodProducts.smaller/range, finite fibres, Nobeling
   lemmas, and Profinite.exists_locallyConstant_*); none states this theorem.
2. `msearch.py Q61 ... loogle '"constructible", "Sheaf"'`: 0 hits.
3. `msearch.py Q61 ... grep
   'nearby.?cycle|vanishing.?topos|Psi.?good|oriented.*constructib'`: 0 Mathlib hits.
4. `rg` of WeilConjectures and lean/Sheaf for the item ID, PsiGood/psiGood/psi_good,
   nearby cycles and oriented constructibility: no existing theorem. The public
   nearby-cycle definition, good Kunneth, trait base-change and modification
   theorems are related but have different hypotheses/conclusions. The item-ID
   search has no upstream result. The upstream Lean name index has no match.
5. Further direct searches/readings found the published two-map `datum`, finite
   limits theorem, `constantRingModuleRestriction` and `realizationRingIso`.
   Earlier scratch copies of the two-map site and scalar restriction were removed
   in favour of these exact existing declarations before delivery.

Validation: all local checks used the authorized scompile.py wrapper. The final
module compiled both as sandbox and actual library path, in roughly 10 and 12
seconds, with no warnings or errors. All lines are at most 100 characters. The
only postponed proofs are the four named theorems listed above; all are `sorry`.
No statement dispute, statement correction or dependency defect is asserted.

## Second reading by Q61

This is the dispatcher's self-delivery workflow: no independent worker was started,
as expressly instructed. The maintainer performs the independent reading. I reread
the final file against the node: the exact scheme hypotheses, positive annihilator,
constructible degree-zero L, canonical Psi-good comparison, nonnegative q, both
finite constructible locally closed partitions, universal-property restrictions,
and finite constant slice trivializations are present. The concrete scalar bridge
is canonical; it neither chooses a new ring/module nor changes finite values.
The existential cover belongs to each oriented stratum and the partitions are
inside the q quantifier. No uniform bound, finite Tor dimension, separatedness,
nonempty strata, or properness of f was inserted. During this check I replaced
the scratch product-site construction and direct scalar-restriction construction
by aliases/composites of the published interfaces, and fixed the explicit site
universe in siteMorphism. The final signature in the node is copied verbatim
from the theorem keyword to the assignment delimiter.
