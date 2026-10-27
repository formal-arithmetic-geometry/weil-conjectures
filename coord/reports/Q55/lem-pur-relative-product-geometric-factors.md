## Worker report

The module `Sheaf.Paper.RelativeProductGeometricFactors` states
`WeilConjectures.RelativeProduct.relative_product_geometric_factors` and
`WeilConjectures.RelativeProduct.relative_product_composition_exchange`, with `sorry`
as each theorem's whole proof. Together these state the node's geometric, witnessed,
composition, normalized exchange, independence, and inverse-image assertions.
Every helper has real data. Two existing-definition nodes now give the imported transport and compactification-comparison data explicit DAG ownership.
The natural-language statement, proof, and proof dependencies are unchanged; statement dependencies gain the two definition nodes. No statement dispute or source fault was found.

I read the item, all seven statement dependencies with their records, the full
recorded interfaces, the relative-product proof (1),(3) in the main-20261015 blueprint,
and the proof dependencies used by the docstrings. The requested CompactObject example
is now a withdrawn module; the delivered file follows the current module/public-import,
source-docstring and public-namespace conventions.

The inputs use ordinary fixed-module sheaves on the actual small pro-etale site.
`D P T` is only an abbreviation for that published derived category. The definitions
`ctf` and `boundedConstructible` apply the EXISTING intrinsic predicates after the
functor of the EXISTING canonical `sfIntrinsicDerivedEquivalence T P.Ring`.
This is a coordinate transport, not a new constructibility or Tor condition.
`external` uses the existing exact inverse images via their left-derived functors
and the existing K-flat derived monoidal tensor. The canonical equivalence realizes
these as the same ring-sheaf operations in the recorded finite conventions.

Clause-by-clause correspondence (the node calls the input schemes P,Q; the file calls
these X,Y and reserves P for the coefficient setting):

- The fixed finite-field datum, distinct coefficient prime, actual finite coefficient
  extension, chosen quotient ring A_(E,n), and n >= 1 are the fields of
  `P : PurityFiniteSetting`. `P.Ring` is the existing quotient, and `P.Coefficient`
  is its prescribed ULift. Finiteness instances are the actual
  `Padic.finite_coefficientExtensionRing` theorem and its ULift instance.
- The separated finite-type k-scheme B is `B : Scheme.{u}`, its map
  `s : B ⟶ Spec (CommRingCat.of P.field.k)`, and the three classes
  `[IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s]`. The statement involves
  several morphisms over this base, so this is the explicit structure-map convention.
- The morphisms f and g are the corresponding scheme morphism binders with exactly
  the same separated, locally-of-finite-type and quasi-compact classes. Finite type
  is rendered by locally finite type plus quasi-compactness.
- K and L are arbitrary objects of `D P X` and `D P Y` with `_hK : ctf P X K`
  and `_hL : ctf P Y L`. The second statement names the bounded-below wrapper K,
  uses its underlying `K.obj`, and retains the same two finite-Tor conditions.
- W is `pullback f g` from the recorded Mathlib declaration. The a and b of the node
  are `pullback.fst f g` and `pullback.snd f g`. Its h is written as a followed by f
  in the geometric assertion and as b followed by g for the compositor; the existing
  pullback condition identifies these morphisms. No extra commutativity datum is assumed.
- H is `external P f g K L`, the actual tensor of the two actual derived pullbacks.
  In the second statement the bound wrapper H satisfies `_hH : H.obj = external ...`;
  this is just a wrapper of this specified object, never an arbitrary substitute.
- The first three triple conjunctions of `relative_product_geometric_factors` say
  X,Y,W are separated finite type over k. The next three say a,b,h are separated
  finite type. Both have the original k and no finiteness restriction beyond the node.
- The next two assertions are `boundedConstructible` for K and H, exactly the
  intrinsic bounded-constructibility predicate through the canonical equivalence.
- The two existentials give bounded-below wrappers with underlying objects K and H
  and `Nonempty (FixedEtaleOriginWitness ... wrapper)`. This is existence of the
  prescribed pair; no definition selects arbitrary data from this existence.
- The second theorem takes arbitrary retained `WK` and `WH`, each containing the
  actual etale antecedent and specified comparison isomorphism. The `origin` helper
  only forgets this pair when evaluating the already-defined transformations on the
  full origin subcategory. `pullbackOrigin` transports it through the specified
  `leftDerivedUpperStarComparisonIso`, without a new choice of antecedent.
- `composition` is the RECORDED `originComposition` for b then g. Its source, middle
  and target are the full bounded-below etale-origin categories, so preservation
  and the domain of the iterated expression are retained by its type. Its component
  at `origin ... H WH` is alpha_(g,b,H). The last two conjuncts assert that its
  forward and inverse components are isomorphisms. This is in the actual derived
  category/full subcategory, not a per-cohomology weakening.
- The compactification parameters c,cg,cb,ch are arbitrary computational choices
  for f,g,b,h. They are not new geometric assumptions: the first theorem's geometric
  domains put them within the field-base compactification theorem's domain, and
  the imported Nagata/refinement construction supplies them. All choices are allowed.
  The composition uses the canonical chosen-comparison convention of its recorded
  definition; its HasCompactification fields are proof-irrelevant existence data.
- E is literally `(exchange P sq c).app K.obj`,
  where sq is `IsPullback.of_hasPullback f g`. This pair component is the specified
  ambient proper unit-square-counit mate followed by the open-extension comparison.
- The first equality identifies E with `compactExchangeTransportAtWitness` at
  `WK.complex` and `WK.iso`. That existing definition uses the RECORDED ordinary
  etale `rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap` with the same
  c and its base change, conjugated by the prescribed proper/open source and target
  comparisons and the actual witness. Thus this asserts the normalized identity,
  not just the existence of an isomorphism with the same endpoints.
- `IsIso E` is the next conjunct. The following universal equality for every W'
  expresses witness independence, including genuinely different antecedents and
  comparison isomorphisms.
- The universal equality for every compactification d says
  `E_c ≫ targetComparison = sourceComparison ≫ E_d`. Both comparisons are the
  existing `rightDerivedLowerShriekOfCompactificationEtaleOriginIso`: the source
  is pulled back by g, and the target is evaluated at the canonically pulled-back
  retained witness with the base-changed c and d. These are the canonical
  compactification comparisons, not freely supplied isomorphisms.
- The isomorphism e is required to have `e.hom = E`. The isomorphism j has precisely
  the endpoints Rg_!(target(E) tensor L) and Rg_!(source(E) tensor L), and its hom
  and inv are required to be `Rg_!.map (e.inv tensor id L)` and
  `Rg_!.map (e.hom tensor id L)`. This says exactly that the requested inverse-tensor
  functor image is a defined isomorphism with the displayed inverse.
- No hypothesis or datum asserts Verdier duality, exceptional adjoint admissibility,
  or an unrestricted ambient pro-etale exceptional adjunction.

Dependency declarations actually used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, `.Ring`,
  `.Coefficient`, and their recorded ring structures.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: the reexported
  `WeilConjectures.finiteTorConstructible` from `FiniteTorAmplitude`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, with the scheme pullback instances.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `AlgebraicGeometry.Scheme.FixedEtaleOriginWitness`, `.complex`, `.iso`.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`:
  `AlgebraicGeometry.ProEtale.originComposition` and its full-origin compact-support functors.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: the RECORDED
  `CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData`.
  `exchange` inserts the actual open extensions, proper pullbacks and right adjoints,
  their canonical derived adjunctions, `leftDerivedUpperStarSquareIso` for the proper
  square and `leftDerivedOpenImmersionLowerShriekBaseChangeIso.symm` for the open square.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`,
  inside the specified transport used by the equality.
- `Sheaf.Paper.CompactSupportExchangeTransport`: `compactExchangeTransportAtWitness`,
  whose source/target paths use the canonical proper counit mate, open-extension and
  pullback comparisons, retaining the same ordinary etale exchange.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`:
  `AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactSupportCandidate`:
  `rightDerivedLowerShriekOfCompactificationEtaleOriginIso` for both endpoint comparisons.

The proof-only imports follow all recorded stated proof dependencies: regrouping,
constructible origin, compactification/refinement, intrinsic compact support, base-changed
compactifications, proper/finite-type/separated geometry, exact etale extension by zero,
normalized proper exchange transport, normalized open exchange, coefficient finiteness,
and finite-level compact-support base change. No downstream theorem about the introduced
maps is assumed. Each theorem docstring gives its part of the node's seven-step proof.

Edge cases checked against the signatures and constructions: empty X,Y,B and hence empty
fibre products; zero K or L; identity f or g and identity base-change squares; level n=1;
non-regular finite quotient coefficients (no semisimplicity/field assumption); arbitrary
etale witnesses including different antecedents; all compactifications c,d; the original
small-site object universe u+1 and morphism universe u with module values in u+1.
No Nonempty scheme, nonzero object, tensor-flat input, Kummer divisibility, exceptional
adjoint datum, or equality of the two site universes is imposed. Level zero is excluded
only by the original positive-level coefficient convention.

Searches actually made on 2026-10-22:

- msearch.py, leanfinder: `Compact support composition and base change exchange are
  isomorphisms on bounded constructible etale origin complexes for a relative fibre
  product`. Eight results concerned affine-transition limits, scheme module pullback
  composition and etale stability; none states this compact-support combination.
- msearch.py, loogle: `"baseChange", "Iso"`. Twelve results on morphism-property stability,
  localization dimensions and Guitart/Kan exchange; none is this assertion.
- msearch.py, grep: `lowerShriek|LowerShriek|etaleOrigin` in `AlgebraicGeometry`:
  returned zero hits.
- rg on `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  `relativeProduct|relative_product|geometricFactors|GeometricFactors|lem-pur-relative-product-geometric-factors`:
  no match. Direct grep for the node id in `lean/WeilConjectures` also found no match.
- Further source searches found the existing generic finite exchange package,
  the normalized `compactSupport_exchange_transport`, and the canonical origin
  compositor. Their signatures were opened and reused; none alone states the node's
  combined geometric, constructible, witnessed and factor assertions.

## Repair of return L at 4edd7db3bcab

The required initial saved-packet dry run passed at a6be384995a. This did not address
independent return L, so the packet was repaired substantively as follows.

1. Removed the sandbox copy of `def-exchange-projection.json` completely. Delivery
   therefore leaves the landed Q14 record byte-identical, including its module, all ten
   SuppliedExchangeProjection declarations, ownership, and note. The item imports that
   recorded module directly. Its new `exchange` helper constructs E from the recorded
   `compactificationExchangeFromData` with the actual finite operations, canonical proper
   derived adjunctions, canonical proper-square pullback comparison, and inverse canonical
   open-base-change comparison. Every occurrence of the rejected finite-package projection
   was replaced by this concrete construction. This takes the reviewer's second repair
   option; no superset re-export or change to the dependency module is needed.
2. Added and cited `def-pur-compact-exchange-witness-transport`, an existing:true definition
   node owning Comparison/Source/Target/AtWitness from CompactSupportExchangeTransport.
   The theorem node lem-pur-co-smooth-exchange-transport is not treated as a definition.
3. Added and cited `def-pur-origin-compactification-comparison`, an existing:true definition
   node owning the upstream canonical EtaleOriginIso. Its statement specifies the actual
   common-refinement comparison transported to the full bounded-below origin category.

The mathematics and both theorem clauses are unchanged. The source/target directions
still match the returned review: E_c followed by the target comparison equals the source
comparison followed by E_d; tensoring E inverse and applying Rg_! has the displayed inverse.
No proof was added and no existing library source was edited.

## New nodes

`def-pur-compact-exchange-witness-transport` records exactly the existing four path/arrow
constructions in `Sheaf.Paper.CompactSupportExchangeTransport`: Comparison is the canonical
proper/open comparison, Source and Target insert its two endpoint paths with canonical
pullback comparisons, and AtWitness conjugates ordinary etale exchange through those paths
and the retained alpha. Its source is relative-product proof (3), expanded by the existing
finite-level compact-support transport proof cited in that module's docstrings. The
statement includes a finite commutative ring, arbitrary Cartesian square and chosen c,
L bounded below and arbitrary ambient N with a specified alpha. No separated/finite-type
hypothesis or invertibility assertion is added to these plain definitions.

`def-pur-origin-compactification-comparison` records the existing upstream
`rightDerivedLowerShriekOfCompactificationEtaleOriginIso`, with finite coefficients and
quasi-compact f, precisely its declared domain. It is the canonical transported etale
common-refinement isomorphism on the full bounded-below etale-origin category, used in
relative-product proof (3)'s compactification-independence clause. It chooses no arbitrary
comparison and imposes no additional condition on the item, which already has finite-type f.

Searches for both nodes: msearch.py leansearch with query "Canonical transport of compact
support exchange through etale origin witnesses and canonical compactification comparisons"
returned eight unrelated topological compact-support results. msearch.py leanfinder with query "Canonical compact support
exchange transported from etale to proetale via witnesses and comparison isomorphisms
between compactifications" returned eight unrelated Mathlib scheme/etale results;
msearch.py loogle with the three expected identifiers returned no hits (unknown identifier);
msearch.py grep `compactExchangeTransport|EtaleOriginIso` in Mathlib/AlgebraicGeometry
returned zero. rg of dag/nodes, lean/Sheaf, lean/WeilConjectures and the upstream name
index found exactly the reused definitions; no definition node already owns them.
blueprint_refs.py search compactExchangeTransport returned zero matching nodes. The raw
msearch outputs are retained in each new node's mathlib_searches, along with the source
search conclusion. These are existing:true records, with no copied definitions/modules.

## Self-check by Q55

Opened the saved node and file, the returned diagnostic, the current Q14 record and its
full generic compactificationExchangeFromData signature. Checked every concrete argument:
J/J' are degreewise open extensions, P/P' and R/R' are the actual proper derived functors,
the adjunctions are the canonical ones, G/H/B are pullbacks along g/g'/the compactifying
base change, theta is the proper square's composition isomorphism and beta the inverse
open comparison. This realizes exactly the specified E, including its normalization.
The replacement changed only its construction's spelling in the theorem statements.
Read the full imported transport definition and the upstream common-refinement comparison
before writing their two definition records. Source/target paths, alpha inverse at the
source, alpha at the target, and common-refinement directions agree with their signatures.
The prior review accepted all geometric clauses, universes, witness quantifiers, intrinsic
constructibility transport and inverse tensor clauses; those were retained.
No second agent was started, as expressly required by the dispatcher brief. The maintainer
performs the independent reading.

Validation: after the repairs scompile.py compiled this module with no errors or warnings,
both under Sheaf.Stage2.Sandbox0 (30.1 s) and its actual module name (38.1 s), within
the unchanged 60-second limit. Final dry-run and delivery results are recorded below.

The first repaired preflight identified missing LeanSearch records, grouped dependency
citations and an array row separator abutting a letter. Added the actual LeanSearch result,
split the dependency citations, and placed TeX array row separators on separate lines.

Final repaired dry run: deliver2.py --no-push returned OK at c8eb4cf7859,
with the item module and both existing-definition nodes passing server preflight and
per-file compilation. The staged paths contain no def-exchange-projection node or module.

## Second reading by Q55

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
