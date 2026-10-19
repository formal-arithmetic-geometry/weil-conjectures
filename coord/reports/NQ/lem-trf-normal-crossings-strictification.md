## Worker report

The delivery states `AlgebraicGeometry.exists_normalCrossings_strictification` in
`Sheaf.AlgebraicGeometry.NormalCrossingsStrictification`. Its only proof is `sorry`.
Two new definition modules supply the missing normal crossings and smooth strict normal
crossings predicates. Both definitions have real data (Prop-valued formulas); neither
chooses a scheme, map, or divisor from an unproved existence theorem. The item's statement,
proof plan and proof dependencies are unchanged. Only `lean` and the two added definition
statement dependencies change.

The source was read directly: ILO, Travaux de Gabber, Expose VIII 4.1.1--4.1.8 and
Remark 4.2.2(i), printed pp.117--119 (PDF pp.123--125), and Lemma 4.2.9 on printed p.121.
Step 2 is strictification of the OLD strict transform. It terminates when that strict
transform is empty, and the full inverse-image boundary is the accumulated SNC exceptional
boundary. The theorem docstring records each of the node's eight proof steps, including
the maximal-depth decrease, Cartier-centre terminal case, density and integrality invariants,
proper composition, and regular-to-smooth passage over the algebraically closed field.

Clause-by-clause rendering of the item:

- Algebraically closed field: `(F : Type u) [Field F] [IsAlgClosed F]`.
- The finite-type F-scheme is `(V : Scheme.{u}) (f : V ⟶ Spec (.of F))` with
  `[LocallyOfFiniteType f] [QuasiCompact f]`. The explicit structure map permits the
  conclusion to state exactly that `q` is an F-morphism.
- Integral: `[IsIntegral V]`, including nonemptiness and reducedness.
- Regular: `hV : ∀ x : V, ∃ U : V.affineOpens, x ∈ U.1 ∧ IsRegularRing Γ(V, U.1)`.
  This is the recorded defining affine-neighbourhood clause, without substituting an
  unproved equivalence to a stalkwise predicate.
- Closed divisor: `Z : V.IdealSheafData`, with its canonical closed immersion
  `Z.subschemeι`. Its effective Cartier and normal crossings hypotheses are
  `hZ : Z.IsNormalCrossingsDivisor`. This predicate uses the recorded `IsInvertible`,
  equivalent to a local nonzerodivisor equation, and etale neighbourhoods with the
  prescribed product of distinct regular parameters.
- Etale locally at every point: the definition quantifies over `x : V`, then
  `W`, `e : W ⟶ V`, `Etale e`, and `w : W` with `e w = x`. It does not assume
  global branches or require the original irreducible components to be smooth.
- Distinct members of a regular system: `s.Sublist t` with the existing
  `IsLocalRing.IsRegularSystemOfParameters t`. A regular system minimally generates the
  maximal ideal and therefore has no repetitions. The equation is equality of the
  extended ideal on the stalk with `Ideal.span {s.prod}`; equality of ideals allows
  multiplication of a generator by a unit. The germ map on an affine neighbourhood
  represents the canonical stalk ideal of `Z.comap e`.
- The empty divisor is allowed: `s = []` gives product 1 and the unit ideal. The
  hypothesis therefore includes the unit ideal everywhere. Global self-intersections
  are allowed because splitting is requested only after etale localization.
- Existence of the new scheme and maps: existential `V₂`, `f₂ : V₂ ⟶ Spec (.of F)`,
  and `q : V₂ ⟶ V`.
- New scheme integral, smooth and finite type: `IsIntegral V₂ ∧ Smooth f₂ ∧
  LocallyOfFiniteType f₂ ∧ QuasiCompact f₂`.
- Proper F-morphism: `q ≫ f = f₂ ∧ IsProper q`.
- Isomorphic over the complement: `IsIso (q ∣_ Z.support.compl)` is the canonical
  restricted morphism from the inverse image of that open to the open itself.
- Dense inverse image: `Dense ((q ⁻¹ᵁ Z.support.compl : V₂.Opens) : Set V₂)`.
- Reduced inverse-image divisor: `((Z.comap q).radical)` is its canonical ideal.
  On each affine chart this first extends the ideal and then takes its radical;
  its subscheme is exactly the reduction of the scheme-theoretic inverse image.
  This uses the existing ideal-sheaf radical and subscheme constructions, not a new
  reduction definition. In particular no arbitrary divisor with the same support is used.
- The explicit SNC conclusion is
  `((Z.comap q).radical).IsSmoothStrictNormalCrossingsDivisor f₂`.
  The predicate states `IsInvertible` and `IsReduced` and exhibits `n : ℕ` integral
  closed subschemes `C : Fin n → V₂.IdealSheafData`. Equality with `⨅ i, C i`
  specifies their scheme-theoretic union. Pairwise noncontainment of supports implies
  they are exactly the irreducible components, without repetitions or extra components.
- All components are smooth: take a singleton `s` in the universally quantified
  `s : Finset (Fin n)`. Its intersection ideal `s.sup C` is that component's ideal.
- Intersections of r distinct components: a finite subset `s` specifies distinct indices
  and `r = s.card`. The sum of the ideals, `s.sup C`, defines the scheme-theoretic
  intersection. `Smooth ((s.sup C).subschemeι ≫ f₂)` gives smoothness, including
  the empty intersection scheme. For every ambient affine chart, every minimal prime
  of that intersection's ideal has `p.height = (s.card : ℕ∞)`. Thus EVERY irreducible
  component of a nonempty intersection has codimension r; an infimum of heights
  alone would not have been sufficient. Empty intersections have no minimal primes.
- The empty family `s = ∅` gives the whole ambient scheme, which the item already
  requires smooth; `r=0` imposes codimension zero. The case `n=0` gives the empty divisor.

Recorded dependency declarations used:

- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`.
- `def-weil-regular-scheme`: `Mathlib.RingTheory.RegularLocalRing.Defs`,
  `IsRegularRing` (and its existing ring and local-ring definitions).
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`; quasi-compactness is
  `AlgebraicGeometry.QuasiCompact` from its imported QuasiCompact module.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`; divisor inclusions use the existing
  canonical `Scheme.IdealSheafData.subschemeι`, whose instance is a closed immersion.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`.
- `def-weil-pbc-scheme-reduction`: `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`,
  `Scheme.IdealSheafData.subscheme` and `subschemeι`, with `radical` from Basic and
  `comap` from Functorial. The recorded `nilradical` is `radical ⊥`; taking the
  radical of the defining ideal gives the same canonical reduced closed subscheme.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`.
- `def-nagata-effective-cartier-ideal`:
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`,
  `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible`. Its full current source
  and docstring were also confirmed with `scompile.py --source`.
- The added normal-crossings definition reuses
  `Sheaf.RingTheory.IsRegularSystemOfParameters`,
  `IsLocalRing.IsRegularSystemOfParameters` (def-weil-pbc-regular-system-of-parameters).
- The strict definition reuses `IsReduced` from Properties and `Ideal.height`
  and `Ideal.minimalPrimes` from Mathlib's ring-theoretic dimension API.

The main module publicly imports the two definition modules and the additional statement
interfaces. Statement interfaces for closed subschemes, reduction, integrality, finite type
and etale morphisms arrive through those public imports. Non-public imports retain the
available proof dependencies: Noetherianity, CartierDivisorNowhereDense, Blowup.Proper,
Blowup.Complement and Blowup.Density. Composition and base-change interfaces are already
imported by these modules. The proof-dependency nodes lem-trf-nc-maximal-branch-blowup,
lem-trf-permissible-boundary-preservation and lem-trf-regular-perfect-field-smooth have no
recorded Lean declaration in the base, so their absent modules are not imported. Their
proof uses remain explicit in the docstring. No dependency record requires repair.

Edge cases checked mathematically before writing: empty original divisor (identity
modification, empty final component family); dimension zero (empty parameter list, so only
the empty divisor); one smooth component (identity Cartier-centre blowup and empty old
strict transform); two crossing coordinate hyperplanes; global self-intersection of a nodal
component (local etale branch splitting, not global smoothness); three distinct lines
through a point in a surface (excluded by the triple codimension condition); empty component
intersections (smooth empty scheme and no minimal-prime height requirements); disconnected
intersections (all minimal primes tested); positive characteristic (no characteristic-zero
hypothesis); nonseparated finite-type schemes (no separatedness added); all universe u
schemes and their etale neighbourhoods (no independent smaller test universe).

Searches for an existing statement and both missing notions:

- `msearch.py ... leanfinder`: normal crossings strictification by a proper modification
  off the divisor returned eight normalization results, none strictifying a divisor.
- `msearch.py ... loogle '"normalCrossings"'`: zero hits.
- `msearch.py ... grep 'normalCrossing|normal_crossing|regularSystemOfParameters|RegularSystemOfParameters'
  AlgebraicGeometry`: zero hits.
- `msearch.py ... leansearch`: normal crossings effective Cartier divisor etale locally
  product of distinct regular parameters returned etale morphisms, etale loci and
  normalization, not a divisor predicate.
- `msearch.py ... leansearch`: reduced effective Cartier divisor with finite smooth
  irreducible components and intersections of pure expected codimension returned
  finite_irreducibleComponents_of_isNoetherian, IsReduced and elementary reducedness
  interfaces, not the divisor condition.
- `msearch.py ... leanfinder`: normal crossings divisors, etale-local product of regular
  parameters, strict smooth intersections returned standard smooth/etale presentations
  and etale loci, no divisor predicate.
- `msearch.py ... grep 'normalCrossing|normal_crossing|StrictNormalCrossing'
  AlgebraicGeometry`: zero hits.
- Direct `rg` in Mathlib/AlgebraicGeometry, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json found no normal crossings divisor definition or theorem.
  The requested literal blueprint-ID search in WeilConjectures also had no hits.
- Direct DAG searches found only theorem nodes using NC/SNC terminology, not a definition
  node for either predicate. `tools/blueprint_refs.py search 'normal crossings'` and
  `search 'strict normal crossings'` returned zero blueprint nodes. A separate regular
  parameter search found the existing definition node and module, which are reused.
- Full search output for the new notions is preserved in their `mathlib_searches` records.

No STATEMENT-DISPUTED flag, no source discrepancy, and no statement correction.

## New nodes

`def-trf-normal-crossings-divisor` owns
`Sheaf.AlgebraicGeometry.NormalCrossingsDivisor` and the predicate
`Scheme.IdealSheafData.IsNormalCrossingsDivisor`. It defines the missing etale-local
product-of-regular-parameters condition from ILO VIII 4.1.1--4.1.2, reusing the effective
Cartier ideal and regular parameter definitions. The searches above found no existing
DAG definition or Mathlib/project declaration. In particular, theorem nodes that mention
the condition do not supply a definition interface. Its new-node record stores the raw
service responses and the local search results.

`def-trf-smooth-strict-normal-crossings-divisor` owns
`Sheaf.AlgebraicGeometry.SmoothStrictNormalCrossingsDivisor` and the predicate
`Scheme.IdealSheafData.IsSmoothStrictNormalCrossingsDivisor`. It renders the explicit
finite smooth-component and pure-codimension intersection criterion of ILO VIII
Remark 4.2.2(i), with the smooth-over-field version supplied by Stacks 0B8X. Its finite
family is existential data inside a proposition, not an arbitrarily chosen construction.
No separate scheme-theoretic union, intersection, reduction, or height definition is
introduced. The searches above found only the basic finite-component/reducedness APIs,
not this condition; all responses are recorded on the new node. Both nodes inherit the
item's chapter, unit and blueprint ancestor, with the item prepended to their via chain.

Validation: `scompile.py NQ lem-trf-normal-crossings-strictification` with all three
modules completed successfully. The wrapper checked each sibling separately in dependency
order, including the private overlay and the server's sandbox/library confirmations.
There were no Lean errors or warnings. The required delivery dry run and final delivery
are performed by `deliver2.py` after this report is written; it repeats the per-file compile
and checks the packet with the server's stage-2 preflight. No global build or direct
repository write was performed.

The first dry run compiled cleanly and identified only a new-node citation-format issue:
two bracketed dependency IDs were grouped together in prose. They were split into separate
`[id]` citations; no Lean signature, definition, or mathematical statement changed.

## Second reading by NQ

Independent maintainer second reading, 2026-10-18. I read the immutable delivery
at a3b89b13f8422c29af9ce83642b22fa248e121b3, starting with packet.md, then the
three snapshot modules, the item and all eleven statement-dependency records.
This section records the independent review, not a second reading by the worker.

Sources actually read: ILO, Expose VIII 4.1.1--4.1.8, Remark 4.2.2(i)--(iii),
and Lemma 4.2.9 (printed pp.117--121, PDF pp.123--127); Stacks varieties.tex,
lemma-dense-smooth-open-variety-over-perfect-field, Tag 0B8X (lines 4730--4754).
The source algorithm decreases the depth of the old strict transform, not the
total boundary, and includes the final Cartier-center blowup. Over a perfect
field regular finite-type ambient schemes and strata are smooth. No source
correction or citer audit is needed: the item's mathematical statement stays intact.

Hypothesis and conclusion audit (all accepted):

- `(F : Type u) [Field F] [IsAlgClosed F]` is exactly the algebraically closed
  field; no characteristic restriction occurs.
- `(V : Scheme.{u}) (f : V ⟶ Spec (.of F))`, `[IsIntegral V]`,
  `[LocallyOfFiniteType f] [QuasiCompact f]` give the integral finite-type
  F-scheme, with no separatedness assumption. `IsIntegral` includes nonemptiness.
- `hV` uses exactly the affine-neighborhood regularity clause of the recorded
  regular-scheme dependency. `IsRegularRing` includes Noetherianity. No stronger
  global affine or projective hypothesis has been introduced.
- `Z : V.IdealSheafData` has its canonical closed immersion. Its normal crossings
  predicate explicitly requires `Z.IsInvertible`, the recorded affine-local
  nonzerodivisor condition, and an etale neighborhood above every point.
  The ideal is extended along the actual germ map of an affine neighborhood.
  The reused parameter-list predicate generates the maximal ideal with length
  equal to Krull dimension. Such a list is minimal and has no repetitions;
  `s.Sublist t` therefore selects distinct parameters. Equality of generated
  ideals permits unit changes of a local equation. This allows self-intersections
  of global components and imposes no global branch labeling.
- The existential `V₂`, `f₂`, `q` has all required clauses: integrality,
  smoothness, finite type as LFT plus QC, `q ≫ f = f₂`, `IsProper q`,
  `IsIso (q ∣_ Z.support.compl)`, and the explicit `Dense` inverse-image open.
  Mathlib's restricted morphism has exactly the inverse-image open as domain.
- `((Z.comap q).radical)` is the canonical reduced scheme-theoretic inverse
  image: `comapIso` identifies its unreduced subscheme with the pullback, and
  radical takes the radical ideal on every affine open. No arbitrary boundary
  with matching support is substituted.
- In the delivered SNC predicate the finite family of integral closed subschemes,
  pairwise noncontainment, and equality of the finite ideal infimum with D give
  exactly the reduced irreducible components and their union. `s.sup C` is the
  sum ideal of their scheme-theoretic intersection. Smoothness for singleton
  subsets gives smooth components; all finite subsets give all intersections.
  Every minimal prime is tested for height, so the condition is pure codimension,
  not merely a minimum over components. This is the explicit source criterion.
- For landing, the conclusion instead reuses the already landed
  `Scheme.IdealSheafData.IsStrictNormalCrossingsDivisor` from
  `Sheaf.AlgebraicGeometry.StrictNormalCrossingsDivisor`
  (def-trf-strict-normal-crossings-divisor). I read its full definition and node.
  On the smooth finite-type V₂ the pointwise equation
  `dim O_(V₂,z) = dim O_(C_J,z) + |J|` is equivalent to every intersection
  component having codimension |J|: regular local rings give this dimension
  formula for regular closed subschemes. Distinct integral codimension-one
  components cannot properly contain one another. Radical D and equality of
  the union of supports give the same reduced scheme-theoretic union. Thus
  this reuse changes no hypothesis or conclusion, including empty cases.

Dependency interfaces actually opened: Mathlib's `IsIntegral` and `IsReduced`
(Properties.lean), `IsRegularRing` and `IsRegularLocalRing`
(RegularLocalRing/Defs.lean), `LocallyOfFiniteType`, `QuasiCompact`,
`IsClosedImmersion`, `Smooth`, `Etale`, and `IsProper` in their recorded
morphism modules; `IdealSheafData.subscheme`, `subschemeι`, `radical`,
`Scheme.nilradical`, `comap`, `comapIso`, finite `ideal_iInf` and `ideal_sup`;
upstream `IdealSheafData.IsInvertible`; and the side module
`Sheaf.RingTheory.IsRegularSystemOfParameters`. Their signatures have the
needed domains and universes. The properness definition supplies QC through
universally closedness; the smooth/etale definitions are the recorded notions,
not formal smoothness of a local ring. No dependency-interface repair is needed.

The proof docstring follows all eight node steps: Cartier density and
Noetherianity; the initial old/total/exceptional boundaries; the maximal-depth
center and proper blowup off the center; permissible boundary preservation;
density and integrality; termination with empty old transform; proper
composition and reduced inverse-image identification; and regular-to-smooth
over the perfect field. Its unavailable geometric proof interfaces remain
named proof dependencies, not extra hypotheses. There is exactly one theorem,
with proof `by sorry`; both delivered definitions are explicit propositions
without holes, choices, or local proofs. All declarations have source-place and
blueprint docstrings, and no line exceeds 100 characters.

Edge cases: empty Z uses the unit ideal and an empty parameter sublist; the
identity modification is allowed. In dimension zero the parameter list is empty,
so only the empty divisor occurs. One smooth component, xy=0, a globally nodal
component, and positive characteristic are covered. Three lines through the
origin of a surface are excluded by the |J|=3 codimension requirement. Empty
intersections impose no pointwise codimension equation; disconnected
intersections test every component. The empty component family has empty union;
the empty intersection is the already smooth ambient scheme. The empty ambient
scheme is excluded exactly by integrality. The universe u is arbitrary and is
shared with all etale neighborhoods, stalks, fields and output schemes; there
is no smaller independent test universe or silent universe equality repair.

Independent searches: direct case-insensitive rg for normal crossings, simple
normal crossings, SNC divisors and strictification in Mathlib algebraic geometry,
both upstream source trees, the group's lean/Sheaf tree, and lean_names_upstream.
Loogle query `"normalCrossings"` returned no hits. LeanSearch for an etale-local
product of distinct parameters and strictification by strata returned etale
localization/locus and formal-etale facts, not the desired divisor definition or
theorem. The worker's recorded three kinds of searches were also read.
The current group clone contains the landed Q119 strict-normal-crossings
predicate mentioned above, absent from this delivery's extracted snapshot.
That is a landing-time H4/H12 duplicate, repaired by reuse, not a mathematical
error in the delivered formula. The normal-crossings hypothesis has no duplicate
found and its new definition node remains necessary. Its statement, dependency
citations, source, blueprint ancestry, empty proof arrays, search records,
creation fields and Lean record satisfy the new-node requirements.

Findings and complete fixes:

1. H4/H12 at landing: drop new node
   `def-trf-smooth-strict-normal-crossings-divisor` with merge_delivery.py's
   `--drop-nodes` option. This also omits its sole module and removes its item
   dependency. The complete replacement theorem module and Lean record import
   and use the landed `IsStrictNormalCrossingsDivisor` predicate. No new alias
   or second definition remains. The node id of that existing interface is
   recorded explicitly in lean.note above.
2. H1/H11: the original second-reading section contained only a disclaimer.
   This complete replacement report preserves the Worker report and supplies
   the actual independent clause-by-clause reading here.

The three immutable Lean signatures were compared programmatically against
lean.statement and are verbatim identical. The corrected theorem's complete
Lean record contains its replacement signature verbatim as well.

Compiler evidence: the prescribed scompile.py invocation on all three immutable
modules exited 0 with no errors or warnings, checking the private dependency
overlay and separate sandbox/library versions of each file under the 60-second
per-file limit. The corrected theorem was additionally compiled with the retained
normal-crossings sibling and the landed SNC dependency; the canonical module-path
repeat also completed cleanly. The installed scompile.py currently performs the
side-overlay and confirmation on the server, rather than on the launcher host;
these are its normal wrapper operations. No direct ssh command, global build,
live Lean edit, git mutation, claim, merge, or delivery was performed by this review.

Verdict: FIX. Apply this fixes directory together with
`--drop-nodes def-trf-smooth-strict-normal-crossings-divisor`.

Final compiler check (2026-10-18):

```
python3 /home/ubuntu/weil-launcher-nt/scompile.py NQ lem-trf-normal-crossings-strictification snapshot/lean/Sheaf/AlgebraicGeometry/NormalCrossingsDivisor.lean fixes/lean/Sheaf/AlgebraicGeometry/NormalCrossingsStrictification.lean
```

Exit 0; retained dependency overlay 2.5 s, preliminary dependency 2.4 s,
sandbox/library dependency 2.5/2.6 s, sandbox/library corrected theorem 2.5/2.7 s.
No errors or warnings. The immutable three-file run also exited 0; its final
sandbox/library theorem checks took 3.7/6.2 s. The replacement signature check
passed verbatim, with exactly one theorem `sorry` and all Lean lines at most
100 characters. No pro-etale replacement or unrelated construction is involved.
All writes made for this review are review.md and the three permitted fixes.
