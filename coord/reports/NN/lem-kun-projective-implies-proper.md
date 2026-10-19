## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper` states
`AlgebraicGeometry.hProjective_properness`, with exactly one theorem and a `sorry` proof.
The node is unchanged except for `lean`. No new notions, dependency modules, or statement
corrections are needed.

Clause-by-clause correspondence:

- “Every projective morphism is proper”: the first conjunct universally quantifies schemes
  `X Y : Scheme.{u}` and their morphism `f`, and states `IsHProjective f → IsProper f`.
  `IsHProjective` is the exact finite projective-space embedding convention recorded by
  `def-kun-projective`; using the separate stronger `IsProjective` class would add an
  unwanted quasi-compactness hypothesis. No base field, Noetherianity, or finite-type
  hypothesis is added. Properness itself includes finite type.
- “The structural morphism P^N_Y → Y is proper”: the second conjunct quantifies `N : ℕ`
  (precisely the integer N ≥ 0) and any scheme `Y`, and states
  `IsProper (ℙ(ULift.{u} (Fin (N + 1)); Y) ↘ Y)`. The recorded projective definition uses
  precisely this space, with N+1 homogeneous coordinates. `ULift` changes only its universe.
  `ProjectiveSpace.over` makes the displayed structure morphism the first pullback projection.
- “Closed immersions are proper”: the third conjunct quantifies any `i : X ⟶ Y` and states
  `IsClosedImmersion i → IsProper i`, without a projectivity hypothesis.
- “The class of proper morphisms is closed under composition”: the fourth conjunct
  quantifies any composable `f : X ⟶ Y`, `g : Y ⟶ Z` and states
  `IsProper f → IsProper g → IsProper (f ≫ g)`. Lean's `f ≫ g` denotes g ∘ f.

All variables and the universe `u` are explicitly bound. The four assertions are conjoined
rather than putting the three parenthetical facts only in a docstring.

Dependency declarations read and used:

- `def-kun-projective`: `Sheaf.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsHProjective` and its `exists_closedImmersion` field. The full class
  signature and docstring give ∃ n, a closed immersion into ℙ(ULift (Fin (n+1)); S),
  with composite equal to f. This is the node's actual recorded declaration, not a copy.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`. Its signature extends separated, universally closed, and
  locally finite type; universal closedness supplies quasi-compactness, hence finite type.
  The recorded separated and universally closed classes were also read: the former asks
  for a closed diagonal, the latter for closed maps after all base changes.
- `def-nagata-projective-space-base-change` and
  `lemma-nagata-projective-space-base-change-proper`:
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`,
  `AlgebraicGeometry.ProjectiveSpace`, `.over`, and `.instIsProper`.
  The actual definition is the pullback of the integral Proj model along the unique map
  to the terminal scheme; `.over` is the first projection and `.instIsProper` assumes
  only `[Finite n]` for the homogeneous-coordinate type.
- `lem-weil-pbc-closed-immersion-proper`: the Mathlib match
  `AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono` in
  `Mathlib.AlgebraicGeometry.ZariskisMainTheorem`, read in full with its doc context.
  Its forward implication gives properness of each closed immersion.
- `lem-weil-pbc-proper-composition`: the Mathlib match
  `AlgebraicGeometry.IsProper.instCompScheme` in
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`, with hypotheses `[IsProper f] [IsProper g]`
  and conclusion `IsProper (f ≫ g)`.

The module imports the statement dependencies publicly and the additional proof-only
Zariski's Main Theorem module privately. The docstring contains the node's entire proof
route: choose the embedding, apply properness of the projective-space projection and the
closed immersion, then compose and use the factorization equality.

Edge cases checked: N = 0 is retained (`Fin 1`, giving the relative projective 0-space).
Empty source and empty target schemes are not excluded. There is no nonemptiness condition
on schemes, no characteristic restriction, and no assumption that the base is affine or
Noetherian. The projective-space coordinate set is finite by construction and is nonempty
for exactly the N+1 convention of this node. The immersion and composition clauses apply
to arbitrary schemes independently of projectivity. Arbitrary scheme universes are
covered by `universe u`, with the coordinate type lifted to that same universe.

Searches performed through `msearch.py NN lem-kun-projective-implies-proper`:

- LeanFinder, “Every projective morphism of schemes is proper”: eight results, including
  `Scheme.Hom.isProperMap`, `IsProper`, its parent projections, properness of finite
  morphisms, and properness of `Proj.toSpecZero`. No result states the theorem for
  `IsHProjective`.
- Loogle, `AlgebraicGeometry.IsProper`: twelve hits, including composition and base-change
  instances and finite-implies-proper; none states the projective implication.
- LeanSearch, “Every projective morphism of schemes is proper”: unavailable with an
  Internal Server Error; no absence inference is drawn from that service failure.
- Mathlib grep, `IsHProjective|IsProjective|projective.*proper`, subdirectory
  `AlgebraicGeometry/`: zero hits. Direct `rg` for `IsHProjective|IsProjective` in the
  available Mathlib algebraic-geometry source also found none.
- `rg` in the upstream `WeilConjectures`, side `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `IsHProjective`, proper/projective combinations,
  and the node id: the side project supplies the projective class; the upstream source
  supplies the projective-space properness instance, but no projective-morphism theorem.
  The name index mentions `AlgebraicGeometry.IsHProjective.isProper`, but that declaration
  is absent from the available upstream source, so its metadata is not evidence of an
  available reusable declaration. The available projective-space instance only handles
  the projection and is not the whole four-clause node statement.
- The same upstream search for the literal node id found no declaration for this item.
- Direct `rg` over Mathlib, upstream, and the side library for the new declaration name
  `hProjective_properness` found no collision.

Source read: the node's full blueprint file in `sk-prop-sf-kunneth-ordinary`, lemma order
1708, agrees with the node's statement and factorization proof. No node faults or
STATEMENT-DISPUTED issues were found.

Validation: `scompile.py` compiled the delivered module cleanly on the server (1.4 s;
nice 19; two threads; 60-second per-file limit). `deliver2.py --no-push` printed OK:
the commit compiles and passes preflight except for the independent second reading,
which the second reader supplies. Nothing was pushed. No proof was attempted and no
local Lean compiler or library build was used.


## Second reading by NN

I independently opened the item JSON, the delivered Lean file, both statement-dependency
nodes, all five proof-dependency nodes and their actual declaration sources. I read the
blueprint lemma (order 1708), its unit introduction, and Stacks `morphisms.tex`, Section
Projective morphisms, Definition 01W8 and Lemma 01WC with its proof. The Stacks section
introduces arbitrary schemes and imposes no standing field, characteristic, finite-type
base or Noetherian assumption. Stacks 01WC proves the more general locally projective
case; the node explicitly uses the finite-space H-projective convention from its dependency.
The unit's coefficient and field hypotheses concern its cohomology target, rather than
restricting this general geometric lemma.

My object/hypothesis/conclusion checklist, matched against the actual signature:

1. Objects: arbitrary schemes X and Y, and a scheme morphism f : X → Y. Rendered by
   `∀ {X Y : Scheme.{u}} (f : X ⟶ Y)` in the first conjunct. Verdict: exact; no additional
   structures or base schemes are required.
2. Hypothesis: f is projective in `def-kun-projective`'s convention. Rendered by
   `IsHProjective f`. I opened `Sheaf.AlgebraicGeometry.Morphisms.Projective` and checked
   `IsHProjective.exists_closedImmersion`: it supplies n : ℕ, a closed immersion into
   `ℙ(ULift.{u} (Fin (n + 1)); Y)`, and `i ≫ projection = f`. This is exactly the dependency
   node's definition. Verdict: exact, with no private replacement. The worker's description
   of `IsProjective` as stronger refers to its extra explicit class field; quasi-compactness
   is in fact a consequence of H-projectivity, so it is not a mathematical extra restriction.
   Using the recorded `IsHProjective` declaration here is nevertheless the correct interface.
3. Conclusion for f: properness, rendered by `IsProper f`. I read the recorded Mathlib
   definition: separated, universally closed and locally of finite type. `IsSeparated`
   requires the closed diagonal; `UniversallyClosed` quantifies closedness after arbitrary
   base change and implies `QuasiCompact` (the instance at UniversallyClosed.lean:167).
   Consequently this is precisely separated, finite type and universally closed as in
   `def-weil-proper-morphism`. Verdict: exact; no finiteness hypothesis is omitted.
4. Parenthetical projective-space clause: arbitrary N ≥ 0 and arbitrary base Y, with the
   structural map P^N_Y → Y proper. Rendered by the second conjunct,
   `∀ (N : ℕ) (Y : Scheme.{u}), IsProper (ℙ(ULift.{u} (Fin (N + 1)); Y) ↘ Y)`.
   I read `ProjectiveSpace`, its `over` instance and `instIsProper` in the upstream module:
   the space is the pullback of the integral polynomial Proj, and this structural morphism
   is exactly the first projection. The coordinate type has N+1 elements, not N elements.
   Verdict: exact, in the quantifier order of the node's proof; no field base is substituted.
5. Parenthetical closed-immersion clause: arbitrary schemes and closed immersion i : X → Y
   imply properness of i. Rendered by the third conjunct,
   `∀ {X Y : Scheme.{u}} (i : X ⟶ Y), IsClosedImmersion i → IsProper i`.
   I opened the recorded `IsClosedImmersion.iff_isProper_and_mono` declaration in
   Mathlib's Zariski's Main Theorem module: its forward first component is this assertion.
   Verdict: exact; the conclusion does not ask the target scheme to be proper.
6. Parenthetical composition clause: arbitrary X, Y, Z and composable proper f and g have
   proper composite. Rendered by the fourth conjunct,
   `∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
   IsProper f → IsProper g → IsProper (f ≫ g)`.
   I read the proper-composition instance in Mathlib's Proper module; its hypotheses and
   composite are identical. Verdict: exact; `f ≫ g` is g ∘ f.

Edge cases: N = 0 gives one homogeneous coordinate (`Fin 1`) and is included. Empty
source, empty target and empty base schemes are allowed throughout; no inhabitedness
hypothesis appears. The zero ring is permitted in affine bases. There is no characteristic
restriction. An empty homogeneous coordinate set is not one of the classical P^N spaces
for N ≥ 0 and therefore need not be added to the second conjunct (the upstream finite-index
properness theorem also covers it). `universe u` is arbitrary, and `ULift.{u}` makes the
finite coordinate type live in the scheme universe without restricting its cardinality.
There is no independently smaller test-object universe or index-universe issue. Every
binder and universe is explicit, and no hidden section hypothesis enters the theorem.

Independent duplicate searches, with queries different from the first reader's:

- `msearch.py NN lem-kun-projective-implies-proper leanfinder` with
  "A morphism factoring through a closed immersion into finite dimensional projective
  space is proper": eight hits, including Proj properness and finite-morphism properness,
  but no H-projective implication or four-clause statement.
- The same wrapper's Loogle query `AlgebraicGeometry.IsProper`: twelve hits, including
  composition and base change, but no complete match.
- Its LeanSearch query "An H-projective morphism of schemes is proper": service returned
  Internal Server Error. This supplies no evidence of absence.
- Direct `rg` over Mathlib algebraic geometry, upstream `WeilConjectures`, and the side
  `lean/Sheaf` for `IsHProjective`, projective/proper combinations in both orders, the item
  id and `hProjective_properness`. I inspected the exact H-projective occurrences: the
  side library defines the class and uses it in base-change statements; the available
  upstream tree does not declare it or its properness theorem. The name-index entry
  `AlgebraicGeometry.IsHProjective.isProper` is metadata for a source unavailable here,
  not a declaration in the pinned tree. The upstream projective-space properness instance
  proves only the projection clause. No usable existing full statement or name collision
  was found, so retaining the new theorem is appropriate.

No mathematical or Lean mismatch was found, and no Lean or node changes were needed.
There are no new definition nodes, dependency modules, statement corrections or disputed
statements in this delivery. I verified the imports against the dependency records, the
source and blueprint tags in both docstrings, and the theorem docstring's complete proof:
choose the embedding, identify its projection, apply projective-space and closed-immersion
properness, compose, then transport along the factorization equality. The final sentence
also accounts for the other three conjuncts. The file contains one named theorem with
whole proof `sorry`, no data definition, no proof attempt, and no file-local notation or
instances. The node's `lean.statement` is verbatim the file's signature.

Second-reader validation: `scompile.py` compiled the delivered file cleanly on the
server in 1.3 seconds (nice 19, two threads, 60 seconds per file); its required side
dependency also compiled in 1.2 seconds. `deliver2.py --no-push` printed OK, confirming
preflight and compilation with the independent second reading included.
