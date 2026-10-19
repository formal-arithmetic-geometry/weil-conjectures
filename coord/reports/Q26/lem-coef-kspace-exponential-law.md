## Worker report

The module `lean/Sheaf/Topology/KSpaceExponentialLaw.lean` states
`CompactlyGenerated.exists_compactTestCurry`, with `sorry` as its only theorem proof.
Three real helper definitions encode the constructions introduced within this very
node: the compact-test function topology, its continuous-function subspace, and a
bundling of Mathlib's existing kification topology. They are all listed in
`lean.declarations`; no other DAG statement is introduced or changed. Every helper
and the theorem has a source/blueprint docstring. There is no hollow data and no
proof supplied at stage 2.

I opened Hovey's source PDF online, Definition 2.4.21 and Proposition 2.4.22(1),(5),
printed pp. 57–58 (zero-based PDF page 67 for Proposition 2.4.22). The source
uses Kelley spaces without weak Hausdorffness for clause (5); its later clause (6)
adds weak Hausdorffness. The node accurately uses clause (5). The project unit is
not itself this foundational statement, and no statement correction is needed.
The node has no proof steps; the theorem docstring supplies a full natural-language
proof plan using compact tests, the tube lemma, and evaluation on compact Hausdorff
domains. The source refers to Lewis, Appendix, for its proof.

Hypothesis and clause correspondence:

- For an arbitrary topological space T, `TopCat.kification T` retains its carrier
  and supplies `TopologicalSpace.compactlyGenerated.{u} T`. I read that declaration
  and its docstring in `Mathlib.Topology.Compactness.CompactlyGeneratedSpace`:
  its coinduced topology is exactly the topology tested by continuous maps from
  compact Hausdorff spaces. No replacement definition of k-topology is made.
- X, Y, Z are k-spaces: all are quantified as `CompactlyGenerated.{u, u}`.
  I read its structure and docstring in `Mathlib.Topology.Category.CompactlyGenerated`.
  Its sole property is `UCompactlyGeneratedSpace.{u}` on the underlying topological
  space, whose signature and docstring I also read. This means equality with the
  compact-test topology by `eq_compactlyGenerated`. Despite the name, Mathlib does
  not include weak Hausdorffness in this structure. The universe is explicit and
  arbitrary; spaces and all compact test spaces lie in one common universe u,
  as do their products and mapping-space carriers.
- The set of all functions from Y to Z is literally `(Y → Z)` in
  `TopCat.compactTestFunctionTopology`. Its topology is `generateFrom` of the sets
  `{f | ∀ c : C, f (a c) ∈ U}`, for `C : CompHaus.{u}`, `a : C(C,Y)`, and `IsOpen U`.
  This is precisely `f(a(C)) ⊆ U`; it is not the possibly different collection of
  all compact subsets of a non-Hausdorff Y. The empty test space is included.
- `TopCat.compactTestMapSpace Y Z` has underlying set
  `{f : Y → Z // Continuous f}`. It uses the recorded dependency
  `instTopologicalSpaceSubtype` explicitly with `compactTestFunctionTopology Y Z`
  as ambient topology. Its opens are therefore the intersections with that
  subtype required by the node. The continuity predicate on f uses the original
  topologies of Y and Z, not the newly constructed topology on function space.
- The left-hand side of E is
  `C(TopCat.kification (TopCat.of (X × Y)), Z)`. The type-level product receives
  the ordinary product topology before kification. There is no categorical
  product topology or hidden separation requirement.
- The right-hand side is
  `C(X, TopCat.kification (TopCat.compactTestMapSpace Y.toTop Z.toTop))`.
  Thus kification applies after taking the continuous-function subspace.
- E is an `Equiv`, expressing bijectivity. Its first clause
  `(E X Y Z h x).val y = h (x,y)` forces exactly currying. The existentially
  quantified family is uniquely determined by this formula, including its
  inverse, rather than an unconstrained equivalence.
- Naturality is the second clause, for arbitrary continuous
  `a : C(X',X)`, `b : C(Y',Y)`, `c : C(Z,Z')` between six arbitrary k-spaces.
  It gives the continuous composite `h'` with formula
  `h'(x,y) = c(h(a(x),b(y)))` and asserts
  `(E X' Y' Z' h' x).val y = c((E X Y Z h (a x)).val (b y))`.
  The defining equation uniquely specifies h', and the final equation is exactly
  the commuting naturality square. In particular it also certifies continuity
  of the resulting family on the right by identifying it with `E ... h'`.
- There are no Hausdorff, weak Hausdorff, local compactness, nonemptiness,
  inhabitedness, or basepoint assumptions on X, Y, or Z.

Recorded statement dependency used: `def-kun-subspace-topology` is recorded as
`Mathlib.Topology.Defs.Induced`, declaration `instTopologicalSpaceSubtype`.
I opened its exact declaration in the source: the subtype topology is
`induced (↑) t`. The module imports this dependency publicly and uses this instance
explicitly. There are no proof dependencies to import.

Edge cases checked mathematically: for X empty both hom sets are singleton; for
Y empty the internal mapping space is singleton and both hom sets again are
singleton; for Z empty and X,Y both nonempty both hom sets are empty. For Y empty
and Z empty the unique empty-domain function remains included. Singleton spaces
reduce to the expected mapping identities. Indiscrete and other non-Hausdorff
k-spaces are allowed: no compact subset is silently treated as Hausdorff. Empty
compact test spaces add only the whole function set as a generator. The ordinary
product is allowed not to be a k-space, since it is explicitly kified.

Searches for existing definitions/statements (all before writing):

- `msearch.py ... leanfinder "Exponential law for compactly generated k spaces
  with compact Hausdorff test mapping topology"`: 8 hits including
  `Homeomorph.curry`, `continuous_from_compactlyGeneratedSpace`, and condensed
  adjunctions. Reading the source signatures showed no match: Homeomorph.curry
  requires local compactness of both factors; condensed adjunctions are different
  statements. The compact-generation declarations are reused here.
- `msearch.py ... loogle "CompactlyGeneratedSpace, ContinuousMap, curry"`: no
  hits, reporting unknown identifier curry. This is recorded as an unsuccessful
  search, not evidence of nonexistence by itself.
- `msearch.py ... leansearch "Exponential law Kelley k-spaces compact test topology
  on continuous maps"`: 8 hits including `ContinuousMap.compactOpen`, evaluation,
  and compact-generation criteria. I read compactOpen and the curry/uncurry
  signatures in `Mathlib/Topology/CompactOpen.lean`. CompactOpen uses every compact
  subset, whereas the node uses images of compact Hausdorff tests; uncurry needs
  a locally compact second factor. Neither is this statement.
- `msearch.py ... grep "compactlyGenerated|compact.*[Tt]est|exponential"
  Topology/Compactness`: 6 hits, locating the existing compactly generated space
  definitions. Their full source was read. Mathlib's category file explicitly
  lists Cartesian closure as TODO.
- `rg` of Mathlib topology/category sources for `compactlyGenerated|kification|
  Kification|compactTest|compact-test` found no bundled kification or test mapping
  space. `TopCat.kification` only wraps the existing topology in `TopCat.of`.
- `rg` of upstream `WeilConjectures` for `exponential|compactlyGenerated|kification|
  Kification` found unrelated algebraic exponential declarations, no match.
  The prescribed grep for the exact node id returned none. `rg` of
  `dag/lean_names_upstream.json` returned no binding for this notion or the
  proposed declaration names.
- `rg` of `lean/Sheaf` for the same topology terms found the realization statement
  that mentions Mathlib kification and the Serre-model modules, but no exponential
  law or compact-test mapping-space definition. A final exact-name search of
  Mathlib, upstream, and Sheaf found none of the four proposed names.

No statement dispute or unusable dependency was found. All declarations are
owned by this node and all variables/universes are explicitly bound. The final `scompile.py` check compiled both the sandbox and library views cleanly
(about 1.1 and 1.2 seconds respectively), with no warnings. The required
`deliver2.py --no-push` check is the final validation step; its outcome is reported
in the worker handoff.

## Second reading by Q26

I independently read the node `lem-coef-kspace-exponential-law`, its source place, the
recorded dependency `def-kun-subspace-topology`, and the complete module
`Sheaf.Topology.KSpaceExponentialLaw`. The source is Hovey, Definition 2.4.21 and
Proposition 2.4.22(5), printed p. 58 (PDF p. 68). Hovey's clause (5) is explicitly for
`X,Y,Z ∈ K`, where `K` is the category of Kelley (k-)spaces; weak Hausdorffness is only
added for the separate category `T` and clause (6). Thus the node correctly imposes no
weak-Hausdorff assumption.

The node's objects and hypotheses match the Lean as follows.

- The ambient arbitrary space `T` and its kification `kT` are rendered by
  `TopCat.kification (T : TopCat.{u})`, whose carrier is unchanged and whose topology is
  `TopologicalSpace.compactlyGenerated.{u}`. Mathlib's definition is the coinduced
  topology from all continuous maps `C → T` with `C : CompHaus.{u}`, exactly the
  compact-test topology in the node.
- The three k-spaces `X,Y,Z` are the explicitly universe-polymorphic
  `CompactlyGenerated.{u,u}` objects. This is Mathlib's k-space structure
  `UCompactlyGeneratedSpace.{u}` and imposes no Hausdorff, local compactness,
  nonemptiness, or inhabitedness hypothesis. The common universe is the ordinary
  universe parameter of the category `K`, and is arbitrary.
- The all-function space `Z^Y` is the carrier `(Y → Z)` in
  `TopCat.compactTestFunctionTopology Y Z`. Its `generateFrom` generators are exactly
  `{f | ∀ c : C, f (a c) ∈ U}` for `C : CompHaus.{u}`, continuous `a : C(C,Y)`, and
  open `U ⊆ Z`; this is precisely Hovey's `S(a,U) = {f | f(a(C)) ⊆ U}`.
- The subset `C(Y,Z)` of continuous maps is rendered by
  `TopCat.compactTestMapSpace Y Z`. It uses the recorded Mathlib declaration
  `instTopologicalSpaceSubtype` and therefore has the induced subspace topology,
  with opens `S(a,U) ∩ C(Y,Z)` as required.
- The source's ordinary product before kification is rendered by
  `TopCat.of (X × Y)` followed by `TopCat.kification`; no categorical product or
  separation condition is introduced.
- The source's `Hom(Y,Z) = kC(Y,Z)` is rendered by
  `TopCat.kification (TopCat.compactTestMapSpace Y.toTop Z.toTop)`. The two hom sets
  are exactly the continuous-map types on the two sides of the asserted bijection.
- The existential `E` is an equivalence for every triple of k-spaces. Its first
  conjunct says pointwise `(E X Y Z h x).val y = h (x,y)`, exactly the currying formula.
  The second conjunct quantifies arbitrary k-spaces `X',Y',Z'`, arbitrary continuous
  `a : X' → X`, `b : Y' → Y`, `c : Z → Z'`, and arbitrary `h`; it supplies the
  continuously induced `h'` with the exact pre/postcomposition formula and states the
  pointwise naturality equation. The quantifier order and both clauses agree with the
  node. The formula determines `h'` uniquely, so the existential does not weaken the
  naturality assertion.

I checked Hovey's source text directly: Definition 2.4.21(4) defines `kX` by compactly
open sets, and Proposition 2.4.22(5) defines the same compact-test subbasis and asserts
`K(k(X × Y), Z) ≅ K(X, Hom(Y,Z))` naturally for all `X,Y,Z ∈ K`. The Lean statement
therefore has every source hypothesis and conclusion, with no added hypothesis or
weakened clause.

Edge cases checked independently are empty `X`, `Y`, or `Z`, empty compact test spaces,
zero/singleton function sets, singleton spaces, and non-Hausdorff k-spaces (including the
indiscrete/Sierpinski cases). The definitions and equivalence statement include all of
these. The ordinary product may fail to be a k-space, as required, because it is
explicitly kified. No characteristic, finiteness, local compactness, or basepoint
condition is present or needed.

I repeated the three required existing-notion searches (LeanSearch, Loogle/LeanFinder,
and `rg` over Mathlib, `WeilConjectures`, `lean/Sheaf`, and the upstream-name index).
The only relevant declarations were Mathlib's compactly generated-space structure,
`TopologicalSpace.compactlyGenerated`, and `instTopologicalSpaceSubtype`; none states
this exponential law or defines either compact-test mapping-space helper. The dependency
record is usable exactly as recorded, so no dependency repair or new definition node is
needed.

No mismatch was found. I changed no Lean declaration or node field. The statement in the
node's `lean.statement` is verbatim the theorem signature in the module, and the required
single-file `scompile.py` check passes for both sandbox and library views with no
warnings.
