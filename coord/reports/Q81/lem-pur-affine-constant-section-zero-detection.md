## Worker report

The module `Sheaf.AlgebraicGeometry.AffineConstantSectionZeroDetection` states
`AlgebraicGeometry.Etale.affine_constant_section_zero_detection`, with one named
`sorry` and the complete five-step proof in its docstring. No theorem is proved.
Only the item's `lean` record changes; its statement and accepted split are preserved.
There are no new DAG nodes or dependency repairs.

The two supporting declarations belong to the same node:
`affineConstantSections` abbreviates evaluation of the recorded constant abelian
sheaf at the terminal object of the ordinary small étale site;
`affineConstantSectionPullback` constructs the actual section pullback. It is the
inverse-image adjunction unit followed by the pushforward of
`Scheme.upperStarConstantSheafIso` and the existing terminal-object pushforward
comparison. Its data contain no sorry or arbitrary choice. In particular, it is
not defined by choosing a merely constant-preserving additive equivalence.

Clause-by-clause reading:

- Any scheme S is `(S : Scheme.{u})`, with no Noetherian, separatedness,
  connectedness, nonemptiness or field hypothesis.
- Any dimension is `(d : ℕ)`, including zero. The space is exactly
  `AffineSpace (ULift.{u} (Fin d)) S`, the recorded definition; projection is
  `AffineSpace (ULift.{u} (Fin d)) S ↘ S`.
- The zero section is the published `AffineSpace.zeroSection`, whose definition
  is `homOfVector (𝟙 S) 0`, hence sends every coordinate to zero.
- Arbitrary abelian coefficients are `(E : Type (u + 1)) [AddCommGroup E]`.
  This is the standard large coefficient convention of the recorded inverse-image
  interface. There is no finite, torsion or topological coefficient assumption.
  The single arbitrary universe u can be enlarged to accommodate any scheme and
  coefficient set; it imposes no bound on cardinality or finiteness.
- The constant sheaf is literally `constantSheaf T.smallEtaleTopology
  AddCommGrpCat.{u+1}` applied to `AddCommGrpCat.of E`; global sections evaluate
  at `⊤_ T.Etale`, the identity étale object. This is sheafification of the constant
  presheaf, not a topological sheaf substituted for the étale one.
- The first conjunct gives an additive equivalence φ between these actual global
  section groups, with its forward hom equal to projection pullback and its inverse
  hom equal to zero-section pullback. Thus both inverse identities and both
  isomorphism assertions are included, for the specified canonical maps.
- The second conjunct quantifies over every `LocallyConstant P E` and every point
  x and states exactly `b x = b (e (p x))`. Function extensionality gives
  `b = (b ∘ e) ∘ p`. Mathlib's `LocallyConstant` is precisely the open-fibre/local
  neighbourhood condition used by the recorded Stacks 03P5 section comparison.
- The third conjunct quantifies over every scheme `S'` in the same scheme universe
  and every `g : S' ⟶ S`. Its two equalities in AddCommGrpCat are the naturality
  squares for projection and zero-section pullbacks, using the existing
  `AffineSpace.map (ULift (Fin d)) g`. In category composition order these are
  p* followed by h* = g* followed by p'*, and h* followed by e'* = e* followed by g*.
- The final conjunct uses `(A : Type (u+1)) [CommRing A]` and a unit in
  `LocallyConstant P A`, whose pointwise ring structure is Mathlib's. Under the
  canonical Stacks 03P5 identification of constant-ring sections with locally
  constant functions this is exactly a unit section of A_P. Its hypothesis says
  restriction along e is identically 1; its conclusion `b = 1` is equality of units.
  Multiplication, inversion and the section 1 are pointwise under this canonical
  identification, so this clause is the node's stated unit-section special case.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace`, its canonical `over`,
  `coord`, and `map`; `WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace`:
  `AffineSpace.zeroSection`, `zeroSection_over`, `zeroSection_appTop_coord`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`,
  whose body is `Functor.const ⋙ presheafToSheaf`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`, `smallEtaleTopology`.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction`, imported through the published constant-sheaf API.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`,
  `upperStarLowerStarAdjunction`, `lowerStar`, `lowerStarCompSheafSectionsTerminalIso`.
- `WeilConjectures.ConstructibleSheaf.Defs`:
  `Scheme.upperStarConstantSheafIso`; it is the uniqueness-of-left-adjoints
  isomorphism for the two constant-sheaf adjunctions, not an arbitrary isomorphism.
- `Sheaf.Paper.ConstantSheafSectionsLocallyConstant`:
  `AlgebraicGeometry.constantSheaf_sections_locallyConstant`, including its
  normalization on the sheafification unit. This imported dependency gives the
  canonical locally constant section model used in the proof and equivalent clause.
- The additional recorded proof dependency is imported from
  `WeilConjectures.AlgebraicGeometry.EtaleConstantSheafPullbackUnitContinuousMap`:
  `AlgebraicGeometry.Etale.constant_pullback_unit_continuousMap`. Its full signature
  identifies the actual unit and comparison with precomposition for arbitrary
  coefficients, in precisely the u+1 coefficient universe used here.
- `lem-pur-affine-projection-connected-fibres` is a Mathlib leaf:
  `Scheme.Hom.isIrreducible_preimage`, specialized to a singleton with the
  `AffineSpace` geometrically irreducible instance and `isOpenMap_over`, then
  `IsIrreducible.isConnected`. These sources are transitively imported, so no
  duplicate statement or dependency module is needed.

Sources checked: the current blueprint at `literature/blueprint/latest/`,
`sec-smooth-purity/sk-prop-sp-orientation/sk-prop-sp-orientation-vector-bundle.proof.md`,
Step 1, including the clopen-locus and connected-geometric-fibre argument;
Stacks `etale-cohomology.tex`, `remark-constant-locally-constant-maps` (03P5),
which explicitly treats abstract groups and arbitrary étale objects.

Edge cases checked mathematically: for empty S all section groups and all function
spaces have their unique section; both naturality squares still make sense.
For d=0 the projection and zero section are inverse canonical isomorphisms.
Disconnected S is allowed because constancy is used on each fibre, not across S.
The trivial group, infinite groups, the zero ring, and nonreduced schemes are
included. Identity and arbitrary base changes are quantified without exclusions.
The unit condition is stated on an actual unit, not on an arbitrary ring-valued
function. No false statement or source correction was found.

Searches actually run:

- `msearch.py` LeanFinder query `constant etale sheaf sections affine space zero
  section restriction`: eight hits, including `AffineSpace.coord`,
  `AffineSpace.homOverEquiv`, `AffineSpace.toSpecMvPolyIntEquiv`, and structure-sheaf
  constant restriction results. None states the constant étale section equivalence.
- `msearch.py` Loogle query `LocallyConstant comapAddMonoidHom AffineSpace`:
  zero hits, with diagnostic `Unknown identifier comapAddMonoidHom`. This is not
  treated as a successful type search; the exact Mathlib declaration was then read
  directly and checked through scompile.
- `msearch.py` grep query `constant.*zero.*section` in Mathlib: zero hits.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for constant-section,
  zero-section and affine/constant combinations found the general 03P5 section
  comparison, the pullback formula and the existing affine-space constructions;
  no declaration states the item's result. Searching the exact node ID in
  `lean/WeilConjectures` gave no hit. `dag/lean_names_upstream.json` likewise has
  no binding for this node. Existing affine-line component statements have stronger
  base hypotheses and dimension one, so are not exact matches.

Validation: the final module is compiled separately through scompile.py against
its live published imports, in module mode. All binders and universe u are explicit;
there are no statement lets, private definitions, local notation, diagnostic
commands, or lines exceeding 100 characters. The expected sorry is the only
postponed proof. The required deliver2.py dry run and push follow compilation.

Additional search verification: `msearch.py` LeanSearch query `Pullback of constant
etale sheaf global sections along affine space projection and zero section are
mutually inverse` returned eight generic adjunction/global-section or module
pullback hits, including `constantSheafΓAdj`, `Sheaf.ΓHomEquiv`, and
`SheafOfModules.pullback`; none states this affine-space assertion.

Dry run completed: `deliver2.py Q81 lem-pur-affine-constant-section-zero-detection
--no-push` reported OK, with the sole delivered module compiling both in sandbox
and at its final library module path, and preflight passing.

## Second reading by Q81

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
