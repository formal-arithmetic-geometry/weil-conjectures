## Worker report

Item: lem-sfb-normal-arithmetic-closed-pair-approximation. The delivery states
`AlgebraicGeometry.normal_arithmetic_closed_pair_approximation` in
`Sheaf.AlgebraicGeometry.NormalArithmeticClosedPairApproximation`; its only proof
is `sorry`. No definitions, dependency replacements, new nodes, or statement
corrections are needed. The module header uses module mode and disables both
forms of automatic implicit binding.

Source read: EGA IV4 Proposition 21.14.3(ii), the arithmetic approximation
paragraph of its proof, at
https://jcreinhold.github.io/ega/iv/34-ch4-21-divisors.html . The web reader refused
the large page, so it was read directly using Python urllib and HTML text
extraction. In particular, the source takes the filtered system of normal
finite-type integer subalgebras, descends the smooth closed pair, retains its
generic codimension and fibre avoidance, and uses excellence to obtain normal
local completions. The strengthened explicit inverse-limit packaging follows
the node's five proof steps. The node's statement and all other fields remain
unchanged except `lean`.

Hypotheses, individually:

- A and B are arbitrary commutative rings in universe u; `[Algebra A B]` gives
  the specified map and `Spec.map (CommRingCat.ofHom (algebraMap A B))` is g.
  Using one universe excludes no pair of rings, since both can be placed in
  their common maximum universe. No finite extension hypothesis is imposed.
- Noetherian A is `[IsNoetherianRing A]`; normal domain A is `[IsDomain A]`
  together with `[IsIntegrallyClosed A]`, as the dependency convention requires.
- The finite equation-and-generator presentation is precisely
  `[Algebra.FinitePresentation A B]`. Scheme smoothness uses the dependency's
  `[Smooth (Spec.map ...)]`. Both source and target are spectra, hence affine;
  no additional affineness hypothesis is necessary.
- Z is `TopologicalSpace.Closeds (Spec (CommRingCat.of B))`, so closedness is
  genuine data. It is a closed subset, not a chosen closed subscheme.
- The named generic point is `η` with `hη : IsGenericPoint η Set.univ`. Such
  a point exists uniquely for Spec of a domain; the binder does not restrict A.
- `havoid` quantifies over every t and each irreducible component C of g.fiber t,
  asserting `¬ C ⊆ g.fiberι t ⁻¹' Z`. This is exactly no component contained
  in Z_t, including nonclosed points.
- `hcodim` quantifies over every point z of g.fiber η mapping into Z and asserts
  `2 ≤ ringKrullDim ((g.fiber η).presheaf.stalk z)`. This is the local ring of
  the fibre, not the total-space local ring.

Conclusion, clause by clause:

- The index set is the subtype `{S : Subalgebra ℤ A // P S}` for an existential
  predicate P. It is small in universe u, with its inherited inclusion partial
  order. `Nonempty` and `IsDirected ... (· ≤ ·)` explicitly provide nonemptiness
  and directedness. Each stage is an actual subalgebra of A, with canonical
  inclusion transitions, rather than an arbitrary abstract ring map.
- `i.val.FG` gives finite generation over the integers.
  `IsIntegrallyClosed i.val` gives normality; each stage is a domain because it
  is a subalgebra of the domain A. `IsNoetherianRing i.val` records the stated
  Noetherian clause explicitly.
- `Nonempty (IsColimit (CommRingCat.subalgebraCocone A P))` is the ring-colimit
  universal property with vertex A and the actual inclusions. The increasing
  directed family therefore has union A as well. The existing cocone and
  diagram were read in full in the upstream filtered-colimits module.
- For every stage prime t, `Localization.AtPrime t.asIdeal` is the required
  local ring. `AdicCompletion (IsLocalRing.maximalIdeal ...) ...` is exactly its
  maximal-ideal completion. Both `IsDomain` and `IsIntegrallyClosed` of that
  completion are asserted explicitly. PrimeSpectrum is the underlying point
  set of Spec, so this quantifies over every base point.
- D is the inverse scheme diagram; its stages satisfy `IsAffine`, so each is
  canonically Spec of its global-sections ring by `Scheme.isoSpec`. This is
  exactly the existence of the unspecified B_i. There is no requirement that
  coordinate rings embed into B. The natural transformation f supplies their
  compatible maps to Spec(A_i). `Smooth (f.app i)` and
  `LocallyOfFinitePresentation (f.app i)` give smooth finite presentation:
  source and target are affine, so the maps are quasi-compact and
  quasi-separated, and the affine coordinate algebra is finitely presented.
- Zi supplies the closed subsets. For every transition a : i ⟶ j in the
  opposite index, `IsPullback (D.map a) (f.app i) (f.app j) (Spec.map ...)`
  states the base change along the literal inclusion A_j ⊆ A_i. The set
  equality `Zi i = D.map a ⁻¹' Zi j` gives the closed-pair part of base change.
- The natural transformation p supplies all compatible original projections.
  `IsPullback (p.app i) g (f.app i) (Spec.map ...val...)` states base change to A;
  `Z = p.app i ⁻¹' Zi i` supplies the original closed subset.
- The two stage fibre clauses repeat havoid and hcodim exactly for f.app i,
  using every point t of Spec(A_i), and every generic point ηi. The generic
  point exists uniquely since A_i is a domain; the implication is not vacuous.
- `IsNoetherian`, `CompactSpace`, and `QuasiSeparatedSpace` are each asserted
  for both D.obj i and E.obj i, exactly the properties of V_i and W_i.
- e : E ⟶ D consists of open immersions with image `(Zi i)ᶜ`. This identifies
  E.obj i with the actual complement W_i as a scheme. Naturality forces every
  E transition to be the restriction of its D transition.
- `IsAffineHom (D.map a)` and `IsAffineHom (E.map a)` give both transition
  affineness clauses, for every comparable pair.
- The first `Nonempty (IsLimit ...)` asserts the universal scheme limit D
  with vertex Spec B and cone p. The second asserts the universal scheme
  limit E with vertex the actual open subscheme Z.compl and cone q. The
  equality `q.app i ≫ e.app i = Scheme.Opens.ι Z.compl ≫ p.app i` specifies
  exactly the restricted projections requested by the node. Explicit namespace
  arguments on `Scheme.Opens.toScheme` and `Scheme.Opens.ι` resolve the
  topological-opens/scheme-opens elaboration; no transport assumption is added.

Dependency declarations used (all recorded dependency interfaces read):

- Mathlib.RingTheory.Noetherian.Defs: `IsNoetherianRing`.
- Mathlib.RingTheory.IntegralClosure.IntegrallyClosed: `IsIntegrallyClosed`,
  with `IsDomain` and the domain/normal-ring inline convention.
- Mathlib.AlgebraicGeometry.Scheme: `Spec`, `Spec.map`.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`; the
  corresponding `IsPullback` universal square expresses the base changes.
- Mathlib.AlgebraicGeometry.ResidueField: `Scheme.residueField`; the existing
  `Scheme.Hom.fiber` in Mathlib.AlgebraicGeometry.Fiber is its pullback along
  `fromSpecResidueField`, and `fiberι` is its first projection.
- Mathlib.Topology.Irreducible: `irreducibleComponents` (the mathlib_match of
  def-weil-irreducible-components, which needs no Lean-record repair).
- Mathlib.Topology.Sober: `IsGenericPoint`.
- Mathlib.RingTheory.KrullDimension.Basic: `ringKrullDim`.
- Mathlib.RingTheory.Localization.AtPrime.Basic: `Localization.AtPrime`.
- Mathlib.RingTheory.AdicCompletion.Basic and LocalRing: `AdicCompletion` and
  its ring structure for the completion of the ring itself.
- Mathlib.Topology.Defs.Filter: `CompactSpace`.
- Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated: `QuasiSeparated`; its
  scheme form is `QuasiSeparatedSpace`, equivalent to quasi-separatedness over
  Spec of the integers as specified in the node record.
- Mathlib.AlgebraicGeometry.Morphisms.Affine: `IsAffineHom`.
- WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits:
  `CommRingCat.subalgebraDiagram`, `CommRingCat.subalgebraCocone`. These are the
  existing general diagrams of actual integer subalgebras; no second definition
  is introduced. The file's helpers are precisely the packaging of this node's
  existing notions, not a new independent mathematical notion.

All currently stated proof dependency modules are imported without public
visibility, including the normal-subalgebra-extension, affine-limit,
constructible-limit, excellence and normal-completion inputs. The only unstated
proof dependency, lem-sfb-smooth-closed-fibre-codimension-locus, has no Lean record
or mathlib_match in the read clone; there is no module to import. It is needed
for the future proof, not for this statement. No dependency cycle is introduced.

Edge cases checked before drafting and again after compiling: Z empty makes
both codimension requirements vacuous and permits E = D; empty V (the zero
B-algebra) also makes both conditions vacuous, and the conclusion allows empty
stages. Fibres may be empty. Z = V is impossible over a nonempty fibre because
havoid forbids its component. Relative dimension zero and one cause no special
restriction: the hypotheses determine the possible generic Z. A may be a field,
including positive characteristic, and no assumption of excellence of A or of
normality of A's own completions was added. There is no bound on the number of
stages, no surjectivity of Spec A → Spec A_i, and no local-dimension equality
under field extension is asserted.

Searches actually run for this item:

- msearch leanfinder: "Normal arithmetic approximation of a smooth affine
  scheme and closed subset by normal finitely generated integer subalgebras
  preserving fibre codimension". Eight hits, on normalization and the smooth
  locus; none is this approximation theorem.
- msearch loogle: "Algebra.Smooth.exists_subalgebra_fg, IsIntegrallyClosed".
  Zero hits.
- msearch grep (Mathlib): "arithmetic.*approximation|closedPair|normal.*[Aa]pproximation".
  Zero hits.
- msearch leansearch: "A smooth affine scheme and closed subset over a normal
  domain descend to normal finitely generated integer subalgebras preserving
  fibre codimension". Eight hits, including Algebra.Smooth.exists_subalgebra_fg;
  it gives smooth descent only, with none of the normality, pair conditions,
  completion assertions or complement-limit packaging.
- rg over lean/WeilConjectures and lean/Sheaf for
  "normalArithmetic|closedPair|arithmetic.*approximation|lem-sfb-normal-arithmetic-closed-pair-approximation".
  Only a docstring citation in SmoothNongenericPuncturedLineTriviality, no theorem.
- rg over dag/lean_names_upstream.json and both source trees for the chosen
  module and theorem names: no existing declarations.
- rg for subalgebra diagrams found the existing `CommRingCat.subalgebraDiagram`
  and cocone, which are reused instead of reconstructing them.

No STATEMENT-DISPUTED flag and no node fault. The withdrawn CompactObject
example was followed to its node's upstream replacement for module conventions.
Initial compiler failures concerned field notation on topological opens;
explicit `Scheme.Opens` namespace applications repaired them. The resulting
module compiled in both sandbox and actual library module mode under scompile.

## Second reading by Q133

This is a second reading by the author; the dispatcher explicitly prohibits
starting other agents, and the maintainer provides the independent delivery
review. I reopened the node and the final Lean file and checked their clauses.
The two places requiring attention were the unspecified coordinate rings B_i
and the complement system: `IsAffine` is equivalent to the former (via the
existing canonical `isoSpec`), and the open immersions e with exact complement
images identify the latter. Naturality and the displayed q/e/p equality force
the correct transition and cone maps, rather than arbitrary limit maps.

I checked that the four edges in each `IsPullback` have the required direction:
original Spec B → D_i above Spec A → Spec A_i, and D_i → D_j above
Spec A_i → Spec A_j for i ⟶ j in the opposite inclusion order. Both closed-set
inverse-image equalities have their domain on the left. The completion
quantifier is over primes of A_i, and the codimension stalk is on the generic
fibre itself. I checked every input and output listed in the Worker report
against the source and node. No missing or extra mathematical hypothesis or
conclusion was found. Only namespace qualification and line wrapping changed
during this reading; explicit public imports of the recorded statement
interfaces were added. One sorry remains, the assigned theorem.
