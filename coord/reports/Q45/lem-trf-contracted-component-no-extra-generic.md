## Worker report

The module `Sheaf.TraceFormula.ContractedComponentNoExtraGeneric` states
`AlgebraicGeometry.contracted_component_no_extra_generic`. Its only theorem has proof `sorry`.
No construction, axiom, helper theorem, or new definition is introduced.
The natural-language statement and proof are unchanged. The only node changes are `lean`
and adding the already landed `def-trf-orgogozo-induction-data` to `stmt_deps`, to reuse its
canonical algebraic-closure point and nodal ring instead of copying those constructions.

Hypothesis-by-hypothesis matching:

- `T : Scheme.{u}` with `IsIntegral T`, `IsLocallyNoetherian T`, `CompactSpace T` is the integral
  Noetherian base. Mathlib's `IsNoetherian` is precisely the latter two properties.
- `Z W : Over T` are the two families, with their structure maps `Z.hom`, `W.hom`.
  `Flat` is flatness. `LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated`
  together are finite presentation, as stated in def-sbc-locally-finite-presentation.
  No separatedness or properness of either structure map is assumed.
- `hpureZ`, `hpureW` apply `Scheme.IsPureDimension 1` to the pullbacks along
  `Orgogozo.geometricPoint T t`. This is exactly the fixed algebraic closure of each residue
  field in def-weil-geometric-fibre. Empty schemes have pure dimension one vacuously, so the
  node's phrase "empty or pure of dimension one" needs no additional disjunction.
- `hnodal` quantifies over every point of that fixed geometric fibre outside its smooth
  locus. The completion is `AdicCompletion (IsLocalRing.maximalIdeal stalk) stalk` and the
  nonempty ring-isomorphism type has target `Orgogozo.nodeRing (AlgebraicClosure ...)`,
  definitionally the specified two-variable power series quotient by uv. This does not
  replace the hypothesis by a nodality test over all larger algebraically closed fields.
- `h : Z ⟶ W` is a T-morphism: commutativity is part of the `Over` morphism. Its underlying
  scheme morphism `h.left` is proper. No generic-isomorphism/modification condition is present.

Clause-by-clause matching:

- The first conjunct quantifies over every base point, every reduced scheme `R` over its
  chosen algebraic closure, and every closed immersion `j` into the geometric Z-fibre with
  image an irreducible component. These are exactly the reduced induced components:
  `reduced_induced_closed_subscheme` identifies any reduced closed immersion with this image
  uniquely up to an isomorphism over the ambient scheme. No second component construction
  is made. The image of `j.left` followed by the canonical base change of `h` is subsingleton.
  Component nonemptiness makes this exactly "maps to one point". The conclusion
  `IsProper R.hom` is properness over that geometric residue field.
- `U : T.Opens`, `(U : Set T).Nonempty`, and `IsAffine U.toScheme` give a nonempty affine open.
- `S`, `π : S ⟶ U.toScheme`, `IsIntegral S`, `IsAffine S`, `IsFinite π`, `Etale π`, `Surjective π`
  give the specified integral affine finite étale surjective cover.
- `n : ℕ`, `H : Fin n → Over S`, and
  `ι : ∀ a, H a ⟶ (Over.pullback (π ≫ U.ι)).obj Z` are a finite list of closed subschemes of
  Z times_T S. `IsClosedImmersion (ι a).left` gives the closed inclusions. The remaining four
  predicates give exactly flatness and finite presentation over S.
- The next conjunct quantifies over all algebraically closed `Ω : Type u` and all geometric
  points `s : Spec Ω ⟶ S`. The fibres `pullback (H a).hom s` are reduced. The canonical fibre
  inclusions are `((Over.pullback s).map (ι a)).left`. Their ranges have injective index map
  and range exactly `irreducibleComponents` of the geometric fibre of Z_S. This says all
  components occur, each once. Closedness follows from base change of the closed immersions;
  reducedness plus these images gives exactly their reduced induced structures.
- The single `J : Set (Fin n)` is chosen before all geometric-point quantifiers. The image of
  each fibre inclusion followed by the canonical base change of `h` is subsingleton iff its
  index lies in J. Since every listed fibre is a component it is nonempty, so subsingleton
  again means precisely one image point, not an empty-image alternative.
- For every generic point ξ, `IsGenericPoint ξ Set.univ`, the last conjunct gives
  `IsProper ((H a).hom.fiberToSpecResidueField ξ)` for each a in J. This is properness of the
  ordinary generic fibre over κ(ξ). Uniqueness of the generic point of integral S makes
  quantifying over its characterizing property equivalent to "writing ξ for the generic point".
- No `IsProper Z.hom`, `IsProper W.hom`, or `IsProper (H a).hom` occurs. There is no restriction
  on n or J beyond their indicated types.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`, `IsReduced`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.snd`,
  and the canonical morphism construction underlying `Over.pullback`.
- `Mathlib.CategoryTheory.Comma.Over.Pullback`: `CategoryTheory.Over.pullback`; its object
  is `Over.mk (pullback.snd ...)`, and its map is the canonical pullback lift.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, `Scheme.Hom.smoothLocus`.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion` and its ring.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `MvPowerSeries.X`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`, especially its uniqueness clause.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec` and `Spec.map`.
- `Mathlib.Topology.Sober`: `IsGenericPoint`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`;
  `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiberToSpecResidueField`.
- `Sheaf.Paper.OrgogozoInductionData`: `Orgogozo.geometricPoint`, `Orgogozo.nodeRing`;
  their full bodies and docstrings were read. Only these helpers are used from that node;
  its stronger connected nodal-curve predicate is not used.

All available Sheaf proof-dependency modules recorded on the node are imported without
`public`, except ReducedInducedClosedSubscheme, which is also a statement dependency and is
public. The two proof-only nodes `lem-trf-finite-etale-generic-component-splitting` and
`lem-trf-nodal-points-reduced-algebraically-closed` have no recorded declaration at this
reading, so no module is invented or imported for them. Their use remains in the proof plan.
Mathlib proof inputs are supplied by the explicit proof imports and the statement imports.
There are no omitted imports due to an import cycle.

Source and edge-case checks:

Read the local Stacks text at 0551 (finite étale splitting), 0559 (geometric irreducibility
on a nonempty open), and 055A (closures and exhaustive component count). The source and the
node's nine-step proof agree on the shrinking-and-cover construction. The extracted proper
image argument is independent of ambient properness. The inherited review explains why the
nodality hypothesis must stay on the fixed closures; the Lean preserves that distinction.
No statement correction and no statement dispute is needed.

For n = 0, `Fin 0` is empty, the image enumeration forces no geometric components and hence
an empty geometric fibre. Its reducedness and every condition on H are vacuous. J is empty
in that case. For n > 0, J may still be empty: generic properness then imposes nothing.
Empty geometric fibres are admitted by the hypotheses. T itself cannot be empty because
integrality includes nonemptiness. No characteristic restrictions are imposed; uv is the
same nodal ring also in characteristic two. All geometric test fields use the scheme
universe u; no smaller independent universe makes a fibre condition vacuous. Distinct
components are distinguished by ranges of their canonical closed immersions, not by
arbitrary chosen names. An image subsingleton cannot be empty for an actual component.

Searches (run with the prescribed msearch wrapper; raw records are in searches.jsonl):

- LeanFinder: "After shrinking and finite etale cover enumerate geometric components of
  nodal curves and constant contracted subset of proper map". Eight hits: Scheme.Etale,
  affine-transition helpers, standard smooth charts, finite fibres, normalization. No exact
  component enumeration with constant contracted subset.
- Loogle: "AlgebraicGeometry.IsProper, AlgebraicGeometry.Flat". Zero hits.
- Mathlib grep: "contract.*component|component.*contract|nodal", AlgebraicGeometry. Zero hits.
- LeanSearch: "finite etale cover enumerates components of geometric fibres contracted by
  proper morphism". Eight hits, including properness of finite morphisms, finite fibres,
  IsProper and IsEtale. None states this lemma.
- `rg` in upstream WeilConjectures with "contract.*component|component.*contract|nodal"
  gives five incidental matches (Euler-characteristic/semistable comments and w-contractible
  terminology). The literal item-id search gives no upstream declaration. The upstream-name
  table inspection gives no binding for this item.
- `rg` in lean/Sheaf finds related nodal geometry and the downstream
  ContractedComponentGenericData theorem, which cites this lemma as an unstated proof input.
  That downstream theorem only claims generic numerical data, not this enumeration. Read
  its statement, helpers, and proof docstring. No existing exact theorem was found.
- Inspected NodalGeometricFibres and NodalOpenLocus: their fibre quantifiers or connectedness
  differ, so neither predicate is substituted for the hypotheses. Reused the already
  published geometricPoint and nodeRing helpers rather than introducing duplicates.

Compilation: the prescribed scompile.py compiled both the sandbox and library-path versions
cleanly (3.6 s and 3.4 s), with no diagnostic. The initial elaboration attempt exposed an
ambiguous pullback-as-Type inference; explicit `(C := Scheme.{u})` on scheme-valued pullbacks
repaired it. Both implicit-variable options are false; universe u and all variables are bound.

## Second reading by Q45

This is the author's self-check required by the direct-delivery workflow, not an independent
review; the maintainer supplies the independent reading. Reopened the node and the final
module together. Checked each hypothesis and conclusion against the matching above. In
particular: finite presentation includes qcqs, purity allows empty fibres, nodality uses
only the chosen algebraic closures, the first properness assertion precedes shrinking,
the cover is finite étale surjective and integral affine, all H fibres are reduced, equality
of component sets gives exhaustiveness, injectivity excludes repetitions, J precedes every
geometric fibre, and properness of H is only at the ordinary generic fibre. Confirmed that
Over.pullback is Mathlib's actual functor and that all inclusions and curve maps are its
canonical base changes. No arbitrary map, surrogate component, or properness hypothesis
has been substituted. The source node has no repair note. No mathematical mismatch was
found; the sole repair was the explicit scheme-category annotation reported above.
