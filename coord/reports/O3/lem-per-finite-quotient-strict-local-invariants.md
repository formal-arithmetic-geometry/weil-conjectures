## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteQuotientStrictLocalInvariants` states
`AlgebraicGeometry.FiniteQuotientStrictLocal.finiteQuotient_strictLocal_invariants`.
Its only theorem has proof `sorry`; all helper structures and definitions have real data.
The natural-language statement is unchanged. The landed definition node
`def-per-fs-log-group-action` is added to `stmt_deps` to use its existing action.

Hypothesis and clause correspondence:

- A Noetherian scheme X with an fs log structure M is represented by
  `X : FineSaturatedLogScheme` and `[IsNoetherian X.scheme]`. Its `logStructure`
  and `fineSaturated` fields are the specified M and fs hypothesis. The packaged
  local Noetherian hypothesis follows from Noetherianity, so adds no restriction.
- The finite group and its action preserving M are `G`, `[Group G]`, `[Finite G]`,
  and `a : FSLogGroupAction G X`. This uses the recorded log automorphisms,
  with their action laws and compatibility with the scheme action.
- The map is `q : X.scheme ⟶ Y`, `[IsFinite q]`, `[Surjective q]`.
  `hinvariant` states invariance. `htopology` and `horbits` state exactly the
  orbit-space topology on ordinary points. No admissibility assumption is added.
- `hsheaf` says on every open U that q.app U is injective and has precisely
  invariant image. Pullbacks and restrictions are compared on all common opens,
  as in the existing admissible-quotient interface, but without requiring its
  additional affine-orbit hypothesis.
- The first conclusion is `IsNoetherian Y`. The next equivalence on every pair
  `Spec Ω ⟶ X.scheme`, for each algebraically closed field Ω, states the geometric
  orbit-fibre assertion. Ω is not fixed and no nonempty scheme is assumed.
- N = (q_* M)^G is specified by the existential `N : EtalePrelogStructure Y`
  and `d : PullbackData ... N q`, followed by injectivity and the exact invariant
  image on EVERY etale test W. The latter uses the actual pullback W ×_Y X.
  `PullbackData.naturality` enforces naturality in both relative test objects;
  `compatibility` enforces the prescribed structural map. These conditions
  characterize the invariant direct image up to unique structure-compatible
  sheaf isomorphism. N is not assumed fs, log regular, or even a log structure.
  Thus the existential is a realization of the specified sheaf, not an arbitrary
  chosen monoid or an assumption of the desired stalk comparison.
- For each geometric x, y is literally `x ≫ q`, A is `strictLocalRing X.scheme x`,
  and B is `strictLocalRing Y (x ≫ q)`. These are the etale structure-sheaf stalks.
  Their monoid counterparts use the recorded `EtalePrelogStructure.stalk`.
- The ring map r is fixed on every pointed relative etale germ by
  `IsRingPullback q x r`. Its injectivity and exact range `IsFixedRing a x`
  identify B with A^H. `r.Finite` states module finiteness for this very ring map.
  H consists exactly of the g satisfying `x ≫ (a.baseAction g).hom = x`.
  No ordinary-point or decomposition-group stabilizer is substituted.
- The monoid map e is fixed on every relative log germ by `IsLogPullback d x e`.
  Its injectivity and exact range `IsFixedLog a x` identify N_y with M_x^H.
  `RingGermImage` and `LogGermImage` describe the graphs of the GIVEN action
  on representatives, not independently supplied stalk actions or arbitrary maps.
  For a stabilizer element source and target points agree; cofilteredness gives
  the simultaneous representatives used in these graph descriptions.
- The equation involving `stalkAlpha` says the structural square commutes with r.
  The two `IsUnit` equivalences restrict r and e to the corresponding unit
  subgroups. Bijectivity of `Units.map (N.stalkAlpha ...)` identifies log units
  with B-units, completing the specified compatible identification of units.
- There is no regularity, stratum-triviality, generic-freeness, tameness,
  invertibility-of-|G|, reducedness, or characteristic hypothesis.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` is the ideal-finiteness
  convention; scheme Noetherianity uses `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsNoetherian` (locally Noetherian and quasi-compact).
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`,
  affine inverse images with module-finite section maps. Its recorded partner
  `IsIntegralHom` in `Morphisms.Integral` was read; integrality is not an extra
  hypothesis of this item.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `EtalePrelogStructure`,
  `EtaleLogStructure`, `FineSaturatedLogScheme`, `EtaleLogHom`,
  `EtalePrelogStructure.stalk`, `germ`, and `stalkAlpha`.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`: `pointedEtaleStalk`, its actual
  pointed-neighbourhood diagram and monoid-colimit instance, used by the log stalk.
- `Sheaf.AlgebraicGeometry.FSLogGroupAction`: `FSLogGroupAction`, `baseAction`,
  `logMap`, `base_eq`, and its relative-test action laws. Its existing quotient
  interface requires an fs TARGET and is therefore not used as a hypothesis here.
- The inherited `strictLocalRing` and `strictLocalGerm` in
  `Sheaf.AlgebraicGeometry.LogRegularPair` use the ring-valued geometric fibre.
  The source of each declaration was read in full, including its docstring.

Helpers belong to the canonical comparison being stated. `PullbackData` is the
relative-test form of the prelog map, obtained for existing log morphisms by
`ofLogHom`. `IsInvariantSection` is the fixed-section condition.
`IsRingPullback` and `IsLogPullback` specify the canonical maps on ALL germs.
The two germ-image relations and fixed predicates merely express those maps
without choosing or postulating a stabilizer representation. None asserts a theorem,
constructs data using sorry, or supplies the comparison as an input hypothesis.

Edge cases checked before writing and on the second pass:

- Empty X: surjectivity forces empty Y; all pointwise clauses are vacuous.
  The unique sheaves and section maps on the empty site give the direct image.
- Trivial action or trivial G: the fixed predicates include every germ and the
  theorem reduces to the expected strict-local and pushforward identifications.
- A free orbit: H is trivial; evaluation at a selected lift gives the full local
  ring and monoid, not the invariants of the entire group at that single lift.
- Nontrivial inertia on a geometric point, including wild characteristic dividing
  |G|: the difference-kernel proof uses flatness and never divides by |G|.
- A group element fixing only an ordinary point but moving its geometric lift
  is excluded from H. Nonreduced fibres are allowed; geometric point lifts, rather
  than reduced-fibre schemes, index the orbit assertion.
- Nonfaithful actions, noninjective log structural maps and trivial log structures
  are allowed. The target is not assumed fs, avoiding a false additional restriction.

Sources checked: opened the local ILO PDF at PDF pages 80--81, printed pp.74--75,
including the paragraph after 3.5 and the opening strict-local reduction of 3.7(b).
The theorem docstring spells out all nine proof steps from the DAG: Noetherian
ring descent, quasi-compactness, strict-local product decomposition, flat invariant
kernel, transitivity by local idempotents, ring evaluation, finite-limit/log stalks,
log evaluation with the structural square, and invariant inverses of units.

Searches made (the wrapper also recorded raw results in searches.jsonl):

- LeanFinder, `Finite group quotient scheme strict local ring stabilizer invariants
  and log structure stalk`: eight hits including
  `Ideal.Quotient.stabilizerHom_surjective` and its fraction-ring/profinite variants;
  none gives the scheme/log-stalk theorem.
- Loogle, `"Algebra.IsInvariant"`: twelve invariant-ring declarations, including
  integrality and orbits of prime ideals; none gives this strict-local/log statement.
- Mathlib grep via msearch, `quotient|invariant`, subdirectory `AlgebraicGeometry`:
  25 hits on projective spectra, quotient-map topology and unrelated constructions;
  no match.
- LeanSearch, `Finite group quotient strict local ring equals geometric stabilizer
  invariant ring and invariant log stalk`: eight hits on group quotients,
  representation invariants and ideal stabilizers; no combined theorem.
- rg over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id:
  no occurrence. Searches for finite quotients, log actions, invariant log structures
  and strict-local maps found no exact theorem there.
- rg over the shared `lean/Sheaf` found `FSLogGroupAction`,
  `AdmissibleFiniteSchemeQuotient`, `InvariantDivisorialDirectImage`,
  `KummerLogMorphism`, and the very-tame quotient theorems. Their sources were
  opened. The first is reused; the others impose additional hypotheses or have
  different coefficient/log structures and do not state this item.
- DAG search for scheme quotients and log actions located their owning definition
  nodes, in particular the landed `def-per-fs-log-group-action` used here.
- rg for the new namespace and theorem name in `lean/Sheaf` and upstream:
  no pre-existing declaration.

Validation: scompile.py compiled the delivered file as both a sandbox module and
its library module, cleanly (3.8 s and 4.3 s). No statement dispute, dependency
repair, hollow definition, or source-based statement correction was needed.

## Second reading by N3

The dispatcher explicitly prohibited starting other agents. This is a fresh second
pass by the same worker; the delivery still requires the maintainer's independent
review. I reopened the node, its dependency records and the completed file and
matched each hypothesis and conclusion as listed above. In particular I checked
that the target N has no fs hypothesis, that H fixes the geometric morphism and
not just its underlying point, that the finite algebra structure is the germ-defined
map r, and that BOTH unit comparisons and the structural square are present.
The comparison maps are in the conclusion and characterized on every germ;
the invariant-image property specifies N rather than assuming its stalk theorem.
The checks found no mismatch requiring a statement correction. All new helper
definitions are explicit structures or predicates, and only the final named theorem
has a postponed proof. There are no auto-bound variables or lines over 100 characters.
