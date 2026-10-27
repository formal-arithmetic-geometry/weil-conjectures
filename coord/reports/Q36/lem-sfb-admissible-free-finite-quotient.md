## Worker report

The module `Sheaf.AlgebraicGeometry.AdmissibleFreeFiniteQuotient` states
`AlgebraicGeometry.exists_admissible_free_finite_quotient`, with `sorry` as its
whole proof. Its two real helper definitions are the specified source and target
of the constant finite-group action relation. No new mathematical notion or
additional DAG node is needed: the helpers instantiate Mathlib's coproduct maps.
No original statement or dependency field changes.

Source read: literature/stacks-project/spaces-properties.tex, lines 1704–1848,
Tags 07S6 (proposition-finite-flat-equivalence-global), 07S7
(lemma-quotient-scheme), and 0BBM(4) (lemma-quotient-separated). The source proves
representability by invariant affine charts and identifies the actual action
relation with the kernel pair. The latest blueprint is the current
literature/blueprint/latest tree; the inherited item is a supporting input,
not its blueprint unit's own statement. The CompactObject example is now a
withdrawn module; its node records the existing compact-object interface.

Hypothesis and conclusion matching:

- A separated scheme over Spec Z is `(M : Scheme.{u}) [M.IsSeparated]`.
  Mathlib's absolute separatedness is separatedness of the terminal map,
  equivalent to a closed-immersion absolute diagonal by
  `Scheme.isSeparated_iff_isClosedImmersion_prod_lift`. Every scheme has its
  unique Spec Z structure, and every scheme automorphism preserves it.
- The finite abstract group and its scheme automorphisms are `(G : Type v)
  [Group G] [Finite G] (a : G →* Aut M)`. No commutativity is assumed.
  Mathlib's multiplication on Aut is reverse categorical composition, so this
  homomorphism encodes the usual left action.
- `finiteActionRelationSource M G` is `Sigma.desc (fun _ : G ↦ 𝟙 M)`.
  `finiteActionRelationTarget a` is `Sigma.desc (fun g : G ↦ (a g).hom)`.
  Both have domain `∐ fun _ : G ↦ M`, canonically G_{Spec Z} times M.
  For a test scheme H, a map H to this coproduct is a clopen partition by group
  labels together with H to M. This is precisely a pair consisting of a section
  of G_H over H and an M-section. It is not restricted to a globally constant
  group element. The coequalizer of these two Yoneda maps therefore is exactly
  H ↦ M(H)/G_H(H), since the generated relation is already an orbit equivalence.
- Freeness is `[Mono (prod.lift (finiteActionRelationTarget a)
  (finiteActionRelationSource M G))]`. By Yoneda this is injectivity on sections
  of every test scheme of (g,m) ↦ (gm,m); it is not freeness merely on the
  underlying points or only on geometric points.
- Affine orbit neighborhoods are `horbit : ∀ x : M, ∃ U : M.affineOpens,
  ∀ g : G, (a g).hom x ∈ U.1`. Mathlib's `affineOpens` bundles exactly an open
  with its `IsAffineOpen` certificate and the canonical open subscheme.
- The represented fppf quotient is the existential `(Q : Scheme.{u}) (q : M ⟶ Q)`
  and the natural transformation `η` from the action-relation presheaf
  coequalizer to `uliftYoneda.obj Q`. The equation `coequalizer.π ... ≫ η =
  uliftYoneda.map q` fixes the quotient map, not just an arbitrary isomorphism
  of presheaves. Bijectivity of `fun k ↦ η ≫ k`, for every fppf sheaf F, is
  exactly the universal property of `sheafificationAdjunction`. The target is
  an fppf sheaf because the fppf topology is subcanonical and ULift preserves
  the sheaf condition. This follows the recorded quotient-dependency interfaces,
  avoiding an extra hypothesis about chosen sheafification for all presheaves.
- Separated Q, finite q, etale q, and surjectivity on underlying points are the
  four conjuncts `Q.IsSeparated ∧ IsFinite q ∧ Etale q ∧ Surjective q`.
- The specified action identifies its relation with M times_Q M through
  `IsPullback (finiteActionRelationTarget a) (finiteActionRelationSource M G) q q`.
  This fixes both maps, hence fixes the canonical relation-to-kernel-pair
  isomorphism with the order (gm,m), rather than an unspecified torsor structure.
- Every base change is quantified as `∀ (T : Scheme.{u}) (f : T ⟶ Q)`.
  Its total space is `pullback q f` and its quotient morphism is `pullback.snd q f`.
  The base-changed relation is `pullback (finiteActionRelationSource M G ≫ q) f`,
  canonically the coproduct of G copies of M times_Q T, or G_T times_T M_T.
  The existential sT and tT are uniquely determined by their four displayed
  projection equations: forget/action on M and the identity on the T coordinate.
  Thus they are the actual base-changed source/action maps. `ηT`, its equation
  with `coequalizer.π`, and bijectivity of precomposition with `ηT` say precisely
  that T represents the fppf sheafification of that action's orbit presheaf.
- For an arbitrary fppf sheaf `F` and `b : uliftYoneda.obj M ⟶ F.obj`,
  invariance is `∀ g : G, uliftYoneda.map (a g).hom ≫ b = b`.
  This is equivalent to invariance under G_H(H) on every test H: pull back the
  group-label coproduct to its clopen pieces, apply constant-label invariance,
  and use the sheaf's separatedness to glue equality. The conclusion
  `∃! c : uliftYoneda.obj Q ⟶ F.obj, uliftYoneda.map q ≫ c = b` is exactly unique
  factorization. The quotient universal property is also present for every
  base-changed relation, so it gives the same invariant-map property there.
- For every `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`, the surjectivity of
  `fun x : Spec (.of Ω) ⟶ M ↦ x ≫ q` and the equivalence
  `x ≫ q = y ≫ q ↔ ∃ g : G, x ≫ (a g).hom = y` state that the induced map on
  orbit sets is a bijection. Both surjectivity and identification of exactly
  the orbit fibres are present. The orientation x acted on to y is equivalent
  to the reversed orbit relation by group inverses.
- The final `CompactSpace M → CompactSpace Q` renders the optional
  quasi-compactness clause, with no Hausdorff condition.
- Universes `u v w` are explicit. The finite group may lie in an independent
  universe; finiteness supplies the smallness needed for its coproduct. Sets of
  scheme sections are lifted by `uliftYoneda.{max (u + 1) w}` to the containing
  universe, and the sheaf targets use precisely `Type (max (u + 1) w)`. No equality
  of site object and morphism universes is assumed. Fields and test schemes
  range over the scheme universe, as in the recorded size convention.
- There is no Noetherianity, finite-type, invertibility-of-cardinality,
  quasi-compactness-of-M, or nonemptiness hypothesis.

Dependency declarations read and used, by module and name:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, and `Spec.map` (the last is part of the recorded
  spectrum interface, though the statement only needs Spec itself).
- Mathlib.AlgebraicGeometry.OpenImmersion: `AlgebraicGeometry.IsOpenImmersion`;
  the statement uses canonical affine open subschemes via `M.affineOpens`.
- Mathlib.AlgebraicGeometry.Sites.Fpqc: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`; the absolute big site agrees with schemes over Spec Z
  via the unique structure morphisms.
- Mathlib.CategoryTheory.Sites.Sheafification: `presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction`; the universal-property formulation is used,
  as in the recorded affine and kernel-pair quotient dependencies.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion:
  `AlgebraicGeometry.IsClosedImmersion`, through Mathlib's separatedness predicate.
- Mathlib.AlgebraicGeometry.Morphisms.Finite: `AlgebraicGeometry.IsFinite`.
- Mathlib.AlgebraicGeometry.Morphisms.Etale: `AlgebraicGeometry.Etale`.
- Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap: `AlgebraicGeometry.Surjective`.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`,
  `pullback.fst`, `pullback.snd`.
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed`, the algebraically closed
  field clause of def-weil-algebraic-closure's mathlib_match.
- def-weil-size-convention is a metatheoretic convention with no Lean
  definiendum; explicit universes implement it.

All recorded proof-dependency modules are imported as plain imports, including
SchemeEtaleSourceTargetProperties, FiberDegree, GroupoidScheme,
EtaleRelationQuotient, FiniteFlatAffineRelationQuotient,
EtaleRelationFindingOpens, Sites.Representability,
FppfKernelPairQuotientDescent, IsFiniteOfFpqcCover,
Morphisms.Proper, IsSeparatedOfSurjectiveUniversallyClosed, and AlgClosed.Basic.
Mathlib matches for coproducts and permanence are supplied by the corresponding
public Mathlib imports. `lem-sfb-locally-free-groupoid-invariant-affine` has no Lean
record or Mathlib match at this reading; it is a proof dependency only, so there
is no module to import. Its statement and use remain in the proof docstring.
No missing statement dependency or unusable recorded interface was found.

Edge cases checked before writing and again on the final signature:

- Empty M is allowed: its affine-orbit hypothesis is vacuous, its relation is
  empty, and the empty Q satisfies all assertions. The field-point surjectivity
  is then the empty-to-empty map. No Nonempty binder is present.
- The trivial group gives the identity quotient and diagonal relation.
- A nontrivial group acting trivially on a nonempty scheme fails freeness,
  even if its underlying topological space has only one point. Conversely a
  nontrivial Galois field torsor may have a one-point underlying orbit and is
  permitted because freeness is on scheme sections, not points.
- Disconnected tests allow different labels on different clopen components;
  the relation coproduct, not the set G acting globally on M(H), is used.
- The zero ring, characteristic dividing |G|, non-Noetherian M and non-quasi-compact
  M are not excluded. Quasi-compactness appears only in the final implication.
- Base change along the identity and along maps from the empty scheme is
  included; no flatness or finite-type condition is placed on f.

Searches for an exact existing statement or an already-defined notion:

- msearch.py leanfinder: "A free finite group acting on a scheme with affine
  orbit neighborhoods has a finite etale separated quotient scheme" returned
  eight Galois-category or set/topological group-action results; none matched.
- msearch.py leansearch: "Free finite group action on a separated scheme
  admissible quotient finite etale" returned eight finite-action or topological
  orbit-quotient results; none matched the scheme quotient theorem.
- msearch.py loogle: `"AlgebraicGeometry", "quotient"` returned six results
  about ring-quotient spectra or the quotient-map topology of a flat surjection;
  none matched. An initial unquoted `AlgebraicGeometry.Scheme, quotient` query
  returned no hits and diagnosed the unknown identifier quotient; it was rerun
  with the quoted query above.
- msearch.py grep: `quotient|orbit` in AlgebraicGeometry returned 25 ring-quotient
  and related occurrences; no admissible free finite-group quotient theorem.
- rg in lean/WeilConjectures and lean/Sheaf for orbitPresheaf/actionQuotient,
  finiteGroupAction/admissibleFree, constantGroupScheme/fppfQuotient found
  constant additive-group schemes, quotient stacks and unrelated quotient
  constructions. The existing additive commutative constant-group interface
  does not encode an arbitrary noncommutative finite group, and is not copied.
- The nearby AdmissibleFiniteTypeFieldQuotient module was read: its theorem
  requires a field and local finite type and does not supply this unrestricted
  free-action fppf quotient theorem. AdmissibleFiniteSchemeQuotient describes
  a different geometric quotient notion; FreeFlatGroupSpaceQuotient supplies an
  algebraic-space quotient, not the scheme and all clauses here.
- rg for this item id in lean/WeilConjectures and dag/lean_names_upstream.json
  found no upstream attachment. Exact-name searches for the three proposed
  declarations in Mathlib, WeilConjectures, Sheaf and the upstream names index
  found no collision. Full msearch responses are in the sandbox's searches.jsonl.

No STATEMENT-DISPUTED issue or node correction. Compile:
`python3 /home/ubuntu/weil-launcher-all/batch2/scompile.py Q36
lem-sfb-admissible-free-finite-quotient <sandbox module>` succeeded for both
sandbox and library module modes, with no error or non-sorry warning.

## Second reading by Q36

The dispatcher explicitly prohibits other agents, so this is a separate second
reading by the same worker, without claiming an independent reviewer. I reopened
both the original node and final module, and checked each item above against the
actual signature. The maintainer's independent review is still required.

The important checks were freeness on every test scheme rather than just point
stabilizers, the locally varying G_H(H) labels on disconnected schemes, and the
order of the two maps in the torsor square. The source is the fold, the target is
the original action, and the IsPullback has (target, source), exactly (gm,m).
The quotient unit equation fixes q. In the base-change clause the four equations
fix the same action/source maps over T, and the unit equation fixes q_T as
pullback.snd, so this is the original base-changed action rather than an arbitrary
relation on M_T. The arbitrary fppf sheaf clause asks for a unique factorization,
and the field-point clause includes onto as well as the exact orbit equivalence.
I also checked absolute separatedness against its Mathlib diagonal equivalence,
explicit universe binding, and the conditional rather than assumed compactness.
No statement mismatch was found and no correction was made during this reading.
