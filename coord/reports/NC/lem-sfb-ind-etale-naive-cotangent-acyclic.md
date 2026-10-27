## Worker report

Stage 2, item `lem-sfb-ind-etale-naive-cotangent-acyclic`. The live node has a
reviewed stage-1 split but no Lean attachment. Its stage-2 queue row is present.
The previous unchanged-item stage-1 rejection therefore does not apply to this
statement delivery (coord/brief-stage2.md §0). No repair note exists for this item.
The delivery adds `Sheaf.RingTheory.IndEtaleNaiveCotangentAcyclic` with the single
sorry theorem `Algebra.indEtale_naiveCotangent_acyclic`. Only the item's `lean`
field changes; its mathematical statement, accepted proof split, and all
statement and proof dependencies are preserved. There are no new nodes or
dependency modules.

Sources read: Stacks `algebra.tex`, `lemma-colimits-NL` (07BQ), including its
canonical-presentation proof; `definition-etale` (00U1); and `more-algebra.tex`,
`lemma-henselization-NL`, especially the first paragraph. They give precisely
filtered-colimit acyclicity without a Noetherian or finite-presentation
restriction on the final map. The module docstring carries the four-step
accepted proof plan, including the compatible inverse differentials and the
S-linearity of the final inverse.

Hypotheses and constructions, clause by clause:

- Commutative rings R and S are `{R : Type u} {S : Type v} [CommRing R]
  [CommRing S]`. Their universes are independent. `[Algebra R S]` specifies
  exactly the ring homomorphism `algebraMap R S`; every ring map supplies such
  an algebra structure. Neither injectivity nor nontriviality is assumed.
- Ind-etaleness is the recorded
  `h : RingHom.IndEtaleAcrossUniverses (algebraMap R S)`. This unfolds to the
  existing `RingHom.IndEtale` on `RingHom.ulift.{v,u}` of the map. Both rings
  are canonically lifted to the common universe, with no new map or presentation
  chosen. Upstream `Algebra.IndEtale` means a small filtered colimit of
  `Algebra.Etale` stages, which already includes finite presentation.
- The specified polynomial presentation R[S] → S is Mathlib's
  `Algebra.Generators.self R S`: its variable-value function is the identity
  on S and its section sends s to X_s. Its `toExtension.Cotangent` is the
  canonical kernel modulo its square, with the quotient S-action.
- The differential is exactly
  `(Algebra.Generators.self R S).toExtension.cotangentComplex`. The source
  formula `cotangentComplex_mk` sends a conormal class [g] to `1 ⊗ dg`.
  `Generators.cotangentSpaceBasis` and `cotangentSpaceBasis_repr_one_tmul`
  identify its target with the free S-module on all s in S and give the
  coordinates γ(∂g/∂[s]). Thus no finite set of generators replaces S.
- The same naive complex in cohomological degrees −1,0 is written using
  `CochainComplex.mappingCone` of the degree-zero single-complex map of that
  differential. Its degree −1 term is the conormal module plus zero; its
  degree zero term is zero plus the differential module, and its other
  terms are zero plus zero. The canonical biproduct-with-zero identifications
  give precisely the node's complex. MappingCone `inl_v_d` identifies the
  only differential with the original δ (with positive sign). No new
  cotangent definition, arbitrary complex, or chosen comparison is introduced.
- The derived conclusion is the first conjunct
  `Nonempty (DerivedCategory.Q.obj (CochainComplex.mappingCone ...) ≅ 0)`.
  `[HasDerivedCategory.{w} (ModuleCat.{max u v} S)]` is the recorded size
  convention for choosing D(Mod S), not a ring property; the standard
  localization always supplies a choice in a sufficiently large universe.
- The assertion that δ is an isomorphism of S-modules is the second conjunct
  `IsIso (ModuleCat.ofHom ...cotangentComplex)`. Because this is an actual
  morphism of S-modules, its inverse is S-linear, not just a set inverse.
- H^{-1}(NL)=0 and H^0(NL)=0 are the remaining two conjuncts, `IsZero` of
  the actual cone's `homology (-1)` and `homology 0`. These are categorical
  cohomology objects in `ModuleCat`, not `IsZero` on bare types. The common
  module universe `max u v` contains the canonical presentation's conormal
  and tensor modules without equating u and v.
- No Noetherian, local-ring, finite-presentation, nonzero-ring, characteristic,
  or flatness instance is required by the theorem. No assertion of vanishing
  of the full cotangent complex in degrees below −1 is made.

Recorded statement dependencies used:

- `def-weil-pbc-ind-etale-algebra`:
  `Sheaf.RingTheory.IndEtaleUniverseTransport`,
  `RingHom.IndEtaleAcrossUniverses`, publicly imported; its exact body and
  the underlying upstream filtered-colimit `Algebra.IndEtale` were read.
- `def-weil-pbc-smooth-ring-map`: `Mathlib.RingTheory.Smooth.Basic`, publicly
  imported. Its existing cotangent definitions are provided by
  `Mathlib.RingTheory.Extension.Cotangent.Basic` through that import:
  `Algebra.Generators.self`, `Algebra.Extension.cotangentComplex`,
  `Algebra.Generators.cotangentSpaceBasis`. The node's main declaration
  `Algebra.Smooth` is a smoothness predicate and is not imposed as an extra
  assumption. No copy of any definition is needed.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, publicly imported.

The generic existing `HomologicalComplex.single` and
`CochainComplex.mappingCone` construct the complex in the statement. Their
modules are public imports. The proof imports preserve the accepted plan:
`Mathlib.RingTheory.FinitePresentation` (`Algebra.FinitePresentation`),
`WeilConjectures.RingTheory.EtaleRingMapConormalCriterion`
(`Algebra.etale_ring_map_conormal_criterion`),
`Mathlib.RingTheory.Kaehler.Polynomial`
(`KaehlerDifferential.mvPolynomialBasis`),
`Sheaf.RingTheory.PresentationsHomotopyEquivalent`
(`Algebra.Extension.presentations_homotopy_equivalent`), and
`Mathlib.CategoryTheory.Limits.HasLimits` (`CategoryTheory.Limits.colimit`).
The accepted proof dependency
`lem-sfb-filtered-colimit-naive-cotangent-comparison` currently has neither
`lean` nor `mathlib_match`; it is a proof-only dependency and has no module
to import yet. It is retained in `proof_deps` and explicitly named in the
proof docstring; it is not needed to type this statement. No downstream
lemma or proof dependency is assumed as a hypothesis.

Edge cases checked mathematically before writing:

- R → R: the canonical presentation has many redundant generators, rather
  than an empty presentation. Its differential is nevertheless an
  isomorphism; the cone represents the contractible two-term complex.
- S the zero ring, including R zero: all S-modules at issue vanish. No
  `Nontrivial` binder excludes this case.
- Finite etale stages and arbitrary filtered presentations, including
  noninjective transition maps: ind-etaleness is the exact existing
  predicate; no directed-union or finite-type replacement occurs.
- An empty indexing category is not filtered under the existing predicate;
  no additional nonemptiness assumption is introduced. Empty finite
  products of etale algebras and the resulting zero algebra are allowed.
- Infinite ind-etale extensions and arbitrary characteristic are retained.
  The arbitrary-variable canonical differential and common module universe
  exclude no such case. The theorem concerns only naive cotangent
  cohomology in −1,0; it asserts no additional full-complex vanishing.

Searches actually run:

- `msearch.py ... leanfinder "The naive cotangent complex of an ind etale
  algebra is acyclic"`: 8 hits, including
  `Algebra.FormallyEtale.subsingleton_h1Cotangent`, `Algebra.formallyEtale_iff`,
  and etale/formally-smooth statements. All vanishing candidates assume formal
  etaleness or standard smoothness; none obtains it from ind-etaleness.
- `msearch.py ... loogle '"cotangentComplex", "IndEtale"'`: 0 hits.
- `msearch.py ... grep
  'IndEtale|indEtale|ind_etale|NaiveCotangent|naiveCotangent' RingTheory`:
  0 Mathlib hits.
- `msearch.py ... leansearch "An ind etale algebra has zero first cotangent
  homology and zero Kahler differentials"`: 8 hits, principally
  `Algebra.formallyEtale_iff` and the formal-etale vanishing declarations;
  none is the ind-etale assertion.
- `rg` over project `lean/Sheaf` and `lean/WeilConjectures` for naive cotangent
  and ind-etale/cotangent names found the general presentation model in
  `Sheaf.RingTheory.NaiveCotangentComparison` but no acyclicity statement.
  That model is a complex of arbitrary bundled surjective presentations in
  one ring universe; the present signature directly reuses Mathlib's
  canonical extension and generic cone with independent ring universes.
- `grep -rn "lem-sfb-ind-etale-naive-cotangent-acyclic"` in the upstream
  `lean/WeilConjectures` returned no occurrences. Further `rg` across
  Mathlib, project source, and upstream sources for ind-etale/formal-etale
  cotangent combinations found no candidate. The intended new theorem name
  was absent from those sources and `dag/lean_names_upstream.json`.

Validation: `scompile.py NC lem-sfb-ind-etale-naive-cotangent-acyclic` compiled
this file in sandbox and library module modes, with no errors or warnings
(1.8 and 1.7 seconds). The first attempt exposed the missing `ZeroObject`
notation scope; `open scoped ZeroObject` repaired it. Every variable and
universe is explicitly bound; `autoImplicit` is false. The one theorem's
whole proof is `by sorry`. No statement dispute or node correction is needed.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
