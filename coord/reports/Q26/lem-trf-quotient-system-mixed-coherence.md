## Worker report

The item is stated by `WeilConjectures.integralQuotientMixedCoherence` in
`Sheaf.Paper.QuotientSystemMixedCoherence`. Its conclusion is the Prop-valued record
`IntegralQuotientMixedCoherence`, whose fields spell out the equations, both on ordinary
strict quotient systems and in their unbounded derived categories. All theorem proofs
in this delivery are `sorry`; the two new scalar comparison definitions choose uniquely
characterized natural isomorphisms, rather than unspecified existence witnesses.

Hypotheses and context:

- The prime is `(l : ℕ) [Fact l.Prime]`.
- A finite coefficient extension is `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`, likewise for L and M. The inclusions in the fixed
  algebraic closure are rendered by `ι : E →ₐ[ℚ_[l]] L`, `j : L →ₐ[ℚ_[l]] M`
  and their actual composite `j.comp ι`. These use the recorded embedding interface;
  no strict inequality of fields is required. The identity is `AlgHom.id ℚ_[l] E`.
- Schemes are `Scheme.{t}`, with t independent of coefficient size u. Every scheme in
  a displayed equation has `[∀ x : X, Invertible (l : X.residueField x)]`. For a finite
  path the recursive predicate `IntegralQuotientPathInvertible l p` imposes exactly
  this condition at each vertex, including the endpoints and the empty path.
- The valuation rings, uniformizers and actual quotients are those already used by
  `coefficientSequenceCommRingSheaf l E X`. The sequence index n denotes exponent n+1;
  thus every positive exponent and every horizontal quotient transition is retained.
- `coefficientSequenceModules` is the recorded category of modules on the ringed
  sequence site, not a category of diagrams in a derived category.
  `coefficientSequenceDerived` is its ordinary unbounded localization. Completion,
  realization and normalization are contextual notation in the node; none is an
  extra hypothesis or an operation used to obtain the asserted equalities.

Clause mapping:

- `ordinary_mixed` and `derived_mixed` state the first displayed equation as an equality
  of natural transformations. In Lean's composition order the left route first
  whiskers c_E by S_Z, then κ_h by U_k, then κ_k by U_h; the right route is κ_(hk)
  followed by c_L whiskered by S_V. Applying this equality at any C is precisely the
  node's displayed component equation, for every derived object C.
- `ordinary_associative` and `derived_associative` give the three-map compositor
  equation. `eqToHom (congrArg ... (Category.assoc f g h))` inserts exactly the
  identification of equal composite scheme maps.
- `ordinary_unital` and `derived_unital` each contain both geometric unit equations,
  using `integralComparisonSequenceUnit` and `integralComparisonSystemUnit` and the
  transports along `Category.id_comp` and `Category.comp_id`.
- `ordinary_finite` and `derived_finite` assert equality for every two binary assemblies
  of the same arbitrary `Quiver.Path` into the same iterated functor. The inductive
  type `IntegralQuotientBracketing` has empty, singleton and composition constructors.
  `integralQuotientBracketFunctor` interprets it by iterated pullback, and
  `integralQuotientBracketComparison` recursively constructs its canonical comparison,
  using only the specified unit and compositor. Its composition clause uses
  `composePath_comp` and the two canonical whiskerings. The finite clause asserts existence of the equality h of the target functors
  together with comparison equality after `eqToIso h`; it does not assume that
  equality as an additional hypothesis. Every finite parenthesization is represented;
  zero-length subpaths permit identity insertions. Functor association and unit
  identifications in these fields are definitional. Transport along equal arrows or
  equal paths is ordinary dependent equality transport, not a new comparison choice.
- `ordinary_scalar_unit` and `derived_scalar_unit` are exactly
  U_f(e_Y) composed with κ_f^(E/E) = e_X U_f.
- `ordinary_scalar_tower` and `derived_scalar_tower` are exactly the displayed scalar
  tower equation, using j.comp ι on its right route. The ordinary associator uses
  the dependency's generator-normalized multiplication; the derived associator is
  normalized against that same ordinary map by the item module's scalar helpers.
- The ordinary fields are equalities before any localization. Mapping them by
  `NatIso.mapHomologicalComplex` gives equal maps of strict-system complexes in every
  degree, including the differential. All components are module-sheaf morphisms on
  the entire sequence site, so vertical restrictions and horizontal quotient maps
  commute by their types and naturality; they are not merely equal after evaluation.
- The maps' local-section formulas are inherited unchanged from the dependency:
  `integralComparisonSequenceGenerator` is the actual inverse-image adjunction unit;
  `integralComparisonSequenceScalarPullback_existsUnique` specifies
  1 tensor gamma_f(x) to gamma_f(1 tensor x);
  `integralComparisonSequenceScalarComposition_existsUnique` specifies
  c tensor (b tensor x) to c*j(b) tensor x;
  `integralComparisonSequenceScalarUnit_existsUnique` specifies s tensor x to s*x;
  `integralComparisonSequenceComposition_existsUnique` specifies the mate of actual
  fibre-product pasting. The derived scalar helper comparisons in the item module are uniquely specified
  by equalities with the universal cochain counits on every K-flat representative.
  The existing derived κ and c already have their prescribed localization definitions.
- No field assumes normalization, boundedness, constructibility, finite Tor-amplitude,
  or flatness of the finite coefficient homomorphisms. The proof docstring records
  all eight DAG proof steps, including simultaneous whole-system flat-term K-flat
  models, preservation under all intermediate operations, and cancellation of the
  chosen resolution isomorphism to obtain equality on arbitrary inputs.

Dependency declarations read and used:

- `Sheaf.Paper.IntegralComparisonSequenceSystems`: the actual pullback, scalar model,
  all ordinary comparisons, derived c and κ, their generator formulas and derived
  normalization, as named above. The item module publicly imports
  this original module, so no existing construction is copied or replaced.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `coefficientDerivedSystemEvaluationCalculus` and its recorded coefficient-system
  interface, imported through the comparison dependency.
- `Sheaf.Paper.CoefficientRingedSequenceSite`: `coefficientSequenceModules`,
  `coefficientSequenceDerived`, `coefficientSequenceCommRingSheaf` and its topology.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel`, its E, T and ε, and
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`. The canonical scalar
  model comes from the recorded dependency and its universal counit.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the coefficient constructions reexported
  from `Sheaf.NumberTheory.Padics.CoefficientExtension`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `Scheme.ProEt.topology`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`; completion is contextual here.
- `Sheaf.Paper.NormalizedDVRTower`: `NormalizedDVRTower`; normalization is explicitly
  not imposed. Its framework is already imported through the dependencies.
- Proof-plan imports include `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
  and `Sheaf.Paper.KFlatRingedToposPullback`. Abstract derived localization is the
  imported Mathlib/upstream `DerivedCategory.Q`.

Edge cases checked before drafting: identity scheme morphisms (both unit equations),
empty and singleton finite strings, arbitrary finite strings with zero-length pieces,
E=L, L=M, E=L=M and identity inclusions, empty schemes (pointwise invertibility is
vacuous), exponent one (sequence index zero), arbitrary unbounded input systems,
non-normalized systems, and ramified/nonflat quotient coefficient maps. None is
excluded. The finite-string predicate remembers the actual path, preventing an
accidental assertion about unrelated strings whose interpreted functors happen to agree.

Searches, all through the prescribed msearch.py wrapper or direct read-only rg:

- LeanFinder query: "Composition identity and scalar pullback comparisons on strict
  quotient module systems satisfy coherence before derived inverse limit". Eight
  hits about `IsAdicComplete.StrictMono` and adic completion; no match.
- Loogle query: `SheafOfModules.pullbackComp`. Five ordinary sheaf-pullback hits:
  pullbackComp, pullback_comp_id, pullback_id_comp, pullback_assoc, and the conjugate
  equivalence characterization. These cover ordinary pieces, not these canonical
  system operations with simultaneous derived scalar coherence.
- Mathlib grep query: `pullback_assoc|pullback_comp_id|pullback_id_comp`, subdirectory
  CategoryTheory. Eight hits on sheaf-over pullback and pullback limits; no match.
- LeanSearch query: "Coherence of pullback composition with extension of scalars on
  towers of sheaves of modules". Eight hits, including the ordinary module scalar
  pseudofunctor and SheafOfModules.pullbackComp/assoc; no entire statement match.
- Project rg queries: `mixed.coherence|SequenceScalarComposition|SystemScalarPullback|
  SystemScalarUnit|Sequence.*coherence|quotient-system-mixed-coherence` in both live
  source roots. The only relevant hits were the recorded comparison module and its
  consumers. `ScalarExtensionTowerCoherence` has termwise scalarComp/scalarUnit,
  not the missing universal-counit-normalized derived scalar comparisons.
  `IntegralPullbackComparisonRealization` concerns realized constructible inputs,
  not this unrestricted whole-system theorem. Searching the item id in the upstream
  root gave no hit. No exact existing declaration was found.

No statement correction, new independent notion, or STATEMENT-DISPUTED finding.
The path predicate, bracketing type and its two interpretations are helper encodings of this node's own
finite-string clause, listed among its declarations, not new mathematical inputs.

## Returned-delivery repair (H13)

The returned head `33e3f1b6d094` replaced N2's live dependency record with a record
listing only four derived scalar helpers. The saved packet reproduced that defect;
its initial dry run passed mechanically at `88bd11122d1`, which did not resolve H13.

The dependency node `def-trf-integral-comparison-sequence-systems` is now byte-identical
to the live node, retaining `Sheaf.Paper.IntegralComparisonSequenceSystems`, N2's
primary declaration and complete 36-declaration list. No dependency module is delivered.
The separate `IntegralComparisonSequenceScalarDerived.lean` is removed. Its four helpers
`integralComparisonSystemScalarComposition_existsUnique`,
`integralComparisonSystemScalarComposition`, `integralComparisonSystemScalarUnit_existsUnique`
and `integralComparisonSystemScalarUnit` now reside in the item module, within a scoped
section so their coefficient variables do not affect the coherence declaration. All four
are listed in the item's `lean.declarations` and carry the item's blueprint tag.

These helpers supply derived α and e omitted by the original interface. Their statements
and constructions are unchanged: each is chosen from its unique characterization by the
universal cochain counits on every K-flat representative and the ordinary generator map.
The existence-and-uniqueness theorem docstrings retain their complete proof plans.
No theorem statement, input universe, coherence field or mathematical assumption changes.

## Second reading by Q26

I reread the node, the delivered item module, its four scalar helpers, the ordinary
comparison signatures and their universal-counit normalizations in a separate pass. The first, scalar-unit and scalar-tower
equations agree in order and in every source/target scheme; Lean's left-to-right composition
reverses the written circle order exactly once. Geometric associativity includes the
transport between the two scheme composites, and both unit equations use the prescribed
inverse-image unit. The explicit finite-path fields include empty and singleton paths.
I added the per-vertex invertibility predicate so the finite clause retains the same
standing scheme hypothesis as the displayed equations. Site universe t and coefficient
universe u remain independent. The ordinary clauses imply the literal cochain equalities;
the derived clauses use the canonically normalized operations on entire quotient diagrams.
No normalization or finiteness assumptions slipped into the input domain. The helper relocation
retains the original constructions and pins its two maps to the original ordinary
multiplication comparisons. I compared the restored dependency file byte for byte with
the current live file and checked that all four helpers are recorded on the item.
No other mathematical mismatch was found. No second agent was used, as required by the dispatcher brief; the maintainer performs independent review.

## Repair validation

The repaired single module compiled cleanly through `scompile.py` in both sandbox
and library modes (34.4 s and 38.3 s respectively). The dependency node was checked
byte for byte against live; the item's fields other than `lean` remain unchanged,
and `lean.statement` matches the main theorem signature verbatim. All ten declarations,
including the relocated four helpers, are recorded on the item.
