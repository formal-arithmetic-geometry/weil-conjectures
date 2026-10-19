## Worker report

This is a repair of returned head 9e0c8c3f86db. The retained draft's arbitrary scalar
functors and `True` coherence placeholders have been removed. The actual module is
`lean/Sheaf/Paper/FiniteClosedShriek.lean`, with its main declaration
`WeilConjectures.finiteCoefficientClosedShriek` and the separately named naturality,
closed-composition, coefficient-chain, and locally closed assertions listed in
`lean.declarations`. Every theorem proof remains `sorry`; every definition has real data.

The sandbox node was refreshed from the shared node; only `lean` and the addition of
the existing compositor and restriction-comparison nodes to `stmt_deps` differ. In particular
no stage-1 proof, proof dependency, search, status or split-report field is delivered.
There is no new unsplit statement node in this packet. The repair-note for this item
is a stage-1 re-split request, not a released stage-2 interface binding. The stage-1
split remains outside this stage-2 packet.

Hypotheses and clauses, matched to the actual file:

- `D : FiniteFieldDatum`, `l`, `[Fact l.Prime]`, and `_hl : l ≠ D.p` give the fixed
  global field and the invertible coefficient prime.
- `E,L`, their field, Padic algebra and finite-dimensional instances give precisely
  the two finite coefficient extensions. Exponent `m+1` (respectively `n+1`) ranges
  over every positive level, with the recorded `Padic.coefficientExtensionRing`.
  `φ` is an arbitrary unital homomorphism of their standard lifted presentations;
  no flatness, injectivity or surjectivity is assumed.
- `X,Z : Over (Spec (.of D.k))` with separated, locally finite type and quasi-compact
  structure maps give the separated finite-type k-schemes. A morphism of `Over`
  is exactly a morphism over k. `[IsClosedImmersion i.left]` is the closed immersion.
- `M` is in the actual small pro-etale derived category of fixed-scalar module
  sheaves. `_hM` uses the recorded `finiteTorConstructibleProEtaleModule`, which
  transports the intrinsic `finiteTorConstructible` through canonical realization.
- `finiteClosedScalar` reuses `ProEtale.pbcFixedScalarExtension` for ordinary
  uncompleted derived coefficient change. No arbitrary functor is quantified over.
- `finiteClosedExceptional` is `sfFiniteExceptionalFixed` at the canonical
  identity-open compactification of the closed immersion. `finiteClosedCounit`
  uses the published relative exceptional counit, preceded by the canonical
  closed compact-support/direct-image comparison. It assumes no ambient adjoint.
- `IsFiniteClosedShriekMap` is precisely the B-linear exceptional-counit equation:
  `i_*(b) ≫ ε_B = c_i⁻¹ ≫ S(ε_A)`. The map is selected only from this *unique*
  normalization, and the main theorem states that normalization has exactly one
  solution and that the selected map satisfies it. This specifies the adjoint
  mate, rather than selecting an unrelated isomorphism.
- The main theorem states `IsIso` for that comparison and the ordinary coefficient
  comparison used inversely, as well as finite-Tor constructibility of `M_B` and
  both displayed vertices over B.
- `finiteCoefficientClosedShriek_naturality` is the actual square for every
  morphism `f : M ⟶ N` of finite-Tor constructible inputs, not merely endomorphisms.
- `IsFiniteClosedComposition` uniquely normalizes the exceptional composition
  comparison by the pasted closed counits and `finiteDirectImageComposition`.
  `finiteCoefficientClosedShriek_comp` states its existence, normalization and
  invertibility on the relevant inputs and the two-path coefficient square.
- `finiteCoefficientClosedShriek_coefficientChain` quantifies a third finite
  coefficient field/stage and an arbitrary next map. Its equation displays
  `pbcFixedScalarExtensionComp` on both the source and target schemes.
- The chosen locally closed factorization has an independent source W, a closed
  leg `k : W ⟶ Z`, and an open leg `j : Z ⟶ X`. Its exceptional functor is
  `j^* ⋙ Rk^!`. `finiteLocallyClosedShriekMap` is exactly the closed comparison on
  `j^*M`, followed by `Rk_B^!` of the open coefficient comparison.
- The locally closed main theorem states `IsIso`, finite-Tor constructibility of
  both vertices, invertibility of the compact-support coefficient map and the
  pasted exceptional-counit equation. Three further theorems give its actual
  naturality square, coefficient-chain equation, and closed-composition equation
  inside the same chosen open.

All fallback zero definitions are total extensions outside the stated bounded,
quasi-compact, uniquely normalized or isomorphism domains. The conclusions explicitly assert the relevant uniqueness,
normalization and invertibility on the claimed inputs; no definition's data is `sorry`.

Dependency declarations used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.coefficientExtensionRing`, `Padic.finite_coefficientExtensionRing` (via
  `sfPositiveCoefficient_finite`).
- `Sheaf.Paper.FiniteTorAmplitudeProEtaleModule`:
  `WeilConjectures.finiteTorConstructibleProEtaleModule`, the published presentation
  of `WeilConjectures.finiteTorConstructible`.
- `Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage`:
  `AlgebraicGeometry.ProEtale.sfFiniteExceptionalFixed`.
- `Sheaf.Paper.FiniteCoefficientDirectImage`:
  `ProEtale.finiteCoefficientChangeDirectImageMap`, including its canonical
  ordinary-adjunction normalization; `ProEtale.finiteDirectImageComposition`.
- `Sheaf.Paper.WitnessCompatibility` (reexported by the preceding dependency):
  `ProEtale.pbcFixedScalarExtension`, `ProEtale.pbcFixedScalarExtensionComp`.
- The current upstream finite-coefficient closed-upper-shriek interface:
  `ProEtale.rightDerivedUpperShriekCounit` and
  `ProEtale.rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar`.
- `Sheaf.AlgebraicGeometry.CompactSupportRestrictionOfScalars`:
  `ProEtale.fixedScalarOpenAdjunction`, `fixedScalarRestrictionPullback`, and
  `fixedScalarRestrictionDirectImage`, whose conjugates specify the open maps.

Edge cases checked at the statement/source level: every positive exponent, including
one; arbitrary nonflat and identity coefficient maps; an independent third finite
extension; zero complexes; empty schemes; identity closed immersions; and an independent
locally closed source, without requiring it to equal Z. There is no nonemptiness or
extra universe equality hypothesis. No statement correction is proposed.

Searches in this repair: `msearch.py` LeanFinder for “Closed exceptional inverse image
commutes with derived change of finite coefficient rings” returned eight unrelated
algebra hits; Loogle for `"shriek"` returned none; Mathlib grep for
`closedShriek|finiteCoefficient.*Shriek` returned none. `rg` for the item id and the
same name patterns in the named upstream checkout and `lean/Sheaf` found no exact
existing comparison statement. The generic exceptional coefficient module is etale,
smooth and quotient-specific; it does not state this pro-etale closed result. Source
inspection used `scompile.py --source` when the local upstream API was stale.

The required initial dry run failed in the main file with universe inference errors
for scalar extension, derived-direct-image type mismatches, and the two missing
coefficient-chain equality signs. The four dependency modules compiled during that
run. Explicit `.{u}` universe instantiations now fix the
scalar-extension and scalar-restriction size; the direct/pullback aliases now give
their actual source/target derived categories explicitly. The first explicit-universe pass exposed a further inference problem in the
implicit essentially-small witness, plus the published quasi-compact-target requirement
for the exceptional counit. A minimal probe with the actual imports confirmed that
passing `essentiallySmallSelf.{0, u, u + 1} _` explicitly fixes scalar extension without
any global instance changes. This witness is now passed explicitly to scalar extension,
restriction and coefficient reassociation; the adjunction definitions use it locally too.
The counit guards target quasi-compactness, already implied by the theorem hypotheses.
These are elaboration repairs, with no new universe-equality hypothesis. The updated five-file packet passed the prescribed `scompile.py` check, both
sandbox and library compilation, with no errors or non-sorry warnings. Delivery
preflight is the remaining required check; no push is claimed before it finishes. The saved packet initially still contained a zero
exceptional counit and two coefficient-chain expressions missing their equality signs.
Those defects are repaired in the actual module: `finiteClosedCounit` now uses
`rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar` and
`rightDerivedUpperShriekCounit`, at the identity-open proper compactification,
with zero used only outside a quasi-compact target and D⁺. The theorem targets
are quasi-compact because they are finite type over k. Both chain assertions are equations.

## Dependency modules

`lem-coef-finite-direct-image`: an import-only §1(B) repair in its existing owning
module `Sheaf.Paper.FiniteCoefficientDirectImage`. The full canonical map definitions,
normalizations and all etale/pro-etale assertions are retained verbatim. Its old import
closure cannot load with the canonical finite-coefficient exceptional interface,
reporting a duplicate `upperStarIsoLowerStarInv`. Imports are reduced to the canonical
finite-coefficient modules and the named side modules used by its signatures. The
mathematical interface is unchanged; only `lean` in the dependency's node changes.

`lem-weil-derived-direct-image-composition`: the same import-only repair to the existing
`Sheaf.Paper.FiniteDirectImageComposition`. Its construction deriving the actual
underived pasting isomorphism is unchanged. The node is added to the item's statement
dependencies because its canonical comparator occurs in the counit normalization of
the exceptional composition map. It already has a landed Lean record. Only `lean` in
this dependency node changes.

`lem-weil-proetale-direct-image-restriction-of-scalars`: retains every declaration
in `Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage`, replacing
its legacy imports by canonical finite-coefficient imports. Its full K-injective
normalization remains unchanged. Only the node's `lean` changes.

`lem-sf-compact-support-restriction-of-scalars`: supplies the existing full fixed-scalar
`Sheaf.AlgebraicGeometry.CompactSupportRestrictionOfScalars` interface with reduced
canonical imports, including the open adjunction, normalized open restriction
comparison, compact-support comparison and coefficient cocycle. The previous record
used the equivalent intrinsic presentation; this consumer uses the fixed-scalar
coordinates of the exceptional functor. Its formulas are retained verbatim, and
only its `lean` record is changed. Both nodes are added to the item's `stmt_deps`.
The canonical imports do not export the legacy derived-open-adjunction abbreviation.
In `fixedScalarOpenAdjunction` its call is unfolded to its exact upstream defining
expression: `openImmersionLowerShriekUpperStarAdjunction` followed by
`mapDerivedCategoryAdjunction`. This preserves the adjunction data definitionally.
The module's remaining declarations are verbatim; its node note records this unfolding.

## Second reading by Q50

This is the dispatcher's requested worker self-check, performed with the node and
all five delivered modules open; independent review belongs to the maintainer.

H1: the main module exists in the sandbox, and its node records its real main
signature and every helper/statement. Each of the four dependency modules is also
owned by exactly one dependency-node record. H2: comparison with the current shared
node files shows that only `lean` changes for the dependencies; for the item only
`lean` and three added, already landed `stmt_deps` change. The stage-1 split fields
are retained from the current shared base; this delivery contains no stage-1 split.
H12: the old unsplit new statement node is absent. H10/H11: validation below refers
only to these five actual files, and not to the absent file claimed by the old head.

The global datum, distinct prime, both finite Padic extensions, all positive levels,
and arbitrary unital homomorphism are explicit in every assertion. The scheme
binders express separated finite type over k and a morphism over k; the input uses
the recorded intrinsic finite-Tor constructibility via its realization predicate.
The exceptional functor is the recorded comparison transport, and the ordinary
coefficient map is the dependency's counit-defined comparison. The repaired counit
is the published exceptional counit under the canonical closed compact-support
identification; it is not a zero substitute on the claimed domain. The current published bounded-below
exceptional interface requires a quasi-compact target; the definition guards that
property, which the finite-type-over-k hypotheses imply, rather than adding a premise
to any theorem. Its equation
uniquely defines b; the main theorem asserts that uniqueness, that same equation,
IsIso, and B-finite-Tor constructibility of both vertices. Naturality is checked for
two independent finite-Tor inputs and any morphism between them. Closed composition
uses the actual direct-image compositor and pasted counits. The scalar-extension and scalar-restriction calls use the declared site universe
explicitly, and the direct/pullback aliases state their category types. The coefficient-chain
square now has its missing `=` restored, on both schemes, with the recorded tensor
reassociation. The independent locally closed source W, closed k and open j give
exactly Rk! j*; its map, counit, naturality, coefficient-chain equation and closed
composition inside V are all present. No clause is replaced by True or a chosen
unconstrained map. No additional statement correction or new node is needed.

For the four dependency modules, source comparison confirms identical declaration
bodies and signatures, except unfolding the open adjunction to its defining
expression; changes otherwise concern only canonical imports. Their source and
blueprint docstrings, naturality/normalization/coherence assertions, and real
construction data are retained. All theorem proofs remain sorry. The level-one,
identity/nonflat coefficient, identity immersion, zero/empty, and independent-W
cases remain within the stated binders.

Validation: `scompile.py Q50 lem-coef-finite-closed-shriek` with all five module
paths completed with exit 0 on 2026-10-17 UTC. Every delivered file was checked
separately in dependency order against the prescribed private overlay. No combined
source file, global build, direct shared-repository write or Git mutation was used.
The report's second reading and node records refer to exactly this packet.
