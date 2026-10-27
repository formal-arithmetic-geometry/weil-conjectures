## Worker report

The module `Sheaf.Paper.CompletedOpenFiniteTransposeCoherence` states the two
finite-reduction/open-transpose identities, naturality, and their strict-chain
transpose version. All three theorem proofs are `sorry`; all helper definitions
are actual composites of published functors, isomorphisms, units and counits.
The original mathematical statement and proof are unchanged. The repair adds three definition-node owners for the published scalar/open,
quotient/open, scalar/pullback and universal-counit transport constructions.
`unitArrow` constructs its integral `StrictTowerRingedSquare` inline using the
recorded `def-weil-pbc-strict-tower-operations`; the unused completed-reduction
pullback-square theorem is no longer a statement dependency.

### Hypotheses and objects

- The coefficient ring is `A : Type (u + 1)` with `[CommRing A]` and
  `d : AdicCoefficientDatum A`. This existing datum includes the ideal,
  Noetherian property, finite generation, additive torsion of A/I, perfectness
  of every positive quotient, and finiteness of every positive quotient. Its
  completed ring is the limit of the recorded function coefficient sheaves.
  Index `n : ℕ` means the positive exponent `n+1`, including the first quotient.
- The four schemes are `U' U T' T : Scheme.{u}`. The four named morphisms and
  `sq : OpenImmersionSquare v j' j g` supply the cartesian square, its chosen
  pullback identification, and open immersions on both vertical edges.
  The explicit open-immersion instances are the same proof-irrelevant properties
  contained in `sq`; they do not impose any additional mathematical condition.
- The pro-etale sites have objects in `u+1` and morphisms in `u`; no equality
  between these universes has been imposed. The completed and constant module
  categories use coefficient/module universe `u+1`.
- `K : d.derived U` is arbitrary in the ordinary unbounded derived category
  of completed-ring module sheaves. No intrinsic completeness property occurs.
- `source` is Q: completed open extension of K, its whole strict reduction tower,
  then `completedTowerPullback g d`. `corner` is C: reduction followed by strict
  pullback along v. `restricted` is M: reduction followed by `exchangeTowerRes`.
  `openTarget` is H = G_v M, and `ambientTarget` is N = G_g J_j M.
  These are abbreviations for the existing constructions, not new categories.
- `cbcRealizationTowerAdj` is the completed-ring open adjunction, with its
  section-normalized ordinary unit descended termwise. `StrictTower.jAdj` is
  the recorded constant-A open adjunction.

### Specified comparisons and conclusions

- `sourceComparison` is a. It first applies scalar restriction to the universal
  actual-to-datum pullback transport, next the fixed scalar/pullback comparison,
  then G_g of `cbcRealizationQuotientOpen`. The last map includes the canonical
  quotient/open tensor identification before scalar/open transport.
- `cornerComparison` is d, using exactly the same universal transport and
  scalar/pullback comparison at v on the reduction tower of K.
- The e used here is `cbcRealizationTowerScalarOpen`. Its ordinary input is
  `cbcRealizationScalarOpen`, the scalar/open mate characterized by the identity
  on the underlying extension presheaves and sheafification. `extensionComparison`
  is e followed by J_j' of d, exactly b = J_j'(d)e.
- The c in the node is `(exchangeResPull d j').hom`: scalar restriction after
  completed open pullback to constant open inverse image after scalar restriction.
  `psi` is, in Lean composition order, d.inv, r(x), c_Q, G_j'(a.hom).
- The first conjunct of `completedOpenFiniteTransposeCoherence` quantifies over
  EVERY morphism x in the derived strict-tower category, including roofs. Its
  left side is b.inv followed by r of the inverse Hom-equivalence transpose of x,
  followed by a.hom. Its right side is J_j'(Psi x) followed by the actual constant
  open counit at N. These are the two maps in the first displayed identity.
- `unitArrow` is the special x. Transport C to the datum pullback, apply v-pullback
  to the completed strict open unit, then the inverse integral square compositor,
  then j'-pullback of the inverse quotient/open identification and inverse actual
  pullback transport. Thus its target is the original Q, rather than a separately
  chosen isomorphic object. `constantSquare` uses the existing unit-preserving
  compositors and the equality `sq.w`; it is G_v G_j to G_j' G_g in mathematical
  composition order. The second conjunct asserts Psi(unitArrow) equals G_v of
  the constant open unit followed by this specified compositor.
- `completedOpenFiniteTransposeCoherence_naturality` gives naturality in K
  and arbitrary x simultaneously. Its hypothesis `hxy` is precisely the input
  arrow-square commutativity; its first conclusion is the corresponding Psi
  square. Its second conclusion is naturality of the special `unitArrow`.
- `strictScalarOpen` is the whole-diagram whiskering of the SAME presheaf-identity
  e. `completedOpenFiniteTransposeCoherence_strict` states the transpose equation
  for arbitrary cochain maps x of strict towers before localization. The types
  are `CochainComplex (d.towers _) ℤ`, so the equation is one equality of chain
  maps, including every quotient transition and differential. The ordinary
  adjunction is the termwise published normalized open adjunction. Its exact
  derived descent, conjugated by a,d, is the first derived formula. The special
  unit formula is specified by `unitArrow` and the second derived equality;
  its proof docstring gives the simultaneous flat-term K-flat calculation,
  scalar insertion, coefficient-transition formula, and universal descent.
- Nothing assumes completeness, quasi-compactness, etale origin, nonempty
  schemes or a bound on degrees. No equality is inferred from derived evaluations.

### Dependency declarations used

The recorded dependencies are retained through their published modules, including
public reexports of the integral strict pullback in `PbcQbarCompletedPullback`.

| Node/interface | Module and declarations used |
| --- | --- |
| Adic datum and reduction | `Sheaf.Paper.AdicCoefficientDatum`: `AdicCoefficientDatum`, `.derived`, `.towers`, `completedReductionTower`, completed ring and projection helpers |
| Open square | `Sheaf.AlgebraicGeometry.OpenImmersionSquare`: `AlgebraicGeometry.OpenImmersionSquare`, inherited `ChosenCartesianSquare` and `.w` |
| Exact open adjunction | `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`: `SheafOfModules.localizedSystemExtension`, `.localizedSystemRestriction`, `.localizedSystemAdjunction`; transported open functors below |
| Completed pullback | `Sheaf.Paper.PbcQbarCompletedPullback` and its public integral imports: `completedTowerPullback`; `CompletedOpenExchangeTransport.cbcDatumTowerTransport` retains its universal counit |
| Scalar restriction | `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`: `SheafOfModules.restrictScalars`, through `exchangeTowerModuleRes` and `exchangeTowerRes` |
| Constant towers | `Sheaf.AlgebraicGeometry.StrictConstantTowerOperations`: `ProEtale.StrictTower.G`, `.gComp`, `.Derived` |
| Constant open extension | `Sheaf.AlgebraicGeometry.StrictTowerOpenExtension`: `ProEtale.StrictTower.J`, `.jAdj`, `.moduleJAdj`, `.towerJ` |
| Completion comparison | `Sheaf.Paper.ConstantCompletionEquivalence`: finite/scalar comparison normalization; specialized here by published `exchangeResPull` and actual/datum transport |
| Open tensor normalization | `Sheaf.SixFunctors.OpenTensorNormalization`: `SheafOfModules.openTensorNormalization`; the published reduction/open comparison below has the specified open-unit transpose formula |
| Mates and transposes | `Mathlib.CategoryTheory.Adjunction.Mates`: `CategoryTheory.mateEquiv`; actual arrow transposes use `Adjunction.homEquiv` |
| Extension presheaf | `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`: `SheafOfModules.extensionByZeroPresheaf` |
| Module sheafification | `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`: `PresheafOfModules.sheafification` and `.sheafificationAdjunction` |
| Integral square | `Sheaf.Paper.StrictTowerOperations`: `StrictTowerRingedSquare` and `.exchangeTowerSquare`; the four rings, four coefficient identifications and coherence are supplied inline from `d` |

The three new definition nodes below own the already published construction
interfaces, using the return's explicitly permitted `existing: true` option.
Their `lean.module` points to each actual source module, so the consumer imports
those modules directly. In particular the realization module remains a source
import for its existing definitions; the new node does not cite its realization
theorem. No claim is made that the physical source definitions have been moved.
The mathematical definition-dependency graph is now below the finite-transpose
item, rather than through its downstream realization theorem. A later source
extraction can move these declarations without changing their construction or
requiring a second definition. This delivery edits no published source module.

All already stated proof-dependency modules are imported as ordinary imports.
`lem-cbc-ringed-open-scalar-adjunction` has no published Lean record, so there is
no proof-only import for it. This stage states the conclusion with `sorry`; it
neither assumes that missing theorem nor chooses data from its existence.

### Edge cases checked

The identity open and identity base-change maps give the same unit-preserving
compositors and transpose formulas. The empty open and empty schemes are included:
extension is the zero module functor where appropriate and all maps remain typed.
The zero complex, zero ring, I = A (zero finite quotients), and I = 0 when the
existing datum's finite/perfect quotient assumptions hold have the same formulas.
Positive index zero is not lost: it denotes A/I. All integer degrees and arbitrary
strict transition maps are allowed. In particular neither C nor its finite
reductions are required to be K-flat: the proof plan resolves strict diagrams
simultaneously and never infers equality from unrelated finite derived maps.
No statement dispute or source-based statement correction was needed.

### Searches and validation

Searches are recorded by the prescribed msearch wrapper in `searches.jsonl`:

- LeanFinder: “Finite reduction of completed coefficient sheaves preserves open
  extension by zero adjunction transpose on derived strict towers” returned eight
  results, including `Condensed.profiniteSolidCounit`,
  `SheafOfModules.Presentation.map_π_eq`, and elementary adic completion lemmas;
  none is this strict open transpose statement.
- Loogle: `CategoryTheory.Adjunction.homEquiv` returned the general Hom bijection
  and its naturality/counit equations. These give the transpose notation, not
  the finite reduction/scalar/open compatibility asserted here.
- Mathlib grep, CategoryTheory: `open.*transpose|transpose.*open` and the reverse
  order returned zero matches.
- LeanSearch: “Finite reduction of completed sheaves intertwines extension by
  zero adjunction transposes on strict derived inverse systems” returned generic
  sheaf adjunctions, degree-zero derived comparisons, and constantSheafAdj;
  no matching finite-transpose theorem.
- `rg` searched `lean/Sheaf`, `lean/WeilConjectures`, and
  `dag/lean_names_upstream.json` for the proposed declaration names and related
  open/scalar/transpose names. Existing scalar/open constructions and downstream
  strict mate statements were read and reused; no exact statement was found.
  Searching the literal node id in `lean/WeilConjectures` returned no declaration.

The repaired file is checked with scompile.py against the current published
library. A first attempt caught the inline record's field separators; these were
repaired. Final compile and delivery-preflight results are recorded below.
All universes and variables are explicitly bound (`autoImplicit false`).
No library build, local compile, direct git operation, or live source edit was run.

## New nodes

- `def-cbc-completed-open-scalar-quotient-interface` records existing definitions
  in `Sheaf.Paper.CompleteProetaleStrictTowerRealization`: ordinary normalized open
  adjunction, whole-tower open extension and derived adjunction; scalar/open mate
  and its inverse; reduced open-unit transpose and its inverse; their composite
  quotient/open/scalar comparison. Its statement explicitly includes the two
  named invertibility assertions used to form these inverses and naturality of
  the quotient/open transpose. These are construction properties, not the
  realization theorem or the finite-transpose conclusion.
- `def-cbc-completed-scalar-pullback-interface` records existing `exchangeScalar`,
  `exchangeTowerModuleRes`, `exchangeTowerRes`, `exchangeConstantPull`,
  `exchangeOrdinaryResPull`, `exchangeModuleResPull` and `exchangeResPull` in
  `Sheaf.Paper.StrictTowerExchangeMateNormalization`. The statement gives the
  constant-section scalar map and the actual ordinary, strict and exactly
  descended scalar/pullback comparisons; no exchange-mate normalization theorem
  is assumed.
- `def-cbc-completed-pullback-counit-transport` records the existing
  `cbcDatumTowerTransport`, the unique universal-counit-normalized comparison,
  its normalization predicate and ordinary/complex functor identifications in
  `Sheaf.Paper.CompletedOpenExchangeTransport`. The predicate is
  `CategoryTheory.Functor.ExactDerivedCounitNormalization`; the other declarations
  are in `AlgebraicGeometry.Scheme`. No extension-zero-comparison conclusion is
  used.

All three have precisely the H12 fields, the item's chapter and unit, the nearest
blueprint ancestor `thm-cbc-complete-proetale`, and the item's via prefixed by the
item itself. All use `existing: true` with no new module or `lean.file`, so there
is one definition per notion. The source is the supplied blueprint finite-open
comparison paragraph. Their statements introduce the adic datum and morphisms,
and cite exactly the recorded dependency nodes in their `stmt_deps`.

Searches were run for this repair, not inferred from unavailable services:
LeanSearch query “Canonical scalar restriction open extension and quotient open
adjunction comparisons on completed strict towers” returned eight generic module
restriction results; Loogle `CategoryTheory.mateEquiv` returned the mate bijection
and its equations; Mathlib grep `cbcRealizationTowerAdj|cbcDatumTowerTransport|
exchangeModuleResPull` returned zero matches. The full wrapper results are retained
in `searches.jsonl` and in each new node. Source grep found the three published
Sheaf implementations and no WeilConjectures implementation. The same declaration
search over definition-node lean records found no existing owner. Blueprint search
`cbcRealizationTowerAdj` returned zero matches. The existing implementations were
read with their docstrings and full signatures; the definitions are reused.

## Repair of the independent return on 593438773e76

1. The theorem dependency `lem-weil-pbc-completed-reduction-pullback-square` was
   added only by the returned packet; it is absent on current main and is removed
   from this packet. Its source module is no longer directly imported.
   `unitArrow` now literally constructs the same `StrictTowerRingedSquare` from
   `d.completedRing`, `d.integralRingIso` and `d.integral_coherent`, invoking the
   already recorded strict-tower operations. No use of the square theorem remains.
2. The unowned helper interfaces now have the three `existing: true` definition
   nodes above, all cited in the item. Their dependencies exclude the downstream
   realization, strict-mate-identification, mate-normalization and completed
   extension-zero-comparison theorem nodes. Physical imports point to the actual
   owning source modules under the explicitly allowed existing-ownership option;
   no duplicate declaration is introduced.

## Second reading by Q91

This is the dispatcher's worker self-check; the maintainer supplies the independent
reading. I compared the saved packet with current main by JSON field comparison:
only `lean` and `stmt_deps` differed before repair. The returned theorem text and
proof plans are retained. The main signature is byte-identical: the universal
quantifier over derived `x`, the transpose/counit equation, and the special unit
normalization are unchanged. The naturality input square and both output squares
are unchanged, as is the equality of strict cochain maps including transitions.
The only changed Lean term is the ringed-square literal in `unitArrow`, whose
nine fields are exactly those of the old plain definition, with the same chosen
cartesian square. All parameters remain explicit, with no new hypothesis.

The new owner statements were checked against their actual composites: the scalar
mate uses the ordinary completed and constant open adjunctions; reduction is the
inverse of the transpose of the reduced unit; quotient/open is restriction of
that inverse followed by the same scalar/open comparison; strict pullback transport
is uniquely fixed by its universal resolving counit. In particular none is the
finite-transpose theorem being stated. The zero complex, empty schemes and empty
open, identity arrows, I=A, first positive quotient and arbitrary unbounded degrees
remain allowed. No target statement, dependency theorem statement, or unit statement
was changed.

Final validation: the repaired theorem passed scompile.py in sandbox mode (18.3 s)
and actual module-name mode (19.6 s), without diagnostics. The repaired dry run
passed server preflight and per-file compilation. The last metadata self-check
fixed extraction of `exchangeResPull`'s verbatim signature: the named argument
`(A := A)` is part of the signature, not the beginning of its definition body.
