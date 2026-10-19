## Worker report

Reuse `AlgebraicGeometry.ProEtale.WitnessCompatibility` from the published module
`Sheaf.Paper.WitnessCompatibility` (`lean/Sheaf/Paper/WitnessCompatibility.lean`,
main declaration at line 455). The node already records this Q09 definition and its
independent review. This delivery marks the same declaration and supporting interface
`existing: true`, with branch `newtargets-dag`; it adds no Lean module, theorem, proof,
definition, or dependency. Every field outside `lean` is preserved. The existing
statement was extracted with `tools/stage2_delivery.py signature` and agrees verbatim
with `lean.statement`.

I read the complete existing module, the eight statement-dependency statements and
records, their recorded signatures and docstrings, and the blueprint source. The
blueprint file is absent in this read-only machine's literature directory, so I read
that exact file from the project server without modifying it. It defines WIT by
commutation with normalization and preservation of compatible retained origins. Its
source note explicitly distinguishes this predicate from per-level existence in
Stacks 09C2 and the hypothesis of 09C9. I also read the current published module using
`scompile.py --source Sheaf.Paper.WitnessCompatibility`; it agrees with the local
interface being reused.

Clause-by-clause correspondence:

- The schemes and four morphisms are the explicit implicit binders
  `{X' X Y' Y : Scheme.{u}}`, `{g' : X' ⟶ X}`, `{f' : X' ⟶ Y'}`,
  `{f : X ⟶ Y}`, `{g : Y' ⟶ Y}`. `_sq : ChosenCartesianSquare g' f' f g`
  retains the chosen pullback identification and commutativity. The predicate depends
  on the four operations, so it need not inspect the proof or identification `_sq`.
- The fixed adic datum is `d : Scheme.AdicCoefficientDatum A`, with the explicit
  section binders `{A : Type (u + 1)} [CommRing A]`. The datum inherits Noetherianness,
  finite generation of the ideal, additive torsion, and perfectness from
  `CompleteCoefficientDatum`; it adds finiteness of all positive quotients.
  `PbcQuotient d n = A ⧸ d.ideal ^ (n + 1)` reindexes all positive levels by `ℕ`.
  Thus Lean level zero is source level one, and none of the positive levels is lost.
- `PbcWitnessAmbient T d n` and `PbcWitnessEtale T d n` are the ambient pro-etale
  and etale derived categories of fixed-ring module sheaves. The canonical
  `finiteCoefficientRealization` identifies the former with the dependency's modules
  over the continuous-function coefficient sheaf. This is the recorded coefficient
  equivalence, not a new constant-coefficient convention for the completed ring.
- The four conjuncts of `WitnessCompatibility` are precisely
  `PbcFamilyWitnessCompatibility X Y d (pbcWitnessDirectImage f d)`, the analogous
  conjunct for `f' : X' ⟶ Y'`, and the two conjuncts for
  `pbcWitnessPullback g d : Y → Y'` and `pbcWitnessPullback g' d : X → X'`.
  The direct images conjugate the recorded ordinary ambient
  `finiteCoefficientDerivedDirectImage` by realization/unrealization; pullbacks
  conjugate the recorded exact `finiteCoefficientDerivedPullback` in the same way.
  There is no completed pushforward or output constructibility restriction.
- `pbcWitnessReduction` and `pbcWitnessEtaleReduction` are derived scalar extension
  along `pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n)`. The latter is the actual
  quotient map `Scheme.adicQuotientMap`, not an arbitrary coefficient homomorphism.
  `pbcFixedScalarExtension` is the left adjoint to actual derived restriction of
  scalars. Its universal property fixes the functor up to its canonical adjunction
  isomorphism. No flatness condition is imposed on the quotient map.
- `pbcWitnessBoundedConstructible` applies the dependency's
  `isBoundedConstructibleFiniteCoefficient` to canonical realization.
  `pbcWitnessReductionDomain T d n K` is exactly bounded constructibility of `K`
  at level `n+1` and of its reduction at level `n`. Its `.ι` is the full input
  subcategory on which `rho` is tested. No hypothesis `HasFiniteLevelAmplification`
  is present: AMP is cited only to identify the input categories, whose definition
  is supplied by the pro-etale-modules node.
- `PbcWitnessedTower.K`, `.theta` are the ambient levels and adjacent normalization
  isomorphisms. `.boundedBelow` is membership in the standard plus subcategory
  after realization, without any fixed lower bound. `.origin` uses the recorded
  `EtaleOriginWitness` pairs with the actual bounded-below etale object `.L` and
  retained comparison isomorphism `.alpha`; it does not replace pairs by existence.
- `PbcWitnessedTower.beta` supplies the etale coefficient-reduction isomorphisms.
  `.compatibility` is the first displayed equation, in Lean composition order:
  comparison inverse image of `beta.hom`, followed by `alpha.hom`, equals the
  inverse canonical tensor comparison, reduction of the next `alpha.hom`, then
  `theta.hom`. `pbcFixedOriginAlpha` reflects the original `.alpha` through the
  fully faithful canonical realization, retaining the same isomorphism.
  `pbcComparisonReduction` is the scalar-extension mate of the actual restriction
  comparison and supplies precisely the required identification of sources.
- Identity reductions and longer reductions are represented by consecutive composites,
  not additional freely chosen maps. `pbcIteratedWitnessReduction` has identity
  at length zero and recursively composes the adjacent reductions.
  `pbcIteratedWitnessTheta` similarly has `Iso.refl` at length zero and composites
  at longer lengths. `pbcFixedScalarExtensionComp` identifies these with direct
  quotient scalar extension. The same adjacent-composite convention applies to
  `beta` and `rho`; quotient cocycles thus impose no independent additional choices.
- `PbcWitnessedTowerHom.u` and `.v` are the two families of levelwise maps.
  `.theta_naturality` and `.beta_naturality` express compatibility with the two
  normalizations. `.origin_naturality` is exactly
  `alpha ≫ u = comparison.map v ≫ alpha`, the displayed retained-origin square.
  The existing tower category composes both maps levelwise.
- `PbcWitnessedInputTowers` is the full subcategory of such towers with all levels
  bounded constructible. `PbcFamilyWitnessCompatibility` existentially quantifies
  natural isomorphisms `rho` on the stated full test subcategory and a functor
  `lift : PbcWitnessedInputTowers T d ⥤ PbcWitnessedTower S d`.
  Thus it asserts functorial transport, rather than unrelated choices per object.
- `hobj` identifies every output level with `(F n).obj (P.obj.K n)`.
  The first conjunct identifies the underlying output morphism with `(F n).map`
  of the input morphism. The `eqToHom`s only transport through these object
  equalities. The final conjunct requires output `theta` to be `rho.hom.app`
  followed by `F n` applied to input `theta`, again with the explicit equality
  transports. It is exactly the prescribed output-normalization formula.
- Because the codomain of `lift` is `PbcWitnessedTower S d`, its retained output
  pairs are bounded below and satisfy the second displayed witness equation via
  that structure's `.beta` and `.compatibility`. It does not require bounded
  constructibility of outputs or assert WIT for arbitrary squares.

Dependency declarations read and used by the existing interface:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`, with `.isoPullback`, `.hom_fst`, `.hom_snd`.
- `Sheaf.Paper.CompletedAdicCoefficientDatum`:
  `AlgebraicGeometry.Scheme.AdicCoefficientDatum`; inherited coefficient fields in
  `Sheaf.Paper.CompleteCoefficientDatum`; `Scheme.adicQuotientMap` for actual quotients.
- `Sheaf.AlgebraicGeometry.FiniteLevelAmplification`:
  `AlgebraicGeometry.ProEtale.HasFiniteLevelAmplification` was read to check the
  referenced input categories. Its AMP property is deliberately not a WIT hypothesis.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage`:
  `finiteCoefficientDerivedDirectImage`, `finiteCoefficientDerivedPullback`,
  `finiteCoefficientRealization_isEquivalence`, `finiteCoefficientUnrealization`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `isBoundedConstructibleFiniteCoefficient`, `finiteCoefficientRealization`,
  `finiteCoefficientComparison` and the finite-coefficient ambient/plus categories.
- `Sheaf.Paper.EtaleOriginWitness`:
  `AlgebraicGeometry.ProEtale.EtaleOriginWitness`, including both fields.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`:
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`, the general
  K-flat derived scalar-extension interface with independent site universes.
  The reused fixed-ring presentation computes the same scalar extension by its
  adjunction to actual restriction, through the canonical coefficient equivalence.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullback`:
  `SheafOfModules.ringedTopoiCanonicalDerivedTensorPullback` and its uniquely
  representative-characterized tensor comparison were inspected. The existing module
  imports this dependency; its specialized `pbcComparisonReductionMap` is concretely
  the mate of the canonical comparison of actual derived restriction functors.
  No arbitrary natural isomorphism replaces that comparison.

Edge cases checked by reading the definitions: exponent one is Lean `n=0`;
length-zero iterated reduction is the identity; successive quotient maps are their
actual composites; zero objects, zero quotient rings, and the empty scheme are not
excluded by any nonzero or nonempty binder. No properness, flatness of reductions,
Noetherianness of schemes, uniform cohomological bound, AMP assumption, or output
constructibility is added. Identity morphisms and arbitrary input tower morphisms
remain included. The site retains its object universe `u+1` and morphism universe
`u`; the fixed-ring coefficient universe is the dependencies' `u+1` convention.
An empty class of normalized input towers still leaves the separately quantified
`rho` condition on its stated full input test category, as the node requires.

Searches made for this delivery:

- `msearch.py ... leanfinder "Compatibility of normalized coefficient reduction towers
  with retained etale-origin witnesses for four derived functor families"`: eight
  results, on etale algebra composition/presentations; none states this predicate.
- `msearch.py ... loogle "CategoryTheory.Functor, CategoryTheory.NatIso"`: unknown
  identifier `CategoryTheory.NatIso`, so this attempt is not evidence of absence.
  Reran with `CategoryTheory.NatTrans`: twelve general natural-transformation API
  results, none giving the four-family retained-witness predicate.
- `msearch.py ... leansearch "normalized inverse systems compatible etale origin
  witnesses derived scalar reduction"`: service unavailable (Internal Server Error).
  No mathematical conclusion is drawn from the unavailable service.
- `msearch.py ... grep "WitnessCompatibility|WitnessedTower|normalization.*witness"`:
  no Mathlib hits. Direct `rg` with the same expression in upstream
  `WeilConjectures/` returned no hits; the node-id search there also returned no hits.
- Direct `rg` in project `lean/Sheaf`: found the exact published definition at
  `Sheaf/Paper/WitnessCompatibility.lean:455` and its supporting tower declarations.
  This exact match is reused, following the one-definition-per-notion rule.

No statement correction, new node, dependency repair, or unresolved statement dispute
is needed. Existing theorem proofs in the reused module remain postponed; this
record-only delivery neither changes them nor claims proof completion.

Validation: the required `deliver2.py NA def-weil-pbc-witness-compatibility --no-push`
performs the existing-declaration compiler probes through `scompile.py` and the
current server preflight. No Lean source files are delivered. The independent second
reading and push are reserved for the next worker; this worker answers READY only
after the prescribed dry run prints OK.

## Second reading by NA

I reread the node statement, its source note (blueprint order 1352, with the distinction from
Stacks Tags 09C2 and 09C9), the complete existing module, and every recorded statement
dependency. The node introduces the following objects and clauses, matched here to the
existing Lean interface:

- A cartesian square consists of schemes `X' X Y' Y`, morphisms `g' f' f g`, and
  `_sq : ChosenCartesianSquare g' f' f g`; these are exactly the implicit binders and
  `_sq` of `WitnessCompatibility`.
- The fixed adic coefficient datum `(A,I)` and positive quotients are represented by
  `d : Scheme.AdicCoefficientDatum A` and `PbcQuotient d n = A ⧸ d.ideal ^ (n+1)`.
  Lean uses `n : ℕ` for source level `n+1`, so every positive level, including level one,
  occurs. The datum supplies the node's Noetherian, finite-generation, torsion,
  perfectness, and quotient-finiteness hypotheses through its recorded fields.
- The four ambient finite-level derived categories and the four operations are rendered by
  `PbcWitnessAmbient`, `PbcWitnessEtale`, `pbcWitnessDirectImage`, and
  `pbcWitnessPullback`. They use the recorded finite-coefficient realization and ordinary
  derived direct image/pullback. No output constructibility or AMP hypothesis is added.
- Coefficient reduction is the canonical quotient map
  `pbcWitnessQuotientMap d (n+1) n (Nat.le_succ n)`, with scalar extension fixed by the
  adjunction to actual restriction of scalars (`pbcWitnessReduction` and
  `pbcWitnessEtaleReduction`). Thus the map is canonical and no flatness is assumed.
- The input test class is `pbcWitnessReductionDomain`, requiring bounded constructibility at
  the next level and after reduction; the all-level tower class is
  `PbcWitnessedInputTowers`. This is the node's full bounded-constructible input domain.
- A normalized tower is `PbcWitnessedTower`: `K`, bounded-below proofs, retained
  `EtaleOriginWitness` pairs, adjacent `theta` and `beta`, and the displayed
  `compatibility` equation. `pbcIteratedWitnessReduction` and
  `pbcIteratedWitnessTheta` make identity and longer reductions the canonical composites,
  encoding the quotient cocycle without extra choices.
- Tower morphisms are `PbcWitnessedTowerHom`, whose `u` and `v` maps and
  `theta_naturality`, `beta_naturality`, and `origin_naturality` fields are exactly the
  three compatibility requirements in the source. The category instance uses the stated
  levelwise identity and composition.
- `PbcFamilyWitnessCompatibility` existentially supplies the natural reduction
  isomorphisms `rho`, a functor `lift` on the full witnessed input category, the object
  identification `hobj`, the levelwise output-map formula, and the output-normalization
  formula. This is the node's functorial transport of retained witnesses and does not
  assert that arbitrary squares have WIT.
- Finally, `WitnessCompatibility` is the conjunction of the four family predicates for
  `f`, `f'`, `g`, and `g'`, in the same order as the node.

Edge cases were checked in the definitions: `n=0` is the first positive quotient, length-zero
iterated reduction is identity, longer reductions are actual composites, zero objects and
zero quotient rings are allowed, and empty schemes or empty test subcategories are not
excluded. Identity morphisms and arbitrary tower morphisms remain in the full categories.
The site and coefficient universes are retained (`Scheme.{u}` and coefficient types in
`Type (u+1)`), with no universe equality or extra finiteness, flatness, properness,
Noetherian-scheme, dimension, AMP, or output-boundedness assumption introduced here.

Searches were rerun with `msearch.py` LeanFinder for normalized towers and étale-origin
compatibility (eight unrelated étale API hits), Loogle/LeanFinder natural-transformation
queries, and whole-tree `rg` searches in Mathlib and upstream `WeilConjectures`. No matching
predicate or declaration was found. The exact declaration and its supporting interface were
found only in `lean/Sheaf/Paper/WitnessCompatibility.lean`; `scompile.py --source
Sheaf.Paper.WitnessCompatibility` confirmed the current source. One malformed earlier
Loogle query (`CategoryTheory.NatIso`) was rerun with `CategoryTheory.NatTrans`; the latter
also produced only generic API declarations.

The only mismatch was the node copy's stale `lean` record (`existing: false`, old fixer
metadata) despite the already published exact declaration. I changed only that record to
`existing: true`, retained the verbatim signature and all supporting declarations, removed
the inapplicable file/fixer fields, and added the exact-existing note. No Lean module,
statement, dependency, or proof was changed; no statement correction or dependency repair
is needed.
