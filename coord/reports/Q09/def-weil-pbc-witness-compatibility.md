## Worker report

The item is `AlgebraicGeometry.ProEtale.WitnessCompatibility` in
`Sheaf.Paper.WitnessCompatibility`. It defines WIT as a compatibility predicate.
The natural-language node statement and its dependencies are unchanged.
The repaired module compiled cleanly through scompile.py; the delivery dry run
is recorded below.

The clause-by-clause correspondence is as follows.

- The four schemes and arrows are the binders of `WitnessCompatibility`, and
  `_sq : ChosenCartesianSquare g' f' f g` retains the chosen fibre-product identification
  and projection equations. The square is not assumed proper or smooth.
- The fixed datum is `d : Scheme.AdicCoefficientDatum A`. Its ring is commutative;
  `.noetherian`, `.finitelyGenerated`, `.quotientTorsion`, `.quotientFinite`, and
  `.quotientPerfect` retain all six coefficient hypotheses. The published datum is independent of a
  scheme, so the same ideal and quotients
  are used on all four sites.
- `PbcQuotient d n` is the actual ideal quotient `A / I^(n+1)` with its quotient ring,
  finite-set proof and discrete topology. Thus Lean n=0 is the paper's positive level 1.
- `PbcWitnessAmbient` and `PbcWitnessEtale` use fixed-ring module sheaves. The former
  is identified with the node's ringed-coefficient category by its recorded canonical
  `finiteCoefficientRealization`; the latter is the recorded fixed-ring presentation
  of modules over the constant etale coefficient sheaf. Neither category is condensed
  modules or the completed coefficient category.
- The four ambient functors are `pbcWitnessDirectImage f d`, the same construction
  for f', and `pbcWitnessPullback g d` and its g' version. They transport the published `finiteCoefficientDerivedDirectImage` and
  `finiteCoefficientDerivedPullback` through the canonical realization and its inverse.
  No restriction to bounded constructible outputs occurs in these definitions.
- `pbcWitnessBoundedConstructible` uses the recorded strictly full constructible
  essential-image property after canonical coefficient realization. The full test
  subcategory `pbcWitnessReductionDomain` requires constructibility both before and
  after reduction, exactly as specified in the node. AMP is not a hypothesis: its
  input categories are already defined by the proetale-modules dependency, and its
  separate output-finiteness assertion is not used in this definition.
- `pbcFixedScalarExtension` is the left adjoint to actual exact derived restriction
  of scalars. Its universal property determines the derived extension, including for
  nonflat quotients. `pbcWitnessReduction` and `pbcWitnessEtaleReduction` specialize
  it to the actual quotient map `pbcWitnessQuotientMap`. The adic dependency supplies the
  ringed-sheaf reduction and its K-flat normalization with the same quotient maps.
- `PbcWitnessedTower.K` and `.theta` retain the ambient normalized levels and their
  adjacent reduction isomorphisms. Longer reductions are iterated adjacent reductions,
  and their normalizations are `pbcIteratedWitnessTheta`; length zero is identity.
  The canonical `pbcFixedScalarExtensionComp`, obtained from the actual composition
  isomorphism for restriction, identifies iterated reduction with direct quotient
  reduction. Hence the identity and successive quotient cocycles carry no extra choices.
- `.boundedBelow` is proof of membership in the recorded D+ on the realized ambient
  object, without fixing a lower bound. `.origin` is the published
  `EtaleOriginWitness`, retaining its actual etale D+ object L and isomorphism alpha.
  `pbcFixedOriginAlpha` reflects that alpha through the canonical realization and
  the recorded derived-composition isomorphism. It does not choose another origin.
- `.beta` is derived quotient normalization on L. `.compatibility` is precisely
  nu*(beta) followed by alpha equals reduction(alpha) followed by theta, with its
  source identified by the inverse canonical comparison-reduction mate.
  `pbcComparisonRestrict` is the conjugate of actual sectionwise commutation with
  coextension of scalars; its exact derived descent and adjunction mate define
  `pbcComparisonReductionMap`. Its named invertibility theorem characterizes this
  particular map on K-flat representatives; `pbcComparisonReduction` uses that map,
  rather than choosing a bare natural isomorphism.
- `PbcWitnessedTowerHom` retains both levelwise maps u and v, compatibility with
  theta and beta, and the displayed alpha square. Identities and composites are
  levelwise. `PbcWitnessedInputTowers` is its full subcategory of constructible levels.
- `PbcFamilyWitnessCompatibility` existentially supplies the natural reduction
  isomorphisms rho on the full test subcategories and a functor `lift` on witnessed
  towers. `hobj` identifies output ambient levels with F_n K_n. The first equality
  forces the ambient output maps to be F_n(u_n), up to only those equality transports.
  The final equality forces output theta to be rho followed by F_n(theta), again with
  only the stated object equality transports. The output category retains bounded-below
  origins and their beta/alpha compatibility, without an output constructibility premise.
- `WitnessCompatibility` conjoins this condition on the four specified source-target
  pairs (X,Y), (X',Y'), (Y,Y') and (X,X'). No universal existence assertion is added.

Dependency interfaces were read from their full signatures and docstrings:
`Sheaf.AlgebraicGeometry.ChosenCartesianSquare`, `AlgebraicGeometry.ChosenCartesianSquare`;
`Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`, `finiteCoefficientRealization`,
`finiteCoefficientComparison`, `FiniteCoefficientDerivedCategoryPlus`, and
`isBoundedConstructibleFiniteCoefficient`;
`Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage`,
`finiteCoefficientDerivedDirectImage`, `finiteCoefficientDerivedPullback`,
`finiteCoefficientUnrealization`, and `finiteCoefficientRealization_isEquivalence`;
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange`,
`CategoryTheory.Sheaf.derivedRestrictScalars` and `derivedRestrictScalarsCompIso`;
`Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`,
`SheafOfModules.derivedChangeOfRingsIndependentCoefficients` (independent site universes);
and `Sheaf.Paper.RingedTopoiCanonicalTensorPullback`, its representative-normalized
comparison and ordinary unit normalization. The current server source was obtained with
`scompile.py --source` where the older checkout lacked the module. The blueprint's
original definition was read on the server at its recorded source path: it asks exactly
for normalization commutation and carrying compatible retained origins for the four
finite-level functors. It explicitly says Stacks 09C9/09C2 do not assert this predicate.

Edge cases checked: n=0 is A/I, never A/I^0; zero-length reductions are identities;
equal and composite quotient maps use the canonical adjunction composition; zero rings,
zero objects, I=0, I=top and empty schemes are permitted. No characteristic, uniform
torsion exponent, completeness, quotient flatness, dimension, properness or output
constructibility is assumed. The small sites retain object universe u+1 and morphism
universe u, with coefficients u+1. All universes and variables are explicitly bound and
`autoImplicit false` is set. The supplied origin interface supports arbitrary finite
rings; WIT specializes it to the commutative quotient rings without redefining it.

Searches repeated with the prescribed wrappers: LeanFinder query
"Compatible retained etale origins for normalized towers and natural coefficient
reduction comparisons for four proetale derived functors" returned eight etale-algebra
results, not WIT; Loogle `CategoryTheory.Functor, CategoryTheory.NatTrans` returned generic
natural-transformation APIs; Mathlib grep `EtaleOriginWitness|witnessCompatibility|normalizedTower`
returned zero hits. Project/source rg for the names and the exact blueprint item id found
no existing WIT declaration. LeanSearch query
"Compatible retained etale origins for normalized inverse systems and natural coefficient
reduction comparisons for derived functors" was also attempted; its service returned
Internal Server Error, so no match or no-match verdict is claimed for that service.
The successful LeanFinder, Loogle and grep searches supply the search evidence.
The searches are retained in `searches.jsonl`. No new independent notion or new DAG
node is needed. No STATEMENT-DISPUTED or natural-language statement correction is asserted.

## Returned dependency-record repair

The return for immutable head 45e5e9a95aba identifies a stale replacement of
`def-weil-pbc-etale-origin-witness`. I opened the current DAG record and the full
published `Sheaf.Paper.EtaleOriginWitness` source using `scompile.py --source`.
Its `AlgebraicGeometry.ProEtale.EtaleOriginWitness` is exactly Q02's retained-pair
interface already used here: finite discrete ring, ambient D+ object K, actual
etale D+ object L, and the specified derived comparison isomorphism alpha.
The sandbox dependency node and module were removed from the delivery. WIT imports
the published module directly; this packet no longer overwrites its current record.

The same audit found that `def-weil-pbc-adic-coefficient-datum` now records Q39's
`Sheaf.Paper.CompletedAdicCoefficientDatum`, declaration
`AlgebraicGeometry.Scheme.AdicCoefficientDatum`. I read that full source and the
inherited `CompleteCoefficientDatum` signature. It retains the same Noetherian ring,
finitely generated ideal, torsion residue, perfect positive quotients and finite
quotient sets. The datum is independent of a scheme. WIT now binds that published
datum directly, and its raw positive quotient uses the same ideal.
`pbcWitnessQuotientMap` specializes the published `Scheme.adicQuotientMap` to
positive levels. It is an actual quotient map, not a new choice or new coefficient
datum. The coefficient dependency node and module were also removed from this
packet. Neither published dependency record is changed.

The current operations record also supplies the canonical realization-equivalence
instance. I removed the superseded local theorem `pbcWitnessRealization_isEquivalence`
and import that recorded operations module directly. The origin-reflection helper
is used only for commutative quotient coefficients and now uses the published instance.
The four fixed-presentation functors explicitly transport the recorded ringed-coefficient
derived operations by realization and its canonical inverse, so no alternative operation
is substituted for the node's functors.

The old independent second reading and validation are saved in the sandbox
scratchpad as history. Their interface checks are superseded by this repair; a new
second reader must inspect the changed datum binder, quotient-map specialization,
and use of the two published dependencies before delivery. No push is performed.

## Validation

The prescribed scompile.py invocation compiled the repaired module twice, as the
isolated sandbox module and its actual library module: 15.7 and 19.3 seconds.
It exited zero with no errors or warnings. Both checks used the current published
dependencies; no dependency replacement or global build was included.
The main lean.statement signature was compared verbatim against the file.
The required deliver2.py --no-push dry run printed OK for commit c779011286:
it compiles and passes preflight except for the independent second reading,
which the assigned second reader writes. The staged set contained only this
report, the item's node and WitnessCompatibility.lean; no dependency record or
module was staged. Nothing was pushed.

## Second reading by Q09

I independently opened the node, the current `WitnessCompatibility.lean`, every
statement dependency record, and the recorded declarations. The item has no
`statement_change` and no new definition or dependency module in this delivery.
The blueprint source note (Stacks 09C9 and 09C2) says WIT is a compatibility
predicate for retained etale origins; it does not assert WIT for every square.
The Lean statement and the node agree clause by clause:

1. The four schemes, four arrows, and chosen Cartesian square are the binders of
   `WitnessCompatibility` and `_sq : ChosenCartesianSquare g' f' f g`. The square
   is genuinely Cartesian through the dependency's chosen pullback data.
2. The single coefficient datum is `d : Scheme.AdicCoefficientDatum A`, with
   the recorded commutative, Noetherian, finitely generated, torsion, finite
   quotient, and perfect quotient fields. `PbcQuotient d n` is the actual
   quotient by `d.ideal ^ (n + 1)`, so Lean index zero is paper level one.
3. `PbcWitnessAmbient` and `PbcWitnessEtale` are the fixed-ring module-sheaf
   derived categories. The canonical realization and unrealization from
   `ProEtaleFiniteModules` transport the published finite-coefficient operations;
   no completed coefficient category or condensed module category is introduced.
4. `pbcWitnessDirectImage` and `pbcWitnessPullback` are the four ordinary
   ambient families at the pairs `(X,Y)`, `(X',Y')`, `(Y,Y')`, and `(X,X')`.
   The input property is `PbcWitnessedInputTowers`; the adjacent test domain
   requires both an object and its reduction to be bounded constructible.
   No output constructibility or AMP hypothesis is added.
5. `pbcFixedScalarExtension` is determined as the left adjoint to actual
   derived restriction of scalars, and the two reduction functors use the
   actual quotient maps. `pbcFixedScalarExtensionComp` supplies the canonical
   comparison for composite quotient maps, including nonflat quotients.
6. `PbcWitnessedTower` retains every level, bounded-below proof, retained
   `EtaleOriginWitness`, adjacent ambient normalizations `theta`, adjacent
   etale normalizations `beta`, and the displayed compatibility equation.
   `pbcIteratedWitnessReduction` and `pbcIteratedWitnessTheta` encode longer
   reductions by the composites of adjacent reductions, with length zero the
   identity; the canonical scalar-extension composition comparison is retained.
   Thus the identity and successive quotient cocycles are the generated
   coherence, with no independently chosen inconsistent longer maps.
7. `PbcWitnessedTowerHom` retains both levelwise maps, both normalization
   naturality equations, and the alpha square. Its category instance uses
   levelwise identities and composites. `PbcWitnessedInputTowers` is the full
   bounded-constructible subcategory.
8. `pbcFixedOriginAlpha` reflects the retained origin isomorphism through the
   canonical realization. `PbcWitnessedTower.compatibility` has exactly the
   source identification supplied by the canonical comparison-reduction mate:
   inverse comparison, reduction of the next alpha, then `theta` equals the
   inverse-image of `beta` followed by the current alpha.
9. `PbcFamilyWitnessCompatibility` existentially binds natural reduction
   isomorphisms `rho` on the full reduction domains and a functor `lift` on
   witnessed input towers. `hobj` fixes output levels to `F n`; the first
   equality fixes output maps to `F.map`; the second fixes output normalization
   to `rho` followed by `F` of the input normalization, with only the stated
   equality transports. The output retains bounded-below origins and their
   beta/alpha compatibility and has no output constructibility premise.
10. `WitnessCompatibility` is exactly the conjunction of the four family
    predicates. The chosen square is retained as the contextual hypothesis;
    no properness, smoothness, completeness, flatness, characteristic, uniform
    bound, or universal existence assertion is added.

Edge cases were checked: the fixed natural indexing has no empty-index omission;
`n = 0` means `A/I`; zero-length reductions are identities; zero rings and
objects, `I = 0`, `I = top`, empty or disconnected schemes, arbitrary
characteristic, and nonflat quotient maps remain allowed when the datum fields
hold. The site object universe is `u + 1`, morphisms use `u`, and coefficient
carriers use `u + 1`; no universe equality or extra size assumption is imposed.

I repeated the existing-definition searches with independent wording. LeanFinder
for “functorial lifts of normalized towers through an etale comparison functor
compatible with derived quotient reductions” returned only unrelated etale and
ring results. Loogle searches for tower/functor and natural-transformation APIs
returned no WIT predicate. Grep over Mathlib, `WeilConjectures`, and the side
Lean tree for `WitnessCompatibility`, `EtaleOriginWitness`, and normalized
witness towers found no existing declaration; the related `IsNormalizedTower`
notion lacks retained etale origins and the four-family predicate. The recorded
LeanSearch attempt was unavailable (Internal Server Error), as stated in the
worker evidence. No mismatch was found, so no Lean or node statement was
changed. The current module compiled with the prescribed `scompile.py` command
(exit zero, no errors or warnings).

## Maintainer reading, 2026-10-16

The independent immutable-delivery audit found local category-instance proofs in
WitnessCompatibility.lean (H5/H6). The complete replacement moves their obligations
to pbcWitnessedTower_id_laws, pbcWitnessedTower_comp_laws and
pbcWitnessedTower_category_laws, each stated with a source/blueprint docstring,
a proof plan and proof `sorry`. The real identity and composition data are
pbcWitnessedTowerId and pbcWitnessedTowerComp; the category instance uses their
named laws. These helpers belong to the witnessed-tower notion defined by this
node. They add no independent mathematical prerequisite, assumption or construction.
All five helpers are listed in the replacement lean record. The main signature,
mathematical predicate, retained pairs, quotient maps and dependency records stay
as delivered. Full clause, source, edge-case, universe and compiler checks are
recorded in the independent review.md.

The complete replacement was compiled through scompile.py using its actual library
path under fixes/lean/Sheaf/Paper: sandbox 15.6 seconds and library 17.3 seconds,
exit zero with no diagnostics. The immutable original also passed (10.3 and
17.9 seconds). No server confirmation was needed. The main lean.statement is
verbatim equal to the replacement signature; no line exceeds 100 characters.
