## Worker report

The delivery states `AlgebraicGeometry.SmallSingularLocusPair.formalCompletion_geometry`
in `Sheaf.AlgebraicGeometry.SmallDivisorFormalCompletion`, with its proof `sorry`.
Two definition modules supply the missing formal geometry. Their data are constructed:
completion is the colimit of the infinitesimal thickenings in **ringed spaces**. Its
structure sheaf is consequently the inverse limit of the thickening structure sheaves;
this is not a colimit in schemes, an arbitrary ringed space, or a chosen existence witness.
The theorem includes the comparison with the formal spectra of actual adic chart rings.
There are no other postponed theorems, no new axioms, no unbound variables, and no
statement correction. The accepted stage-1 split is retained.

The previous worker ending described a stage-1 unchanged-item refusal. The current
queue lists the item at stage 2 with no Lean record. The current standing brief §0
explicitly distinguishes the two stages, so this packet proceeds through deliver2.py.

Hypotheses, one by one, are the fields of the already landed
`AlgebraicGeometry.SmallSingularLocusPair` in `Sheaf.AlgebraicGeometry.SmallSingularLocusPair`:

- `scheme : Scheme.{u}` and `structureMap : scheme ⟶ Spec (.of (ULift.{u} ℚ))`
  give the scheme over Q. The lift is the same convention as that definition.
- `reduced : IsReduced scheme` gives reducedness.
- `noetherian : IsNoetherian scheme` gives locally Noetherian and quasi-compact,
  equivalently the finite affine Noetherian cover in the node.
- `quasiExcellent : ∀ U : scheme.affineOpens, IsQuasiExcellent Γ(scheme,U.1)`
  gives quasi-excellence on every affine open.
- `divisor : scheme.IdealSheafData` and `cartier : divisor.IsInvertible` give the
  effective Cartier divisor, including its quasi-coherent ideal and inclusion.
  The actual recorded predicate is local generation by a non-zero-divisor.
- `singularSupport` puts every nonregular stalk point in the divisor support.
- `divisorPresentation` asserts the existence of `n`, `V : Fin n → Scheme`, fields
  `K i : CommRingCat`, finite-type maps `s i` (both `LocallyOfFiniteType` and
  `QuasiCompact`), and `Nonempty (divisor.subscheme ≅ ∐ V)`. Each `K i` has
  `IsField` and `CharZero`; the fields can differ. No presentation is fixed in the
  hypothesis. These are exactly the node's hypotheses, without a separatedness,
  irreducibility, reduced-divisor or common-field assumption.

Conclusions, clause by clause:

- `P.completion` is the constructed presentation `⟨P.scheme,P.divisor⟩`.
  `AdicFormalCompletion.IsNoetherianFormalSpace P.completion.space` asserts a finite
  open cover by formal spectra of complete separated Noetherian rings with finitely
  generated ideals of definition. The empty cover is permitted.
- `IsReducedQuasiExcellent` tests reducedness and `IsQuasiExcellent` on **every**
  complete Noetherian formal affine chart of the ringed space, including charts not
  inherited from X. It does not merely test a supplied list of rings.
- The next conjunct identifies `chartSpace U` with
  `formalSpectrum (.of (chartRing U)) (chartIdeal U)` for each ambient affine U.
  Here `chartRing U` is the actual `AdicCompletion (I.ideal U) Γ(X,U)`;
  `chartIdeal` is its extension of I. Thus the formal charts and sheaf in the
  statement refer to the specified completion, not independent formal objects.
- `Nonempty (space ≃ₜ closedFibre)` identifies its point space with that of the
  reduced closed fibre. `closedFibre` is `I.radical.subscheme`, allowing nonreduced D.
- `HasInvertibleIdealOfDefinition` says the extended ideals are finitely generated,
  their powers make the completed rings complete/separated, and on a finite affine
  cover their generators are non-zero-divisors. It requires no global generator.
- `IsFiniteDisjointUnionOfFormalVarieties` gives a finite pairwise-disjoint clopen
  cover, ringed-space isomorphisms to Noetherian formal completions on those pieces,
  and finite-type structure maps of their reduced closed fibres to characteristic-zero
  fields, independently for each piece. It supplies an actual partition of the formal
  space, in addition to a condition on its closed fibre.
- `HasCompletedSingularLocus` says **equality of ideals on every completed affine**:
  `absoluteSingularIdeal (chartRing U) = extendedIdeal (singularLocusIdeal X) U`.
  The left side is the vanishing ideal of the absolute nonregular locus, not the
  relative nonsmoothness ideal `Algebra.singularIdeal`. The right side uses the
  reduced closed singular subscheme. The construction `closedSubspace J` uses the
  sheaves of `X/(J+I^(n+1))`, so this equality identifies the global singular formal
  closed subscheme with the completion of X_sing: equality on the affine basis
  specifies the same closed subsheaf and the same quotient sheaf. It is stronger
  than equality of closed-point supports, as needed in the node.
- `IsRigRegular` supplies a **positive** power of `chartIdeal U` contained in the
  singular ideal for every original affine U. This is the node's open-ideal
  condition. Local existence of powers is equivalent to this version, since U is
  quasi-compact and finitely many exponents can be bounded above. No uniform
  exponent on all of X is assumed.
- `P.divisor = ⊤ → IsEmpty P.completion.space` gives the empty-divisor case. On the
  empty space the sheaf of rings is the zero sheaf, so this is the empty formal scheme.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Properties: `AlgebraicGeometry.IsReduced`, sectionwise
  reducedness and its stalkwise equivalent.
- Mathlib.AlgebraicGeometry.Noetherian: `IsLocallyNoetherian`, `IsNoetherian`, and
  the finite affine-cover characterization.
- Sheaf.RingTheory.ExcellentRing: `IsQuasiExcellent`, with its Noetherian, G-ring
  and J-2 clauses (not the stronger `IsExcellent`).
- Sheaf.AlgebraicGeometry.IsRegularScheme and WeilConjectures.AlgebraicGeometry.Regular:
  `IsRegularScheme = IsLocallyNoetherian ∧ IsRegular`, with the actual stalk predicate.
  Mathlib.RingTheory.RegularLocalRing.Defs supplies `IsRegularLocalRing` and
  `IsRegularRing` for the absolute singular ideals.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and Morphisms.QuasiCompact:
  `LocallyOfFiniteType` and `QuasiCompact`, used together for finite type.
- Mathlib.RingTheory.AdicCompletion.Basic and Algebra: `AdicCompletion`,
  `IsAdicComplete`, the ring and algebra structures and canonical algebra map.
- Sheaf.AlgebraicGeometry.SmallSingularLocusPair: the existing full input structure;
  WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible: its Cartier predicate.
- Mathlib.AlgebraicGeometry.IdealSheaf.Functorial and Subscheme: `IdealSheafData`,
  `subschemeFunctor`, `vanishingIdeal`, `radical`, and the canonical closed inclusions.
- Mathlib.Geometry.RingedSpace.Basic: `RingedSpace` and actual ringed-space colimits;
  Mathlib.CategoryTheory.Functor.OfSequence: the canonical thickening functor.

Every recorded stated proof-dependency module is imported with a plain import in the
item module. The only proof dependency without a declaration is
`lem-per-qe-complete-pair-lifting`; it is not needed to type the statement and no import
can yet name it. The other proof dependencies use their published upstream modules
or their precise Mathlib matches. There is no import cycle. The theorem docstring
carries all eight proof steps, including reduced base change, singular-ideal equality,
quotient-completion compatibility and overlap checks.

Edge cases checked: X empty; D empty, with I=top and all thickening rings zero; n=0
for the finite coproduct and clopen partition; a nonreduced divisor V(t^2), whose
reduced fibre uses radical I; the reduced node xy=0 with Cartier parameter x+y;
a regular X with nonempty divisor (singular ideal is top); multiple components
with different characteristic-zero fields; a nonprincipal invertible ideal
(the finite trivializing cover suffices). No nonempty or nontrivial-ring assumption
was added. Universes are explicit and autoImplicit is false in all modules.

Searches: `msearch.py` LeanFinder for the completion theorem, LeanSearch for formal
spectrum/completion, LeanFinder for Noetherian formal geometry, Loogle `"FormalScheme"`,
and Mathlib grep `FormalScheme|formalSpectrum|RigRegular|absoluteSingularIdeal`.
The raw outputs are retained in both new nodes' `mathlib_searches`: adic completion,
ordinary schemes, normalization, formal smoothness and relative singular ideals occur;
none provides the missing formal spectrum or absolute geometric interface. Direct rg
of both lean/WeilConjectures and lean/Sheaf, and the upstream name index, finds no
formal-scheme definitions or the newly introduced declaration names. The requested
node-id search in WeilConjectures finds no statement of the item. DAG searches found
only theorem nodes about formal completion, with no Lean records, and the already
landed SmallSingularLocusPair. The two blueprint_refs searches return zero blueprint
nodes for "formal scheme" and "formal completion"; ancestor returns
lem-per-artin-gabber-affine-curve. The current latest ancestor file was read; its
inherited resolution support is preserved, without changing its statement or route.

Source read: Temkin's Non_Embedded_Desingularization.pdf, §§2.4.1,2.4.3,2.4.9,2.4.11,
3.1.1--3.1.4, and the first paragraph of the proof of Theorem 3.4.1 (printed p.26).
No STATEMENT-DISPUTED flag and no dependency interface replacement are needed.

Validation: scompile.py compiled each of the three delivery modules separately in
dependency order against the published live library. All are clean; the sole expected
warning is that the main theorem uses sorry. The final dry run and push revalidate
all files and the node records on the server.

## New nodes

`def-per-adic-formal-completion`, module `Sheaf.AlgebraicGeometry.AdicFormalCompletion`,
constructs a formal completion presentation, infinitesimal thickening diagram, actual
ringed-space colimit, canonical ambient map, completed affine rings and extended
ideals, reduced closed fibre, formal spectrum and the finite Noetherian formal-cover
predicate. Source: Temkin §2.4 and the completion in Theorem 3.4.1. Each helper has
the node's source/blueprint docstring and is in lean.declarations. No existing DAG
node defines formal schemes or formal spectra; the recorded adic completion is a
ring/module construction and is reused inside these definitions. The searches above
are recorded verbatim in the node. No theorem or chart comparison is assumed as data.

`def-per-formal-completion-geometry`, module `Sheaf.AlgebraicGeometry.FormalCompletionGeometry`,
defines the absolute nonregular ideal, reduced singular subscheme, canonical presentation
of an existing small pair, and the reduced/quasi-excellent, invertible-definition-ideal,
formal-variety partition, completed-singular-locus and rig-regular predicates on the
constructed formal completion. Source: Temkin §§2.4.1,2.4.3,2.4.9,2.4.11 and 3.1.1,3.1.4.
These are constituent geometric definitions, with full data and no postponed claims.
The existing small-pair structure, ring regularity and quasi-excellence are reused.
The searches above find no equivalent formal-geometry interface; relative
`Algebra.singularIdeal` would specify the wrong locus. Both new nodes are cited
directly by the item; geometry also cites the completion node. Neither changes the
stage-1 proof or its dependencies.

Preflight repair: the live server requires `import_flags` on new definition nodes,
although the local brief field list omits it. Both new records now have empty lists;
the first dry run found no other defect. No tool or gate was changed.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
