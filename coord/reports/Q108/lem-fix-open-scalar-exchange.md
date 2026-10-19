## Worker report

The module `Sheaf.SecSmoothPurity.OpenScalarExchange` states the requested scalar/open
exchange theorem in `AlgebraicGeometry.ProEtale.openScalarExchange`.  It also gives the
constant-ring specializations used to render every object in the statement:
`scalarExtension`, `scalarRestriction`, `constantPullback`, `openExtension`,
`tensorPullbackIso`, `openScalarIso`, and `openBaseChangeIso`.  The latter is the inverse
of the canonical open-adjunction mate, with the mate-isomorphism assertion isolated as
the named postponed theorem `openBaseChangeMate_isIso`.

The hypotheses are rendered as follows.  `A B : Type u` with `[CommRing A]` and
`[CommRing B]` render the finite commutative coefficient rings, and `[Finite A]` and
`[Finite B]` render finiteness.  `φ : A →+* B` is the coefficient homomorphism.  The
four schemes and morphisms `gU`, `j'`, `j`, and `g` render the displayed square, while
`OpenImmersionSquare gU j' j g` supplies its commutativity and chosen Cartesian square;
`[IsOpenImmersion j]` and `[IsOpenImmersion j']` render the two open immersions.  The
object `K` is exactly an object of the unbounded derived category of constant-
`A` pro-etale modules on `U`.

The conclusion is rendered term by term.  `openScalarIso φ j` and
`openScalarIso φ j'` are the two scalar/open left-adjoint comparisons `β_j` and
`β_{j'}`.  `tensorPullbackIso φ g` and `tensorPullbackIso φ gU` are the canonical
inverse-image tensor comparisons `λ_g` and `λ_h`.  `openBaseChangeIso gU j' j g sq`
is the actual open base-change comparison `e_j`, obtained from the ambient pullback
comparison and the open adjunction mate.  Functor maps and composition in the displayed
Lean equality give, in order, the three composites on the two sides of the node's
formula, with the same source and target in the derived category over `X'` with
coefficients `B`.  No flatness or finite-projective-dimension assumption is added.

The dependency declarations used are: `AlgebraicGeometry.OpenImmersionSquare` from
`Sheaf.AlgebraicGeometry.OpenImmersionSquare`; `Scheme.proEtaleRingDerivedExtension`
and the derived change-of-rings adjunction from `Sheaf.Paper.FourCorners` and
`Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`;
`Scheme.proEtaleReductionPullbackIso` from `Sheaf.Paper.FourCorners`;
`Scheme.proEtaleRingDerivedOpenAdjunction` and
`Scheme.proEtaleRingDerivedOpenExtension` from
`Sheaf.Paper.ProjectionFormulaCompactified`; and the constant-ring comparison and
composition theorem from `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`,
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`, and
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison`.  The ambient
comparison is `Scheme.proEtaleAmbientRingedPullbackComparison` from
`Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange`.

Edge cases checked were identity morphisms (the square and constant comparison reduce
to identity comparisons), zero coefficient rings and zero objects (all constructions
remain ordinary derived functors), identity coefficient maps, and arbitrary `g` (no
flatness, properness, or finite-projective-dimension class is introduced).  The
composition equality uses the square's explicit commutativity proof and does not assume
that `g` is an open immersion.

Searches made before writing the module included:

- `msearch.py Q108 lem-fix-open-scalar-exchange leanfinder "scalar extension open immersion base change exchange"`;
  no exact project declaration was returned.
- `msearch.py Q108 lem-fix-open-scalar-exchange loogle "openImmersionLowerShriekBaseChangeMap, proEtaleAmbientRingedPullbackComparison, proEtaleRingDerivedOpenAdjunction"`;
  the published pro-etale mate and ambient comparison interfaces were found, but no
  constant-ring derived exchange theorem matching this node.
- `msearch.py Q108 lem-fix-open-scalar-exchange grep "open.*BaseChange|scalar.*Exchange"`;
  existing declarations were generic or strict-tower specializations.
- `rg` over `WeilConjectures/` and `lean/Sheaf/` for
  `lem-fix-open-scalar-exchange`, `openScalarExchange`, and
  `proEtaleRingDerivedOpenAdjunction`; no exact item declaration exists.
- `rg` over the Mathlib source for open-extension scalar exchange; no matching notion
  exists there.

No `STATEMENT-DISPUTED` flag or node fault was found.  No new DAG node was needed: the
missing ringed mate normalization belongs to this item and is recorded as the named
helper theorem `openBaseChangeMate_isIso` in the owning module, with its proof postponed
for stage 3.

## Second reading by Q108

I reread the node and the module independently.  The theorem has exactly the node's
finite-ring hypotheses, square data, open-immersion assumptions, arbitrary `g`, and
unbounded constant-ring derived-category object.  Each clause of the displayed
composition is present in the same order, and the helper constructions use the
recorded canonical comparisons rather than a freely chosen map.  No mismatch was found.

## Maintainer review fix (2026-10-18)

The open base-change map `openBaseChangeIso` was a second construction of the notion of
lem-cbc-proetale-extension-zero-base-change (a private ambient-pullback mate with its own
postponed invertibility theorem `openBaseChangeMate_isIso`), although the node uses "the
actual base-change map" of that dependency and proof steps 3–4 use its recorded inverse-unit
normalization (lem-cbc-finite-open-exchange-scalars, stated for `StrictTower.singleBeta`).
`openBaseChangeIso` is now `StrictTower.singleBeta (ULift A)`: its `coefficients`,
`modulePullback` and `moduleJ` are definitionally `proEtaleConstantRing`, `constantPullback`
and `openExtension` here, and the cartesian hypothesis is
`IsPullback.of_iso_pullback` from the chosen square. `openBaseChangeMate` and
`openBaseChangeMate_isIso` are removed. Helper docstrings now give source places and
blueprint ids, and the item docstring gives the node's proof steps. The item signature
is unchanged. Compiled clean with nt_compile.py.
