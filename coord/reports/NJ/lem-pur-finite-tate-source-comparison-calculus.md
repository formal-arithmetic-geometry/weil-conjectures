## Worker report

### Returned-delivery repair

The returned delivery's source maps used the plain structure map on both sides of
finite reduction.  I repaired this by copying the `φpur` source construction with
its source-side over-structure `g_X ≫ a_X`: the source scheme is
`Over.mk (g_X ≫ a_X)`, while the target scheme keeps `a_X`.  The helper's body is
the same `finiteReductionBaseChangeSource` composite as `φpur`, followed by the
strict map `φK`, with the twisted source structure passed explicitly.  The square
version uses the same construction for an arbitrary pullback Frobenius square.
The helper docstrings record that these are the unbundled definitionally equal
forms of the `φpur` composite.

### New nodes

`def-pur-finite-tate-source-map` defines the twisted canonical source map
`finiteTateSourceMap`, the corresponding square construction
`finiteTateSourceMapOfSquare`, and the pasted pullback comparison
`finiteTatePullbackComparison`.  The source-side structure is
`⟨g_X ≫ a_X⟩`, exactly the structure used in `Purity.φpur`; the target side is
`⟨a_X⟩`.  The square helper now has explicit over-k structures and uses the
passed Cartesian pullback witness.

### Worker report

The item module `Sheaf.Paper.PurityFiniteTateSourceComparisonCalculus` contains
`finiteTateSourceComparisonReduction` and
`finiteTateSourceComparisonCartesian`, each with a postponed `sorry` proof.

For the reduction clause, `P`, `f₀`, and `d` are the finite-field setting,
separated finite-type morphism, and smooth pure relative dimension.  `K` is the
finite-coefficient pro-etale derived object, `hK` is its finite-Tor
constructibility hypothesis, and `φK` is its strict Frobenius isomorphism.  The
`let` binders define the coefficient reductions `QX,QY`, the canonical
Frobenius comparison `C_Y`, the transported strict datum
`φK' = C_Y.symm ≪≫ QY.mapIso φK`, the original and reduced twisted source maps
`ψ,ψ'`, the canonical source comparison `a_P`, and the canonical `C_X`.  The
conclusion is the displayed equality
`QX.map ψ.hom ≫ a_P.hom = C_X.hom ≫ GX'.map a_P.hom ≫ ψ'.hom`.

For the Cartesian clause, `u,f',f,v` are morphisms of schemes over
`Spec k`; the four `IsOver` hypotheses make the ordinary derived pullbacks
coherent over the coefficient base.  `sq : ChosenCartesianSquare u f' f v`
provides the pullback witness
`IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd`.
The separated, finite-type, quasi-compact, and smooth hypotheses are stated for
both horizontal maps.  `gX,gX',gY,gY'` and `hX,hY` give the two commuting
Frobenius squares, with `hXpb` and `hX'pb` their pullback witnesses.  `C_X` and
`C_Y` are the canonical pasted pullback comparisons, `φK'` is the transported
strict datum, `ψ` and `ψ'` use `finiteTateSourceMapOfSquare` with the twisted
source structures, and `a_P` is the canonical ordinary derived base-change
source comparison.  The conclusion is the stated equality from the pulled-back
source to the primed Tate source.  No exceptional base change is asserted.

### Dependency declarations used

- `PurityFiniteSetting`, `frobeniusMap`, `frobeniusFiber`, and
  `frobeniusGaloisMap`: `Sheaf.SixFunctors.SchemeGeometricFrobenius`.
- `finiteReductionBaseChangeSource` and its pullback-square interface:
  `Sheaf.Paper.FiniteSmoothPullbackExchange`.
- `finiteReductionSourceComparison`, `finiteReductionPullbackComparison`, and
  coefficient reductions: `Sheaf.Paper.FiniteReductionComparisons`.
- `ChosenCartesianSquare`: `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`.
- The twisted source structure and strict datum are the `φpur` construction in
  `Sheaf.Paper.PurityTateDatum`; the delivered helper is its unbundled
  definitionally equal form.

### Edge cases checked

I checked `d = 0`, identity coefficient reduction (`m = n`), identity Cartesian
squares, identity Frobenius maps, and the zero derived object.  The source-side
twist remains present for positive `d`, specializes to the tensor-unit case at
`d = 0`, and all endpoints remain well-typed.

### Searches made

I searched with `msearch.py` LeanFinder and Loogle queries for finite Tate source
comparisons, pullback/tensor Frobenius naturality, and canonical reduction source
maps; with `rg` over `lean/Sheaf`, `lean/WeilConjectures`, and `dag/nodes`; and
with `grep` for the item identifier.  The searches found the component
comparisons and the landed `Purity.φpur`, but no prior finite source-comparison
calculus or twisted unbundled helper.  The new helper was compiled by
`scompile.py` against the live published build.

No `STATEMENT-DISPUTED` flag applies.

## Second reading by NJ

I reread the structure on both sides against `UniformPurityTateDatum.φpur`.
Every occurrence of the source finite-reduction functor is formed over
`g_X ≫ a_X`, and every target occurrence is formed over `a_X`.  The reduction
clause retains `1 ≤ m ≤ P.level`, finite-Tor `K`, strict `φK`, canonical `C_Y`,
`C_X`, and `a_P`.  The Cartesian clause now uses the chosen square itself,
explicit over-k morphisms, ordinary pullback comparisons, and the same twisted
source construction on both the original and primed Frobenius squares.  Both
postponed proofs and their proof-step docstrings remain present.
