## Worker report

The module `Sheaf.Paper.FrobeniusPullbackComparisonCoherence` states
`WeilConjectures.TraceFormulaCoefficientConventions.frobenius_pullback_comparison_coherence`.
Its only postponed theorem is this statement. The other five declarations are actual
constructions of the functor powers and their canonical comparisons, all belonging to
the notation introduced by this node. No new notion or mathematical statement correction is needed. A lean-only dependency
repair below records the smaller owning module of the same general comparison.

Hypotheses, matched against the node and the recorded definitions:

- `S : TraceFormulaCoefficientConventions.{u}` bundles the exact finite-field and
  coefficient conventions. `S.datum` stores the prime `p`, positive `a`, `q = p^a`,
  finite field `k₀` of cardinality `q`, and its fixed algebraic closure `k`.
- `S.coefficients` stores the prime `ℓ`, its inequality with `p`, and the chosen
  algebraic closure of the ℓ-adic coefficient field. `S.extension` is the finite
  extension in that closure. `S.coefficientField` is its already recorded small model;
  `S.coefficientRing` is exactly `Padic.coefficientExtensionRing ℓ E S.level`, the
  recorded quotient by the power of the chosen uniformizer. `S.level_pos` is `1 ≤ n`.
  No coefficient field, valuation ring, uniformizer or quotient is redefined.
- `S.X₀` is over `Spec k₀`; the instance fields `finite_type`, `quasi_compact`, and
  `separated` are respectively locally finite type, quasi-compactness (together finite
  type), and separatedness. `S.geometricBaseChange` is the recorded fibre product `X`.
- `S.datum.geometricGaloisFrobenius S.X₀` is the recorded geometric Galois map
  `id × Spec(γ)`, with `γ` the inverse q-power automorphism. Its construction was read
  in `SchemeFrobenius.lean` and `FrobeniusDetailed.lean`; it is not the scheme Frobenius.
- `frobeniusPullbackPower S r` uses `proEtaleConstantRingDerivedPullback` along the
  actual scheme-endomorphism power `g^(r+1)` and the actual coefficient ring. Thus
  every positive exponent is represented once, with no assumption on a derived object.
  The category is `proEtaleDerivedCategory S.geometricBaseChange S.coefficientRing`,
  the ambient ordinary unbounded category; bounded constructibility is not imposed.

Clauses of the conclusion:

- Index `r : ℕ` always means the source's positive integer `r+1`. In particular index
  zero is exponent one, and `S.frobeniusPullbackPower 0` is exactly `T = P₁`.
- `trfPositiveFunctorPower T 0 = T` and its successor is the preceding power `⋙ T`.
  Since Lean's `F ⋙ G` means `G ∘ F`, this is the requested parenthesization
  `T^(r+1) = T ∘ T^r`, not its reversed convention.
- `frobeniusPullbackPowerSplit S a b` is `C_(a+1,b+1)`. It transports only the equality
  of scheme powers, then uses the inverse of the published
  `proEtaleConstantRingPullbackComposition`. That helper is the constant-coefficient
  specialization of `proEtaleCanonicalPullbackComposition`, including the original
  termwise K-flat normalization; its definition uses the named equality between the
  canonical constant coefficient map and the composite map. No arbitrary comparison
  or extra compatibility assumption is supplied.
- `frobeniusPullbackPowerComparison S` constructs the natural isomorphisms by recursion:
  identity at exponent one, then `C_(1,r)` followed by whiskering `d_r` with `T`.
  The first conjunct explicitly records the source's identity normalization.
- For every `a b : ℕ`, the next two conjuncts say that expanding the root split
  `(a+1,b+1)` and expanding both branches, in either order, gives `d_(a+b+2)` followed
  by `trfPositiveFunctorPowerSplit T a b`. The latter consists solely of the canonical
  functor associators. This is an equivalent finite binary formulation of the node's
  quantification over every positive partition and every repeated splitting: expand a
  partition into an ordered binary tree; induction on that tree gives `d` at the root.
  Conversely each displayed binary expansion is a repeated splitting covered by the
  source's assertion. Both orders of refining the two branches are included explicitly;
  applying the same statement inside each whiskered context covers interleavings at
  deeper vertices. Reassociation corresponds to choosing another binary tree. A
  one-part partition introduces no root split and retains the identity normalization.
- In the final conjunct, `r : ℕ` represents the source's `r+1 ≥ 1`, and `M` is any
  object of the ambient unbounded category. Its left side is `T(d_r)` followed by
  `d_(r+1)^(-1)`; its right side is the inverse of `C_(1,r)`, exactly `b_r`.
  In writing `T = P₁`, the factor uses `g^1`; the standard equality `pow_one` identifies
  this with the source's `g`. This is transport along equality of arrows, not a new map.

Dependency declarations read and reused:

- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `WeilConjectures.TraceFormulaCoefficientConventions`, `.coefficientRing`,
  `.geometricBaseChange`, with the instance fields of the structure.
- `Sheaf.SixFunctors.SchemeFrobenius`:
  `WeilConjectures.FiniteFieldDatum.geometricGaloisFrobenius`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback` and its specified
  constant-section coefficient identification.
- `Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition`:
  the exact general construction `AlgebraicGeometry.Scheme.proEtaleCanonicalPullbackComposition`
  is the body of the previous alias `integralTowerGeneralPullbackComposition`. Its published
  specialization in `Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison`
  is `AlgebraicGeometry.Scheme.proEtaleConstantRingPullbackComposition`; its owning
  landed node `pur713-def-pullback-comparison` is added to `stmt_deps` to record this use.
- Proof imports: `Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence`, theorem
  `proEtaleConstantRingDerivedPullback_composition_coherence`;
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`, theorem
  `proEtaleCoefficientInverseImageMap_comp`; and
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, theorem
  `Padic.finite_coefficientExtensionRing`. They implement the three existing proof
  dependencies beyond the statement dependencies; their signatures and docstrings
  were read. They add no hypotheses to this statement.

The source was opened at the node's blueprint proof and at
`literature/stacks-project/sites-cohomology.tex`,
`lemma-derived-pullback-composition` (Tag 0D6D). The full six-step node proof is
included in the theorem docstring: constant coefficients, triple coherence, recursion,
positive-integer binary induction, splitting-tree induction/naturality interchange,
and inverse cancellation.

Edge cases checked: exponent one has no split and an identity comparison; exponent two
uses exactly `C_(1,1)`; either branch can have weight one (`a=0` or `b=0`); every
partition has at least one part so no exponent-zero pullback unit is silently needed.
The successor equation includes `r=1`. `M` can be the zero object or an unbounded
complex. `X₀` and its geometric fibre can be empty. The smallest permitted coefficient
level is one, with either residue characteristic two or any other prime distinct from
`p`. Site and coefficient universes remain those of the recorded operations, without
new equalities or smallness assumptions.

Searches actually run:

- `msearch.py leanfinder`: “Coherence of repeated derived pro-etale pullback along
  powers of geometric Frobenius, independent of splitting and reassociation”. Eight
  hits about field Frobenius iterations; no derived comparison coherence statement.
- `msearch.py loogle`: `SheafOfModules.pullback_assoc`. One hit, the ordinary sheaf
  pullback associativity lemma, not the specified iterated derived comparison.
- `msearch.py grep`: `pullback_assoc|leftDerivedFunctorCompIso` in `CategoryTheory`.
  Four hits (over-site pullback associativity and pullback-limit associativity);
  none states this node.
- `msearch.py leansearch`: “Coherence of canonical comparisons for iterated derived
  inverse image functors along powers of a scheme automorphism”. Eight hits about
  general localization/right-derived comparisons, ordinary scheme modules, and
  over-site sheaves. No exact match.
- `rg` of project and upstream sources for Frobenius/pullback coherence and iterated
  comparisons found the recorded triple-coherence theorem and
  `PullbackCoefficientIterateCoherence.lean`. The latter was read in full: its theorem
  concerns commuting squares and coefficient-map iterates, not independence of all
  positive Frobenius-power splittings. Its successor comparison is a specialization
  of the general two-summand comparison needed here, not a replacement theorem.
- `grep -rn` of the item id in the upstream `WeilConjectures` tree and `rg` of
  `dag/lean_names_upstream.json`: no match. Further `rg` of the proposed helper names
  in Mathlib CategoryTheory, upstream and `lean/Sheaf` found no existing declarations.

## Second reading by Q20

Reopened the node and reread the final module, including every recursive definition
and both orders of whiskering. Checked the bundled coefficient and geometric
hypotheses against the source as listed above. Checked that `End` multiplication is
reverse categorical composition: `g^b * g^a` is `g^a ≫ g^b`, so the power-addition
transport has exactly the source and target required by the canonical pullback map.
Checked that the addition index `b+a+1` means total exponent `(b+1)+(a+1)` and that
both summands remain positive, including `a=b=0`. Checked the target of each
whiskering and the associator direction. Checked the final morphism has source
`T(P_r(M))` and target `P_(r+1)(M)`, with composition in Lean's order.

The first compile detected unqualified whiskering names; the definitions and statement
were repaired to use `Functor.isoWhiskerLeft` and `Functor.isoWhiskerRight`.
The helper's owning landed node is explicitly added to the statement dependencies.
No mathematical hypothesis or clause was changed. The two binary equalities are the
full splitting independence assertion in its recursive formulation, not an assumption
of coherence and not just the successor assertion. This is the author's second pass;
the maintainer provides the independent delivery review required by the direct brief.

The subsequent compile identified an unused pattern binder in the identity branch of
`trfPositiveFunctorPowerSplit`; it was renamed `_b`, preserving the definition and
removing the warning without changing linter settings.

