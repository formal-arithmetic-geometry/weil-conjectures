## Worker report

Delivered `Sheaf.Paper.ExceptionalMateSiteComparison`, with main declaration
`AlgebraicGeometry.ProEtale.exceptionalMateSiteComparison`. This is stage 2:
the main theorem has exactly `by sorry`; all twelve auxiliary constructions have
actual terms. There is no new axiom, arbitrary comparison, chosen `Nonempty`
isomorphism, or proof hidden in a definition.

Source read: current blueprint
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/thm-pur-affine-line-purity.proof.md`,
particularly its actual-adjoint comparison and final base-change sentences.
I also read every statement-dependency node, its recorded declaration and source
signature/docstring, the stage-2 contract and H errors, and the resolved repair
note for this item. Missing upstream files were read with `scompile.py --source`,
including the ordinary derived-category and finite-coefficient lower-shriek modules.

The repair note withdraws the Q95 statement because its transport aliases came
from `GlobalTransportChartNormalization`, on the removed local-extension branch.
This delivery replaces that module in place. It does not rebind the archived
statement as existing. No chart-normalization or local-extension module is imported.
`cbcGlobalSource`, `cbcGlobalTarget`, and `cbcGlobalPullbackComparison` now come
from the ordinary `GlobalFiniteLevelCompactSupportBaseChange` module.
The actual proper/open comparison is `compactSupportSiteComparisonPlus`.
The module docstring and eight-step proof docstring describe the current route,
including the witness-conjugation argument that replaces the old chart step.

### Every hypothesis and construction

- The finite-field and coefficient data are the binder
  `D : WeilConjectures.PurityFiniteSetting.{u}`. Its `field` is the fixed algebraic
  closure of the finite field, its `coefficients` includes the prime different
  from the characteristic and the fixed coefficient closure, `extension` is the
  finite intermediate extension, and `level_pos` says `1 ≤ level`.
  `D.Coefficient` is the recorded standard `ULift` of the actual quotient
  `D.Ring = O_E/(varpi_E^n)`. `exceptionalMateRingFinite` applies the recorded
  quotient finiteness theorem; `exceptionalMateCoeffFinite` transports it through
  `Equiv.ulift`. These instances add no hypothesis.
- `X`, `Y`, `Y'` are `Scheme.{u}`, with their displayed structure morphisms
  `aX`, `aY`, `aY'` to `Spec (.of D.field.k)`. The three sets of
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` instances say precisely
  separated finite type over k. These are the explicit-structure-map form
  permitted by the project conventions because the node names k-morphisms.
- The node's k-morphisms are `f`, `g`, with `_hf : f ≫ aY = aX` and
  `_hg : g ≫ aY = aY'`. The hypotheses `IsSeparated f`,
  `LocallyOfFiniteType f`, `QuasiCompact f` are separated finite type.
- `sq : IsPullback g' f' f g` specifies the Cartesian square. An arbitrary
  pullback object is used, as in the dependency's `ofIsPullback` interface;
  this includes the literal fibre product. Its k-structure is induced by
  `f' ≫ aY'`. No condition on g is introduced.
- `c : Compactification f` contains the open immersion `c.i`, proper map `c.g`,
  ambient `c.Z`, and factorization equation. `c.ofIsPullback sq` is exactly
  its specified pullback compactification, not a new chosen compactification.
- The two `LocallyOfFiniteType` and `QuasiCompact` pairs for `c.g ≫ aY` and
  `(c.ofIsPullback sq).g ≫ aY'` are the two finite-type ambient schemes.
  `d d' : ℕ` and `_hd`, `_hd'` state both nonnegative dimension bounds via
  `topologicalKrullDim ... ≤ (d : WithBot ℕ∞)`. This retains dimension −∞
  for an empty ambient scheme.
- All etale objects are in `DerivedCategory.Plus (Sheaf T.smallEtaleTopology
  (ModuleCat.{u + 1} D.Coefficient))`. Pro-etale objects use
  `Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} D.Coefficient)`.
  This is the canonical ordinary constant-scalar presentation explicitly used
  by the node; the recorded finite-coefficient realization identifies it with
  the ring-sheaf module presentation. The small sites retain object universe
  u+1 and morphism universe u. No site-universe equality is imposed.
- `siteComparisonDerivedPullbackPlus T A` is the recorded exact C_T.
  `comparisonLowerStar ... |>.rightDerivedFunctorPlus` is U_T.
  The two compact-support functors are the upstream etale and pro-etale
  `rightDerivedLowerShriekOfCompactificationPlus`, at c and `c.ofIsPullback sq`.
  These are the D+ restrictions of the recorded ordinary derived functors.
- `R`, `R'`, `adj`, `adj'` name the ordinary etale right adjoints on their
  stipulated bounded-below domains. They are parameters for the chosen
  adjunctions, rather than parameters for arbitrary exceptional maps. The
  ordinary ambient adjoints restrict to these because the node explicitly
  stipulates bounded-below typing, supplied by the comparison-class theorem.
  There is no additional adjoint-existence premise on the pro-etale category.
- `exceptionalMateH A R` writes the very composite U_Y ⋙ R ⋙ C_X on D+.
  It is the bounded-below coordinate expression of the recorded
  `sfFiniteExceptionalAt` for the chosen ordinary adjunction. The latter's
  unbounded API hardcodes the noncomputably selected representative of R;
  this auxiliary expression keeps the chosen R and its counit visible, as
  the item requires. It constructs no second exceptional adjoint.
- `exceptionalMateUnit` is `(R ⋙ C_X).mapIso` of the actual
  `compactSupportComparisonUnit Y A`, hence exactly h_{f,L}.
- `exceptionalMateTranspose` implements the four-arrow Hom chain literally:
  insert `P.map α.hom`, precompose with
  `(compactSupportSiteComparisonPlus A c).hom.app G = a_G^{-1}`, apply the
  comparison adjunction's `homEquiv`, then the ordinary adjunction's
  `homEquiv`, apply C_X, and precompose with `α.inv`.
  The comparison adjunction's `homEquiv` is U(z) composed with the unit,
  so this is exactly the stated normalization. Its inputs and target are D+.
- `exceptionalMateCounit` reverses that normalized chain at the identity of
  H(N). It uses C_c inverse, C_Y applied to the ordinary counit at U_Y N,
  and the comparison counit at N. Its source has the literal etale witness
  `(R(U_Y N), Iso.refl _)`, so there is no unspecified witness choice.
- `exceptionalMateEtaleExchange` is `asIso` of the recorded
  `Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap A sq c`
  at G, with invertibility from `Etale.compactSupportFiniteTorsion`.
  Thus its hom is the specified B^e, and its inv is its actual inverse.
- `exceptionalMateProExchange` is exactly
  `(cbcGlobalSource A g c).app G` inverse, followed by C_{Y'} of B^e_G,
  followed by `(cbcGlobalTarget A sq c).app G`.
  These are the S^c and T^c of the restated finite-level theorem; their
  definitions use the specified C_c and kappa. This is the transported
  compactification exchange on C_X G, rather than a substitute exchange.
- `exceptionalMateEtale` applies `adj'.homEquiv` to B^e inverse followed
  by g^* of the actual counit. It is precisely beta^e, in the counit-transpose
  convention of `CategoryTheory.mateEquiv` and `mateEquiv_counit`.
- `exceptionalMatePro` applies the normalized primed relative transpose to
  B^p inverse followed by S of the relative counit. H(N) is literally
  C_X R U_Y N; thus the identity witness is available, and the source
  witness after pullback is the actual component of
  `cbcGlobalPullbackComparison A g'`. For H(C_Y L) the witness h_{f,L}
  gives the same exchange by the finite-level witness-independence clause.
- `exceptionalMateV` is T applied to h inverse followed by kappa_{g_X}^{-1}.
  `exceptionalMateW` is H' applied to kappa_g inverse followed by h' inverse.
  They are isomorphisms of the exact source and target in the node.

### Every conclusion

The main theorem has four conjuncts, with Lean's `≫` writing composition
in the opposite textual order from the node's `∘`:

1. For every L, `exceptionalMatePro ... (C_Y.obj L) ≫ W.hom =
   V.hom ≫ C_X'.map (exceptionalMateEtale ... L)` is exactly
   w_L beta^p_{C_Y L} = C_X'(beta^e_L) v_L.
2. For every b:L→M, the second conjunct is
   T H(C_Y b) followed by beta^p_M = beta^p_L followed by H' S(C_Y b).
3. The third conjunct is t R(b) followed by beta^e_M = beta^e_L followed
   by R' s(b). Together with the natural unit and kappa used in V and W,
   these express naturality of the equality in L, with the actual mates.
4. For every `α : C_Y.obj L ≅ N`, the fourth conjunct is the equality
   beta^p_N followed by H'(S α^{-1}) followed by W =
   T(H α^{-1}) followed by V followed by C_X'(beta^e_L).
   These are precisely the specified transported endpoints w^N and v^N.
   It includes every isomorphic witnessed replacement, not just an identity
   witness, and does not renormalize the Hom bijection after replacement.

No isomorphy of either exceptional mate, smoothness of f, constructibility,
or unrestricted pro-etale adjunction is used as a hypothesis.

### Dependency declarations used

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `.Ring`, `.Coefficient`; its existing coefficient finiteness theorem is
  `Padic.finite_coefficientExtensionRing`.
- `WeilConjectures.Compactification.BaseChange` and `.Refinement`:
  `Compactification`, `.ofIsPullback`, `.Refinement`. Scheme and morphism
  properties and `topologicalKrullDim` are the Mathlib declarations specified
  by their dependency records; the morphism-properties node is a convention.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  ordinary `DerivedCategory`, `DerivedCategory.Plus`, and the fixed-scalar
  etale module-sheaf presentation (torsion cohomology is not needed here).
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  the fixed-scalar presentation and its canonical `finiteCoefficientRealization`;
  this is also the presentation used by the ordinary global-exchange module.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  `siteComparisonDerivedPullbackPlus`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek` and
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`:
  both sites' `rightDerivedLowerShriekOfCompactificationPlus` and their
  documented compatibility with the unbounded functors.
- `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`:
  `Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification` (ordinary
  existence); `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`:
  `sfFiniteExceptionalAt` (the ambient expression whose D+ coordinates we use).
- `Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction`:
  `FixedComparisonClassAdjunction`, `exists_fixedComparisonClassAdjunction`
  (the relative Hom bijections, normalization, and bounded-below typing).
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`:
  `isIso_compactSupportComparisonUnit`, `compactSupportComparisonUnit`.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `supportSiteComparisonCoefficientPullbackIso`, through its degreewise
  `cbcGlobalPullbackComparison` in the ordinary global-exchange module.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`:
  `Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`.
- `Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion`:
  `Etale.compactSupportFiniteTorsion`.
- `Sheaf.Paper.GlobalFiniteLevelCompactSupportBaseChange`:
  `cbcGlobalSource`, `cbcGlobalTarget`, `cbcGlobalPullbackComparison`,
  `globalFiniteLevelCompactSupportBaseChange`; the latter supplies independence
  of the etale-origin witness used in the proof.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `CategoryTheory.mateEquiv`,
  `mateEquiv_counit`. The definition uses `Adjunction.homEquiv` for its
  componentwise counit-transpose characterization.
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `compactSupportSiteComparisonPlus`, `compactSupportSiteComparison`.

Proof dependencies remain reachable through the ordinary imports, including the
non-public `FiniteComparisonClassAdjunction` and `Adjunction.Mates` imports.
No dependency record, natural-language statement, or DAG edge was changed.
No new nodes or dependency modules were needed: the missing chart-free
coordinates are existing constructions, used directly rather than redefined.

### Edge cases

Checked the empty source and empty base: `topologicalKrullDim` retains bottom,
and no nonemptiness hypothesis or empty maximum occurs. d=d'=0 is allowed.
Identity base change and identity witness are included, as are arbitrary
isomorphic witnesses and arbitrary maps between L and M. The chosen
compactification need not have a dense open. The construction does not require
finite cohomology groups or constructibility of L. The generalized auxiliary
constructions allow the zero coefficient ring; the main finite purity quotient
still retains its positive level and the prime different from the characteristic.
The source/target of each of the four Hom-chain arrows and both mate transposes
were checked; only compact-support exchange is inverted, never beta^e or beta^p.

### Searches

- `msearch.py ... leanfinder` query:
  `The normalized exceptional base change counit transpose commutes with etale to proetale comparison on bounded below etale origin complexes`.
  Result: 8 hits, including `Condensed.profiniteSolidCounit`, Dold–Kan comparison
  equations, and `Algebra.Etale.comp`; none is this site-comparison statement.
- `msearch.py ... loogle '"mateEquiv"'`: 12 hits, including
  `CategoryTheory.mateEquiv`, `mateEquiv_counit`, pasting lemmas and iterated
  mate equivalences. Read the actual signature and construction in
  Mathlib/CategoryTheory/Adjunction/Mates.lean: these supply abstract mates,
  not the present comparison of normalized relative adjunctions.
- `msearch.py ... grep 'exceptional.*(mate|comparison)|(mate|comparison).*exceptional'`:
  0 Mathlib hits.
- `rg -n 'exceptionalMate|lem-pur-exceptional-mate-site-comparison'` in the
  upstream `WeilConjectures` source found only trace-formula pairing mates,
  whose source/target are tensor-Hom pairings, not this theorem.
  `grep -rn` for this item id in that tree returned no hit.
- `rg` of `lean/Sheaf` found the archived withdrawn module and its downstream
  references. The withdrawn module is repaired in its original owning path;
  it is not an existing usable statement. Searches for `sfFiniteExceptionalAt`,
  Plus variants, and `siteComparisonDerivedPullbackPlus` identified the existing
  ordinary comparison APIs used above. The upstream name index has no matching
  normalized exceptional site-comparison declaration.

### Verification and consumer validation

`scompile.py Q129 lem-pur-exceptional-mate-site-comparison <module>` compiled
both its sandbox and owning-module forms cleanly (8.5 s and 10.7 s in the clean
run). An earlier run elaborated successfully but reported long-line warnings;
all such lines were wrapped and the clean run has no errors or warnings.
`autoImplicit false` is set and universe u is explicitly declared. There is one
postponed theorem, matching this DAG node and carrying its eight-step proof.

For the repair-note consumer check, `exceptionalMateProExchange` consumes both
new ordinary endpoint comparisons with their exact source/target; then
`exceptionalMatePro` consumes that exchange and the normalized primed Hom chain;
finally all four clauses of the main theorem consume those maps. The clean
owning-module compile therefore validates the actual consumer interfaces after
removing every chart alias. No unchanged archived binding was reused.

No statement dispute or source correction was necessary.

## Second reading by Q129

This section records the author's separate clause-by-clause self-check; the
independent review is the maintainer's, as in the dispatch brief. No sub-agent
was started and no independent reviewer is claimed here.

I reopened the current node, the repair note, the ordinary global-exchange
module, and the complete generated module. The geometric binders retain all
three separated finite-type k-schemes, both k-map equations, the fixed pullback
square, both chosen compactifications and both dimension bounds. The four
conjuncts retain the equality, naturality of both specified mates, and every
isomorphic witnessed replacement. Checking compositions from source to target
confirmed both inverse directions in V and W and the inverse witness on each
endpoint of the final clause.

The mismatch repaired relative to the archived source is its use of the
withdrawn chart-module aliases, especially Cc, S and T. These now use the exact
ordinary canonical comparison and `cbcGlobalSource`/`cbcGlobalTarget` from the
restated finite-level theorem. C_T is the recorded `siteComparisonDerivedPullbackPlus`,
and the other operations are the actual upstream constructions. The displayed
Hom chain still precomposes by Cc.hom = a_G inverse. The counit still reverses
that chain at the identity. No free Hom equivalence or arbitrary isomorphism is
introduced. After wrapping the long expanded expressions, I recompiled the
whole file cleanly. The natural-language statement and DAG dependencies are
unchanged.
