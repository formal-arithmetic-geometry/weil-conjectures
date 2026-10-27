## Worker report

The delivery states `WeilConjectures.purity_ordinary_unit_exchange_naturality` in
`Sheaf.Paper.OrdinaryUnitExchangeNaturality`. Its sole postponed proof is `sorry`.
The other declarations are transparent abbreviations, explicit canonical maps,
or predicates spelling out the equations of this same node. They introduce no
independent mathematical notion, arbitrary comparison, chosen root, or chosen
trivialization. Every declaration is listed in `lean.declarations`.
The node changes only in `lean`; no statement correction or dependency repair is needed.

Source read: Stacks categories.tex, label
`lemma-transformation-between-functors-and-adjoints` (0B65), and the current
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/`
`sk-prop-a1-kummer.proof.md`, paragraphs Base change on Y and Coefficients.
The item is a refinement of those paragraphs, not the unit's own statement.

### Hypotheses and objects

| Node | Lean |
| --- | --- |
| Fixed k, ell, E and positive n | `P : PurityFiniteSetting.{u}`: existing field/coefficient datum, finite extension in its specified closure, positive level. |
| A=O_E/(varpi^n) | `P.Coefficient`, the existing universe lift of `P.Ring`; no abstract substitute ring. |
| X and X' are k-schemes, v a k-morphism | The two `Over (Spec (CommRingCat.of P.field.k))` instances and `v.IsOver` binder. There is no smoothness, finite-type, quasi-compactness, or separation assumption on v. |
| Signed twist r | `r : ℤ`; `ordinaryEtaleTwist` specializes `Scheme.finiteEtaleTateSheaf` to the actual coefficient ring. |
| A finite annihilating exponent | `ringChar P.Coefficient` and `CharP.cast_eq_zero`; this standard canonical exponent is used in the existing `PurityFiniteSetting.a1TateLine` construction as well. The characteristic is a positive ell-power for this nonzero finite quotient; ell differs from char k, so it is invertible on every k-scheme. No e-divides-n restriction is imposed. The exponent-change clause of `etaleFiniteTwistPullback` canonically identifies this realization with any sufficiently large ell-power realization. |
| Pro-etale finite twist | `comparisonUpperStar` of the same etale coefficient, including the canonical exact single-functor compatibility. |
| p, p', w | `purityLineProjection X`, `purityLineProjection X'`, `purityLineMap v` are the actual Mathlib affine-space projections and induced map, with coordinate type `ULift.{u} (Fin 1)`. |
| Cartesian square | `purityAffineLineSquare` uses `AffineSpace.isPullback_map`; `purityChosenLineSquare` uses its actual `isoPullback` and existing two projection equalities. |
| Ordinary, uncompleted operations on either site | The published `Etale` and `ProEtale` derived upper/lower-star adjunctions. Exact inverse image is identified with its left derived functor by the published canonical isomorphism. |

### Every conclusion clause

1. **Unit/exchange equation on both sites.** The first two conjuncts instantiate
   `purityUnitExchangeEquation` with the actual derived adjunctions, the published
   `Etale.derivedSquareUpperStarIso` / `ProEtale.leftDerivedUpperStarSquareIso`,
   and the actual `derivedBaseChangeMap`. Unfolding the helper gives
   `g.map (eta M) ≫ beta.app (l.obj M) ≫ r'.map (theta.inv.app M)
   = eta'.app (g.obj M)`, exactly the displayed equation in Lean's composition order.
   On the etale side this is the unbounded module exchange reexported by
   `BaseChangeMapAbelianAndSets`, not the abelian exchange substituted for it.
   Inspection of both `derivedBaseChangeMap` constructions shows that beta is
   `mateEquiv` of precisely theta.hom; hence its transpose is the specified
   pulled-back counit after theta. The exchange has no invertibility assumption.
2. **Conditional invertibility.** The second clause of that predicate is
   `IsIso eta → IsIso eta' → IsIso (beta.app (l.obj M))`.
   These assumptions occur only inside the conditional conclusion.
3. **Canonical site identification of units and exchanges.** Conjuncts 3 and 4
   are `purityComparisonUnitEquation` for p at L and p' at v*L, with the exact
   `fixedComparisonDirectImageMatePlus` and `fixedComparisonPullbackPlus`.
   Their formula is `C.map eta_e ≫ b.app (l_e M) ≫ R_p.map a.hom = eta_p`.
   Note that `fixedComparisonPullbackPlus` runs from l_e followed by C to C
   followed by l_p; this is the a of the source, so the formula has that direction.
   D+ is used only to express the specified finite comparison interface: the
   input is a sheaf in degree zero or its exact pullback, and the canonical
   faithful inclusion and derived-functor compatibilities identify these with
   the unbounded units in conjuncts 1 and 2. Conjunct 5 spells out the actual
   `comparison_derivedBaseChangeMap` equation, using the named source and target
   comparison isomorphisms, at p_e*L. Conjunct 6 is the canonical
   `ComparisonSquareComponent (comparisonSquareData ...) L`; it identifies the
   square comparison itself, and therefore also its inverse. Naturality of beta
   and the canonical p pullback comparison identify the pro-etale input of
   conjunct 5 with p_p*C(L). These are the identifications of the entire equation,
   not just an assertion that its endpoints happen to be isomorphic.
4. **Ordinary pullback composition.** Conjuncts 7 and 8 instantiate
   `purityCohomologySquare` on the etale and pro-etale projection square.
   Its first equation is `w* (p* x) = H(theta.hom) (p'* (v* x))`.
   Thus the two paths have a common codomain under exactly the canonical
   inverse-image identification, as the node's displayed notation requires.
5. **All integer degrees and ordinary cohomology.** Every ordinary predicate
   quantifies `q : ℤ`. `purityH Z M q` is the existing `ShiftedHom` from Z[0]
   to M[0] of degree q, with Z the constant abelian sheaf `ULift ℤ`.
   This is the standard derived-Hom presentation of ordinary sheaf cohomology;
   for q≥0 it is canonically `Sheaf.H`, and for q<0 it is zero, by the standard
   t-structure or a nonnegative injective resolution. No truncation of q or
   replacement by `q.toNat` occurs. `purityHPull` applies the exact inverse image
   termwise and the canonical constant-integer comparison, with the published
   single-functor and shift comparisons. `purityHMap` is postcomposition by the
   coefficient map in degree q. These are the ordinary cohomological pullbacks
   and coefficient maps, not a new cohomology theory or arbitrary map.
6. **Identification of ordinary equations across sites.** Conjuncts 9–12 are
   `puritySiteCohomologySquare` for v, p, p' at v*L, and w at p*L. This is exactly
   the square of geometric pullback and `comparisonUpperStar`, with the existing
   `comparisonUpperStarCompUpperStarIso` and
   `constantIntIsoComparisonUpperStar`. The latter is the standard cohomological
   site comparison, induced by the same comparison adjunction unit used in the
   normalized global-sections comparison. The four squares identify both paths
   in the ordinary projection-square equation.
7. **All finite coefficient morphisms, including level changes and quotients.**
   The last conjunct quantifies every positive target level `n`, signed target
   twist `s`, and abelian-sheaf morphism
   `a : P.ordinaryTwistAb X r ⟶ (P.ordinaryAtLevel n hn).ordinaryTwistAb X s`.
   `ordinaryAtLevel` is just the record update of n, retaining the fixed field,
   ell and E. Each morphism is linear over a common finite integer coefficient
   ring Z/ell^N annihilating both sheaves, so this covers the cross-level
   coefficient morphisms without imposing A-linearity over two unequal rings.
   A same-level map is included by taking the original level. Quotient maps
   and zero maps are included. The first four `purityCohomologyNaturality`
   predicates give `p* H(a)=H(p*a) p*` on both sites and their base changes;
   the last four identify these equations under site comparison at each corner.
   The formula is naturality of a cohomology functor, not exactness of tensoring
   by a quotient. There is no flatness binder on a, its source or its target.
8. **Inverses.** Both ordinary predicates include the inverse square, using
   `Function.invFun` of the exact named pullback and only under its
   `Function.Bijective` hypotheses. In the projection square the lower horizontal
   pullback is expressed in the common codomain by H(theta.hom). Its bijectivity
   is equivalent to that of p'* because theta is an isomorphism. Thus no extra
   invertibility hypothesis is imposed. The same clause in the site squares
   gives inverse site compatibility. The coefficient predicate gives the inverse
   naturality square for every quantified coefficient map. `invFun` is used only
   as the canonical inverse when the two stated bijectivity hypotheses hold.

### Dependency declarations used

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `Coefficient`, `forgetEtale`; all finite data are reused literally.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AlgebraicGeometry.AffineSpace`,
  `AffineSpace.map`, the `over` projection, and `AffineSpace.isPullback_map`.
- `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`: the reexported module
  `Etale.derivedBaseChangeMap`, with the original mate normalization; the
  recorded abelian-specific arrow is not appropriate to the module unit.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `comparisonSquareData`, `ComparisonSquareComponent`, and the canonical
  `comparisonUpperStarCompUpperStarIso` publicly available in this interface.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `fixedComparisonDirectImageMatePlus`, `fixedComparisonPullbackPlus`.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: reexports the recorded
  signed coefficient-twist convention; its finite constant-coefficient etale
  realization is the separately recorded `finiteEtaleTateSheaf` used here.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`:
  `Scheme.finiteEtaleTateSheaf`, `etaleFiniteTwistPullback`, with its signed,
  composition and exponent-change normalizations; no private root-line copy.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `Etale.upperStar`, `Etale.lowerStar`, their adjunction, through public imports.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: reexports the
  ordinary uncompleted pro-etale operations; the equivalent fixed-ModuleCat
  presentation uses `ProEtale.upperStar`, `lowerStar` and their published derived
  adjunctions, not a new intrinsic module category.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: preserves the recorded site/sheaf
  convention, including its existing ordinary sheaf cohomology definitions.
- Proof imports: `unit_mateEquiv` / `mateEquiv` (Mathlib Mates);
  affine-morphism permanence via AffineSpace's existing affine projection;
  `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`
  (`comparison_derivedBaseChangeMap` and its source/target comparisons);
  `Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget`
  (`leftModuleDerivedEvaluationForget`);
  `Sheaf.CategoryTheory.SiteCohomologyPullback` (`siteCohomology_pullback`);
  `Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized`
  (`finiteComparisonGlobalSections`, its unit normalization).
- The integral-degree ordinary maps additionally use the existing
  `DerivedCategory.singleFunctor`, `ShiftedHom`, `Functor.mapDerivedCategory`,
  `mapDerivedCategorySingleFunctor`, and the canonical constant-sheaf adjunction.
  `purityProEtaleIntegerPullback` explicitly transports the abstract sheaf pullback
  constant comparison through `sheafPullbackConstruction.sheafPullbackIso` to
  the actual constructed `ProEtale.upperStar`; it does not assume these two
  left adjoints are definitionally equal.

### Searches and edge cases

Searches made on 2026-10-24 using the prescribed msearch wrapper:
- leanfinder: "Base change exchange composed with the pulled back adjunction unit
  equals the new adjunction unit and ordinary cohomology pullback naturality".
  Eight generic module/adjunction hits, no complete finite geometric/site theorem.
- loogle: `CategoryTheory.unit_mateEquiv`. Exact generic mate-unit equation,
  already the recorded dependency; no complete match to this node.
- grep: `unit_mateEquiv|cohomologyMap_comp`, Mathlib CategoryTheory.
  Generic Mates and monoidal-closed results only.
- leansearch: "Ordinary cohomology pullback for finite Tate twists compatible with
  base change adjunction units and etale pro etale site comparison". Eight generic
  pullback/unit hits; none supplies this full statement.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf`: the item ID and searches
  for ordinary unit/exchange/naturality; no existing complete statement. Searches
  for the new full names and in `dag/lean_names_upstream.json` found no collision.
  Concept searches did find `PurityFiniteSetting.a1TateLine`, signed finite
  etale twists, the existing derived exchanges, and cohomology comparison; these
  constructions were reused. The old CompactObject example is withdrawn, with
  its record pointing to the identical upstream module; the required module-mode
  header and declaration conventions are nevertheless followed.

Checked before and during writing: v=id, empty source/target schemes, all r in Z
(including r=0 and negative duals), q=0 and q<0, n=1 and ramification index not
necessarily dividing n, identity and zero coefficient maps, quotient maps with
nonflat target, and arbitrary v without qcqs hypotheses. The projections alone
are qcqs, supplied by Mathlib instances. Source and morphism universes on the
small sites remain u+1 and u; no equality of those universes is introduced.
All generic helper universes and binders are explicitly declared; autoImplicit
is false. No disputed statement or node fault was found.

Validation: scompile.py compiled the delivered file, separately in sandbox mode
and its intended library module, with no diagnostics except the allowed postponed
proof. Compiler-guided repairs were the abstract/constructed inverse-image
transport and Lean's line-break syntax for a dot projection; neither changed
mathematical content. Dry-run and delivery results are recorded by deliver2.py.

## Second reading by Q148

The worker re-read the final node and final module clause by clause using the
mapping above. This is a self-audit, not a claim of an independent second agent:
the dispatcher's instructions expressly prohibit starting other agents and
specify that the maintainer independently reviews the delivered statement.
The re-reading checked the directions of theta and the fixed comparison a,
actual beta inputs under the canonical single/pullback identifications, the
common coefficient ring at unequal levels, all integer degrees, and the
conditional placement of every invertibility assumption. The corrected
abstract-to-constructed constant comparison is explicit in the final file.
The delivered statement and each helper remain available for that independent
maintainer reading.
