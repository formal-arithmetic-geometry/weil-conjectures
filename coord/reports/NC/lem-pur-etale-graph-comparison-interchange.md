## Worker report

Delivered module: `Sheaf.AlgebraicGeometry.EtaleGraphComparisonInterchange`.
Main declaration: `AlgebraicGeometry.Etale.etaleGraphComparisonInterchange`.
The main theorem has the only `sorry`. All helper definitions have real data; the
factorization proofs inside geometric records only verify the supplied commutativities.
No node statement, dependency list, or proof was changed. No new DAG node or dependency
repair was needed.

Source read: `literature/stacks-project/more-etale.tex`, lemma-shriek-composition,
Tag 0F7J, lines 3158--3370, especially the final A--F comparison. Its literal theorem
concerns finite-type separated maps of qcqs schemes; this DAG node deliberately records
the agent-stated product-graph extension to arbitrary supplied presentations. I retained
that extension exactly, rather than importing the existence-only compact-support
composition theorem as a replacement. I also read the recorded graph-comparison module,
the normalized exchange-cube statement and proof docstring, the triangle exchange and
proper/open compositors in upstream `LowerShriekComposition.lean`, and the statement
dependencies' recorded declarations and docstrings.

Hypothesis and clause correspondence:

- The finite commutative coefficient ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  Schemes have universe `u`, following the recorded six-functor coefficient convention.
- The categories are the dependency's `DerivedCategoryModule A X`, namely the ordinary
  unbounded derived category of `Sheaf X.smallEtaleTopology (ModuleCat A)`. There is no
  plus, bounded, constructible, torsion-amplitude, or localization restriction.
- Presentations use the recorded `EtaleGraphPresentation` and `.functor A`, whose fields
  supply proper `a`, open `e`, proper `p`, and `a ≫ e ≫ p = h`. Thus the first clause's
  `H` supplies exactly the node's `a,e,p`, including their properties and equation.
- The first clause quantifies over arbitrary `W`, proper `a' : X ⟶ W`, open
  `v : W ⟶ H.U`, and `fac : a' ≫ v = H.a`. This `v` is the node's `u`.
  `H.shrink a' v fac` is exactly `S = (a', eu, p)`, with open `v ≫ H.e`.
- `(c : Compactification h)` supplies the required open-then-proper factorization of
  `pea`. It imposes no quasi-compactness on `h` or any supporting open.
- The first equality has left side `(etaleGraphComparison A c H S).hom`, exactly
  `C_{S,H}` with the specified B-based construction from the recorded dependency.
- Its right side is `etaleGraphShrinkInterchange`. It starts with the inverse of
  `rightDerivedLowerStarCompOpenImmersionLowerShriekIso A a' v H.a fac`, then applies
  `J_e`, `R_p`, associators, and the inverse open compositor. The square with top
  identity and bottom `v` is automatically Cartesian, because `v` is mono and
  `a' ≫ v = H.a`. The normalized cube dependency identifies Gamma for this square
  with the upstream Cartesian exchange. Removing `J_id` gives precisely the cited
  upstream triangle isomorphism. Consequently this word is `R_p J_e Gamma_Q^{-1}`
  with the required identity normalization and compositor to `F_S`.
- In the second clause, `f` and `g` are arbitrary scheme maps. The binders
  `cf : Compactification f` and `ch : Compactification (f ≫ g)` supply exactly the
  two required open-then-proper factorizations, of `f` and `h = gf`.
- `d₁ d₂ : EtaleGraphInterchangeDiagram f g` independently supply every scheme
  `W,V,P,T` and all seven maps `a,e,r,k,p,i,q` for each index. Their instance fields
  require exactly the four proper maps and three open maps in the node. `facF`,
  `facG`, and `square : CommSq k r p i` are exactly its three commutativities.
- `.sourcePresentation` is `t = (a,e,r)`. `.compactification` is `(i,q)` and
  `EtaleGraphPresentation.ofCompactification` gives `d = (id_Y,i,q)`.
  `.compositePresentation` is `s = (a,e ≫ k,p ≫ q)`. Its factorization follows
  directly from the three recorded commutativities, with no additional assumption.
- `etaleGraphDiagramInterchange A d` is the specified `I`: remove `R(id_Y)_*`
  using `etaleGraphOpenNormalization`, insert `Gamma_Q` after `R_a,J_e` and before
  `R_q`, and use the inverse open compositor and forward proper compositor to
  reach the functor of `s`. All intermediate associators are explicit.
- `etaleGraphNormalizedProperOpenExchange` selects the family from
  `etaleProperOpenExchangeCube` together with its support and representative
  normalization, rather than choosing from `Nonempty` of the endpoint isomorphism
  type. The support inclusion determines the sheaf comparison, and normalization
  on every K-injective representative determines the derived map. This is the
  permitted use of an existence theorem determining the object, not hollow data.
- The second equality reads, in Lean's first-then convention,
  `I₁.hom ≫ C_s21.hom = whiskerRight C_t21.hom F_d1 ≫
  whiskerLeft F_t2 C_d21.hom ≫ I₂.hom`. Thus it is exactly
  `C_s21 ∘ I₁ = I₂ ∘ (C_d21 F_t2) ∘ F_d1(C_t21)`.
  Each side is a natural transformation from `F_t1 ⋙ F_d1` to `F_s2`.
- `C_d21` uses `d₁.compactification` as auxiliary compactification of `g`, which
  the supplied diagram already provides. The recorded independence theorem
  makes this the same specified graph map for any auxiliary choice.
- Only `CommSq`, never `IsPullback`, is required of either supplied square.
  No map between the diagrams, quasi-compactness, Noetherianity, boundedness,
  constructibility, inverse-image compatibility, or tensor compatibility occurs.

Dependency declarations used:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and the publicly available
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` (the recorded category encoding).
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `AlgebraicGeometry.Etale.preservesFiniteLimits_openImmersionLowerShriek`, together
  with the canonical extension-by-zero functor and its derived functor.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Sheaf.AlgebraicGeometry.EtaleGraphComparisonBaseChange`:
  `AlgebraicGeometry.Etale.EtaleGraphPresentation`, its `functor` and
  `ofCompactification`, `etaleGraphComparison`, and `etaleGraphOpenNormalization`.
  The comparison is definitionally the actual product/intersection B construction.
- `Sheaf.AlgebraicGeometry.EtaleProperOpenExchangeCube`:
  `AlgebraicGeometry.Etale.ProperOpenDerivedComparisonFamily` and
  `AlgebraicGeometry.Etale.etaleProperOpenExchangeCube`, with its sheaf support,
  K-injective representative, Cartesian, pasting, and identity normalizations.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`:
  `CategoryTheory.ringedToposDerivedPushforwardComposition` is publicly imported;
  for these constant-coefficient scheme functors the existing canonical compositor
  is `AlgebraicGeometry.Etale.rightDerivedLowerStarComp`, used directly.
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriekComp` and
  `openImmersionLowerShriekComp_coherence` are publicly imported; the existing
  derived compositor `mapDerivedCategoryOpenImmersionLowerShriekComp` is used.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition`:
  `rightDerivedLowerStarCompOpenImmersionLowerShriekIso` and the derived proper/open
  compositors, re-exported by the statement dependency, were read and reused.

Available proof modules are imported, including the graph model, ringed monoidal
comparisons, pullbacks, closed immersions and natural-transformation whisker exchange.
`lem-pur-etale-pairwise-product-graph-normalization` has no recorded Lean module in the
read snapshot, so no import can yet be added for that proof-only dependency; its use
remains in the theorem's complete eight-step proof docstring. This does not affect typing
of the statement and does not substitute a new statement for that node.

Edge cases checked before writing: the empty scheme is allowed throughout; no nonempty
or inhabited binder was added. Zero-ring coefficients are allowed by `CommRing` and
`Finite`. Identity maps, identity opens, equal presentations, and equal diagrams remain
allowed. The triangle normalization explicitly includes `J_id` removal. A supplied open
need not be quasi-compact, and the composite diagrams' squares can be non-Cartesian.
Neither functor is restricted by the cohomology of its input. No independent undersized
universe for coefficient sheaves or test schemes is introduced.

Searches for an existing statement:

1. `msearch.py ... leanfinder "Canonical product graph comparison between proper open
   proper presentations intertwines proper open interchange"`: eight unrelated product
   comparisons and profinite presentation results; no match.
2. `msearch.py ... loogle '"whiskerLeft", "whiskerRight"'`: twelve results, including
   `Functor.whiskerLeft_comp_whiskerRight` and the corresponding iso laws, but no graph
   comparison/interchange theorem.
3. `msearch.py ... grep 'GraphComparison|ProperOpenExchange|whiskerLeft_comp_whiskerRight'
   CategoryTheory`: only the two generic whiskering declarations in Mathlib.
4. `rg` on `lean/WeilConjectures` and `lean/Sheaf` for the item id,
   `etaleGraphComparisonInterchange`, and `graph.*interchange`: no existing item theorem;
   the only incidental text hit was unrelated cone interchange. A separate item-id
   search of `dag/lean_names_upstream.json` also found no attachment.
5. Source searches located the upstream Cartesian triangle comparison and compositors,
   so those constructions were reused instead of redefined. Searches and direct reads
   located the already landed graph comparison and the non-Cartesian exchange family.

Validation: `scompile.py NC lem-pur-etale-graph-comparison-interchange <module>` compiled
both sandbox and final module modes cleanly (17.1 and 17.4 seconds on the successful
pass). Earlier diagnostics were repaired by explicit family typing, record instance
fields, a nondependent factorization calculation, and explicit functor associators.
No warnings remain. `autoImplicit false` enforces explicit binders and universes.
No mathematical statement dispute or source correction was found.

## Second reading by NC

Author's second reading, as required for this dispatcher-started direct delivery; no
independent worker was started. The maintainer supplies the independent review.

I reopened the final module and node, checked both conjunction clauses and each record
field, and traced the endpoints of both words. The first comparison is H to S, using
the inverse triangle, not its forward map. The second uses C from index 1 to index 2
for f, g, and h, and changes the f presentation before changing the g presentation,
exactly matching the displayed source equation. The g presentation still includes
R(id_Y), which is explicitly removed only within I; the C maps themselves retain the
recorded presentation normalization. I checked that facF, facG and square supply all
factorizations, and that neither square silently became Cartesian. I also checked
that selecting Gamma retains the cube theorem's full support/representative
normalization. The dependent rewrite and associator issues found during this pass
were repaired before the clean compile. No hypothesis or conclusion was changed,
and no new nodes or dependency modules require an additional reading.
