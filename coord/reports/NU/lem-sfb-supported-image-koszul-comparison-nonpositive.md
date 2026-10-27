## Worker report

The module `Sheaf.Paper.SupportedImageKoszulComparisonNonpositive` states
`AlgebraicGeometry.ProEtale.supported_image_koszul_comparison_nonpositive` with one
`sorry` proof. Its two real-data helpers construct the literal underlying abelian
Koszul complex and its ordinary, uncompleted, derived comparison direct image.
No other theorem is added or proved.

The previous BLOCKED ending concerned the accepted stage-1 split, not this stage-2
assignment. I read the maintenance stage-handoff paragraph in coord/brief-stage2.md,
the current node, its Q09 review and queue.tsv (stage 2, no Lean record). There is
no released repair note for this item. The accepted statement and proof are preserved.
In particular, this delivery retains Noetherianity of S, as required by Q09's correction;
it does not claim to repair the unrestricted parent's application.

### Hypothesis and clause correspondence

| Node text | Lean rendering |
| --- | --- |
| X is an affine scheme | `(X : Scheme.{u}) [IsAffine X]` |
| Small etale and pro-etale sites in a common indexing universe | `Scheme.smallEtaleTopology`, `Scheme.ProEt.topology`, both for `Scheme.{u}`; sheaves valued in `Ab.{u + 1}`. Site objects live in u+1, morphisms in u. No equality of those site universes is imposed. |
| A prime ell and a finite field extension E/Q_ell | `(ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]` |
| Norm-topological valuation ring B and specified uniformizer pi | `DerivedNakayama.integerRing ℓ E` is the existing continuous condensed integer ring with the topology from `Padic.coefficientExtensionAbsoluteValue`. The selected `derived_nakayama_resolution` witness is uniquely characterized on every profinite section as multiplication by `Padic.coefficientExtensionUniformizer ℓ E`. |
| B_T = p_T^* C(-,B), with internal module objects | `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj (DerivedNakayama.integerRing ℓ E) T)` |
| Any finite allowed support chain S -> ... -> X | `(tree : QcqsOpenClosedTree X) (p : tree.Path S)`, using the existing definition node `def-sfb-qcqs-open-closed-tree` |
| Quasi-compact open arrows, or closed arrows with quasi-compact open complement | Tree splits carry the actual complementary open and closed immersions and their quasi-compactness; their two subtrees have qcqs roots. Over affine X this encodes every chain in the node; see the encoding argument below. |
| J is the composite of open ! and closed * | `p.extension (DerivedNakayama.integerRing ℓ E)` recursively appends precisely `CondensedRing.openImmersionLowerShriek` and `CondensedRing.lowerStar` |
| Empty chain gives identity | `QcqsOpenClosedTree.Path.root`; its `extension` is definitionally the identity |
| S is Noetherian, meaning quasi-compact and locally Noetherian | `[CompactSpace S] [IsLocallyNoetherian S]`; there is no Noetherian hypothesis on X or U |
| Arbitrary map f:L -> M | `(L M : Mod ...) (f : L ⟶ M)`; no restriction on its entries, ranks, or images |
| Separately pro-etale locally finite scalar models for L and M | `_hL : HasFiniteConstantLocalModel ... S L` and `_hM : HasFiniteConstantLocalModel ... S M`, separately quantified covers and finite presentations in the existing definition |
| Actual abelian image I, no topological closure | `CategoryTheory.Limits.image f` in the internal-module abelian category |
| Affine pro-etale object v:U -> X | `(U : Scheme.{u}) (v : U ⟶ X) (_hv : proAffineEtale v)`; `proAffineEtale.isAffine` supplies affineness, so no extra affineness assumption is necessary |
| N = v^* J(I) using module pullback | `(CondensedRing.upperStar ... v).obj ((p.extension ...).obj (image f))` |
| n >= 1 | `(n : ℕ) (_hn : 1 ≤ n)`; this is the literal positive exponent n, not the shifted n+1 tower convention |
| C_n(N) has underlying abelian sheaf N in degrees -1 and 0 and differential pi^n | `supportedImageKoszulComplex` applies `HomologicalComplex.double` to the underlying `.hom` of the existing `DerivedNakayama.scalarOnModules` action of the n-th power of the specified regular-module endomorphism |
| Zero elsewhere | `HomologicalComplex.double` is exactly zero in all other degrees; its shape is `ComplexShape.up ℤ` with indices -1 and 0 |
| nu_U is the geometric comparison | `comparisonLowerStar Ab.{u + 1} U`, the restriction along `Scheme.toProEt U` used by the recorded `proEtaleSiteComparison` |
| Ordinary derived abelian direct image R nu_* | `(comparisonLowerStar Ab.{u + 1} U).rightDerivedFunctor.obj (DerivedCategory.Q.obj ...)`; the coefficient category here is abelian sheaves, not completed internal modules |
| Membership in D^{<=0} | `(supportedImageKoszulComparison ℓ E p f v n).IsLE 0` |
| H^q = 0 for every q>0 | `∀ q : ℤ, 0 < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj ...)` |
| Ordinary localization at quasi-isomorphisms | `DerivedCategory.Q` and `DerivedCategory` from the recorded Mathlib definition; the ordinary right derived functor is computed on K-injective resolutions |
| No cohomological-dimension bound; no classicality, derived completeness, constant rank or elementary-divisor hypothesis | None of these occurs among the binders; classicality is only a step in the postponed proof |
| Empty schemes, empty chains and zero maps included | No nonemptiness, positive chain length, nonzero map or nonzero image hypotheses |

The tree-path encoding introduces no geometric restriction: starting with affine X,
each successive allowed open or closed immersion has qcqs source. For a qc open
step add its closed complement as a leaf sibling. For a closed step add its
specified qc open complement as a leaf sibling. A closed immersion is affine and
qcqs, and a quasi-compact open in a qcqs scheme is qcqs. Thus all the resulting
vertices and sibling leaves satisfy the tree requirements. Inductively one gets
the original chain, with the same actual maps, as a path in a finite tree. In the
other direction each tree path is such a chain: the complementary open subtree
is quasi-compact, as required for any closed edge. The arbitrary scheme structure
on a closed source is retained; complementarity is only an equality of underlying
point sets. No locally closed composite is substituted for the sequence of functors.

The `choose` in the complex definition does not select an arbitrary existence-model:
the published resolution theorem fixes the endomorphism d on every section of
every profinite object by `(d a)(s) = pi * a(s)`. These equations determine d
uniquely by faithful forgetting and natural-transformation extensionality. The
helper uses only that uniquely determined component, not the theorem's arbitrary
triangle connecting maps. The existing `scalarOnModules` gives its actual action
on any internal module via pullback and tensor unitors. Taking d^n gives pi^n,
with its underlying abelian-sheaf morphism used as the double's differential.

### Dependency declarations used

I read every original statement-dependency node and its record (including Mathlib
matches), then the source declarations and docstrings. The following are reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`, `Scheme.smallEtaleTopology`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `def-weil-size-convention` is a convention record; it supplies no declaration.
  Explicit universe u and the standard Grothendieck-abelian localization instances
  implement the common universe convention, with no hidden auto-bound universe.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` publicly exposes
  `Padic.coefficientExtensionAbsoluteValue`, `coefficientExtensionIntegers`,
  `coefficientExtensionUniformizer` and the finite coefficient constructions.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `upperStarFromPoint`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, its morphisms,
  regular module and forgetful functor.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` publicly exposes the recorded
  `QuasiCompact` predicate from `Morphisms.QuasiCompact`; no finite-type condition
  beyond the support-chain conditions is imposed.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `CondensedRing.openImmersionLowerShriek`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `CondensedRing.lowerStar`, `CondensedRing.upperStar`.
- `Sheaf.Paper.CondensedConstantConstructibility`: `HasFiniteConstantLocalModel`.
  It takes finite presentations on the point before scheme pullback; it is the
  scalar-model notion, not arbitrary presentations with varying matrix entries.
- `WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale`: `proAffineEtale`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: the recorded geometric
  adjunction built from `Scheme.toProEt`; its underlying abelian direct image is
  `comparisonLowerStar` from `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`.

Two already-landed nodes are added to stmt_deps, with no new definitions or nodes:

- `def-sfb-qcqs-open-closed-tree`: `Sheaf.Paper.QcqsOpenClosedTree`,
  `QcqsOpenClosedTree`, `Path`, `Path.extension`, for the exact support-chain encoding.
- `det-pe-derived-nakayama-resolution`: `Sheaf.Paper.DerivedNakayamaResolution`,
  `DerivedNakayama.integerRing`, `scalarOnModules`, and
  `derived_nakayama_resolution`, for the continuous coefficient specialization and
  the fully specified uniformizer action already provided by that node.

The two helper definitions are listed with the main theorem in lean.declarations,
and have source/blueprint docstrings. They just implement objects explicitly
introduced in this item's statement and need no independent definition nodes.

All stated proof dependencies are imported (plain imports unless also needed for
the statement), including the Noetherian constructible heart, finite reductions,
principal cone calculus, constructible comparison, extension-by-zero comparison,
direct-image comparison, operations transport, open-closed exactness, pullback
exactness, bounded-below comparison, classical derived equivalence and classical
sheaves. The three Mathlib proof leaves use Noetherian/AffineScheme/QuasiSeparated
and ShortComplex.PreservesHomology. The six-step proof is copied in mathematical
form into the theorem docstring, including its exact use of Noetherianity and its
warning about the unrestricted parent. The local statement is an agent-created
prerequisite, not asserted to be a quotation from HRS Lemma 8.6. I inspected HRS
Theorem 6.2(3), Remark 6.4 and the current blueprint ancestor proof locally.

### Searches and edge cases

The prescribed msearch.py searches were made for this group/item:

- leanfinder: `Higher direct images of pro etale to etale comparison of uniformizer two term complexes of supported images of finite scalar modules vanish in positive degrees`.
  Eight hits about algebraic etale loci, formally etale composition and derived
  maps from/to single objects; none states the comparison bound.
- loogle: `AlgebraicGeometry.ProEtale.comparisonLowerStar`.
  Zero hits / unknown identifier in Mathlib search; the project declaration was
  found and read in `WeilConjectures/SixFunctors/ProEtale/Comparison/Defs.lean`.
- leansearch: `Comparison higher direct images of the uniformizer Koszul complex of an image of constructible pro etale sheaves are zero in positive degrees`.
  Eight hits about strict cochain support, opcycles, and formally etale modules;
  none states this theorem.
- grep: `twoTerm|TwoTerm|two_term` in Mathlib Algebra/Homology: no hits.
  Direct rg then found the existing `HomologicalComplex.double` in
  `Mathlib/Algebra/Homology/Double.lean`, exactly the literal two-term constructor.
- grep: `proetale.*image|image.*proetale|Koszul` in Mathlib AlgebraicGeometry/Sites:
  no hits.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for support-chain,
  supported-image and Koszul material found the existing tree and the related
  `SupportedImageTorsionReductionsCd`, `SupportedImageDerivedCompleteness`, and
  resolution modules, not an existing theorem with this conclusion.
- Direct node-id search in `lean/WeilConjectures` found no declaration. Direct rg
  for all three proposed declaration names in both Lean roots and
  `dag/lean_names_upstream.json` found no matches before creation.

Edge cases checked before and after writing: the root path gives the empty chain;
empty schemes are permitted by the tree and scheme binders; f=0 has categorical
image zero; no hypothesis excludes torsion scalar modules or rank-zero finite
presentations. At n=1 the differential is the uniformizer itself; n=0 is excluded
only in the theorem, not needed as a special convention in the helper. Arbitrary
finite E/Q_ell is allowed without an embedding into a chosen algebraic closure.
Neither X nor U is required to be Noetherian. Positive q is an arbitrary integer,
with no cohomological-dimension restriction. The auxiliary complexes use no
completed derived category, and I is never replaced by an image after reduction.

No new statement correction or unresolved STATEMENT-DISPUTED flag. The already
reviewed Noetherian correction and the known downstream application fault remain
visible in the unchanged node proof and review. No dependency interface is replaced.

Validation: the initial module compiled cleanly via the prescribed scompile.py
(sandbox 21.9 seconds; library 11.9 seconds). After making statement and proof
imports explicit, the final module is recompiled and deliver2.py preflight is run.

## Second reading by NU

No second reading by a worker: the worker delivers directly under the current
brief; the maintainer's independent review reads the delivery. I performed a
separate clause-by-clause reread of the node and final source, checking the exact
ordinary abelian derived functor, the degree indices, the positive exponent,
the separate finite-model hypotheses, the actual image and the tree-path encoding.
No mismatch was found. No independent worker review is claimed.

Final verification: scompile.py compiled the final explicit-import module cleanly
(sandbox 10.1 seconds; library 12.3 seconds). The prescribed deliver2.py --no-push
returned `OK (dry run): commit 7e1713bce24 passes the preflight and compiles; nothing pushed`.
A node-field comparison confirmed that only lean and the two added statement
dependencies differ; statement, proof and proof_deps are identical to the live node.
