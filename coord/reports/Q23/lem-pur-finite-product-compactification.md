## Worker report

The delivery states `AlgebraicGeometry.ProEtale.finiteProduct_compactification` in
`Sheaf.Paper.FiniteProductCompactification`. It constructs the actual product
compactification, its specified two-stage open tensor map e, the ordinary Omega,
and the compactification-relative forward T. The main theorem is postponed with
`sorry`, as is the node's assertion that the explicitly constructed e is an
isomorphism. Every definition contains real data. These helpers are the maps,
objects and coordinate expression introduced in this node, not independent notions.
No node statement, dependency list, proof plan or source is changed.

Hypothesis and clause correspondence:

- The finite-field and finite-coefficient datum is `C : PurityFiniteSetting.{u}`.
  The ring is exactly `C.Coefficient`, the standard size lift of
  O_E/(varpi_E^n), with positive level and distinct primes retained in C.
- Each of B, X, Z has `Over (Spec (CommRingCat.of C.field.k))`.
  `IsSeparated` on each structure map renders "separated k-schemes".
  `LocallyOfFiniteType` and `QuasiCompact` on each structure map render
  "finite type over k". The same three morphism instances on f and g render
  separated finite-type morphisms, and `f.IsOver`, `g.IsOver` retain the k-structure.
- `FiniteProductGeometry` packages the three Cartesian products and their
  projection maps, using the existing `IsPullback` notion. It contains only
  geometry, with no derived functors or transformation data. The main proposition
  supplies `finiteProductGeometry cf cg`, whose P,W,T are literally Mathlib's
  `pullback f g`, `pullback f cg.g`, and `pullback cf.g cg.g`. Thus no geometric
  package is requested as an additional hypothesis. The abstract fields let the
  intermediate derived maps compile without expanding concrete limit schemes.
- P is therefore literally `pullback f g`; p and q are its canonical projections.
  The structure map h is q followed by g, identified with p followed by f by sqP.
- M and N are ordinary fixed-scalar small pro-etale `DerivedCategory.Plus`
  objects. `wM`, `wN : Scheme.FixedEtaleOriginWitness` retain their actual
  bounded-below etale antecedents and specified comparison isomorphisms.
- `FiniteProductCompactificationDomain` records the six tensor objects in T:
  input, swapped input, first projection output, its transposition, the
  exchanged tensor, and the external tensor D, in this conjunction order.
  Each conjunct is exactly
  `DerivedCategory.plusEtaleOrigin`, combining bounded-below and etale origin.
  There are no domain assumptions on auxiliary ordinary proper tensor objects.
- `finiteProductChosenForward` is symmetry; PF_g; Rg_! of symmetry;
  Rg_! of Ex_! tensor identity; Rg_! of PF_q; normalized alpha_{g,q}.
  PF_q uses precisely `cf₀.ofIsPullback G.sqP`, the base change of the
  original f compactification. The alpha is
  `finiteProductComposition`, conjugating the recorded origin compositor by
  the specified normalized compactification comparisons, so it also works
  for original choices different from the global choice.
- `cf₀`, `cg₀`, `ch₀` are arbitrary original compactifications defining the
  forward source and target. Independently, `cf`, `cg` are any displayed pair
  (aj,bk). Their `i`, `g`, `Z` fields are j,a,Xbar and k,b,Zbar.
- `finiteProductFirstOpen` is P to X times_B Zbar, the canonical lift with
  projections p and q followed by k. `finiteProductFirstSquare` is its
  cartesian open square, obtained by canceling the defining lower pullback.
  The open-immersion instance is the existing base-change lemma specialized
  to that square.
- `finiteProductCompactification G` has ambient scheme G.T, proper map G.t
  followed by G.cg.g, and open the first open followed by the second open.
  At `finiteProductGeometry cf cg`, G.T and its projections are literally
  `pullback cf.g cg.g` and its canonical projections. The second open is the
  unique lift with projections s followed by j and v. Thus C, r, t, c and u
  are exactly the node's product geometry. The square G.sqT also identifies
  c=t followed by b with r followed by a. The commutativity proof uses the
  two open projection equations and cg.comm; the properness and openness
  proofs use the existing base-change and composition stability instances.
- H and J are the exact termwise fixed-scalar open extensions of M and N.
  They are the canonical presentation of the recorded intrinsic extension
  `Scheme.sfIntrinsicExtensionByZero` through `sfIntrinsicModuleEquivalence`.
- `finiteProductExternal` is exactly D=Lp*M tensor Lq*N.
  `finiteProductExtendedTensor` is exactly Lr*H tensor Lt*J.
- `finiteProductInnerOpenTensor` and `finiteProductOuterOpenTensor` factor the
  two actual open steps. Typed components of pullback comparison, tensor on maps
  and extension on maps keep the same existing canonical operations. The two
  tensor object expressions are transparent abbreviations. The canonical geometry is
  supplied only when stating the final proposition. Both opens are real unique
  Cartesian lifts; their openness is inherited from the two Cartesian squares.
- `finiteProductOpenTensor` is the specified canonical e: open base change
  for j, inverse open projection for its base change, pullback composition,
  open base change for k, symmetry, inverse open projection for its base
  change, pullback composition and symmetry, then open composition. Although
  the formula is read from its source to its target, its extensions are
  first P to X times_B Zbar, then to Xbar times_B Zbar. The two swaps cancel
  after restriction. The beta, gamma, and open-composition maps use their
  existing section-unit/adjunction normalization, so e restricts to 1_D.
  `finiteProductOpenTensor_isIso` is the node's displayed isomorphism assertion.
- `finiteProductOrdinary` is exactly Omega: signed symmetry; pi_b; Rb_* of
  signed symmetry; Rb_* of the ordinary exchange tensor identity; Rb_* pi_t;
  inverse of `finiteDirectImageComposition A t b`. This has the node's
  orientation from Ra_*H tensor Rb_*J to Rc_*(Lr*H tensor Lt*J).
- `FiniteProductCompactificationEquation` postcomposes T by the normalized
  target comparison ch₀ to the product compactification. Its right side
  first compares each original source compactification to cf,cg, then applies
  Omega followed by Rc_* of the actual e. This is precisely the displayed
  equality under the node's specified source and target identifications.
- `FinitePurityProductCompactification` universally quantifies all three
  original choices, both displayed choices and every tensor-domain witness.
  Its local compact-space and quasi-separated-space instances follow from
  finite type and separatedness over the field, solely to instantiate Nagata.
  They add no hypotheses. The main theorem asserts this proposition.

Dependency declarations inspected and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `.Coefficient`, `.coefficientCommRing`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the finite intrinsic operations and
  their canonical fixed-scalar realization; the concrete fixed-scalar operations
  below are the ones already used by the recorded composition interface.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift`, `pullback.condition`;
  the actual cartesian-square/pasting lemmas from Mathlib are used as well.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `Scheme.FixedEtaleOriginWitness`, its `complex` and `iso` fields.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: the recorded counit/mate
  formulas. Their concrete finite components are the existing
  `projectionMapOfCompactification`, `rightDerivedLowerStarProjectionMap`,
  `rightDerivedLowerShriekOfCompactificationBaseChangeMap`,
  `derivedBaseChangeMap` in the published `FiniteCoefficient.Derived` modules.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`:
  `originCompositionAmbient`, with its specified etale model and faithful descent.
- `WeilConjectures.Compactification.Refinement` and the imported `Defs`,
  `BaseChange`: `Compactification`, `.baseChange`, and its projection equations.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `sfIntrinsicModuleEquivalence`, `sfIntrinsicExtensionByZero`; the same
  construction in fixed-scalar coordinates is `openImmersionLowerShriek`.
- `Sheaf.SixFunctors.OpenTensorNormalization`: the finite beta/gamma identification
  with the published ordinary open maps and section-unit normalization;
  `derivedOpenImmersionLowerShriekBaseChangeIso`,
  `derivedOpenImmersionLowerShriekProjectionIso` are those canonical finite maps.
- `Sheaf.Paper.FiniteDirectImageComposition`: `finiteDirectImageComposition`.
- The normalized compactification comparisons are reused as
  `finiteForwardCompactificationComparison`, already defined in
  `Sheaf.Paper.FiniteForwardProductSymmetry` by canonical etale common-refinement
  comparison and fully faithful descent. The same module's exposed component
  wrappers `finiteForwardTensorSymmetry` and `finiteForwardProjectionMap` are
  reused; its symmetry theorem is never used. This preserves one construction
  of these maps. Do not add the reverse proof import of this delivery into that
  module: it would close an import cycle. This is the omission authorized by
  stages/2-statements.md §3(7); a later proof module may factor the shared helpers.
- The recorded `Sheaf.Paper.CompactificationCoherence` was read. Importing it
  directly pulls in the retired ordinary LowerShriek path through
  ComparisonGlobalCohomology and conflicts with the current finite path.
  The smaller canonical etale comparison interface already imported by
  `finiteForwardCompactificationComparison` supplies the normalized comparison
  used here, as authorized by the duplicate-import repair instruction. The
  main proof docstring still cites the coherence theorem and its refinement law.
- Available proof modules `PfRefinementCompatibility` and
  `ProEtaleDerivedOpenRestriction` are imported. The other proof prerequisites
  without recorded modules are retained in the DAG/proof docstring.

Edge cases checked: empty X or Z and hence empty P; zero M or N; identity and
proper morphisms (including identity compactifications); arbitrary original
choices distinct from the displayed pair; positive level n=1; arbitrary universe u.
No nonemptiness or nonzero-coefficient hypothesis is introduced. The site keeps
object universe u+1 and morphism universe u, and modules have size u+1.
The forward-domain condition is explicit: bounded-below M,N alone do not imply
bounded-below derived tensor over a nonregular Artinian coefficient ring.
There is no constructibility, finite Tor-amplitude, exceptional-adjoint, or
abstract six-functor datum. Only open projection and open base-change maps are
inverted; every ordinary/compact-support pi, PF, Ex map remains forward.

Searches (2026-10-18):

- msearch.py leanfinder, query "finite forward product compactification comparison
  of compact support Kunneth map with ordinary direct image projection exchange":
  eight unrelated topological finite-product hits; no exact statement.
- msearch.py loogle, query "CategoryTheory.mateEquiv, CategoryTheory.Limits.pullback":
  zero hits. The local declarations and signatures were inspected directly.
- msearch.py grep, query "compactification|projectionFormula" in CategoryTheory:
  zero hits.
- rg in slopmaster2/WeilConjectures and the side lean/Sheaf for
  "finiteProduct|finite.*[Pp]roduct.*[Cc]ompactification|lem-pur-finite-product-compactification":
  only the related symmetry module and unrelated finite-product results. The
  symmetry module cites this item as a future proof dependency, not an existing
  proof of this equality. Its already-defined map helpers are reused.
- The exact item id has no declaration in the upstream source. Mathlib's
  pullback and mate APIs are reused, rather than redefined.

No statement fault or mathematical dispute was found. The complete ten-step
natural-language proof is included in the main theorem's docstring.

Validation: the prescribed scompile.py check compiled the final module without
warnings in approximately 19 seconds per invocation. The required deliver2.py
dry run passed preflight and per-file compilation.

## Second reading by Q23

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
