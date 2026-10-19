## Worker report

The module `Sheaf.Paper.RingedKunnethFactorizations` states
`SheafOfModules.ringedKunnethFactorizations`, with `sorry` as its whole proof.
It defines the two displayed composites, their common transpose, the opposite mate,
the canonical right-adjoint path comparison, and the fixed-first-factor form of the
projection arrow. Every definition contains real map data. It reuses the existing
`RingedTensorSquare.exchange` for beta rather than defining that map again.
No new nodes, dependency repairs, or statement correction are needed. The only
additional statement dependency is the already landed
`def-weil-pbc-ringed-tensor-square-presentation`, whose existing presentation is used
verbatim. The original statement and proof are unchanged.

Hypotheses and clauses, matched individually:

- Topoi X, Y, W presented by small sites with commutative coefficient rings:
  `Y X W : RingedTensorCorner.{u,w}`. Each corner contains its site, category,
  topology, and `Sheaf topology CommRingCat.{u}`. The sites and Hom sets are small
  in the module universe u; w is the separately specified derived Hom universe.
  The statement does not concern the distinct small pro-etale presentation whose
  object and Hom universes differ. These are the existing arbitrary small-site
  presentations; universe u is polymorphic and no particular bound is fixed.
- Ordinary unbounded derived categories of module sheaves: the corners carry
  `HasDerivedCategory.{w}` on the actual Mathlib `SheafOfModules`, and the binders
  for M and N use `DerivedCategory (SheafOfModules ...)` explicitly. No bounded,
  constructible, flat-object, or exact-underived-pullback restriction occurs.
- Morphisms q:X→Y and a,b:W→X: `q : RingedTensorEdge Y X` and
  `a b : RingedTensorEdge X W`, in inverse-image direction. These are the existing
  presentations: geometric inverse image with its left exactness, structural ring
  map, scalar-extension module pullback, its total left-derived functor, and
  ordinary and derived right adjoints. They include the representative-normalized
  canonical ordinary tensor comparison, rather than an arbitrary tensor map.
  By the presentation node's statement, arbitrary right-adjoint models are allowed
  and identified with direct image by the unique adjunction-compatible comparison.
- Specified ringed commutation isomorphism qa≅qb:
  `s : RingedTensorSquare Y X X W q q a b`. Its set-sheaf comparison and linear
  module comparison satisfy the scalar insertion equation. It imposes no
  cartesianness and includes no derived tensor coherence as a hypothesis.
- L,R,A,B,S,U are respectively `q.left`, `q.right`, `a.left`, `b.left`,
  `a.right`, `b.right`. The ringed square's existing `s.derivedComparison` is
  theta: `q.left ⋙ b.left ≅ q.left ⋙ a.left`, that is BL≅AL. It is fixed by
  the unique K-flat-representative characterization, not supplied freely.
- The canonical identification RS≅RU is `RingedKunneth.directComparison s`:
  `conjugateIsoEquiv (q.derivedAdjunction.comp a.derivedAdjunction)
  (q.derivedAdjunction.comp b.derivedAdjunction) s.derivedComparison`.
  This is specifically the right-adjoint comparison used in Stacks 0D6E:
  its proof identifies composite right adjoints by uniqueness after identifying
  composite left adjoints. No independent isomorphism of direct images is a binder.
  Its inverse component has exactly the direction RU(Z)→RS(Z) used in the first
  conjunct. Composition comparison and ringed commutation are represented by the
  same theta throughout.
- Beta_M:LRM→UAM is exactly `s.exchange.app M`, already defined by `mateEquiv`
  in `RingedExchangeTensorCoherence`. The opposite mate bar-beta_N:LRN→SBN is
  `(RingedKunneth.betaBar s).app N`, using `mateEquiv` on theta inverse. Neither
  mate has an `IsIso` assumption or an inverse in the delivery.
- The ordinary displayed order of pi is the existing
  `RingedTensorEdge.projection`, whose transpose is the canonical tensor
  comparison followed by counit tensor identity. The fixed-factor-first order
  is `RingedTensorEdge.projectionFixedFirst`; its explicit transpose is tensor
  comparison followed by identity tensor counit. This is exactly pi with tensor
  symmetry putting factors in the displayed order, without presupposing pi is
  invertible or adding another tensor structure.
- For every M,N: the theorem has two independent binders in D(X). The first
  displayed composite is `RingedKunneth.first s aY aX aW M N`: its first arrow
  is `q.projectionFixedFirst aY aX (q.right.obj M) N`, with target
  R(LRM tensor N); its next arrow is R(beta_M tensor identity_N); its final
  arrow is R of `b.projection aX aW (a.left.obj M) N`, with target
  RU(AM tensor BN). The definition groups the last two arrows inside `R.map`,
  equivalently the three arrows as displayed by functoriality.
- The second displayed composite is `RingedKunneth.second s aY aX aW M N`:
  `q.projection aY aX M (q.right.obj N)` targets R(M tensor LRN);
  R(identity_M tensor bar-beta_N) is followed by R of the fixed-first-factor
  a-projection, targeting RS(AM tensor BN).
- Equality under RU≅RS is the first conjunct, `first ... ≫ directComparison.inv.app
  (W.tensor.obj (a.left.obj M, b.left.obj N)) = second ...`. In particular,
  the two arrows are compared in their actual canonical targets, not by an
  arbitrary chosen target identification.
- Their common transpose is the second conjunct. It applies the inverse hom
  equivalence of `q.derivedAdjunction.comp a.derivedAdjunction` to `second ...`,
  so its source is AL(RM tensor RN), the composite model of (qa)*. Equality of
  first and second under the canonical target comparison makes this the
  common transpose, rather than an additional unrelated map.
- The displayed transpose itself is `RingedKunneth.commonTranspose`. First
  `a.left.map (q.tensorComparison ...).hom` and `a.tensorComparison` give d_A.
  The second tensor factor is changed by theta_RN inverse from ALRN to BLRN.
  The two remaining factors are `a.left.map (q.derivedAdjunction.counit.app M)`
  and `b.left.map (q.derivedAdjunction.counit.app N)`. The implementation
  combines the second factor's theta inverse and B(v_N) in one tensor map;
  bifunctoriality identifies it with the displayed initial isomorphism followed
  by A(v_M) tensor B(v_N). No conclusion has been omitted.
- The final negative clause is reflected by the absence of cartesian, proper,
  boundedness, or any `IsIso` hypothesis on beta, bar-beta, or pi. Only theta
  and its canonical conjugate are inverted.

The model binders `aY`, `aX`, `aW : RingedTensorModel ...` specify the ordinary
derived tensor bifunctors by their total-tensor identification on flat K-flat
representatives. They do not assume the coherence identity being asserted.
This is the published interface of the ringed tensor theorem and introduces no
new mathematical hypotheses on the topoi or the derived objects.

Dependency declarations read and used:

- `def-weil-size-convention`: metatheoretic convention, rendered by explicit u,w.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  transparent abbreviation of Mathlib `SheafOfModules`. The presentation uses
  the latter directly, definitionally the same category, not a private copy.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`: actual unbounded localizations of cochain complexes.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`:
  current primary tensor comparison interface, imported publicly. The corner/edge
  interface uses its retained equal-site-universe specialization
  `SheafOfModules.ringedTopoiCanonicalDerivedTensorComparison`, through
  `RingedTensorEdge.tensorComparison`; the unique representative normalization
  is retained and no separate comparison is chosen.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`,
  `CategoryTheory.ringedToposDerivedPushforwardComposition`: the current canonical
  composition assertion, with its unit characterization and K-injective-resolution
  normalization. Imported publicly. Its proof constructs the comparison by
  conjugation of pullback composition; `directComparison` uses precisely that
  construction for the two ringed paths, as in the cited Stacks proof.
- `Mathlib.CategoryTheory.Adjunction.Mates`, `CategoryTheory.mateEquiv`,
  `mateEquiv_counit`, `conjugateIsoEquiv`, `conjugateEquiv_counit`: both exchange
  orientations and the canonical right-adjoint comparison.
- `Mathlib.CategoryTheory.Adjunction.Basic`, `CategoryTheory.Adjunction.comp`:
  composite adjunction and the hom equivalence in the transpose clause.
- `Sheaf.Paper.RingedExchangeTensorCoherence`, `RingedTensorSquare.derivedComparison`,
  `RingedTensorSquare.exchange`, `RingedTensorEdge.projection`: the canonical
  comparison and maps already recorded for the exchange-tensor dependency.
- `Sheaf.CategoryTheory.RingedToposMorphism`, `CategoryTheory.RingedToposMorphism`:
  the recorded geometric and structural-ring-map notion was read. The existing
  richer `RingedTensorEdge` presents precisely its inverse-image and induced
  module adjunction data; no new single-morphism structure is defined.
- `Sheaf.Paper.RingedTensorSquarePresentation`, `SheafOfModules.RingedTensorCorner`,
  `RingedTensorModel`, `RingedTensorEdge`, `RingedTensorSquare`,
  `RingedTensorEdge.tensorComparison`: already landed presentation used verbatim.
  This node is added to stmt_deps, not duplicated or repaired.

The proof-dependency `lem-sfb-ringed-comparison-tensor-adjunction` has no Lean
record or Mathlib match in the current DAG. It is retained in the proof plan and
its full statement was read; it contributes no missing object needed to type this
statement: the canonical theta is already defined by the exchange dependency,
and conjugation itself constructs the direct-image comparison. Accordingly no
import of a nonexistent proof module is added. All already-stated proof dependencies
are present through the public imports. The one postponed theorem has the matching
item node and its six-step natural-language proof in its docstring.

Edge cases checked before writing: M=0 or N=0 are allowed; arbitrary unbounded
complexes and nonflat cohomology are allowed; q or a or b may be identity, a=b is
allowed, and a nontrivial specified commutation isomorphism is not replaced by an
identity. Empty sites/topoi and zero commutative coefficient rings are not excluded.
No index set occurs and there is no hidden nonempty, finite, perfect, or invertibility
condition. Factors M and N remain independent. The theta inverse is on RN in the
common transpose, and the target comparison is the inverse RS≅RU, so both direction
edge checks agree with the node.

Searches for an existing full statement:

- `msearch.py leanfinder`, query “The two projection formula and exchange
  factorizations of the external product of derived module sheaves on ringed topoi
  have common transpose the tensor of counits”: eight results, including
  `SheafOfModules.pushforwardPushforwardAdj_counit_app_val_app` and the ordinary
  pullback adjunction's unit/counit normalization. These concern underived site
  functors, not the two displayed unbounded ringed-topos composites.
- `msearch.py loogle`, query `CategoryTheory.mateEquiv, CategoryTheory.Adjunction`:
  twelve results including `mateEquiv`, `mateEquiv_counit`, and
  `iterated_mateEquiv_conjugateEquiv`; these are reusable formal mate identities,
  not the node's statement on actual module derived categories.
- `msearch.py grep`, query `kunneth|Kunneth|projectionFormula|projection_formula`
  in Mathlib CategoryTheory: zero results.
- `msearch.py leansearch`, query “Two projection and exchange factorizations of
  derived external product have common transpose the tensor of adjunction counits”:
  eight results including `Adjunction.derivedε`, `Adjunction.derived_counit`, and
  `frobeniusMorphism`, none stating the required two factorizations.
- `rg` for Kunneth/kunneth in the upstream project and `lean/Sheaf` found specialized
  etale/pro-etale Kunneth maps and tensor homology/Kunneth formulas, and the already
  used generic exchange-tensor module, not this statement.
- `grep -rn` for the exact item id in upstream `WeilConjectures` and `rg` in the
  upstream-name DAG index: no results. Searches for the new declaration names
  `projectionFixedFirst`, `ringedKunnethFactorizations`, and `RingedKunneth` in
  Mathlib, upstream, and the side library: no collisions.

Validation: the initial file compiled cleanly through `scompile.py`, separately as
sandbox and library module, in 3.1s and 4.2s. The final packet is checked again by
`deliver2.py --no-push`, including every delivered file. No statement dispute found.

## Returned-delivery repair

The retained delivery was returned at immutable head `31773df2bf5b` solely because
the reviewer-fix packet named the repository path
`coord/reports/Q36/lem-sfb-ringed-kunneth-factorizations.md`. Stage-2
`--apply-fixes` accepts the flat item report name in its fix directory; it does not
accept that repository pathname. I therefore repaired the packet by updating this
worker report and delivering it through the ordinary `deliver2.py` packet layout.
The Lean module, item statement, declaration record, and dependency declarations
remain unchanged. The prescribed dry run after this repair passes preflight and
per-file compilation.

## Second reading by Q36

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
