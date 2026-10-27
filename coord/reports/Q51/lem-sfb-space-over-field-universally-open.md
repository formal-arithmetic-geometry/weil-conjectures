## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceOverFieldUniversallyOpen` states
`AlgebraicGeometry.AlgebraicSpace.isOpenMap_prod_snd_overField`, with one postponed
proof and no new definitions. Source read: Stacks Project, spaces-morphisms.tex,
Tag 06DN, lemma-space-over-field-universally-open, statement and complete proof.
The node already expands that proof from scheme tests to arbitrary algebraic-space
tests using Tags 03H4 and 03BX; its three steps are retained in the docstring.

Clause-by-clause correspondence:

- A field k: `(k : Type u) [Field k]`, the existing Mathlib Field class.
- X and Y are algebraic spaces over Spec k:
  `(X Y : AlgebraicSpace (Spec (CommRingCat.of k)))`. The existing category consists
  of fppf sheaves on schemes over the specified base with representable diagonal
  and a representable surjective etale scheme atlas. No extra structure is chosen.
- Their sheaf fibre product over k: `Limits.prod X.obj Y.obj`. Since both are
  sheaves on schemes over Spec k, this categorical product is precisely X ×_k Y.
  On every scheme T over k its sections are pairs of sections of X and Y. The
  base-compatibility condition is automatic because the base is already fixed.
  The fibre-product dependency supplies algebraic-space closure; no new notion
  of product or algebraic space is introduced.
- Its second projection on point classes:
  `mapPoint (Limits.prod.snd (X := X.obj) (Y := Y.obj)).hom`. Here `.hom` forgets a sheaf
  morphism to its natural transformation, and mapPoint applies it to the already
  defined field-valued representatives and passes to their quotient classes.
- Atlas topology: the existing `pointTopologicalSpace` instances are inferred
  for the product presheaf and Y's presheaf. They are the final topologies for
  all representable etale scheme-source maps, exactly as the dependency states.
- Sends every open subset to an open subset: `IsOpenMap` of that actual point map.
- Universal openness after every algebraic-space base change: Y is an arbitrary
  algebraic space over Spec k, so the theorem's Y binder covers exactly those
  tests. The node's equivalent reformulation introduces no separate property.
- No nonemptiness, quasi-compactness, quasi-separatedness, finite type, or
  finite presentation assumption appears. Universe u is explicit throughout;
  autoImplicit is disabled. No characteristic restriction is imposed.

Dependencies read and used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs, lines 169–180.
- def-weil-affine-spectrum: `AlgebraicGeometry.Spec`,
  Mathlib.AlgebraicGeometry.Scheme, lines 469–472 (Spec.map also read).
- def-trf-algebraic-space: `AlgebraicGeometry.AlgebraicSpace`,
  Sheaf.AlgebraicGeometry.AlgebraicSpace; its full definition, diagonal and atlas
  conditions were read.
- def-a1-space-point-topology: `AlgebraicGeometry.AlgebraicSpace.pointTopologicalSpace`,
  Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology, and its existing point classes.
- lem-trf-space-fibre-products-etale-covers:
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace`,
  `etaleCover_pullback`, `etale_fibreProduct_isScheme`, in
  Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers. Full signatures
  and proof docstrings read. The module is publicly imported.
- Added already-landed stmt_dep def-sfb-proper-curve-moduli solely to use its
  canonical `AlgebraicGeometry.AlgebraicSpace.mapPoint`, in
  Sheaf.AlgebraicGeometry.ProperCurveModuli. This is the existing quotient map,
  not a proper-curve assumption; its complete construction was read.
- Proof-only import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus:
  `AlgebraicGeometry.AlgebraicSpace.point_open_calculus`, the recorded proof input,
  including continuity, point-surjectivity and compatible-point lifting.
- Proof-only import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen: the
  integral-subsingleton-target instance giving the scheme-over-field input
  lem-sc-scheme-over-field-universally-open, plus base-change projection
  instances and `Scheme.Hom.isOpenMap`. Full signatures and implementation read.

Edge cases checked before writing: if X or Y is empty, the product point space
is empty and every image is empty/open. With X = Spec k the projection is the
identity up to the canonical identification. Arbitrary characteristic, infinite
discrete spaces, and non-quasi-separated spaces are allowed: none is excluded
by the signature. Fixing arbitrary u does not impose an independent smaller
universe on test spaces. No statement correction or disputed statement was needed.

Searches actually performed:

- msearch.py leanfinder: "The projection from a fibre product of algebraic spaces
  over a field is an open map". Eight hits, including UniversallyOpen.snd/fst;
  all concern schemes and do not state the arbitrary-algebraic-space result.
- msearch.py loogle: `"UniversallyOpen"`. Twelve hits, all for schemes, including
  the class, base-change instances, and flat locally finitely presented case.
- msearch.py grep: `AlgebraicSpace|algebraic.space`, Mathlib/AlgebraicGeometry.
  Zero hits: no Mathlib algebraic-space theorem.
- msearch.py leansearch: "Every algebraic space over a field is universally open".
  Eight hits, all scheme universal-openness declarations; no exact match.
- rg over lean/WeilConjectures: `AlgebraicSpace|algebraic.space|isOpenMap_prod_snd_overField`;
  no hits. grep for this item's blueprint id there likewise had no hits.
- rg over lean/Sheaf and lean/WeilConjectures for mapPoint, universal openness and
  this item: found the existing point map in ProperCurveModuli, point calculus,
  and the flat-lfp algebraic-space theorem (which adds finite-presentation
  assumptions and is not an exact match). No theorem stating this item found.
- rg for `isOpenMap_prod_snd_overField|spaceOverField` across Sheaf and Mathlib
  and the chosen name in WeilConjectures found no prior declaration.

The published compact-object example module is withdrawn (no declarations);
its node was also read. This delivery follows the active AlgebraicSpace module
header and public-section conventions instead. All writes are in the prescribed
sandbox; all compilation is through scompile.py.

Validation: scompile.py compiled both the sandbox and final library module cleanly
(1.5 seconds each). The initial application of prod.snd used explicit positional
arguments; reading its signature showed implicit X/Y arguments, and the final
statement uses the named arguments `(X := X.obj) (Y := Y.obj)`. No other warning
or error remains. This was an elaboration repair with no mathematical change.

## Second reading by Q51

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
