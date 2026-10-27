## Worker report

This is stage 2. The ledger's 2026-10-23 11:59 PASS completed the stage-1 split,
not a Lean statement: the base node has no lean record, its queue entry is stage 2,
and the report currently in the repository is the stage-1 report. The inherited
unchanged-delivery failure therefore does not prevent this stage-2 delivery
(coord/brief-stage2.md section 0). No released repair note exists for this item.

The module Sheaf.AlgebraicTopology.WeakPosetChainNormalization states the node in
namespace AlgebraicTopology.WeakPosetChains. The main theorem is normalization.
Its helper declarations construct the very weak complex, repeated span, canonical
projection, and induced quotient maps introduced by this node; they are recorded
in lean.declarations. They are not independent missing notions. All data are
explicit Finsupp constructions or Submodule.mapQ; no object is chosen from an
unproved existence assertion. Five named theorems have sorry proofs:
boundary_laws, map_laws, quotient_boundary_laws, quotient_map_comm, normalization.
Their docstrings give the corresponding portions of all six node proof steps.
No mathematical claim is proved in this stage.

Hypotheses and clauses, with all names below relative to that namespace:

- The coefficient ring is an arbitrary R : Type u with [CommRing R]. There is no
  field, nonzero, or characteristic assumption. Posets range over Type v with
  [PartialOrder P], and the statements and packaged complexes have [Finite P].
  There is no Nonempty assumption. Universe variables u and v are explicit and
  independent; ModuleCat.{max u v} accommodates the free modules.
- Weak tuples in degree n are Simplex P n: lists l with l.Pairwise (· ≤ ·) and
  (l.length : ℤ) = n + 1. The free module is chains R P n = Simplex P n →₀ R.
  Thus for n ≥ 0 it has every weak tuple as a separate generator, including
  repetitions; for n = -1 the basis is the singleton empty list; for n < -1
  the length equation is impossible, so the module is zero. This is the same
  canonical free-module encoding used by the strict-chain dependency.
- bracket is Finsupp.single c 1 for a valid weak list. boundary is the linear
  extension of the sum over Finset.range l.length of (-1 : R)^k times the bracket
  of l.eraseIdx k, in adjacent degrees, and zero elsewhere. A vertex deletes to
  the empty list. The empty-list sum is zero; below degree -1 there are no basis
  elements. These give precisely the node's d_n for every integer degree.
- repeated R P n is the span of Finsupp.single c 1 with ¬ c.val.Nodup when
  1 ≤ n; it is bottom otherwise. This is exactly D_n, not a quotient in which
  repetitions were already removed. The third conjunct of boundary_laws says
  D_i ≤ D_j.comap d_ij, including the required adjacent indices.
- The first two conjuncts of boundary_laws give the shape and d² = 0. complex
  packages the actual modules and boundary in Mathlib's integer ChainComplex.
- The target is precisely AugmentedPosetChains.complex R P from the dependency.
  projection linearly sends each weak basis list to its strict bracket, using
  AugmentedPosetChains.bracket (not a private strict-chain definition). Thus it
  kills repeated lists, preserves strict generators, and fixes the empty one.
  boundary_laws gives its chain-map equation. comparison packages this chain map.
- The first conjunct of normalization asserts Function.Surjective in every
  integer degree, and LinearMap.ker ((comparison R P).f n).hom = repeated R P n.
  The final conjunct of boundary_laws explicitly states projection kills D.
- quotientBoundary is Submodule.mapQ of the actual weak boundary. Its required
  compatibility proof is boundary_laws; quotient_boundary_laws gives shape and
  square-zero. quotientComplex therefore has exactly W_n / D_n as its terms
  and the differential [w] ↦ [d(w)]. No arbitrary quotient complex is supplied.
- normalization supplies a family e P : quotientComplex R P ≅
  AugmentedPosetChains.complex R P. Its first equation specifies the forward map
  on EVERY quotient class, e.hom([x]) = q(x). This determines the isomorphism
  uniquely, including its inverse; the theorem is an existence assertion about
  that canonical comparison, not a definition making an unconstrained choice.
- mapComponent is linear extension of bracket R n (c.val.map f) for f : P →o Q.
  Thus its formula is exactly the entrywise image of a weak tuple, including the
  empty tuple. The degree -1 map is the identity on its canonical R basis; lower
  maps are the unique zero maps. map_laws states the chain-map equation and
  repeated-span preservation. map packages the chain map W(f).
- normalization's second and third conjuncts assert W(id) = id and
  W(g.comp f) = W(f) ≫ W(g), which is W(g) composed after W(f).
- quotientMapComponent is Submodule.mapQ of mapComponent with map_laws' proof.
  quotient_map_comm and quotientMap package the induced CHAIN map on the actual
  degreewise quotient. normalization's final equation evaluates this chain map
  on the class of every strict generator, then applies e Q. The result is
  AugmentedPosetChains.bracket R n (c.val.map f): the strict image generator
  when strict, and zero otherwise. This includes the unique strict generator
  in degree -1 (the empty list), so its preservation is included without an
  exception or an additional hypothesis.

Dependencies read and used:

- def-weil-pbc-module-chain-complex-homology records
  Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex,
  HomologicalComplex.homology. I read its full signature and docstring (line 90)
  together with ChainComplex, HomologicalComplex and HomologicalComplex.Hom in
  Mathlib.Algebra.Homology.HomologicalComplex. No homology assertion is needed
  here: the node uses this dependency for precisely those complex and morphism
  conventions. The recorded module is publicly imported transitively by the
  strict-chain module.
- def-sfb-augmented-poset-chains records
  Sheaf.AlgebraicTopology.AugmentedPosetChains,
  AlgebraicTopology.AugmentedPosetChains.complex. I read the whole file, including
  Simplex, chains, bracket, boundary, boundary_laws and complex. The module is
  publicly imported and its complex and bracket are used directly. No dependency
  record needed repair. Both proof dependencies are the same two statement
  dependencies; no additional proof import or cycle is introduced.
- Mathlib.LinearAlgebra.Quotient.Basic, Submodule.mapQ is used for both induced
  maps. I read its signature and its implementation via liftQ (lines 120,174),
  including the required submodule-comap condition.

Edge cases checked before writing: empty P has only its degree -1 R summand;
P a singleton has [x,x] in W_1 with boundary [x]-[x] and D_0 = 0; the empty
list has zero outgoing boundary. A strict two-point chain collapsed by a constant
map has zero strict image and boundary [y]-[y]. Antichains still have constant
weak lists; three equal vertices give a repeated boundary, not zero in every
positive degree. Degrees below -1 have empty basis. In characteristic two the
paired signs still cancel; over the zero ring all free modules are zero and
the surjectivity and kernel assertions retain their meanings. Identities and
composition preserve the empty generator even for empty source or target when
an actual monotone map exists. No statement is disputed or corrected.

Searches (actual calls for this stage-2 run):

- msearch.py leanfinder: "The augmented free chain complex on weakly increasing
  poset lists modulo repeated lists is the strict chain complex, naturally for
  monotone maps". Eight hits: DoldKan.c, ChainComplex.alternatingConst,
  AlternatingFaceMapComplex.obj, ChainComplex.augment, ChainComplex.of,
  DoldKan.Γ₀.Obj.summand, ChainComplex, ChainComplex.augment_X_succ. None states
  the augmented poset quotient comparison or its kernel and map formula.
- msearch.py loogle: '"AlternatingFaceMapComplex", "map"'. Twelve hits, including
  AlternatingFaceMapComplex.obj, objD, map, map_f, d_squared and ε. I read the
  objD/obj/map declarations in Mathlib.AlgebraicTopology.AlternatingFaceMapComplex.
  They take a simplicial object and give a nonnegative complex; identifying its
  poset model, repeated span, strict basis and integer augmentation is precisely
  additional work here. There is no one-line specialization of the whole node.
- msearch.py grep: "weak.*tuple|poset.*chain|repeated.*tuple" in AlgebraicTopology:
  zero hits. The earlier split's searches are also retained verbatim in the node.
- rg over lean/WeilConjectures and lean/Sheaf for
  "weak.*tuple|poset.*chain|repeated.*tuple|lem-sfb-poset-weak-chain-normalization":
  the strict-chain definition, its downstream prism, and ordered Čech sorting
  constructions. The latter concern Čech sections, not these free poset modules.
  I read AugmentedPosetChainPrism's mapComponent/map_comm/map: these define the
  strict entrywise map but not W, D, or their quotient comparison. Importing that
  downstream module would also run against the normalization proof route.
  No declaration already states the full item or defines its weak-list complex.
- Whole-DAG inspection retains the two existing definition nodes; weak tuple
  and normalization occurrences are this item and its downstream prism, rather
  than an independent definition to copy. No new node is required.

Source checked: literature/stacks-project/simplicial.tex, section-complexes
(Tag 0194, lines 3605–3648), remark-degenerate-subcomplex (Tag 0FKI, lines
3898–3915 and preceding equal-face cancellation), and equation-homotopy-to-homotopy
near Tag 019S. As the node states, this is an explicit augmented poset adaptation,
not a claim that Tag 019S already proves this entire assertion.

Validation: every compile uses scompile.py against the published live library.
The first compile found one missing pair of parentheses around the component
map in Function.Surjective; that syntax was corrected. The final clean compile
and the required deliver2.py preflight/delivery are run on this exact packet.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
