## Worker report

The module Sheaf.AlgebraicGeometry.SimplyConnectedMultiplicativeLifting states
AlgebraicGeometry.simplyConnected_multiplicative_lifting with one postponed proof.
The source was read directly using pdftotext on
literature/milne-algebraic-groups_iAG2017.pdf: Definition 18.5, Proposition 18.6(a),
Definition 18.7 and Proposition 18.8, printed pp.388--389. The algebraically closed
field is perfect, so Proposition 18.6(a) applies. No correction to the statement
or to the accepted seven-step proof is needed.

Clause and hypothesis correspondence:

- F is an algebraically closed field: `{F : Type u} [Field F] [IsAlgClosed F]`.
- H, G and E are group schemes over F: objects of `Over (Spec (.of F))` with
  `GrpObj` instances. A group homomorphism is an `IsMonHom` over-morphism.
- Each group is affine: `IsAffine H.left`, `IsAffine G.left`, `IsAffine E.left`.
- Smoothness: `Smooth` of each structure map `.hom`.
- Connectedness: `ConnectedSpace` of each underlying scheme; this includes nonemptiness.
- Finite type: `LocallyOfFiniteType` and `QuasiCompact` of all three structure maps.
- The scheme-theoretic kernels are `GrpObj.ker q`, `GrpObj.ker p`, and, inside
  simple connectedness, `GrpObj.ker r`. Their definition is the pullback along
  the target unit, not the kernel on rational points. Their inclusions are
  closed subgroup schemes by the existing kernel result in GroupScheme.Defs.
- Faithful flatness of q and p: `hq` and `hp` state
  `.left.appTop.hom.FaithfullyFlat`. On affine schemes this is the indicated
  coordinate-algebra map; RingHom.FaithfullyFlat is Module.FaithfullyFlat for
  its induced algebra, i.e. scalar extension is exact and detects zero modules.
- Finite kernels: `IsFinite (GrpObj.ker q).hom` and the corresponding p condition.
  For an affine group over F these say its coordinate algebra is finite over F,
  equivalently finite dimensional.
- Diagonalizability: `hqdiag` and `hpdiag` use the landed
  `IsFiniteDiagonalizableGroupScheme`, which is natural group isomorphism on
  every test scheme to characters of a finite abelian group M. By its source
  Proposition 12.3 this is exactly the group scheme Spec F[M] with the stated
  group-algebra Hopf operations. It retains infinitesimal points.
- Centrality: `hqcentral` and `hpcentral` require every kernel point to commute
  with every group point over every F-scheme T. Restriction to affine T gives
  precisely all F-algebras in the node; the converse follows by gluing on
  affine open covers. This is scheme-theoretic centrality.
- Multiplicative simple connectedness: `hH` quantifies over every smooth,
  connected, affine finite-type F-group H1 and every homomorphism r to H with
  exactly the faithful-flat, finite, diagonalizable and central-kernel conditions
  above, and asserts `IsIso r`. An inverse of an isomorphic group homomorphism
  automatically respects multiplication; an isomorphism of underlying
  over-schemes is therefore exactly the group-scheme isomorphism here.
- Unique lifting: `∃! u : H ⟶ E, IsMonHom u ∧ u ≫ p = q` asserts existence of
  a homomorphism with p composed after u equal to q, and uniqueness among all
  homomorphisms satisfying the same equation. It imposes no property on other
  scheme maps.
- No reducedness assumption on the kernels, no separability assumption, and no
  restriction on characteristic is imposed.

Dependency declarations used, read in their source files:

- Mathlib.Algebra.Field.Defs: `Field`.
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed` (the algebraically closed
  clause of def-weil-algebraic-closure; no algebraic-closure extension is needed).
- Mathlib.CategoryTheory.Monoidal.Grp: `CategoryTheory.GrpObj`;
  Mathlib.CategoryTheory.Monoidal.Mon: `CategoryTheory.IsMonHom`.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs: `IsClosedSubgroupScheme`
  and its `isClosedSubgroupScheme_kerι` result. Its imported
  WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp supplies
  `GrpObj.ker` and `GrpObj.kerι`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `LocallyOfFiniteType`;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: `QuasiCompact`.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`.
- Mathlib.Topology.Connected.Basic: `ConnectedSpace`.
- Sheaf.AlgebraicGeometry.FiniteDiagonalizableGroupScheme:
  `AlgebraicGeometry.IsFiniteDiagonalizableGroupScheme`. The item's stmt_deps
  gains its already landed node def-sfb-finite-diagonalizable-group-scheme;
  that definition and its node are not copied or changed.
- Mathlib.AlgebraicGeometry.Morphisms.Finite: `IsFinite`;
  Mathlib.RingTheory.RingHom.FaithfullyFlat: `RingHom.FaithfullyFlat`.

Public imports provide the statement dependencies. Plain imports provide the
recorded proof-dependency modules: pullbacks and affine fibre products, faithful
flat base change and spectrum surjectivity, finite discrete spectrum, prime
radicals, the locally algebraic identity component, reduced-source closed
factorization, and smooth geometric reducedness. The proof dependencies
lem-sfb-algebraic-group-homomorphism-factorization,
lem-sfb-group-neutral-component-translates,
lem-sfb-reduced-target-dominant-group-flatness and
lem-sfb-split-torus-subgroups-diagonalizable have no usable Lean record in the
read repository, so no import can yet be given for these proof-only prerequisites.
They are retained verbatim in the node proof and proof_deps, and their mathematical
uses are all explicit in the theorem docstring.

Edge cases checked before writing: H = 1 gives its unique identity-valued lift;
p = id gives u = q; q = id allows the universal cover itself to be the target;
trivial kernels are permitted (the finite character group can be trivial).
In characteristic p the kernel may be μ_p; only H, G, E and H1 have Smooth
instances. Kernels have no Smooth or IsReduced assumption. The empty scheme
cannot be a group scheme over a field and is also excluded exactly by the node's
connectedness. G_m does not satisfy hH, since nontrivial power isogenies exist.
All schemes and the base field share the arbitrary universe u, as in the landed
finite-diagonalizable definition; test objects are all schemes of that universe,
never an independently smaller universe. Every identifier and universe is bound;
`autoImplicit false` is explicit.

Searches actually run in this attempt:

- msearch.py leanfinder: "A multiplicatively simply connected smooth connected
  affine algebraic group lifts uniquely through any central isogeny with finite
  diagonalizable kernel"; 8 hits, abstract abelianization, covering maps,
  Galois categories and formal unramified lifting, no exact group-scheme result.
- msearch.py loogle: "GrpObj, IsMonHom, HopfAlgebra"; 0 hits, service reports
  unknown identifier GrpObj. This is not evidence that GrpObj is absent locally.
- msearch.py grep in AlgebraicGeometry:
  "multiplicativeIsogeny|MultiplicativeIsogeny|simplyConnected|SimplyConnected";
  no Mathlib match.
- msearch.py leansearch: "A simply connected smooth connected algebraic group
  has a unique homomorphism lifting its universal covering through every
  multiplicative isogeny"; 8 hits, WithOne, topological coverings, formally
  smooth lifting and abelianization, no exact match.
- rg of those names and of multiplicative isogeny / diagonalizable keywords
  in lean/WeilConjectures and lean/Sheaf; also search by this exact node id.
  No existing lifting theorem. Found MultiplicativeIsogenyComposition and
  SemisimpleCentralIsogenyMultiplicative, and followed their shared landed
  FiniteDiagonalizableGroupScheme interface. No existing named simple-connectedness
  or multiplicative-isogeny predicate was found, so their conditions are written
  inline, without introducing a second definition.

No STATEMENT-DISPUTED issue. The inherited BLOCKED message describes the old
stage-1 reviewed-split gate; coord/brief-stage2.md §0 explicitly permits this
stage-2 delivery. coord/queue.tsv lists the item at stage 2 with no lean record.
There is no released repair note. Only the item lean field and addition of the
landed definition dependency change; the reviewed split remains intact.

## Second reading by NX

A separate rereading by the same worker (the dispatcher explicitly prohibits
starting other agents) compared the full node, Milne 18.5--18.8, the finite
character-functor definition and the final signature. Each outer structural
condition occurs for H, G and E; hH repeats those exact conditions for H1.
Both p and q have the full isogeny assumptions, including centrality, even
though some are unnecessary for individual proof steps. The uniqueness predicate
includes IsMonHom u, so uniqueness applies exactly to group-scheme lifts, not to
all over-scheme maps. The direction u ≫ p = q matches p ∘ u = q. All-test-scheme
centrality agrees with all-algebra centrality by affine-local gluing. IsIso r is
a group isomorphism because r is a group homomorphism. The defining finite
character functor includes all infinitesimal points, and no kernel is required
to be smooth. No statement mismatch or source correction was found. The only
interface addition is citation of the already landed finite diagonalizable node.
