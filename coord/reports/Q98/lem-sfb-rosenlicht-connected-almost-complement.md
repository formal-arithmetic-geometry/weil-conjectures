## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.RosenlichtConnectedAlmostComplement`
states `AlgebraicGeometry.rosenlicht_connected_almostComplement`, with its sole
proof `sorry`. No definitions, helpers, dependency repairs, new nodes, or statement
corrections are needed. The original natural-language statement and dependency
lists are unchanged. The module docstring and theorem docstring name Milne,
Algebraic Groups (2017), Theorem 8.24, printed p.153; the theorem docstring gives
all ten DAG proof steps, including the connected refinement and dimension formula.
I read the theorem in the supplied PDF: its product map is faithfully flat with
finite kernel, and the smooth refinement applies over a perfect field. The DAG
expands taking the reduced identity component over the algebraically closed base.

Clause-by-clause rendering:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
  `universe u` is explicit and `autoImplicit` is disabled.
- The two k-group schemes are `G A : Over (Spec (.of k))` with `[GrpObj G]`
  and `[GrpObj A]`. These use exactly the recorded group-object encoding.
- Smoothness, connectedness (including nonemptiness), separatedness, and finite
  type of G are `[Smooth G.hom]`, `[ConnectedSpace G.left]`,
  `[IsSeparated G.hom]`, and `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`.
- A is an abelian variety via `[IsAbelianVariety A]`, which supplies its properness,
  smoothness and connectedness. Its group structure remains the explicitly
  supplied `GrpObj A`, as required by the existing definition's docstring.
- The central closed subgroup inclusion is `(i : A ⟶ G)` with
  `[IsClosedSubgroupScheme i]`. This class includes the homomorphism and pointwise
  injectivity requirements, as well as a closed immersion on schemes.
- Centrality is `hcentral`: for every commutative k-algebra R, every R-point a of A
  and every R-point g of G, `Commute (a ≫ i) g`. The test object is explicitly
  `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R)))`. This tests algebras,
  including nonreduced ones, rather than merely k-valued or geometric points.
  Test algebras use the same universe u as the base and schemes, following the
  recorded `IsSubgroupScheme` and `IsNormalSubgroupScheme` interfaces.
- The conclusion existentially supplies `N`, its actual `GrpObj N`, an inclusion
  j and a product map m. Its five structure conditions are `Smooth N.hom`,
  `ConnectedSpace N.left`, `IsSeparated N.hom`, `LocallyOfFiniteType N.hom`,
  and `QuasiCompact N.hom`.
- Closedness and normality are `IsClosedSubgroupScheme j ∧ IsNormalSubgroupScheme j`.
  Normality is the existing scheme-theoretic, all-algebra-points predicate.
- `A ⊗ N` is the cartesian tensor in the over-category: its underlying scheme is
  definitionally `pullback A.hom N.hom`, with the standard componentwise group law.
  `m = (fst A N ≫ i) * (snd A N ≫ j)` fixes m to the canonical multiplication map.
  Multiplication in Hom into a group object is pointwise multiplication. Thus m
  has exactly the prescribed value `(a,n) ↦ i(a)j(n)`; existential m is not an
  unconstrained map. `IsMonHom m` expresses that this map is a homomorphism.
- Faithful flatness is `Flat m.left ∧ Surjective m.left`.
- Finite presentation is all three clauses `LocallyOfFinitePresentation m.left`,
  `QuasiCompact m.left`, and `QuasiSeparated m.left`.
- The scheme-theoretic finite kernel is `IsFinite (GrpObj.ker m).hom`.
  `GrpObj.ker` is the pullback against the target identity section, not the kernel
  of a map of k-points.
- The final dimension equality is
  `topologicalKrullDim G.left = topologicalKrullDim A.left + topologicalKrullDim N.left`.
  This retains the recorded topological Krull dimension in `WithBot ℕ∞`.
- The statement imposes no affine or commutative structure on G or N. The word
  affine in the node explains terminology; it is not an assumption or conclusion.

Dependency declarations used (I read their signatures and docstrings):

- `Field`: Mathlib.Algebra.Field.Defs; `IsAlgClosed`:
  Mathlib.FieldTheory.IsAlgClosed.Basic (the algebraic-closure node records this
  exact component notion in its mathlib_match).
- `CategoryTheory.GrpObj`: Mathlib.CategoryTheory.Monoidal.Grp;
  `CategoryTheory.IsMonHom` and its inherited homomorphism interface;
  `CategoryTheory.GrpObj.ker`: WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp.
- `AlgebraicGeometry.IsSubgroupScheme`, `IsClosedSubgroupScheme`, and
  `IsNormalSubgroupScheme`: WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `AlgebraicGeometry.IsAbelianVariety`:
  WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs.
- `AlgebraicGeometry.Smooth`: Mathlib.AlgebraicGeometry.Morphisms.Smooth;
  `ConnectedSpace`: Mathlib.Topology.Connected.Basic;
  `AlgebraicGeometry.LocallyOfFiniteType`: Mathlib.AlgebraicGeometry.Morphisms.FiniteType;
  `AlgebraicGeometry.QuasiCompact`: Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact;
  `AlgebraicGeometry.IsSeparated`: Mathlib.AlgebraicGeometry.Morphisms.Separated,
  the separatedness component recorded by def-weil-proper-morphism.
- `AlgebraicGeometry.Scheme`: Mathlib.AlgebraicGeometry.Scheme;
  `CategoryTheory.Limits.pullback`: Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback;
  `CategoryTheory.Over.tensorObj_left`, `fst_left`, `snd_left`:
  Mathlib.CategoryTheory.Monoidal.Cartesian.Over, identifying tensor with that pullback.
- `AlgebraicGeometry.IsFinite`: Mathlib.AlgebraicGeometry.Morphisms.Finite;
  `AlgebraicGeometry.Flat`: Mathlib.AlgebraicGeometry.Morphisms.Flat;
  `AlgebraicGeometry.LocallyOfFinitePresentation`:
  Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation;
  `AlgebraicGeometry.QuasiSeparated`: Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated.
- `topologicalKrullDim`: Mathlib.Topology.KrullDimension.

The module also imports recorded proof-dependency modules, with ordinary imports,
including the identity component, homomorphism factorization, translations,
product dimension, reduced-source factorization, finite-surjective dimension,
finite-kernel multiplication/isogeny, fpqc descent, and Mathlib leaf modules.
The three proof-only nodes with no recorded declaration or mathlib_match are
lem-sfb-abelian-subgroup-equivariant-multiple-map,
lem-sfb-abelian-product-axis-rigidity, and
lem-sfb-homogeneous-quotient-krull-dimension. They are named in the proof docstring;
no nonexistent module is imported. Their absence does not affect the statement.

Edge cases checked before writing:

- The identity gives nonempty groups; ConnectedSpace excludes the empty scheme.
- A trivial central abelian variety allows N=G; A=G allows the trivial N.
  Both dimension-zero cases are included by the signature.
- Positive characteristic is unrestricted, and a finite kernel is allowed to be
  nonreduced. In particular no étale or smooth-kernel assumption has slipped in.
- A non-affine N is allowed. A noncommutative G or N is allowed; centrality of A
  is the precise commutation input making the product map a homomorphism.
- All three finite-presentation clauses and both finite-type clauses are retained.
- The all-algebra-points centrality includes nilpotent test rings and matches
  exactly the quantifier range of the recorded normal-subgroup interface.

Searches made for an existing statement:

- msearch.py, leanfinder: “A central abelian subvariety of a smooth connected
  algebraic group has a smooth connected closed normal almost complement with
  finite kernel product map”. Eight hits, concerning abstract group complements,
  commutators and path components; none is a group-scheme decomposition theorem.
- msearch.py, loogle: “GrpObj, IsNormalSubgroupScheme, IsAbelianVariety”. No hits;
  remote Loogle reported unknown identifier GrpObj. I therefore also read the
  local declarations directly and performed the semantic and grep searches.
- msearch.py, grep: “Rosenlicht|almost.?complement|rosenlicht” in AlgebraicGeometry.
  Zero Mathlib hits.
- msearch.py, leansearch: “A connected smooth algebraic group admits a normal
  almost complement to a central abelian subvariety”. Eight hits for abstract
  group centers, normality and complements; no matching theorem.
- rg over WeilConjectures and Sheaf for “Rosenlicht|almost.?[Cc]omplement|rosenlicht|IsCentral”:
  only unrelated central algebras and references to Rosenlicht's product-unit
  theorem, with no almost-complement theorem or central-subgroup predicate.
- grep over WeilConjectures for the exact node id: no hits.
- rg over Mathlib, WeilConjectures and Sheaf for the proposed declaration name:
  no hits. The Hom product, tensor product, subgroup predicates and kernel are
  existing notions and are reused without new definitions.

No STATEMENT-DISPUTED issue or source correction was found.

Validation: scompile.py compiled the delivered file cleanly on the server in both
sandbox and library module contexts (4.1 s and 1.9 s); no errors or unexpected
warnings. deliver2.py --no-push reported OK: the packet passes the maintainer
preflight and compiles. The recorded signature was checked verbatim against
the source, and every source line is at most 100 characters.

## Second reading by Q98

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
