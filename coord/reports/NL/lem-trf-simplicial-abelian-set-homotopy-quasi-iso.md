## Worker report

The module `Sheaf.AlgebraicTopology.SimplicialAbelianSetHomotopyQuasiIso` states
`AlgebraicTopology.quasiIso_alternatingFaceMap_of_underlying_homotopy_equivalence`,
with one `sorry` and no new definitions. It states exactly Stacks Tag 08P2 in the
nonpositive cochain indexing prescribed by the node. Read the complete source proof
in `literature/stacks-project/simplicial.tex`, lines 5883–5961. Its free-abelian-group
argument, normalization comparison, surjectivity and injectivity arguments are in
the declaration docstring. No statement correction or mathematical dispute.

Hypotheses and clauses, matched individually:

- Simplicial abelian groups `X,Y : Δᵒᵖ → Ab` are
  `{X Y : SimplicialObject AddCommGrpCat.{u}}`. Their morphism is `(f : X ⟶ Y)`;
  natural transformations in this category are additive in each simplicial degree.
- Their underlying simplicial sets are `X ⋙ forget AddCommGrpCat.{u}` and
  `Y ⋙ forget AddCommGrpCat.{u}`. The underlying map of `f` is
  `Functor.whiskerRight f (forget AddCommGrpCat.{u})`.
- Existence of the simplicial-set inverse is the existential `∃ g` in `h`.
  Its type is the natural-transformation type between these Type-valued functors.
  It has no additive structure requirement.
- The composite `gf` in the node is the categorical composite `Uf ≫ g`;
  the first `Relation.EqvGen` relates it to `𝟙 (X ⋙ forget AddCommGrpCat.{u})`.
- The composite `fg` is `g ≫ Uf`; the second `Relation.EqvGen` relates it to
  `𝟙 (Y ⋙ forget AddCommGrpCat.{u})`. Both use the very same existential inverse.
- An elementary homotopy is `Nonempty (SSet.Homotopy a b)`. Read its definition,
  full type and docstring in `Mathlib/AlgebraicTopology/SimplicialSet/Homotopy.lean`
  (48), and the endpoint equations `h₀`, `h₁`. Its cylinder is `K ⊗ Δ[1]`.
  This is the degreewise cartesian product. Read `Monoidal.lean` (174–206):
  `ι₀` and `ι₁` insert the constant simplices 0 and 1. Read `StdSimplex.lean`
  (39, 68): `stdSimplex` is `uliftYoneda` and `objEquiv` identifies its simplices
  with order-preserving maps `[n] → [1]`. ULift only implements universe sizing.
- The finite zigzag convention is exactly `Relation.EqvGen` of that elementary
  relation, not just existence of one elementary homotopy. Read its constructors
  in `Mathlib/Logic/Relation.lean` (355): elementary relation, reflexivity,
  symmetry and finite transitivity. These allow either direction at each step
  and every finite chain, including a chain of length zero.
- `alternatingFaceMapComplex AddCommGrpCat.{u}` has degree-n object `X_n`.
  Read `AlternatingFaceMapComplex.objD` (69), `obj` (124), `map` (142), and
  `alternatingFaceMapComplex` (160): its differential from n+1 to n is
  `∑ i : Fin (n+2), (-1 : ℤ)^i.val • X.δ i`, and its map in degree n is `f.app`.
- `HomologicalComplex.extendMap` applies exactly the canonical extension along
  `ComplexShape.embeddingDownNat`. Read `Embedding/Basic.lean` (225): this
  embedding sends n to -n. Read `Embedding/Extend.lean` (118, 186): extension
  uses the original objects/differentials/maps in the image and zero outside.
  Thus degree -n is X_n, the differential is the node's alternating sum, and
  all positive degrees are zero. No arbitrary comparison map is introduced.
- The conclusion `QuasiIso` for this extended map is isomorphism on the homology
  objects in every integer degree. Read `QuasiIso` (139) and its docstring in
  `Mathlib/Algebra/Homology/QuasiIso.lean`; for the shape `up ℤ` this is precisely
  cohomology `ker(d^r)/im(d^(r-1))`, including degree zero and positive degrees.

Dependency declarations read and used:

- `def-weil-pbc-simplicial-object`: Mathlib's
  `CategoryTheory.SimplicialObject`, `SimplicialObject.δ`, `SimplicialObject.σ`,
  in `Mathlib.AlgebraicTopology.SimplicialObject.Basic`. Read their complete
  signatures and docstrings (52, 91, 97). Imported through the simplicial modules.
- `def-weil-pbc-simplicial-set`: its `mathlib_match` is usable without a Lean
  record: `SSet` in `Mathlib.AlgebraicTopology.SimplicialSet.Basic` (36), which is
  exactly the Type-valued specialization of `SimplicialObject`. The extra
  degeneracy/subcomplex/finiteness notions of that node are not required here.
- `def-weil-abstract-derived-category`: the recorded module
  `Mathlib.Algebra.Homology.DerivedCategory.Basic` is publicly imported. Read
  `DerivedCategory`, `HasDerivedCategory`, and the localization `Q` (74–98).
  This node also supplies Mathlib's complex/cohomology/quasi-isomorphism notion;
  the theorem uses `QuasiIso` directly and therefore needs no localization-size
  assumption. Read `HomologicalComplex.homology` as `(K.sc i).homology` (90).

Edge cases checked before finalizing:

- Zero simplicial abelian groups give singleton underlying sets; the existential
  inverse and both homotopy relations remain meaningful. No nonzero hypothesis.
- Degree zero is retained: the outgoing differential is zero and the incoming
  alternating sum gives H⁰. The free-cycle lift `[x]-[0]` works in this degree.
- Every positive cochain degree is zero, so its induced homology map is an
  isomorphism automatically. There is no truncation that omits degree zero.
- Constant simplicial groups are included; in degree zero the assertion reduces
  to invertibility of the induced group map, as a homotopy equivalence requires.
- A zigzag of length zero is accepted by `EqvGen.refl`; reversed elementary
  homotopies and arbitrary finite lengths are accepted. No finiteness or
  boundedness condition is put on the simplicial objects themselves.
- The inverse and all intermediate maps live in simplicial sets, so they can be
  nonadditive and need not fix zero. Only f is required to be additive.
- Universe `u` is explicitly declared and appears on `AddCommGrpCat` and its
  forgetful functor. No auto-bound variables, site restrictions or equality of
  independent universes. Arbitrary pairs of sizes fit in their common maximum.

Searches (2026-10-19), using the prescribed `msearch.py NL <item>` wrapper:

- LeanFinder: "A morphism of simplicial abelian groups with a homotopy inverse
  on underlying simplicial sets induces a quasi-isomorphism". Eight hits:
  `homotopyEquivalences_le_quasiIso`, `HomotopyEquiv.quasiIso_hom`, its degreewise
  and inverse variants, and localization lemmas. None supplies an inverse or
  homotopies that are only maps of underlying sets.
- Loogle: `SSet.Homotopy, HomologicalComplex.extend`. Zero hits for the combined
  query. Direct source reads located both existing constructions.
- Mathlib grep: `homotopy.*quasiIso|quasiIso.*homotopy|homotopic.*[Hh]omology`
  under AlgebraicTopology. Three hits in normalized singular chain comparison
  and homotopy invariance of free singular complexes. Those concern the free
  complex of the underlying simplicial set, not its given abelian group law.
- LeanSearch: "simplicial abelian group morphism underlying simplicial set
  homotopy equivalence quasi isomorphism". Eight hits, again general chain
  homotopy equivalence/quasi-isomorphism facts, and the definition of QuasiIso.
- Direct `rg` of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and
  `lean/Sheaf`: `simplicial.*[Hh]omotopy|setHomotopy|SSet.Homotopy|alternatingFaceMapComplex`.
  Existing results concern free complexes, trivial Kan fibrations, and unrelated
  simplicial constructions. No exact statement. Also checked the item id in
  upstream sources and `dag/lean_names_upstream.json`: no occurrence.
- Direct `rg` for `Underlying.*homotopy|underlying.*homotopy|homotopy_equivalence.*quasi|
  quasiIso_alternatingFaceMap_of_underlying` in Mathlib AlgebraicTopology,
  WeilConjectures and lean/Sheaf: no matching theorem (two irrelevant text hits).
  The proposed fully qualified declaration name does not already exist.

Validation: `scompile.py` compiled both the sandbox and library module cleanly,
2.1 s and 2.0 s respectively. The first attempt exposed the required namespace
`Functor.whiskerRight`; that was repaired and compilation repeated successfully.
The original node has status `unsplit`; this metadata is preserved because the
brief permits only the `lean` field to change in this delivery.

## Second reading by NL

I performed a separate second pass with the original node and final module open.
The dispatcher prohibits starting another agent; this is a self-review, and the
maintainer's independent review remains necessary. The explicit existential
inverse, two composite equations up to `EqvGen`, cylinder endpoints, finite
zigzags, nonadditive maps, alternating differential, zero extension and
all-degree conclusion match the corresponding clauses listed above. In
particular, using just `Nonempty (SSet.Homotopy _ _)` would have made the
hypothesis stronger than the node: the final statement correctly uses EqvGen.
`embeddingDownNat` has the required sign of the integer index, unlike a
nonnegative extension. There are no local notations, helper predicates or
postponed data definitions. No mathematical mismatch found and no statement
change made. The namespace repair was the only compiler-driven edit.
