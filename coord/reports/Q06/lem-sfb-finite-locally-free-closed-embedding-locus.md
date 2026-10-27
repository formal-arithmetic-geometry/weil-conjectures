## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteLocallyFreeClosedEmbeddingLocus` states
`AlgebraicGeometry.exists_finiteLocallyFree_closedEmbeddingLocus`, with `sorry` as its
only theorem proof. No definitions are introduced. The item is unchanged except for
its `lean` record. There is no statement dispute or dependency-interface fault.

Hypotheses and conclusion, clause by clause:

- Schemes P, D and X: `{P D X : Scheme.{u}}`, with an explicitly bound universe `u`.
- Structure maps D → P and X → P: `d : D ⟶ P` and `x : X ⟶ P`.
- Finite locally free D → P: `[d.IsFiniteLocallyFree]`. The recorded upstream class
  extends exactly `IsFinite d`, `Flat d`, and `LocallyOfFinitePresentation d`;
  it imposes no fixed rank and no positive rank.
- Affine X → P: `[IsAffineHom x]`.
- Finite presentation X → P: `[LocallyOfFinitePresentation x] [QuasiCompact x]
  `[QuasiSeparated x]`, exactly the three properties in the conventions node.
  The latter two follow from affineness but are written explicitly to render the
  node's stated meaning of finite presentation.
- P-morphism f: `f : D ⟶ X` and `hf : f ≫ x = d`.
- Open subscheme V and its open immersion: `∃ V : P.Opens` and its canonical
  inclusion `V.ι : V.toScheme ⟶ P`. Mathlib supplies the open-immersion instance
  for this canonical inclusion, so a further existential immersion witness or
  redundant propositional conjunct is unnecessary.
- Relative quasi-compactness: `QuasiCompact V.ι`. This does not assert that V
  or P is a quasi-compact scheme.
- Every test T and t: `∀ (T : Scheme.{u}) (t : T ⟶ P)`.
- Factorization through V: `∃ l : T ⟶ V.toScheme, l ≫ V.ι = t`.
- Base-changed f is a closed immersion: `IsClosedImmersion (pullback.map d t x t
  f (𝟙 T) (𝟙 P) ... ...)`. Its projection to X is projection to D followed by f,
  and its projection to T is projection to T. The two proof arguments encode
  exactly hf and the identity square, without an extra mathematical hypothesis.
- Residue-field description: `∀ p : P, p ∈ V ↔ IsClosedImmersion (...)`, with
  the same `pullback.map` at `P.fromSpecResidueField p : Spec (P.residueField p) ⟶ P`.
- Arbitrary base change: for every `P' : Scheme.{u}` and `b : P' ⟶ P`, the
  inverse-image open `b ⁻¹ᵁ V` has `QuasiCompact (b ⁻¹ᵁ V).ι` and satisfies
  the same factorization equivalence for every `T ⟶ P'`. Here the morphism
  inside `IsClosedImmersion` is explicitly the iterated base change of f,
  first along b and then along t, using the two structure maps
  `pullback.snd d b` and `pullback.snd x b`. Thus compatibility is asserted
  for the actual base-changed morphism, including arbitrary nonflat b.
- All schemes and test schemes live in the same arbitrary universe u, as in
  Mathlib's category of schemes. No independent test universe makes a case vacuous.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` (class at current local line 899).
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- The convention-only `def-weil-pbc-scheme-conventions` has no declaration or
  module; use its designated `AlgebraicGeometry.QuasiCompact` and `QuasiSeparated`
  from Mathlib's corresponding morphism modules.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`,
  the canonical open subscheme and inclusion `Scheme.Opens.toScheme`, `Scheme.Opens.ι`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, `pullback.map`;
  `Mathlib.AlgebraicGeometry.Pullbacks` supplies scheme pullbacks.
- `Mathlib.AlgebraicGeometry.ResidueField`: `AlgebraicGeometry.Scheme.residueField`,
  `Scheme.fromSpecResidueField`. Its recorded `Scheme.Hom.residueFieldMap` is the
  induced residue-field map; this assertion only needs the canonical field point.

All recorded, stated proof-dependency modules are imported with plain `import`
when they are not already public statement imports. This includes the finite
pushforward, characteristic polynomial, tensor right exactness, tilde, Fitting
locus, determinant, spectrum topology and finite-type modules. The affine fibre
product lemma is in the public Pullbacks module. The two proof-only nodes
`lem-trf-fitting-sheaf-arbitrary-pullback` and
`lem-trf-fitting-ideal-sheaf-affine-sections` currently have no Lean record,
upstream audit or Mathlib match, so there is no module for them to import.
They are not prerequisites for typing this statement. The full ten-step DAG
proof is reproduced in the theorem docstring, including those future inputs.

Sources checked: Conrad, Reductive Group Schemes, Lemma 2.3.4, printed p.70,
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf (PDF page index 69,
text lines 3406–3425): the source constructs the open monicity locus after a
Noetherian reduction. The node explicitly records its general finite-source,
arbitrary-base version as agent-stated, with the finite-coordinate/minor proof.
I preserve that approved statement and proof rather than adding Noetherianity.
The latest blueprint direct-images proof in
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
was read; this supporting algebraic-geometric lemma does not alter that unit.

Edge cases checked before writing:

- D empty / rank zero: every map out of the empty scheme is a closed immersion;
  V = P, and its identity inclusion is quasi-compact even if P is not.
- P empty: D and X are empty, and V is the empty open; all test schemes over P
  are empty. Both factorization equivalences and the fibre clause hold.
- No algebra generators: the monomial list contains the empty product 1, so the
  proof does not accidentally use an empty spanning list.
- B = A × A and the image of x is (0,a): the closed-embedding locus is D(a).
  Over a nonreduced ring with a nilpotent a this is empty, as required; no
  reducedness or positive-dimensional-fibre assumption is present.
- P a non-quasi-compact disjoint union and D → X already a closed immersion:
  the locus is all P and its inclusion is still quasi-compact. This confirms
  why `QuasiCompact V.ι` is the required conclusion, not compactness of V.
- Nonflat base change, identity base change, and test t equal to a residue-field
  point all occur in the explicitly quantified clauses.

Searches for an existing statement (all on 2026-10-24):

- `msearch.py ... leanfinder "Finite locally free source closed immersion quasi
  compact open locus arbitrary base change"`: eight hits on finite and closed
  immersion properties, including `IsFinite.instOfIsClosedImmersion` and
  `IsImmersion.isImmersion_iff_exists_of_quasiCompact`; no locus theorem.
- `msearch.py ... leansearch "Finite locally free source closed immersion quasi
  compact open locus"`: eight hits on closed immersions and finite presentation,
  no universal quasi-compact locus theorem.
- `msearch.py ... loogle '"IsClosedImmersion", "locus"'`: zero hits.
- `msearch.py ... grep 'immersion.*locus|locus.*immersion|surjectiv.*locus'
  AlgebraicGeometry`: two unrelated quasi-finite-locus hits in ZariskisMainTheorem.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for closed-immersion/locus
  patterns, and `grep -rn` of the exact item id over `lean/WeilConjectures`:
  no exact existing statement. The existing
  `Sheaf.AlgebraicGeometry.UniversalClosedImmersionOpen`,
  `AlgebraicGeometry.exists_universalClosedImmersionOpen`, was read in full:
  it asserts existence of a universal open, under more general assumptions,
  but does not assert quasi-compactness, the fibre clause or this explicit
  base-change clause, so it is not an exact existing match for this node.
- Full-name searches for `closedImmersion.*Locus`, `closedEmbedding.*Locus` and
  `finiteLocallyFree.*Locus` found no conflicting declaration.

Validation: the delivered file compiled through the required `scompile.py` in
both its sandbox module mode and final library module mode (14.3 s and 20.3 s).
There were no errors or unexpected warnings. `autoImplicit false` enforces
explicit binding of all variables; the universe is declared explicitly.

## Second reading by Q06

I reread the node and the complete module after compilation as a separate review
pass. No other agent was started, as required by the dispatcher brief; this is
an additional worker self-check, with the maintainer's independent review still
required. I checked d finite locally free against the upstream class definition,
x affine and all three finite-presentation properties, and hf's direction.
The factorization side is existential with the correct composite into P. The
pullback.map has source D ×_P T and target X ×_P T. At a residue-field point
it uses the ordinary residue field rather than an algebraic closure. The final
clause uses the inverse-image open and the iterated pullback morphism over P',
with all tests quantified. `QuasiCompact` is applied to the inclusions rather
than asserting absolute compactness. No missing clause, changed hypothesis,
new notion, hollow definition, or statement correction was found. No changes
were needed in this pass.
