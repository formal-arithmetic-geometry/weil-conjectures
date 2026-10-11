## Worker report

Module: `Sheaf.AlgebraicGeometry.EtaleLocalFiniteAtPoint`.
Declaration: `AlgebraicGeometry.exists_etale_finite_open_of_isolated_fiber_point`.
This is a statement only, with a single `sorry` proof and no new definitions.
The node is unchanged outside its `lean` record. No dependency modules or new nodes are needed.

Source checked: https://stacks.math.columbia.edu/tag/02LK, Lemma 37.41.1.
The repository's referenced local Stacks TeX is absent on this machine; the official page was
opened instead. Its hypotheses and clauses (a), (b), (i)-(iii) match the node. Its final
persistence assertion is intentionally assigned to the separate persistence node.

Clause-by-clause rendering:

- A morphism of schemes: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Locally of finite type: `[LocallyOfFiniteType f]`.
- The point: `(x : X)`; `s` is everywhere the expression `f x`.
- Isolated in the scheme-theoretic fibre: `hx : IsOpen ({f.asFiber x} : Set (f.fiber (f x)))`.
  Mathlib's `asFiber` is the inverse of `fiberHomeo` at `⟨x, rfl⟩`, so this is precisely
  openness of the singleton corresponding to x, rather than openness in X itself.
- A scheme U, a morphism φ, and a point u: `∃ (U : Scheme.{u}) (φ : U ⟶ S) (u : U)`.
- Étaleness: `Etale φ`.
- The point lies over s: `φ u = f x`.
- The induced map κ(s) → κ(u) is an isomorphism: `IsIso (φ.residueFieldMap u)`.
  The source is κ(φ(u)), identified with κ(s) by the preceding equality. `IsIso` is in
  CommRingCat, so it asserts the actual induced field map is invertible.
- An open subscheme V of X ×_S U: `∃ (V : (pullback f φ).Opens)`; `V.ι` is its inclusion.
- Clause (i): `IsFinite (V.ι ≫ pullback.snd f φ)`.
- Clause (ii): `∃ (v : V), (V.ι ≫ pullback.snd f φ) v = u` together with
  `∀ (w : V), (V.ι ≫ pullback.snd f φ) w = u → w = v`.
  Uniqueness quantifies only the fibre condition, independently of clause (iii).
- Clause (iii), image: `(V.ι ≫ pullback.fst f φ) v = x`.
- Clause (iii), induced residue-field isomorphism:
  `IsIso ((V.ι ≫ pullback.fst f φ).residueFieldMap v)`.
  This uses the residue field in the open subscheme V, through the actual composite to X.

Dependencies read and used:

- def-pc-scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  Mathlib.AlgebraicGeometry.Scheme (imported transitively).
- def-weil-finite-type-morphism: `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType (transitive). Its other notion,
  QuasiCompact, is not a hypothesis of this node.
- def-pc-scheme-fibre: `Scheme.Hom.fiber`, `fiberHomeo`, `asFiber`,
  Mathlib.AlgebraicGeometry.Fiber (direct import).
- def-weil-etale-morphism: `AlgebraicGeometry.Etale`,
  Mathlib.AlgebraicGeometry.Morphisms.Etale (direct import).
- def-weil-residue-field: `Scheme.residueField`, `Scheme.Hom.residueFieldMap`,
  Mathlib.AlgebraicGeometry.ResidueField (transitive).
- def-pc-fibre-product: `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback (transitive via Fiber).
- def-weil-finite-integral-morphism: `AlgebraicGeometry.IsFinite`,
  Mathlib.AlgebraicGeometry.Morphisms.Finite (transitive via Fiber).
- Open subschemes use `Scheme.Opens.toScheme` and `Scheme.Opens.ι`,
  Mathlib.AlgebraicGeometry.Restrict, rather than a private definition.

Edge cases checked before writing:

- Empty X admits no x; empty S admits no morphism with such a point. No extra nonemptiness
  assumption appears. The existential u and v correctly prevent an empty chosen U or V.
- A nonreduced fibre with one isolated point is allowed; openness does not require reduction
  or an étale original morphism. Finiteness of the piece does not require it to be étale.
- Other fibre points and nonseparated X or f are allowed; no global uniqueness,
  quasi-compactness, separatedness, or complementary open piece is imposed.
- All characteristics and residue-field extensions κ(x)/κ(s) are allowed. Only the specified
  induced maps after the elementary neighbourhood must be isomorphisms.
- `universe u` is explicit; X, S, U and their pullbacks have an arbitrary common scheme
  universe, as do the dependency declarations. There are no auto-bound variables.

Searches:

- msearch.py leanfinder: "An isolated point of a scheme fibre becomes a finite open piece
  after elementary etale base change with identical residue fields". Eight hits, including
  finite-fibre and polynomial factorization results; none gives the scheme statement.
- msearch.py loogle: `AlgebraicGeometry.exists_etale_isCompl_of_quasiFiniteAt`. One hit in
  Mathlib.AlgebraicGeometry.ZariskisMainTheorem. The full signature and surrounding comment
  were read: it assumes IsSeparated and supplies neither a residue-trivial distinguished
  base point, uniqueness in that fibre, nor the residue-field conclusion. It is not a match.
- msearch.py grep: `02LK|exists_etale_isCompl_of_quasiFiniteAt|elementary.*[Ee]tale`,
  AlgebraicGeometry. Two hits, both involving the preceding weaker Zariski-main theorem.
- rg in WeilConjectures: `elementary.*[Ee]tale|exists_etale_isCompl|finite_at_point`.
  One unrelated universal-homeomorphism base-change comment, no matching declaration.
- rg of this item's blueprint id in WeilConjectures: no hits.
- rg in lean/Sheaf/AlgebraicGeometry:
  `elementary.*[Ee]tale|exists_etale_isCompl|finite_at_point|asFiber|residueFieldMap`.
  Only unrelated residue-field, tangent-space, and fibre-dimension declarations.

The declaration docstring carries all eight proof steps and their lemma node ids.
No statement correction or STATEMENT-DISPUTED issue was found.

## Second reading by F1

I read the repository node, the delivered node and module, all seven statement-dependency
nodes, and the actual Mathlib declarations below. The delivered node differs from the base
only in `lean`; there is no statement correction, new definition node, or dependency module.

Source: Stacks 02LK, More on Morphisms, Lemma 37.41.1. The local Stacks TeX is absent.
I read the official tag page https://stacks.math.columbia.edu/tag/02LK and fetched the
source https://raw.githubusercontent.com/stacks/stacks-project/master/more-morphisms.tex
read-only. I read `lemma-etale-makes-quasi-finite-finite-at-point`, its proof, and the
preceding section setup and `equation-basic-diagram`. There is no standing separatedness,
Noetherian, quasi-compactness, or field hypothesis. The source writes the factors of X_U
in the opposite order; pullback symmetry identifies this with `pullback f φ` and preserves
the named projections. The source's final persistence assertion belongs to the separate
node explicitly named by this item's source record, not to this item's conclusion.

Object, hypothesis and conclusion checklist (each verdict PASS):

1. Schemes X and S, and a morphism f: `{X S : Scheme.{u}} (f : X ⟶ S)`.
   `Scheme` and `Scheme.Hom` in Mathlib.AlgebraicGeometry.Scheme are locally affine
   locally ringed spaces and their morphisms, exactly def-pc-scheme. No extra structures.
2. f locally of finite type: `[LocallyOfFiniteType f]`. I read the class and its
   `HasRingHomProperty` instance in Morphisms.FiniteType: finite type on affine pairs.
   This is the dependency's locally finite type notion; no QuasiCompact instance is added.
3. A point x and s = f(x): `(x : X)` and the expression `f x` throughout. Substituting
   the defined s removes no quantifier or hypothesis.
4. Scheme-theoretic fibre X_s and isolated x: `(hx : IsOpen ({f.asFiber x} :
   Set (f.fiber (f x))))`. I read `Scheme.Hom.fiber`, `fiberι`, `fiberHomeo`, and
   `asFiber` in Mathlib.AlgebraicGeometry.Fiber: the fibre is the pullback along
   `S.fromSpecResidueField`, and `asFiber` is the inverse homeomorphism at `⟨x, rfl⟩`.
   Thus the singleton is open in the fibre, not in X. The homeomorphism needs no
   finite type, separatedness, or compactness instance.
5. A scheme U, morphism φ: U → S, and point u: `∃ (U : Scheme.{u}) (φ : U ⟶ S)
   (u : U)`. These are existentially chosen after the input x and hx.
6. Elementary étale neighbourhood: `Etale φ ∧ φ u = f x ∧
   IsIso (φ.residueFieldMap u)`. I read `Etale` in Morphisms.Etale and its affine
   ring-map definition. I read `Scheme.residueField` and `Hom.residueFieldMap` in
   ResidueField: κ(φ(u)) → κ(u) is induced by the local stalk map. The equality of
   points identifies κ(φ(u)) with κ(s), so IsIso asserts invertibility of the actual
   induced field map, not an unrelated abstract field isomorphism.
7. Fibre product X_U and projections p and q: `pullback f φ`, `pullback.fst f φ`,
   `pullback.snd f φ`. I read the signatures and docstrings in
   CategoryTheory.Limits.Shapes.Pullback.HasPullback. Scheme pullbacks are available
   without any extra binder; the dependency is the usual universal fibre product.
8. Open subscheme V of X_U: `∃ (V : (pullback f φ).Opens)`. I read `Scheme.Opens`,
   `Scheme.Opens.toScheme`, `ι`, and `ι_apply` in Scheme and Restrict: this is the
   restriction scheme of an arbitrary open, with inclusion `V.ι`.
9. Clause (i), V → U finite: `IsFinite (V.ι ≫ pullback.snd f φ)`. I read IsFinite
   in Morphisms.Finite: affine preimages of affine opens and finite induced ring maps,
   exactly def-weil-finite-integral-morphism. No integral/étale replacement is used.
10. Clause (ii), exactly one point over u: `∃ (v : V),
    (V.ι ≫ pullback.snd f φ) v = u ∧
    (∀ (w : V), (V.ι ≫ pullback.snd f φ) w = u → w = v)`.
    Existence and uniqueness are both present. Uniqueness ranges over every point
    over u, without imposing the subsequent image or residue-field conditions on w.
11. Clause (iii), this same v maps to x: `(V.ι ≫ pullback.fst f φ) v = x`.
    The witness v is shared with clause (ii); the composite is the correct projection.
12. Clause (iii), the induced κ(x) → κ(v) is an isomorphism:
    `IsIso ((V.ι ≫ pullback.fst f φ).residueFieldMap v)`. The preceding equality
    identifies its domain with κ(x). Its codomain is the residue field in the open
    subscheme V, as required. All clauses occur under the same U, φ, u, V, v witnesses.

Edge cases: an empty X (including Spec of the zero ring) has no input x; an empty S has
no image of such a point. There is no added Nonempty hypothesis. U and V cannot be empty
because their required points are witnesses. Nonreduced fibres, arbitrary characteristics,
and arbitrary extensions κ(x)/κ(s) are admitted. X and f may be nonseparated or non-quasi-
compact, and other points in X_s are allowed: the hypothesis isolates x rather than making
it the entire fibre. There is no index set, degree n, or rank parameter, so empty indexing
and n = 0 introduce no omitted case. The explicit arbitrary universe u is the universe of
the dependency's category Scheme; there is no finite universe specialization or unbound
variable. U and the pullback stay in this category, which permits the affine construction
from the proof.

Independent searches (new queries, using msearch.py and direct rg):

- LeanFinder: "A locally finite type scheme morphism near an isolated fiber point admits
  an etale neighborhood with finite open subscheme and unique point of equal residue
  field". Eight hits: étale definitions and algebra étale-locus lemmas; no exact statement.
- Loogle: `AlgebraicGeometry.Scheme.Hom.asFiber`. Six hits, including
  `quasiFiniteAt_iff_isOpen_singleton_asFiber`, confirming the isolation hypothesis.
  Neither the fibre definitions nor the quasi-finite-at equivalence states the conclusion.
- msearch grep: `quasiFiniteAt|isolated|residueFieldMap`, AlgebraicGeometry. Twenty-five
  displayed hits in étale sites, residue fields, pullback carriers, and Zariski's main
  theorem; no exact existing declaration.
- Direct rg in Mathlib/AlgebraicGeometry, WeilConjectures, lean/Sheaf, and
  dag/lean_names_upstream.json for `exists_etale_finite_open_of_isolated_fiber_point`,
  `02LK`, `etale.*finite.*point`, `isolated.*fibre`, `isolated.*fiber`: one source
  comment about an isolated fibre point in Morphisms/Etale, no duplicate declaration.
- Direct rg for `quasiFiniteAt` and broader finite-open and étale-neighbourhood phrases
  in the source and project. I opened the candidate
  `exists_etale_isCompl_of_quasiFiniteAt` in Mathlib.AlgebraicGeometry.ZariskisMainTheorem:
  it adds `[IsSeparated f]`, supplies a complementary open piece, and does not state
  elementary residue-field triviality or uniqueness over u. It is not the same statement.
  I also opened the source's `Scheme.Hom.quasiFiniteAt_of_preimage_singleton` and
  `Hom.isIso_residueFieldMap`: the former only proves quasi-finiteness from global fibre
  uniqueness; the latter assumes SurjectiveOnStalks for an already given morphism.
  Neither gives this existence theorem.

H5/H6/H8/H9: the module has one named theorem with exactly `by sorry`, and no definitions
or auxiliary proofs. Both docstrings have the source and blueprint id. I matched all eight
node proof steps to the docstring: affine charts, isolation transfer, 00UJ, elementary
neighbourhood, open pullback piece, finiteness, unique point and image, induced residue
field identification. Both imports are used (Fiber and Etale); the declaration is in
AlgebraicGeometry with no Sheaf namespace prefix. Maximum Lean line length is 92.
The node's `lean.statement` equals the file's signature verbatim, checked by extraction.

Mismatches found: none. Changes: appended this second reading only; the Lean and node
record are retained. No new definitions or dependency repairs are needed.
Validation: scompile.py compiled the delivery's sole module against the server library
in 1.8 seconds, exit code 0, with no errors or warnings.
