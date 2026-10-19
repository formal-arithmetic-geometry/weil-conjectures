## Worker report

The module `Sheaf.AlgebraicGeometry.AffineRootsRepresentability` states
`AlgebraicGeometry.affineRoots_representability`, with its sole theorem proof `sorry`.
The two helper definitions contain real data: `affineRootsOver R n` is the spectrum
of `AdjoinRoot ((Polynomial.X : R[X]) ^ n - 1)`, with its quotient-algebra structure
map to `Spec R`; `affineRootsCoordinate R n` is the image of `AdjoinRoot.root` under
`Scheme.ΓSpecIso.inv`. Mathlib defines `AdjoinRoot f` to be exactly
`R[X] ⧸ Ideal.span {f}`. These helpers name the specific scheme and section introduced
in this node; no independent notion or replacement for a dependency is introduced.

Source read: `literature/stacks-project/groupoids.tex`, Example
`example-roots-of-unity` (Tag 040M), including the paragraph about base change to
arbitrary schemes; `literature/stacks-project/etale-cohomology.tex`, Section
`section-kummer` (Tag 03PK). The source's representation is by pullback of the
coordinate. No invertibility of n, field, reducedness, affineness of a test scheme,
or etaleness of the root scheme is assumed.

Hypothesis and clause correspondence:

- A commutative ring R: `(R : Type u) [CommRing R]`. Positive n:
  `(n : ℕ) (hn : 1 ≤ n)`. The base V is `Spec (CommRingCat.of R)`.
- P is the spectrum of the stated quotient with its structure map:
  `affineRootsOver R n`; its underlying scheme is `.left` and its structure map
  is `.hom`. The class of t in global sections is `affineRootsCoordinate R n`.
- The coordinate is a unit: the existential `x : Γ(P, ⊤)ˣ` and its first value
  equality identify the value of that unit with the explicit coordinate. Its
  inverse has value `affineRootsCoordinate R n ^ (n - 1)` by the second equality.
- Every V-scheme, including nonaffine schemes: `U : Over (Spec (CommRingCat.of R))`.
  Morphisms over V are `U ⟶ affineRootsOver R n` in the actual over category.
- Bijection to the units satisfying the equation: the existential family
  `E : ∀ U, (U ⟶ affineRootsOver R n) ≃ {z : Γ(U.left, ⊤)ˣ // z ^ n = 1}`.
  The immediately following equality specifies its value as
  `a.left.appTop (affineRootsCoordinate R n)`; the equivalences cannot be arbitrary
  bijections because this equality uniquely determines them.
- Naturality in all V-morphisms: for every `f : U ⟶ W` and `a : W ⟶ P`,
  `(E U (f ≫ a)).val = Units.map f.left.appTop.hom.toMonoidHom (E W a).val`.
- The small etale representable sheaf is identified with the underlying roots
  sheaf: `e` is a natural presheaf isomorphism from the restriction of `yoneda.obj P`
  along `(Scheme.Etale.forget V).op` to
  `(V.rootsOfUnitySheaf n).obj ⋙ forget AddCommGrpCat`. The former is a sheaf by
  the recorded `smallEtaleRepresentablePresheaf_isSheaf`, while the latter is the
  underlying presheaf of the recorded roots sheaf, so this is exactly an
  identification of their sheaves. The isomorphism is pinned to E: the kernel
  inclusion into `gmSheaf`, followed by `.down` and `Additive.toMul`, gives exactly
  `(E ((Scheme.Etale.forget V).obj W) a).val`.
- Coefficient universes in this identification: `rootsOfUnitySheaf` takes values
  in `AddCommGrpCat.{u+1}`. Morphisms of schemes lie in `Type u`, so the left
  presheaf is composed with `uliftFunctor.{u+1,u}`, and the formula evaluates it
  on `⟨a⟩`. This is the standard canonical universe transport of a set, with no
  size or mathematical restriction on the statement.
- Arbitrary change of base: `(V' : Scheme.{u}) (v : V' ⟶ Spec (CommRingCat.of R))`,
  with no property of v imposed. `Over.pullback v` is the recorded categorical
  fibre product construction. Mathlib orders its factors as `P ×_V V'`; this is
  the fibre product written `V' ×_V P` in the node, with the factors exchanged
  canonically. Its projection p to P is `pullback.fst P.hom v`.
- For every V'-scheme U the equivalence `E' U` has the same root-unit subtype;
  its prescribed value is
  `a.left.appTop ((pullback.fst P.hom v).appTop (affineRootsCoordinate R n))`,
  exactly pullback of p-pullback of x. Its next conjunct is naturality for every
  V'-morphism, in the same unit-map form as for E.
- Base-changing any original morphism a: the last equality compares
  `E' ((Over.pullback v).obj U) ((Over.pullback v).map a)` with the image of
  `E U a` under the unit map induced by `pullback.fst U.hom v`.
  This is pullback of the root along `U ×_V V' ⟶ U`, the node's
  `V' ×_V U ⟶ U` with the same harmless convention on factor ordering.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, `Spec.map`, and `Scheme.ΓSpecIso` (the last maps
  global sections to the ring, so its inverse sends the residue class to x).
- `Mathlib.Algebra.Polynomial.Basic`: `Polynomial`, `Polynomial.X`.
- `Mathlib.Algebra.Algebra.Hom`: `AlgHom`; and
  `Mathlib.RingTheory.Ideal.Quotient.Operations`: quotient algebra and
  `Ideal.Quotient.mkₐ`. The exact quotient is supplied by the existing
  `Mathlib.RingTheory.AdjoinRoot` definition, not a new copy of a quotient notion.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Scheme.Etale` and its forget functor.
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`: `Scheme.rootsOfUnitySheaf`,
  with the recorded definition `kernel (n • 𝟙 X.gmSheaf)`; its source and the
  definition of `gmSheaf` in `WeilConjectures.AlgebraicGeometry.Sites.Gm` were read.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback` and
  `pullback.fst`; `Mathlib.CategoryTheory.Comma.Over.Pullback`: `Over.pullback`,
  whose object and map definitions specify the exact canonical base change.
- `WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf`:
  `AlgebraicGeometry.smallEtaleRepresentablePresheaf_isSheaf`. The recorded module
  was absent in the older local checkout, so its full current source was read
  using `scompile.py --source`; it was available to compilation and needed no repair.

Edge cases checked before stating: R may be the zero ring (V and P empty), U may
be empty, V' may be empty, and n=1 gives P canonically V and a singleton root
set. In positive characteristic dividing n the scheme may be nonreduced, but
representability and arbitrary base change still hold; no etaleness is asserted.
n=0 is excluded exactly as in the node (the coordinate inverse formula would
otherwise be inappropriate). Scheme and ring universes agree at arbitrary u;
there is no independent smaller test universe or affine-test restriction.
Naturality includes identity maps and arbitrary compositions, and v may be
identity or an arbitrary nonflat morphism. All constructions use actual maps.

Searches for an existing exact statement (2026-10-17):

- `msearch.py leanfinder`, query "Spec R[X]/(X^n-1) represents roots of unity
  functor on schemes naturally under base change": 8 hits, on affine space
  and cyclotomic characters; none is this roots-scheme representation.
- `msearch.py loogle`, query `"rootsOfUnity"`: 12 hits on the algebraic subgroup
  and elementary properties; none states representability on schemes.
- `msearch.py leansearch`, query "the scheme Spec R[X]/(X^n-1) represents roots
  of unity naturally under base change": 8 hits on cyclotomic polynomial roots,
  roots in rings, and the affine-space Spec map; none is the statement.
- `msearch.py grep`, query `rootsOfUnity|roots.of.unity|muSheaf` in
  `Mathlib/AlgebraicGeometry`: no hits; direct rg of that directory agrees.
- Direct rg of `WeilConjectures` and `lean/Sheaf` for roots-of-unity names and
  representability finds the recorded Kummer sheaf and downstream uses, but
  no declaration with this representation. Targeted rg for
  `affineRoots|rootsOfUnity.*represent|represent.*rootsOfUnity|Spec.*AdjoinRoot`
  finds only unrelated root covers in the side library and no exact theorem.
- Search for the item id in upstream `WeilConjectures` finds no declaration;
  `dag/lean_names_upstream.json` has no affine-roots representation declaration.

No statement correction, disputed statement, new node, or dependency repair is
needed. There are no proof-dependency modules (the node's proof_deps is empty).
The module compiled cleanly with `scompile.py`, including its module path check;
there are no non-sorry warnings. The delivery dry run and push follow this report.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
