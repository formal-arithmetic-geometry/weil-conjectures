## Worker report

Recorded an exact existing upstream package in
`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic`; no module is written.
The main declaration is `CategoryTheory.Functor.Monoidal.commIhom` (lines 190–191).
The additional declarations in `lean.declarations` expose every clause of the node.
Only the item's `lean` field changes. No statement correction, dependency repair,
new notion, or disputed statement is needed.

Hypotheses and clauses, matched against the node and the full source:

- The categories C and D have `Category`, `MonoidalCategory` and `MonoidalClosed`
  instances. The source's `C D : Type*` and `Category*` bind independent object and
  morphism universes. `MonoidalClosed.closed M` supplies a `Closed M`, whose data
  are the specified right adjoint `Closed.rightAdj` and adjunction `Closed.adj`.
  Thus the two original closed structures are retained, rather than replacing one
  by a transported closed structure. `ihom M` is that right adjoint and
  `(ihom.ev M).app N` is the counit evaluation M tensor [M,N] -> N.
- The source variable `G : C ⥤ D` is F. Its `[G.Monoidal]` is exactly a strong
  monoidal structure. The dependency records `Functor.CoreMonoidal`; that explicit
  isomorphism structure converts via `CoreMonoidal.toMonoidal`, preserving the
  forward unit and tensorator (`toLaxMonoidal` uses `h.μIso X Y |>.hom`). Conversely
  `Functor.Monoidal.εIso` and `.μIso` supply the specified isomorphisms. This is
  the same notion, with no extra hypothesis. `[G.IsEquivalence]` asserts that the
  underlying functor is an equivalence.
- The map c is `(Functor.LaxMonoidal.ihomComparison G M).natTrans.app N`.
  `ihomComparison` is defined by `mateEquiv` for the TWO specified adjunctions,
  applied to the tensorator square `μTwoSquare`. More explicitly, the already
  proved `ihomComparison_app_eq_curry G M N` says it is
  `MonoidalClosed.curry (Functor.LaxMonoidal.μ G M _ ≫ G.map ((ihom.ev M).app N))`.
  This is exactly the transpose in the question, with the same tensorator direction.
- Invertibility is `commIhom G M`, defined as
  `asIso (Functor.LaxMonoidal.ihomComparison G M).natTrans`. The immediately
  preceding instance proves that this exact natural transformation is invertible
  for a monoidal equivalence. `ihomObjIso G M N` is `(commIhom G M).app N`.
  Its forward arrow is the specified c, not an arbitrary isomorphism.
- Covariant naturality in N is the naturality of `(commIhom G M).hom`, equivalently
  of `(ihomComparison G M).natTrans`. At v : N -> N' it reads
  `G.map ((ihom M).map v) ≫ c(M,N') = c(M,N) ≫ (ihom (G.obj M)).map (G.map v)`.
- Contravariant naturality in M is the full existing theorem
  `Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app G u N` (lines 302–307):
  `G.map ((MonoidalClosed.pre u).app N) ≫ c(M',N) =
   c(M,N) ≫ (MonoidalClosed.pre (G.map u)).app (G.obj N)` for u : M' -> M.
  Mathlib's `MonoidalClosed.pre` is the conjugate of tensoring with u; its
  evaluation characterization `id_tensor_pre_app_comp_ev` identifies it with
  precisely the transpose-defined precomposition map used in node proof Step 6.
- The displayed evaluation equation is exactly
  `Functor.LaxMonoidal.ihomComparison_ev G M N` (lines 121–124):
  `G.obj M ◁ c(M,N) ≫ (ihom.ev (G.obj M)).app (G.obj N) =
   Functor.LaxMonoidal.μ G M _ ≫ G.map ((ihom.ev M).app N)`.
  Lean composition is left-to-right, explaining the reversal from the displayed
  mathematical composition order. Whiskering is identity tensor c.
- No declaration above assumes `ExactPairing`, dualizability, braiding, symmetry,
  cartesian tensor, finiteness, additivity, or zero objects. The module imports a
  braiding module for unrelated declarations, but no braiding instance occurs in
  these signatures. Closedness is the given tensor-left/right-adjoint condition.

Dependencies read and used: `def-sfb-monoidal-category` matches
`CategoryTheory.MonoidalCategory` in `Mathlib.CategoryTheory.Monoidal.Category`
(including `MonoidalCategoryStruct`, pentagon and triangle); the strong-functor
node matches `CategoryTheory.Functor.CoreMonoidal` in
`Mathlib.CategoryTheory.Monoidal.Functor` (all fields and its conversion read).
Both are Mathlib nodes, requiring no `lean` repair. Internal Homs, evaluation,
currying and precomposition are Mathlib's `MonoidalClosed`, `ihom`, `ihom.ev`,
`MonoidalClosed.curry` and `MonoidalClosed.pre` in
`Mathlib.CategoryTheory.Monoidal.Closed.Basic`.

Edge checks: the identity equivalence gives the identity mate for its specified
closed structure; arbitrarily different choices of right adjoints in C and D are
allowed and compared by the mate. Non-symmetric monoidal categories are included.
M need not be dualizable. If zero objects exist, M = 0 and N = 0 remain included;
no nonzero or inhabited Hom hypothesis is present. A monoidal category has its
unit object, so an empty category is already excluded by the node itself.
Different object and morphism universes on the two sides remain allowed.

Searches made using `msearch.py NE lem-pur-monoidal-equivalence-hom-comparison`:

- LeanFinder: `strong monoidal equivalence canonical internal Hom comparison
  isomorphism natural evaluation`; eight hits, principally `expComparison`,
  `expComparison_ev`, Frobenius-comparison and cartesian closed functor results.
  These Mathlib results alone require cartesian tensor and are insufficient.
- Loogle: `CategoryTheory.MonoidalClosed, CategoryTheory.MonoidalClosedFunctor`;
  four hits for the cartesian closed functor API, also insufficient in general.
- Mathlib grep: `comparison|ofEquiv|pre` in `CategoryTheory/Monoidal/Closed`;
  25 reported hits, including `MonoidalClosed.pre` and cartesian comparisons.
- LeanSearch: `strong monoidal equivalence preserves internal Hom comparison`;
  eight hits including `MonoidalClosed.ofEquiv`, which constructs a closed
  structure rather than comparing the two given structures.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for `homComparison`,
  `closedComparison`, `MonoidalClosedFunctor` and monoidal comparison patterns
  found uses of the upstream `Functor.LaxMonoidal.ihomComparison`.
  A focused `rg` for `def ihomComparison|theorem ihomComparison|lemma ihomComparison`
  and invertibility names located the exact upstream module. Its entire source,
  including commIhom, the invertibility instance, evaluation/transpose theorems
  and first-variable naturality, was read. `rg` of DAG records and upstream names
  checked existing usage. `grep -rn` of the item's id in `lean/WeilConjectures`
  found no prior blueprint attachment, but the declarations are an exact match.

Source checked: current blueprint `sec-smooth-purity/sk-def-sf-weil-complexes/_section.md`,
contragredient composite, especially the first arrow and its canonical pullback
isomorphism. The node is its general categorical prerequisite, as its source says.
The package above realizes exactly that prerequisite. Existing source proofs are
left intact; no new proof or construction is added in stage 2. Server checks of
all six recorded declarations are performed by deliver2.py through scompile.py.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
