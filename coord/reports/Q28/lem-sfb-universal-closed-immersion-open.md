## Worker report

The module `Sheaf.AlgebraicGeometry.UniversalClosedImmersionOpen` states
`AlgebraicGeometry.exists_universalClosedImmersionOpen`, the scheme specialization
of Stacks Tag 05XA, `spaces-more-morphisms-lemma-where-closed-immersion`.
Its only theorem has proof `sorry`. There are no new definitions or auxiliary
statements. Only the item's `lean` field changes; its reviewed stage-1 split,
statement and dependencies are retained verbatim.

Clause-by-clause translation:

- Schemes B, A and C: `{B A C : Scheme.{u}}`.
- Morphisms p : A → B, q : C → B and f : A → C: the three explicit morphism
  binders `(p : A ⟶ B) (q : C ⟶ B) (f : A ⟶ C)`.
- The compatibility q ∘ f = p: `(hf : f ≫ q = p)`, using Lean's composition order.
- p locally of finite type: `[LocallyOfFiniteType p]`.
- p universally closed: `[UniversallyClosed p]`.
- q separated: `[IsSeparated q]`. There is no separatedness assumption on p,
  and no finite-type assumption on q or properness assumption on p.
- An open subscheme V of B: `∃ V : B.Opens`, represented by the canonical
  scheme `V.toScheme` and its open immersion `V.ι`.
- Every scheme T and map h : T → B: `∀ (T : Scheme.{u}) (h : T ⟶ B)`.
  The universe u is explicit and polymorphic, using the common scheme-category
  universe, just as the adjacent universal-isomorphism statement does.
- The canonical base-changed arrow A ×_B T → C ×_B T:
  `pullback.map p h q h f (𝟙 T) (𝟙 B) ... ...`. Its first square uses hf.symm
  after eliminating p ≫ 𝟙 B, and its second square is the identity square for h.
  Thus this is the induced arrow on the specified fibre products, not an
  arbitrary map or a fibrewise replacement.
- This arrow is a closed immersion: `IsClosedImmersion (pullback.map ...)`.
- If and only if h factors through V: `↔ ∃ l : T ⟶ V.toScheme, l ≫ V.ι = h`.
  Factorization is an equality of scheme morphisms, retaining nilpotents and
  arbitrary nonreduced test schemes. No extra uniqueness clause is asserted.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (def-pc-scheme).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` (def-weil-finite-type-morphism).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`, and its imported Separated and
  UniversallyClosed modules: `AlgebraicGeometry.IsSeparated` and
  `AlgebraicGeometry.UniversallyClosed` (def-weil-proper-morphism).
  The node's principal declaration IsProper is deliberately not assumed:
  the node explicitly supplies the two weaker, separate properties above.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Restrict`: `AlgebraicGeometry.Scheme.Opens.toScheme`
  and `AlgebraicGeometry.Scheme.Opens.ι` (def-weil-open-immersion).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, its projections and `pullback.map`
  (def-pc-fibre-product); `Mathlib.AlgebraicGeometry.Pullbacks` supplies scheme
  pullbacks.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (def-weil-closed-immersion).

Statement dependencies are public imports. For the proof plan, plain imports
include the recorded `Sheaf.AlgebraicGeometry.UnramifiedMorphism` and its
`AlgebraicGeometry.IsUnramified`, Mathlib's UniversallyInjective module, and
`Mathlib.AlgebraicGeometry.ZariskisMainTheorem` with
`AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono`. The other stated
proof dependencies (closed-immersion and universal-closedness base change,
properness and quasi-compactness) are Mathlib leaves already available through
the imported modules. `lem-sfb-universal-unramified-radicial-open` presently has
neither a Lean record nor a Mathlib match, so no import for it exists yet. It is
only a proof dependency and is not needed to type this stage-2 statement; the
maintainer can add that proof import when its module is stated. The theorem's
docstring includes all six steps of the reviewed proof, including this input.

Edge cases checked against the node, Tag 05XA and this signature:

- A empty: the induced maps are closed immersions for every test, so V = B is
  permitted. No nonemptiness hypothesis excludes this case.
- B empty: all schemes mapping to B and all tests are empty; its unique open
  satisfies the statement.
- T empty: the canonical base-change map is an isomorphism of empty schemes,
  and the empty map factors through every open, including the empty open.
- f an identity (and p = q): V = B has the required universal property.
- A two-point scheme mapping to a point C over a field: the good locus is
  empty; the only maps factoring through it have empty source. This checks
  that existence of a good locus is not assumed to mean it is nonempty.
- Spec k → Spec(k[ε]/ε²) over Spec k: f is a closed immersion though not an
  isomorphism, and V = B is allowed. Nonreduced test schemes are quantified
  with the full canonical scheme base change.
- Local finite type and universal closedness of p are kept separate; no
  unmentioned separatedness or finiteness assumption on p is introduced.

Searches performed with msearch.py, group Q28, this item:

- LeanFinder query: "The universal locus in the base where a morphism from a
  locally finite type universally closed family to a separated family is a
  closed immersion is open". Eight results: universal closedness locality,
  cancellation against separated maps, closed-immersion locality and related
  permanence statements. None constructs the parameter open with this
  universal property.
- Loogle query: `"IsClosedImmersion", "Opens"`. Zero results.
- Mathlib grep query: `where.*closed.*immersion|closedImmersionLocus|closed.*immersion.*locus`,
  restricted to AlgebraicGeometry. One hit, the introductory text of AffineAnd;
  it concerns affine criteria, not this parameter open.
- LeanSearch query: "An open subscheme of the base represents the base changes
  making a morphism between families a closed immersion". Eight results:
  IsClosedImmersion, its constructors and stability under base change, plus
  open-immersion base change. No universal parameter-locus statement.
- rg searches of the project sources `lean/WeilConjectures` and `lean/Sheaf`
  for `universal.*[Cc]losed.*[Ii]mmersion|closedImmersionLocus|closed_immersion.*[Oo]pen`
  and the item's blueprint id found permanence statements about single
  morphisms and the adjacent UniversalIsomorphismOpen proof's citation of this
  node. None is this statement. Further rg for `05XA` and
  `exists_universalClosedImmersionOpen` in Mathlib, project sources and
  dag/lean_names_upstream.json found no declaration for the item.

No statement correction, disputed statement, new node or dependency repair is
needed. The earlier worker's refusal confused the already reviewed stage-1
split with a new split: this delivery only adds the missing stage-2 Lean
record and module, preserving that split.

Validation: scompile.py compiled this module both as an isolated sandbox module
and at its intended library module path; both checks passed without errors or
warnings. Delivery preflight and its additional compile are run by deliver2.py.

## Second reading by Q28

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
