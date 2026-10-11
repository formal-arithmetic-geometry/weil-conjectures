## Worker report

Module `Sheaf.CategoryTheory.Filtration` formalizes the definitions in
`def-sp-filtration`, following Stacks Project, Homology, Definition 12.19.1
(Tag 0121). No theorem statement is added and no `sorry` occurs.

Clause-by-clause correspondence:

- The ambient abelian category is `[Category.{v} C] [Abelian C]`.
  The dependency `def-sp-abelian` records `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic`; its full class definition requires
  preadditivity, finite products, kernels, cokernels, and normal mono/epi
  categories, and that file derives the zero object and finite biproducts.
- `DecreasingFiltration.step : ℤ → Subobject A` is the family of subobjects;
  `antitone_step : Antitone step` gives `F^(n+1) A ≤ F^n A` and all other
  descending inequalities. Every step lies between `⊥` and `⊤` by the
  bounded subobject order, so the displayed end inclusions impose no bounds.
- `FilteredObject.obj` and `FilteredObject.filtration` are the pair `(A,F)`.
- `FilteredObject.Hom.hom` is `φ : A → B`; its `preserves` field says that for
  each integer `i`, the restriction of `φ` to `F^i A` factors through `F^i B`.
  This is exactly `φ(F^i A) ⊆ F^i B`. The `Category (FilteredObject C)`
  instance gives `Fil(C)` with identities and composition of those maps.
- `DecreasingFiltration.induced F X` pulls each step back along `X.arrow`.
  This is the intersection `X ∩ F^n A` regarded as a subobject of `X`.
- `DecreasingFiltration.quotient F π [Epi π]` takes the image of each step
  under the surjection `π`, using Mathlib's `Subobject.exists` image functor.
- `DecreasingFiltration.IsFinite` is `∃ n m : ℤ, F.step n = ⊤ ∧ F.step m = ⊥`;
  the two bounds are independent, as in Stacks.
- `HasIntersection` and `HasUnion` spell out existence of a greatest lower
  and least upper subobject, respectively. `IsSeparated` says that any common
  lower subobject is `⊥`; `IsExhaustive` says that any common upper subobject
  is `⊤`. Since `⊥` and `⊤` are always such bounds, these predicates also
  assert the relevant extremal subobject exists, without assuming arbitrary
  intersections or unions in the ambient category.
- `gradedPiece F n` is the cokernel of `Subobject.ofLE` from `F^(n+1) A`
  to `F^n A`, hence the quotient `F^n A / F^(n+1) A`.

Edge cases checked: the zero object admits the constant zero filtration;
the full and zero filtrations on any object are allowed; finite filtration
bounds may be any integers, including negative integers and zero. Constant
full and constant zero filtrations distinguish the separated and exhaustive
conditions. No completeness or boundedness hypothesis is imposed.

Searches for an existing declaration:

- `msearch leanfinder` query “decreasing filtration on an object of an
  abelian category as integer indexed subobjects, filtered morphisms and
  graded quotients”: eight hits about module or ideal filtrations and a
  Grothendieck-category construction; none matches.
- `msearch loogle` query `CategoryTheory.Subobject,
  CategoryTheory.Abelian, FilteredObject`: zero hits; `FilteredObject` unknown.
- `msearch grep` query `Filtration|FilteredObject|DecreasingFiltration` under
  Mathlib `CategoryTheory`: zero hits.
- `rg` in Mathlib `CategoryTheory` for a filtration on `Subobject` found no
  general filtered-object API. `rg` in the source `WeilConjectures` found
  truncation and spectral-sequence filtrations only; `grep -rn
  "def-sp-filtration"` found no declaration. `rg` in the project's
  `lean/Sheaf/CategoryTheory` found no matching definition.

The local `literature/stacks-project/` source tree is absent on this machine;
Stacks Tag 0121 was read at https://stacks.math.columbia.edu/tag/0121.

## Second reading by E1

The node statement was read against Stacks Project Homology Definition 12.19.1,
Tag 0121, and the module was read in full.

Clause-by-clause correspondence:

- The hypothesis is an abelian category `C`, rendered by the module variables
  `{C : Type u} [Category.{v} C] [Abelian C]`. This uses the recorded dependency
  `def-sp-abelian` as `CategoryTheory.Abelian` from
  `Mathlib.CategoryTheory.Abelian.Basic`; no Noetherian, finiteness,
  completeness, or universe restriction is added.
- A decreasing filtration on `A` is rendered by
  `DecreasingFiltration A`, with `step : ℤ → Subobject A` and
  `antitone_step : Antitone step`. This is exactly the chain of subobjects in
  Tag 0121; the displayed `A` and `0` are the top and bottom bounds already
  present in `Subobject A`, not eventual boundedness hypotheses.
- A filtered object is `FilteredObject.obj` together with
  `FilteredObject.filtration : DecreasingFiltration obj`.
- A filtered morphism is `FilteredObject.Hom.hom` together with, for every
  integer `i`, a factorization through the target subobject in `preserves`.
  This is the categorical rendering of `φ(F^i A) ⊆ F^i B`.
- The `Category (FilteredObject C)` instance supplies `Fil(C)`, with identity
  and composition preserving the factorizations.
- `DecreasingFiltration.induced` uses `Subobject.pullback X.arrow`, i.e. the
  intersection filtration on a subobject.
- `DecreasingFiltration.quotient` uses the image functor
  `Subobject.«exists» π` for an epimorphism, i.e. the quotient filtration.
- `IsFinite` is `∃ n m : ℤ, step n = ⊤ ∧ step m = ⊥`, with independent
  indices as in the node.
- `HasIntersection` and `HasUnion` render the greatest common lower and least
  common upper subobjects. `IsSeparated` and `IsExhaustive` state that these
  extremal subobjects are respectively `⊥` and `⊤`.
- `gradedPiece F n` is the cokernel of the inclusion of step `n+1` into step
  `n`, rendering `F^n A / F^(n+1) A`.

No mismatch was found and no change was made in the second reading. The only
potential ambiguity, the chain's terminal `A` and `0`, was checked against the
source: Tag 0121 requires monotonicity only, while eventual top/bottom values
are separately the definition of finite filtration; the Lean code preserves
that distinction.

Edge cases checked: `C` may be any universe-sized abelian category; the zero
object, empty subobject intersections, constant zero and constant top
filtrations, negative and zero integer indices, and non-finite filtrations are
all admitted. `IsFinite` permits arbitrary integer witnesses. Pullback and
image constructions use the abelian-category instances supplied by the
dependency and impose no extra assumptions.

Searches were independently checked: the recorded LeanFinder, Loogle, grep,
and unavailable LeanSearch queries found no matching general categorical
filtration declaration; `rg` over Mathlib `CategoryTheory` and the
slopmaster2 `WeilConjectures` source likewise found no duplicate. The existing
module was compiled with
`python3 /home/ubuntu/weil-launcher/scompile.py E1 def-sp-filtration
lean/Sheaf/CategoryTheory/Filtration.lean`; it completed with no errors or
warnings.
