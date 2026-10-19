## Worker report

Item: `lem-coef-dgcat-cone-word-normal-form`, group Q51, stage 2.

The main module is `Sheaf.CategoryTheory.DgCategoryConeWordNormalForm`; its only theorem is
`CategoryTheory.Dg.coneWordNormalForm`, with proof `sorry`. All supporting definitions contain
actual data and transports; none chooses an object from a `Nonempty` assertion. The theorem
is universal in the dependency's characterized `FormalConeCalculus` and its `ArrowCell`
realizations. The module imports both statement/proof dependencies publicly, as well as the
new graded-linear interface. No dependency record is repaired or copied.

Hypothesis and clause correspondence:

- Commutative ring: `(R : Type u) [CommRing R]`.
- Small cochain dg category: `{A : Cat R}`, the recorded enrichment in cochain ModuleCat.
- Closed degree-zero arrow `u : x → y`: `(a : ClosedArrow R A)` packages `source`, `target`,
  `arrow` in degree zero and `closed : d arrow = 0`; no invertibility is required.
- Labelled cone enlargement: `(K : FormalConeCalculus R)` uses the dependency's actual
  `cones`, `coordinates` and full `embedding`, including all their normalizations.
- Full subcategory on the representables and `Z=C_u`: `coneWordBase R K a` pulls back the
  actual cone enrichment along `coneWordLabel`. Its objects are `Option A`; `some x` is
  the representable at `x` and `none` is the chosen cone, including when `x=y` or the cone
  is isomorphic to a representable. The label map is injective because the dependency's
  labels are an equivalence and its `ConeLabel.rep`/`cone` constructors are disjoint.
  Thus no other cone is accidentally included and no required cone is excluded.
- Free adjunction: `(E : ConeContractingCell R K a)` is exactly the recorded `ArrowCell`
  of degree -1 from `none` to `none`, attached to the identity. Its `differential` and
  `universal` fields enforce `dh=1` and freedom; no word-spanning hypothesis is added.
  The arbitrary realization formulation does not choose an unspecified object. The
  dependency guarantees existence (the identity is closed), and its universal property
  identifies all such realizations, including their graded arrows, with its word model.
- Full old-object category with labels identified with `A`: `coneWordOldCategory R E`
  has object type literally `A` and Hom complexes literally those of `E.category`
  between the images of `some x`. This is a construction, not an extra assumed category.
- Old homogeneous arrows: `coneWordOld` applies `K.cones A`'s embedding map followed by
  `E.inclusion`; it transports only the embedding's recorded object equalities.
- Cone inclusions/projections: `coneWordInY`, `coneWordOutY`, `coneWordInX`, `coneWordOutX`
  are `K.coordinates A a`'s actual arrows mapped by `E.inclusion`, in degrees `0,0,-1,1`.
  Their types impose no cycle/closedness conditions.
- New generator: `coneWordH` is the dependency's `generator R (-1) E.arrow`.
- Four extra arrows: `coneWordV`, `coneWordA`, `coneWordB`, `coneWordW` are exactly
  `π_x h ι_y`, `π_x h ι_x`, `-π_y h ι_y`, `-π_y h ι_x`. Their types are respectively
  `y→x` degree 0, `x→x` degree -1, `y→y` degree -1 and `x→y` degree -2.
  `coneWordMul` is only `mul` transported along a proved equality of integer degrees.
- First displayed graded identity: the first conjunct of `ConeWordNormalForm` states
  `ι_y π_y + ι_x π_x = 1_Z` in the actual free extension.
- Second displayed graded identity: its second conjunct states exactly
  `h = -ι_y b_h π_y - ι_y w_h π_x + ι_x v_h π_y + ι_x a_h π_x`.
  Each term is normalized to degree -1; no additional sign or closedness is asserted.
- Generation / finite linear combinations of composable words: the third conjunct
  quantifies every `x y n` and every degree-`n` arrow and supplies a finite dependency
  `Term` evaluating to it. `ConeWordLetter` contains every old homogeneous arrow plus
  the four new arrows, with the exact source, target and degree functions. `Term` has
  only generator, identity, zero, finite binary sum, scalar, composition and degree-cast
  constructors. It has no infinite-sum/completion constructor. Distributivity converts
  precisely these finite expressions into finite R-linear combinations of words.
- Equality of functors: the fourth conjunct quantifies `(O : Type v)` and
  `(D : GradedLinearCategory.{u,v,w} R O)` and all `GradedLinearFunctor`s to it, requires
  equality of their object functions and agreement on every `ConeWordLetter`, and
  concludes equality of the functors themselves. The `old` constructor ranges over
  exactly every homogeneous arrow of `A`; the four remaining constructors give the
  four other agreements. `HEq` only transports the equal object functions, and never
  forgets degree or endpoints. There is no differential on the target or requirement
  that a functor be a dg functor. Object and arrow universe parameters are independent.
- The final sentence excluding closedness assertions is respected: no coordinate arrow
  is constrained to be closed, and no relation `h²=0` is imposed.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.DgCategoryFreeCellCalculus`: `CategoryTheory.Dg.Cat`, `hom`,
  `unit`, `mul`, `Term`, `eval`, `ArrowCell`, `generator`, `FreeCellCalculus` and
  `freeCellCalculus` (notably `exists_arrowCell` and its `HasWordFiltration` clause).
- `Sheaf.CategoryTheory.DgCategoryFormalConeEnlargement`: `degreeCast`, `ClosedArrow`,
  `ConeLabel`, `ConeSystem`, `ConeCoordinates`, `FormalConeCalculus` and
  `formalConeEnlargement`; full signatures and docstrings were read. The construction
  uses `cones`, `coordinates`, `embedding`, `embedding_obj`, the four coordinates;
  the proof will use `embedding_full`, `partition`, and the word-filtration theorem.
- New module `Sheaf.CategoryTheory.GradedLinearCategory`: `GradedLinearCategory` and
  `GradedLinearFunctor` (definition node described below).
- Mathlib `EnrichedCategory`, `eId`, `eComp`, `e_id_comp`, `e_comp_id`, `e_assoc`,
  `ModuleCat`, linear maps and integer degree transport are reused.

Edge cases checked before drafting: zero ring and characteristic 2 (signs remain literal
additive inverses, with no nonzero assumption); zero attaching arrow; coincident `x=y`;
length-zero and length-one words; zero and identity homogeneous arrows; all integer degrees;
cones isomorphic to old objects (labels remain distinct); any target object type, including
empty targets when a functor exists; independent target object/module universes. No flatness,
finite presentation of Hom modules, invertibility of `u`, or extra differential equation is
assumed. The two identities were checked term by term for endpoints and degrees. The proof
uses bilinearity and associativity, never an interchange of homogeneous factors.

Searches made:

1. `msearch.py leanfinder`: "In a free graded linear category adjoining a contracting
   endomorphism of a cone, arrows between old objects are generated by its four matrix
   entries". Eight hits: ordinary free R-linear categories, simplex generators and finite
   matrix categories. None states this dg cone word theorem.
2. `msearch.py loogle`: `CategoryTheory.EnrichedCat, CategoryTheory.GradedObject,
   CategoryTheory.Dg.Term`. No hits (the side-project Term is unknown to the index).
3. `msearch.py grep`: `dg[Cc]at|DGCategory|GradedLinear|GradedFunctor|cone.*word|word.*cone`.
   Three unrelated limit-cone prose hits in Mathlib; no dg or cone-word theorem.
4. Direct `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and
   `/home/ubuntu/weil-newtargets-shared/lean/Sheaf`, and grep of `dag/lean_names_upstream.json`:
   no existing declaration of the item or its graded functors. The existing dg free-cell
   and formal-cone modules were inspected and reused. `SemiFreeDGModule`'s integral dg
   category is neither this recorded R-linear enrichment nor the required differential-free
   target. Ordinary free-factor word and simplicial-arrow word modules have different objects.
5. Missing-definition searches: LeanSearch, LeanFinder, Mathlib grep, direct project/upstream
   grep, DAG grep and `tools/blueprint_refs.py search 'graded linear'`. Exact queries and
   unabridged search-service outputs are in the new node's `mathlib_searches`.
   Ordinary `CategoryTheory.Linear`/`Functor.Linear` have no degree-indexed arrow modules;
   `HomologicalComplex.forget` forgets an individual complex, not composition. Generic
   Mathlib `EnrichedCategory` has no recorded specialization providing this homogeneous
   right-to-left interface without differential/size restrictions.

Source checked: downloaded and read arXiv:0710.4303, printed pp. 29–31, especially p. 29's
full module subcategory containing the cone and representables, free contraction, old-object
full subcategory, four components and inverse verification, and pp. 29–30's graded word sum.
The node's phrase "on the labelled representables and Z=C_u" is read as including both the
representables and the chosen cone, exactly as the source specifies; the Lean makes this
explicit as `Option A`. No statement correction is needed or made.

Validation: both delivered modules compile through the prescribed `scompile.py`, individually
and in dependency order, against the side-project overlay. The final run has no errors or
warnings; only the main theorem has `sorry`. Explicit `autoImplicit false` binds every
variable and universe. All lines are at most 100 characters. No other Lean theorem is added.
No `STATEMENT-DISPUTED` finding or dependency interface fault remains.

## New nodes

`def-coef-graded-linear-category`, in the same chapter and unit, supplies exactly the notion
spelled out in the item's final paragraph: graded module Hom families, two-sided units,
bilinear degree-additive associative composition, and graded linear functors out of the
recorded dg category. Its module is `Sheaf.CategoryTheory.GradedLinearCategory`. The category
has an explicit object type with independent morphism universe, and the functor structure
requires no differential compatibility. Both are complete data structures with actual
fields and law proofs as inputs; there is no theorem or `sorry` in this module. The node
cites `lem-coef-dgcat-free-cell-calculus` for its dg-source notion. The item now cites this
new node in `stmt_deps`; no other original node field changes apart from `lean`.

## Second reading by Q51

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
