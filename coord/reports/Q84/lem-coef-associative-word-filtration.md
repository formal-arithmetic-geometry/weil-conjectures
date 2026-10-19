# Q84: lem-coef-associative-word-filtration

## Worker report

The module `Sheaf.CategoryTheory.AssociativeWordFiltration` states
`CategoryTheory.tensor_word_free_associative_filtration`, whose sole proof is
`sorry`. Its conclusion is the existence of `AssociativeWordFiltration.Construction C`.
All other declarations describe this node's own ordered words, structural maps,
and filtration. They have real recursive data or are structures specifying the
asserted construction; no object is chosen from an uncharacterized existence
claim. Their names are listed in `lean.declarations`. There are no new independent
notions or dependency modules, and the original node is unchanged outside `lean`.

The earlier sandbox attempt was replaced. Its filtration converged to `A` rather
than the pushout; its arbitrary successor arrows did not express pushouts of the
specified `q_n`; its free algebra had no concatenation equations; its monad had
neither specified unit/multiplication nor an algebra equivalence. Its report's
claims of completed independent review and conceptual reruns of searches were
removed. This worker performed actual searches and the required wrapper compile.

The statement is rendered hypothesis by hypothesis and clause by clause as follows.
Names in the second column are fields of `Construction` unless qualified otherwise.

| Natural-language hypothesis or clause | Lean rendering |
| --- | --- |
| Fix a universe U; C has U-small Hom sets | Explicit universes `u v`, `{C : Type u}`, `[Category.{v} C]`; U is `v`, with no equality imposed on the object universe `u`. |
| All U-small colimits | `[HasColimits C]`, which Mathlib defines as `HasColimitsOfSize.{v,v} C`. This includes initial objects, countable coproducts, pushouts and the sequential colimit. |
| Monoidal structure, not assumed symmetric | `[MonoidalCategory C]`; no braided or symmetric instance is a binder. |
| Each left tensor functor has a right adjoint | `leftAdj : ∀ X : C, ((tensoringLeft C).obj X).IsLeftAdjoint`. Mathlib `Functor.IsLeftAdjoint` asserts existence of a right adjoint and adjunction. |
| Each right tensor functor has a right adjoint | The analogous `rightAdj` on `tensoringRight`. |
| 0 is initial | Mathlib's chosen initial object is the source of `initial.to A.X`. |
| Associative unital algebra objects, algebra morphisms, and U | Mathlib `Mon C`, `MonObj`, `Mon.Hom`, and `Mon.forget C`; their laws have exactly the monoidal associator/unitors and preservation of unit/multiplication. |
| X to the power 0 is the unit; all finite ordered tensor powers | `power 0` is the constant unit functor; `power (n+1)` is the pointwise tensor of `power n` and the identity functor. The extra initial unit factor is removed by canonical unitors. |
| P(X) is the coproduct over all word lengths | `ι X n` and `coproduct X : IsColimit (Cofan.mk (monad.obj X) (ι X))`. This is Mathlib's coproduct universal property, with every n including 0. |
| P acts by the tensor powers of each arrow | `naturality f n` specifies the map on every coproduct summand. |
| Monad structure and its length-one unit | `monad : Monad C` includes the laws; `monad_unit X` is the left-unitor inverse followed by `ι X 1`. |
| Monad multiplication concatenates words of words | `monad_mul X ns` specifies its composite on every finite list of word lengths, using `insertBlocks`, `flatten`, and `blockLength`. Both the outer empty word and empty inner words are included. |
| Monad algebras identify with the specified associative algebras | `algebras : monad.Algebra ≌ Mon C` and `algebraUnderlying` are an equivalence over C. `algebra_one` and `algebra_mul` require its operations to be exactly the length-zero and length-two parts of the monad action, transported along that underlying isomorphism. Naturality of the isomorphism also fixes the underlying morphisms. |
| T(X) has underlying object P(X) | `free : C ⥤ Mon C` and `freeUnderlying : free ⋙ Mon.forget C ≅ monad.toFunctor`. |
| T(X)'s unit is the length-zero inclusion | `free_one X`. |
| T(X)'s multiplication concatenates words | `free_mul X m n`, for every pair including zero lengths, uses the explicitly constructed structural `concat X m n`. |
| T is left adjoint to U | `adjunction : free ⊣ Mon.forget C`. `adjunction_unit` identifies its universal generator with the length-one inclusion. |
| P preserves small filtered colimits | `preserves_filtered` quantifies over `J : Type v`, `[SmallCategory J]`, `[IsFiltered J]`, every `D : J ⥤ C`, and asserts `PreservesColimit D monad.toFunctor`. |
| U creates those colimits, including their universal property | `creates_filtered` quantifies over the same sizes and filteredness and asserts Mathlib `CreatesColimit D (Mon.forget C)`, not merely preservation. For this faithful algebra forgetful functor, lifting an arbitrary underlying colimit and reflecting colimits gives precisely creation. On a fixed underlying object the lifted multiplication is determined on the filtered colimit of the binary tensor powers and the unit at any index, so the structure is unique as stated by the node. |
| Filtered includes nonempty and cocones on all finite diagrams | Mathlib `IsFiltered` includes `Nonempty`, common targets and equalization of parallel arrows. These are equivalent to the finite-diagram formulation used in the node. |
| Initial algebra is the unit with its canonical structure | `initial_algebra : IsInitial (Mon.trivial C)`; Mathlib's `Mon.trivial C` has object `𝟙_ C`, identity unit and left-unitor multiplication. |
| For every f and g the algebra pushout exists | `pushout_filtration` quantifies over every `f : X ⟶ Y`, `A : Mon C`, and `g : free.obj X ⟶ A`, then gives `B`, `inA`, `inY` and `IsPushout g (free.map f) inA inY` in `Mon C`. |
| Underlying map has stages beginning at A | `Filtration f A inA.hom` has `stage : ℕ ⥤ C` and `start : A.X ≅ stage.obj 0`. The stage-zero identification accounts for choices of objects, without changing the asserted diagram. |
| Underlying pushout object is the sequential colimit | `Filtration.cocone`, `isColimit` and `tip : cocone.pt ≅ B.X` give exactly this colimit and its identification. |
| Compatibility with the actual map from A to B | `Filtration.initial_leg : start.hom ≫ cocone.ι.app 0 ≫ tip.hom = inA.hom`. |
| Each B_n to B_(n+1) is a pushout of q_(n+1) | `Filtration.isPushout n` is an `IsPushout` square whose left edge is that alternating arrow and whose bottom-to-right transition is `stage.map (homOfLE (Nat.le_succ n))`. Its other maps are `attach n` and `cell n`. |
| q_n has n copies of f and n+1 copies of j in alternating order | `alternating j f 0 = j` and `alternating j f (n+1) = (alternating j f n □ f) □ j`; in the filtration `j = Arrow.mk (initial.to A.X)`. Thus q_1 is `(j □ f) □ j`, q_2 is `(((j □ f) □ j) □ f) □ j`. |
| The specified pushout product | `MonoidalCategory.Arrow.pushoutProduct` is Mathlib's Leibniz tensor construction with domain `(L ⊗ M) ⨿_(K ⊗ M) (K ⊗ N)` and the canonical arrow to `L ⊗ N`. It is reused, not redefined. |
| Parenthesization and canonical structural identifications | `alternating` is left-associated. `concat` and `flatten` use the actual associators and unitors. Mathlib's `PushoutProduct.associator` supplies the other parenthesizations under the tensor-colimit preservation obtained from the given adjoints; the imported coherence leaf identifies structural reassociations. |
| No model structure, cofibrancy, monoid axiom or symmetry | None occurs among the theorem's binders or the construction's fields. |

Lists of block lengths are stored in reverse order: `blocks X (n :: ns)`
appends the n-block to the right of `blocks X ns`. `insertBlocks` and `flatten`
use the very same convention, so no factor is permuted. Every ordered list of
blocks occurs, and `blockLength` is its total length. The tensor powers include
a unit factor at the far left, so the singleton generator uses `(λ_ X).inv`
and the binary algebra operation uses `((λ_ K.A).inv ▷ K.A)`. These are the
canonical monoidal constraints allowed by the statement, not a strictness
assumption on the ambient monoidal category.

Dependencies and exact declarations read:

- `def-weil-pbc-category-colimit`: its recorded
  `Mathlib.CategoryTheory.Limits.HasLimits` supplies `CategoryTheory.Limits.colimit`,
  `Cocone`, `IsColimit`, `HasColimit`, and `HasColimits`; the universal property is
  used through `IsColimit` and `Cofan.mk` (`Limits.Shapes.Products`). The generated
  dual declarations were read together with the corresponding limit source.
- `def-sfb-monoidal-category`: its Mathlib match is
  `CategoryTheory.MonoidalCategory`, in `Mathlib.CategoryTheory.Monoidal.Category`.
  Its full structural data and laws were read. `Monoidal.Mon` imports this module;
  no duplicate dependency module is needed.
- Proof dependency `lem-weil-pbc-left-adjoint-preserves-colimits`: the exact match
  `CategoryTheory.Adjunction.leftAdjoint_preservesColimits` in
  `Mathlib.CategoryTheory.Adjunction.Limits` is imported without `public`.
- Proof dependency `lem-coef-monoidal-structural-coherence`: the exact match
  `CategoryTheory.FreeMonoidalCategory.subsingleton_hom` in
  `Mathlib.CategoryTheory.Monoidal.Free.Coherence` is imported without `public`.
- Additional existing Mathlib interfaces read and reused: `MonObj`/`Mon` and
  `Mon.Hom`/`Mon.forget`/`Mon.trivial` in `Monoidal.Mon`; `Monad.Algebra`, its action
  law and `Monad.forget` in `Monad.Algebra`; the pointwise `tensorObj` in
  `Monoidal.FunctorCategory`; `MonoidalCategory.Arrow.pushoutProduct` and its
  associator in `Monoidal.PushoutProduct`; `CreatesColimit` in `Limits.Creates`;
  and `IsFiltered` in `Filtered.Basic`.

Sources opened: the node's primary URL
https://arxiv.org/html/1312.3881v4 (Section 3.2, Theorem 3.10) and its external URL
https://msp.org/agt/2011/11-3/agt-v11-n3-p13-p.pdf (Section 8, Theorem 8.3, and
page 1592). The former gives the precise alternating attaching arrows; the latter
supplies the free-algebra and filtered-monad descriptions. The node's fifteen
proof steps were read in full and are reproduced as the theorem's numbered proof
plan, including the ordinary algebraic construction that precedes model transfer.
No statement correction or disputed statement is needed.

Edge cases checked before writing the replacement:

- Empty words: `power 0` is the unit, `blocks []` is the unit, and `flatten []`
  and `insertBlocks []` are identities. `monad_mul` includes this case.
- Empty inner words: zero entries are allowed in every list; flattening removes
  their unit blocks canonically through `concat`.
- One word: the left unitor identifies `power 1` with X; the theorem explicitly
  uses its inverse for the generator and its binary tensor for length two.
- Zero generators: the tensor adjoints preserve the initial object, so positive
  tensor words on it are initial and T(0) is the canonical unit algebra.
- n = 0: the filtration starts at A and its first square is q_1, never q_0.
  The auxiliary q_0 = j is only the recurrence base.
- n = 1 and n = 2: expanding `alternating` gives respectively the three-factor
  and five-factor ordered attaching arrows, with no symmetry used.
- f is an identity, including X = Y = 0: its pushout is A; the alternating
  attaching arrows are isomorphisms, allowing all stage transitions to be
  isomorphisms. No nonidentity or nonzero condition excludes these cases.
- A may be the initial/unit algebra or any zero algebra when present. No
  nonzero-object, inhabited-generator or characteristic restriction occurs.
- Filtered index categories are nonempty by `IsFiltered`; the empty indexing
  category is appropriately excluded only from the filtered assertions. Empty
  diagrams are still allowed by the overall colimit hypothesis.
- The object universe `u` is independent of U = `v`; index sizes match the Hom
  universe, so the older attempt's mismatch with its object-universe indexing is
  repaired without imposing equality of universes.

Actual searches (all wrapper searches used group Q84 and this item):

| Tool and query | Result |
| --- | --- |
| `msearch.py leanfinder`: “In a cocomplete nonsymmetric biclosed monoidal category the free associative monoid tensor word monad has an alternating pushout product word filtration for free algebra pushouts” | Eight hits: algebraic free products, `MonCat` filtered colimits, and free monoidal syntax. No statement for arbitrary C. |
| `msearch.py loogle`: `"Mon", "free"` | Free monoids/additive monoids on types and their algebraic instances; no exact match. |
| `msearch.py grep`: `tensorPow\|tensorPower\|pushoutProduct\|pushoutProd`, subdirectory `CategoryTheory` | Found Mathlib's existing pushout-product and arrow-monoidal constructions, which were read and reused. No tensor-word free-algebra theorem. |
| `msearch.py leansearch`: “Free monoid objects in a biclosed monoidal category have a tensor word monad and a pushout product filtration” | Eight hits: `MonCat.adj`, free semigroup monad, `Monad.free_obj_A`/`free_obj_a`, and free-monoidal syntax. These do not state the node. |
| `msearch.py loogle`: `"pushoutProduct"` | Existing Leibniz tensor arrow and its auxiliary isomorphisms. Reused its exact declaration. |
| `msearch.py grep`: `tensor_word_free_associative_filtration\|AssociativeWordFiltration\|tensorWord\|wordFiltration`, subdirectory `CategoryTheory` | Zero hits. |
| `rg` on Mathlib's `CategoryTheory/Monoidal`: tensor-power and pushout-product patterns | Located `Monoidal/PushoutProduct.lean`; its definition agrees with the node. No general free monoid object construction. |
| `rg` on `WeilConjectures/` and shared `lean/Sheaf/`: `tensorWord\|SequentialColimit\|WordCoproduct\|AttachedFiltration\|associative.word\|free.*[Mm]on\|pushout[Pp]roduct` | Hits concerned special module/free resolutions, algebraic topology and the flat-model axiom; no duplicate of this node. |
| `rg` on `WeilConjectures/`: literal item id | Zero hits. |
| `rg` on upstream sources, shared `lean/Sheaf/` and `dag/lean_names_upstream.json`: `AssociativeWordFiltration\|tensor_word_free_associative_filtration\|def tensorWordPower\|structure WordCoproduct\|structure AttachedFiltration` | Zero hits. New helper names are within the distinct `CategoryTheory.AssociativeWordFiltration` namespace. |
| Full DAG statement scan for tensor-word, tensor-power and pushout-product notions | The existing word-filtration node owns this construction. No separate pre-existing general word-construction definition node was found; the other hits concern particular algebras, tensor axioms, or unrelated geometric tensor powers. |

Validation: the prescribed `scompile.py Q84 lem-coef-associative-word-filtration`
compiled the replacement separately as both sandbox and library module with no
errors or warnings (reported compiler times 1.9 s and 2.8 s). The declaration and
signature were checked using the read-only `stage2_delivery.py decls/signature`
reader. All variables and universe parameters are explicit; no file-local
notation, private definition or local instance is used. The required `deliver2.py Q84 lem-coef-associative-word-filtration --no-push`
printed `OK (dry run): commit e076928864 passes the preflight and compiles;
nothing pushed`. The final report is checked again by the same dry-run command.

## Earlier second reading (a previous round; superseded)

Pending independent second reading by the dispatcher's next worker. This worker
has not claimed to perform that independent review and will not push a delivery.

## Second reading by Q84

Independent second reader: I opened the node, all its statement and proof
prerequisite records, the complete delivered Lean module, and the actual Mathlib
interfaces listed below. The node introduces the following objects, hypotheses
and conclusions. In the table, unqualified fields belong to
`AssociativeWordFiltration.Construction`; every row passes.

| Node item | Lean rendering and verdict |
| --- | --- |
| A universe U and a category with U-small Hom sets | `{C : Type u} [Category.{v} C]`, U = v; u and v are independent. Pass. |
| All U-small colimits | `[HasColimits C]` abbreviates `HasColimitsOfSize.{v,v} C`. Pass. |
| Specified monoidal tensor, unit, associator and unitors | `[MonoidalCategory C]`, using the dependency's exact Mathlib class. Pass. |
| Tensoring on either side has a right adjoint for every object | `leftAdj` and `rightAdj`, each universally quantified over X and asserting `Functor.IsLeftAdjoint`. No stronger adjoint data or extra instances are assumed. Pass. |
| Initial object 0 | `initial.to A.X` in the filtration; supplied by the colimit hypothesis. Pass. |
| Associative unital algebras and operation-preserving morphisms | `Mon C`, `MonObj.one`, `MonObj.mul` and `Mon.Hom`; these include the two unit equations and the associator-corrected associative equation. Pass. |
| Forgetful functor U | The existing `Mon.forget C`, object A.X and morphism f.hom. Pass. |
| Ordered powers, including the empty power | `power 0` is the constant tensor unit; `power (n+1)` tensors the previous functor with the identity. The harmless leading unit is identified by unitors. Pass. |
| P(X) is the coproduct over every natural word length | `ι` and `coproduct : IsColimit (Cofan.mk ...)`; `naturality` fixes the functor on each summand. Pass. |
| P has monad laws | `monad : Monad C`; this is data asserted to exist, not a new axiom or a hollow definition. Pass. |
| Its unit inserts length one | `monad_unit` includes `(λ_ X).inv` for the leading unit in `power 1`. Pass. |
| Its multiplication concatenates words of words | `monad_mul` specifies the composite on every list through `insertBlocks`, `flatten`, `blockLength` and `ι`. The recursion uses exactly the same reverse-list convention for both domain and target, so it never reverses the factors of an actual tensor expression. Pass. |
| Monad algebras identify with associative unital algebras | `algebras` is an equivalence, and `algebraUnderlying` is a natural isomorphism over C. `algebra_one` and `algebra_mul` fix the actual operations from action lengths zero and two; this is not an unrelated abstract equivalence. Pass. |
| T is the free-algebra functor with underlying P | `free` and the natural isomorphism `freeUnderlying`. Pass. |
| T's algebra unit is the empty-word inclusion | `free_one`. Pass. |
| T's multiplication concatenates each pair of words | `free_mul X m n`, using the real recursive structural map `concat X m n`. Pass. |
| T is left adjoint to U, with the stated generators | `adjunction` and `adjunction_unit`. The specified generator also determines the associated adjunction monad multiplication as evaluation of words of words. Pass. |
| P preserves small filtered colimits | `preserves_filtered` for every `J : Type v` with `SmallCategory J`, `IsFiltered J`, and every `D : J ⥤ C`. Pass. |
| U creates these colimits, with their algebra universal property | `creates_filtered` asserts `CreatesColimit D (Mon.forget C)`, rather than merely preservation. Pass. |
| Unique algebra structure on a fixed underlying colimit | Mathlib creation lifts every underlying colimit cocone up to isomorphism and reflects colimits. Transport gives a structure on its fixed vertex. Any second structure with those legs is also a colimit by reflection; the unique algebra isomorphism between them has underlying identity by the underlying colimit's hom-ext, hence equates their operations. Thus the class has the node's stated uniqueness for this concrete forgetful functor. Pass. |
| Filtered means nonempty and every finite diagram admits a cocone | Mathlib `IsFiltered` explicitly includes nonemptiness, common targets and equalization of parallel arrows, the equivalent finite-diagram criterion. Pass. |
| The initial algebra is the canonical unit algebra | `initial_algebra : IsInitial (Mon.trivial C)`; the existing trivial object has underlying tensor unit and canonical operations. Pass. |
| For every f:X→Y and g:T(X)→A the algebra pushout exists | `pushout_filtration` universally quantifies f,A,g before the existential B,inA,inY and asserts `IsPushout g (free.map f) inA inY` in `Mon C`. Pass. |
| The underlying filtration begins at U(A) | `Filtration.stage : ℕ ⥤ C` and `start : A.X ≅ stage.obj 0`. The initial isomorphism is an equivalent choice of presentation of B_0 = A. Pass. |
| U(B) is its sequential colimit | `Filtration.cocone`, `isColimit` and `tip : cocone.pt ≅ B`. The B here is the actual algebra pushout's underlying object. Pass. |
| Compatibility with the given map U(A)→U(B) | `Filtration.initial_leg` equates the stage-zero cocone leg, with both identifications, to `inA.hom`. Pass. |
| Every B_(n-1)→B_n, n≥1, is a pushout of q_n | `Filtration.isPushout n` uses q_(n+1), `attach n`, `cell n`, and the actual successor morphism of `stage`. Reindexing n≥1 by n+1 covers exactly the node. Pass. |
| q_n has n f's and n+1 j's, in alternating order | `alternating j f 0 = j`; its successor is `(alternating j f n □ f) □ j`, using j = `Arrow.mk (initial.to A.X)`. Pass. |
| Pushout product has the displayed source and canonical target map | The existing `MonoidalCategory.Arrow.pushoutProduct`, read as the tensor Leibniz pushout, has precisely `(L ⊗ M) ⨿_(K ⊗ M) (K ⊗ N) → L ⊗ N`. Pass. |
| Left parenthesization and canonical other parenthesizations | The recursion is left-associated. The imported existing `PushoutProduct.associator` applies after tensor-colimit preservation from the two adjunction hypotheses, and structural coherence identifies reassociations. No extra hypothesis is needed. Pass. |
| No symmetry, model structure, cofibrancy or monoid axiom | None is a binder or a field. Pass. |

Source reading: I opened Haugseng, Section 3.2, especially Theorem 3.10,
https://arxiv.org/html/1312.3881v4#S3.SS2, and Muro, Section 8 (printed
pp. 1587–1590) and the proof on printed p. 1592,
https://msp.org/agt/2011/11-3/agt-v11-n3-p13-p.pdf. This node has no Stacks
source tag. Haugseng's displayed attaching maps have exactly the alternating
order used here. His theorem has model hypotheses, whereas this node explicitly
states their ordinary algebraic construction separately. Muro's standing
notation assumes completeness, cocompleteness and biclosedness, with symmetry
on V, not C. His free-algebra formula, its summandwise evaluation, and the
algebra-pushout construction precede the additional model hypotheses in
Section 9. I checked the node's fifteen-step argument for this stated algebraic
generality: it only takes the specified colimits and separately colimit-preserving
tensor products; it uses no limits, symmetry or model structure. Its monad,
filtered-diagonal, and word-presentation arguments justify the additional
ordinary assertions. No source hypothesis needed by this construction is missing.

I independently opened the dependency declarations: `MonoidalCategoryStruct`
and `MonoidalCategory` (Monoidal/Category), `HasColimitsOfSize` and the dual
of `HasLimits` (Limits/HasLimits), `Cofan.mk` (Limits/Shapes/Products),
`Functor.IsLeftAdjoint` (Adjunction/Basic),
`Adjunction.leftAdjoint_preservesColimits` (Adjunction/Limits), and
`FreeMonoidalCategory.subsingleton_hom` (Monoidal/Free/Coherence).
I also read `MonObj`, `Mon`, `Mon.Hom`, `Mon.forget`, `Mon.trivial`,
`Monad.Algebra` and its morphisms, `Monoidal.FunctorCategory.tensorObj`,
`LiftableCocone`, `CreatesColimit`, `IsFiltered`, and `Arrow.pushoutProduct`.
These implement the node's notions at the required generality. There is no
unusable dependency, dependency repair, new definition node, statement_change,
or repair note for this item. The auxiliary recursions and the two structures
package only this node's own construction, and are all recorded in
`lean.declarations`; they do not replace any prerequisite notion.

Independent H4 searches, with different phrasing from the worker:

- `msearch.py leanfinder`: “A free monoid object in a cocomplete closed monoidal
  category is the coproduct of finite tensor powers and admits a cellular pushout
  filtration”: eight hits, including `FreeMonoidalCategory.projectObj` and
  `MonCat.FilteredColimits.colimit`; formal monoidal syntax and monoids in Type
  do not state this arbitrary-category theorem.
- `msearch.py loogle`: `"Mon", "adjunction"`: twelve generic adjunction and
  monomorphism hits; no free internal associative algebra or this filtration.
- `msearch.py grep` under CategoryTheory/Monoidal:
  `word.*monad|free.*associative|tensor.*power|tensorPower`: two hits,
  Types/Basic and introductory text in Monoidal/Mon, neither a matching theorem.
- Direct `rg` of upstream WeilConjectures, shared lean/Sheaf, and Mathlib's
  Monoidal directory for `word.?filtration|tensor.?word|free.{0,20}monoid|monoid.{0,20}free|monad.{0,20}tensor`:
  no exact match. I opened the nearby `ArrowCell.HasWordFiltration` in
  DgCategoryFreeCellCalculus: it is a specialized dg-category single-arrow cell,
  using degreewise quotients and retractions, not this general monoidal theorem.
- A second direct search for `tensorPow|tensorPower|tensor_power` and power
  definitions found no existing general tensor-power functor here.
- A parsed full-DAG scan for tensor-word, tensor word, pushout product and word
  filtration found this owner and model/coherent-diagram consumers, no separate
  definition of this same construction. Existing Mon and pushout-product
  interfaces are reused rather than redefined.

Edge cases: `power 0`, `blocks []`, `insertBlocks []`, and `flatten []`
include the empty outer word. Zero entries in lists include empty inner words;
the length-zero free multiplication equations are included. Length one uses
its unitor, length two uses precisely the tensor of that unitor with identity.
The filtration at n=0 starts at A and first attaches q_1, not q_0; direct
expansion at n=1,2 gives j,f,j and j,f,j,f,j without a permutation. For X=0,
positive word powers are initial, so T(0) is the unit algebra. For f an identity
(including X=Y=0), all q_n for n≥1 are isomorphisms and a constant filtration
up to isomorphism is allowed. A can be the unit algebra or a zero algebra when
one exists. A completely empty ambient category cannot meet the monoidal-unit
hypothesis; the theorem makes no unrelated inhabited or nonzero restriction.
Empty filtered index categories are excluded exactly by filteredness; other
empty colimits are allowed. There is no characteristic or scheme hypothesis.
The object universe may differ from the Hom universe; the filtered shapes use
exactly U = v and the countable word and sequence indices fit every v.

H5/H6/H8/H9: every recursive helper has real data (identities, tensor maps,
unitors, associators, or the existing pushout product). No choice is taken from
the final `Nonempty Construction` to define any object. The sole postponed
result is the named main theorem, with its complete fifteen-step node proof
plan and source/blueprint docstring. Every helper has the same source and
blueprint documentation. There are no proved results, local notation, private
definitions, local instances, implicit variables, or lines over 100 columns.
The two proof-only imports match the recorded Mathlib proof prerequisites.
I compared the sandbox node with the read-only base: only `lean` differs.
The main signature extracted from `theorem` through its result is verbatim equal
to `lean.statement`.

Mismatches found: none. I retained the Lean module and node record unchanged;
this second reading adds this independent audit to the report only. Compilation
and delivery-preflight outcomes are recorded below after running the prescribed
wrappers.

Second-reader validation: `scompile.py Q84
lem-coef-associative-word-filtration
lean/Sheaf/CategoryTheory/AssociativeWordFiltration.lean` succeeded for both
sandbox and library module, with no diagnostics (2.1 s and 2.3 s).

The second-reader dry run printed `OK (dry run): commit a883e547d8 passes the
preflight and compiles; nothing pushed`. The wrapper refreshed the base and
excluded an inherited `lean_audit` difference from the delivered delta.
An additional direct `rg` for `AssociativeWordFiltration` and
`tensor_word_free_associative_filtration` in `dag/lean_names_upstream.json`,
upstream WeilConjectures, and shared lean/Sheaf returned no name collision.
