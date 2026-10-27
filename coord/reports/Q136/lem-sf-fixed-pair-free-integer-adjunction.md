## Worker report

The module `Sheaf.CategoryTheory.FixedPairFreeIntegerAdjunction` states
`CategoryTheory.Endofunctor.IsoAlgebra.fixedPairFreeIntegerAdjunction`.
Its sole proof is `sorry`. It introduces no definitions, auxiliary axioms, new nodes,
or dependency repairs. The item's JSON changes only in `lean`; its statement is unchanged.

The source read is `WeilConjectures/CategoryTheory/Endofunctor/IsoAlgebra.lean`,
namespace `Free`, especially `posObj`, `negObj`, `obj`, `objSucc`, `objMap`, `str`,
`map`, `functor`, `hom`, `desc`, `hom_ext`, and `adjunction` (lines 120--356).
The theorem uses those existing constructions rather than defining them again.
The source's chosen quasi-inverse is `F.inv`, with counit from `F.asEquivalence`;
this is also the choice used by the Lean statement. The full step-by-step proof of
this node is recorded in the theorem docstring.

Hypothesis and clause correspondence:

| Node | Lean rendering |
| --- | --- |
| A category with small morphism sets in a fixed universe | `{C : Type u} [Category.{v} C]`, with the morphism universe `v` independent of the object universe `u` |
| All integer-indexed coproducts | `[HasColimitsOfShape (Discrete ℤ) C]`, requiring precisely these coproducts and no general cocompleteness |
| Autoequivalence with a chosen quasi-inverse | `(F : C ⥤ C) [F.IsEquivalence]`; the existing `F.inv` and `F.asEquivalence.counitIso` supply the chosen inverse and counit used in all orbit terms |
| Integer powers, zeroth power identity, and successor comparison | `Free.obj F M n`, `Free.objMap F f n`, and `Free.objSucc F M n`; their definitions are natural-number recursion for each sign, with `obj F M 0` definitionally `M` |
| The actual fixed-pair category and forgetting | `IsoAlgebra F` and `forget F`, exactly the dependency's recorded declarations |
| A functor into the fixed pairs | The already constructed `Free.functor F : C ⥤ IsoAlgebra F` |
| Its carrier is the sum of integer powers | First conjunct: `((Free.functor F).obj M).carrier = ∐ (Free.obj F M)` for every `M` |
| Its carrier morphism is the coproduct of the iterated maps | Second conjunct: `((Free.functor F).map f).hom.f = Limits.Sigma.map (Free.objMap F f)` |
| Its invertible structure shifts the summands by the canonical comparison | Third conjunct: `F.map (Sigma.ι ... n) ≫ ...str.hom = (Free.objSucc ... n).hom ≫ Sigma.ι ... (n + 1)` |
| The structure is characterized by that formula | Fourth conjunct: every isomorphism `σ` satisfying the injection formula equals the structure of the actual free object |
| Every prescribed zeroth arrow has a unique family indexed by all integers | Fifth conjunct: `∃! a : (n : ℤ) → (Free.obj F M n ⟶ K.carrier), a 0 = a0 ∧ ...` |
| The recurrence for this family | `(Free.objSucc F M n).hom ≫ a (n + 1) = F.map (a n) ≫ K.str.hom`, with composition written in Lean's left-to-right order |
| The free functor is left adjoint to forgetting | Sixth conjunct: `∃ adj : Free.functor F ⊣ forget F, ...` |
| The hom-bijection is restriction to the zeroth summand | First clause under `adj`: `adj.homEquiv M K a = Sigma.ι ... 0 ≫ a.hom.f` |
| Its inverse is induced by the unique recursive family | Second clause under `adj`: for every family `a` with the prescribed zeroth value and recurrence, `((adj.homEquiv M K).symm a0).hom.f = Sigma.desc a` |
| Naturality in the source variable | Third clause under `adj`: restriction of `(Free.functor F).map f ≫ a` equals `f ≫ adj.homEquiv N K a` |
| Naturality in the fixed-pair target variable | Fourth clause under `adj`: restriction of `a ≫ b` equals `adj.homEquiv M K a ≫ (forget F).map b` |
| Conditional additivity with inherited Hom addition | Last conjunct universally binds `[Preadditive C] [HasFiniteBiproducts C] [F.Additive]` and concludes `(Free.functor F).Additive`. These assumptions scope only over the additive clause. The preadditive structure on `IsoAlgebra F` is the existing inherited full-subcategory instance. |

Here biproducts have their usual finite-biproduct meaning for an additive category;
the integer orbit itself uses the explicitly assumed coproduct, and is never replaced
by an integer product. The addition is the inherited addition from
`WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor` (lines 97--106),
which is imported by the source construction. No alternative preadditive structure is
chosen in the statement.

Dependency declarations read and used:

- `def-weil-endofunctor-fixed-pair-category`: the recorded
  `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra`,
  `CategoryTheory.Endofunctor.IsoAlgebra` and `.IsoAlgebra.forget`.
  The full subcategory includes the required invertibility; plain `Algebra F` would not.
- `def-weil-pbc-category-colimit`: the recorded
  `Mathlib.CategoryTheory.Limits.HasLimits`, `CategoryTheory.Limits.colimit`,
  `Cocone`, and `IsColimit`; `Sigma.ι`, `Limits.Sigma.map`, and `Sigma.desc`
  specialize the chosen colimit and its universal property to the discrete integer diagram.
- `def-weil-preadditive-category`: its Mathlib match
  `Mathlib.CategoryTheory.Preadditive.Basic`, `CategoryTheory.Preadditive`.
- `def-weil-pbc-additive-functor`: its Mathlib match
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`, `CategoryTheory.Functor.Additive`.
- Proof dependency `lem-galois-equivalence-preserves-limits`: its matches
  `CategoryTheory.Adjunction.isEquivalencePreservesLimits` and
  `CategoryTheory.Adjunction.isEquivalence_preservesColimits`,
  in `Mathlib.CategoryTheory.Adjunction.Limits`.
- Proof dependency `lem-sf-quasi-inverse-hom-bijection`: its match
  `CategoryTheory.Equivalence.fullyFaithfulFunctor`, in
  `Mathlib.CategoryTheory.Equivalence`.
- Proof dependency `lem-weil-pbc-adjunction-of-natural-bijection`: its match
  `CategoryTheory.Adjunction.mkOfHomEquiv`, in `Mathlib.CategoryTheory.Adjunction.Basic`.

All statement-dependency modules are explicit public imports. The three proof-dependency
modules are explicit ordinary imports. No proof import is omitted for a cycle.

Edge cases checked before writing:

- For `F = id` with identity target structure, the recursion is the constant family,
  and restriction at zero is exactly the coproduct universal map for that family.
- For `F = id` and a nonidentity invertible target structure, the family runs through
  positive powers and inverse powers of that structure. Negative indices must not be
  omitted, and the type uses all of `ℤ` throughout.
- At `n = -1`, `Free.objSucc` is the counit `F(F.inv M) ≅ M`, so the recurrence is
  typed across zero with the required direction. At `n = 0`, it is identity.
- For a zero object in an additive category the orbit sum and arrows are zero, and
  uniqueness and additivity continue to hold. No nonzero or nonempty-object hypothesis
  is used. An empty category is also permitted; quantified object clauses are vacuous.
- The index is the fixed nonempty set of integers. No hypothesis on arbitrary index
  sets, arbitrary products, AB4, abelianness, exactness, or Grothendieck structure is added.
- The main assertions require no preadditivity. Only the final conditional does.

Searches for an existing declaration (2026-10-24):

- `msearch.py ... leanfinder`, query “Free fixed pair of an autoequivalence coproduct
  integer iterates adjunction additive”: eight hits, including `Equivalence.pow` and
  Dold--Kan equivalence comparisons, no full match.
- `msearch.py ... loogle`, query `"IsoAlgebra", "Free"`: zero hits.
- `msearch.py ... grep`, query `IsoAlgebra|objSucc|negHom|Free.adjunction` restricted
  to `CategoryTheory`: sixteen unrelated transfinite/small-object successor hits.
- `msearch.py ... leansearch`, query “The coproduct of all integer powers of an
  autoequivalence is a free fixed pair left adjoint to forgetting, and this free
  functor is additive”: eight hits, including `Adjunction.left_adjoint_additive`
  and the free (commutative) monoid/group adjunctions. These are ingredients, not
  the integer-orbit theorem with its displayed normalizations and unique family.
- `rg` of `lean/WeilConjectures` for `Free.adjunction`, `IsoAlgebra`, `objSucc`, and
  the item id located the source construction and its derived consumers. There is
  no existing declaration aggregating all clauses. The derived `Free` additivity
  instance is under `[Abelian C]` and `[HasExactColimitsOfShape (Discrete ℤ) C]`,
  whereas the present additive clause assumes neither.
- `rg` of `lean/Sheaf` found `EquivalenceOrbitInduction` and
  `FixedPairDerivedForgetComparison`. The former assumes a Grothendieck abelian
  category and the latter has abelian/derived hypotheses; neither states the
  present result for arbitrary categories with integer coproducts and its precise
  conditional additive clause.
- `rg` of `dag/lean_names_upstream.json` and the source for the item id and proposed
  new declaration name found no declaration collision. The current blueprint does
  not carry this auxiliary node id; its node records synthetic ancestry and points
  directly to the Free source construction.

Validation: every compile used the prescribed `scompile.py` server wrapper. An initial
compile exposed the root `Sigma.map` name collision; the statement now uses
`Limits.Sigma.map`. The second compile passed both sandbox and library checks, with
no errors or unexpected warnings. The inverse formula was also checked in the stronger
explicit form covering every family satisfying the node's recursion, not just an
uncharacterized selected family. Final delivery validation is recorded by the dry run.

No statement correction, disputed statement, missing notion, or dependency interface
fault was found. There are no new nodes or dependency modules.

## Second reading by Q136

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
