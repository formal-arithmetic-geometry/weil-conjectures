## Worker report

The module `Sheaf.CategoryTheory.AssociativeAlgebraModelTransfer` states
`HomotopicalAlgebra.associativeAlgebraModelTransfer`, with `sorry` as its entire proof.
`AssociativeAlgebraTransfer` bundles exactly the model-structure conclusions. The theorem
also supplies the already recorded `AssociativeWordFiltration.Construction`; its free functor
and structural formulas are reused, not reconstructed. There is no choice of model-structure
data from an unproved mere existence theorem. The statement is unchanged.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Fixed-universe model category, complete and cocomplete | `M : Type u`, `Category.{v} M`, `ModelCategory M`, `HasLimits M`, `HasColimits M`; smallness universe is `v` |
| Locally presentable, both lifting systems set-generated and functorial | `_hM : CombinatorialModelCategory.{u, v, v} M`, using the published structure |
| Associative unital monoidal category, no symmetry assumed | `MonoidalCategory M`; its associator and unitors satisfy pentagon and triangle |
| Both tensor functors have right adjoints | `_leftAdj`, `_rightAdj`, each `∀ X, ...IsLeftAdjoint` |
| Cofibrant tensor unit | `_unit : IsCofibrant (𝟙_ M)` |
| Pushout product preserves cofibrations and is trivial if either input is trivial | `_pushoutProduct`, using Mathlib `MonoidalCategory.Arrow.pushoutProduct`; the disjunction of weak equivalences supplies the trivial clause |
| Arbitrary-object nonsymmetric monoid axiom | `_monoidAxiom : NonsymmetricMonoidAxiom M`; its generators allow `initial.to X` for every `X : M`, with at least one trivial factor |
| Small continuous transfinite composites, pushouts and retracts | The witnessing class `K` has `IsStableUnderCobaseChange`, `IsStableUnderTransfiniteComposition.{v}`, `IsStableUnderRetracts`, and `K ≤ weakEquivalences M` |
| Strict associative unital algebras and their morphisms | Mathlib `Mon M`, with its existing `MonObj` multiplication/unit identities and multiplication/unit-preserving morphisms |
| Forgetful functor | Mathlib `Mon.forget M`, on objects `A.X` and morphisms `f.hom` |
| Existence of a combinatorial model structure on algebras | `∃ W, Nonempty (AssociativeAlgebraTransfer W)`; fields `model`, `limits`, `colimits`, `combinatorial` |
| Fibrations and weak equivalences exactly created by U | `fibrations_eq`, `weakEquivalences_eq`, both equalities with `inverseImage (Mon.forget M)` |
| Free-forgetful adjunction | `W.adjunction : W.free ⊣ Mon.forget M` |
| Free algebra is the coproduct of all tensor powers, including length zero | `W.freeUnderlying`, `W.ι`, `W.coproduct`; `AssociativeWordFiltration.power 0` is the unit |
| Free multiplication concatenates factors; unit is the zeroth summand | `W.free_mul` uses the existing `concat`; `W.free_one` identifies the algebra unit with `W.ι X 0` |
| Quillen condition | `free_cofibrations` and `free_trivialCofibrations` |
| For any generating cofibrations I and trivial cofibrations J, T(I),T(J) generate the lifting systems | `generating_cofibrations`, `generating_trivialCofibrations`, each quantifying over every small family `Type v → Arrow M`; `ofHoms ... .rlp` equals the respective right class |
| U preserves cofibrant objects | `underlying_cofibrant`; its premise is cofibrancy using the canonical initial algebra `W.initial_algebra`, and its conclusion is `IsCofibrant A.X` |

The initial-map formulation of the last field is equivalent to the chosen-initial-object
formulation: `W.initial_algebra` proves that `Mon.trivial M` is initial, and model
cofibrations respect isomorphisms. No cofibrancy of generating domains or of arbitrary
algebras appears. The witness `W` carries the canonical free-algebra operations and their
already established universal properties, including the filtration; it is supplied by the
existing word-filtration dependency, not imposed as an extra hypothesis of transfer.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction`:
  `HomotopicalAlgebra.ModelInfinity.quillenAdjunctionInfinityLocalization`, with the published
  Mathlib `ModelCategory`/`IsCofibrant` conventions; no infinity-localization assumption is
  imposed on this ordinary transfer theorem.
- `Sheaf.CategoryTheory.CombinatorialLocalizationPresentability`:
  `HomotopicalAlgebra.ModelLocalization.combinatorialLocalizationPresentability` and its
  reexported `HomotopicalAlgebra.CombinatorialModelCategory` (owned by
  `Sheaf.CategoryTheory.ModelColimitLocalizationComparison`). The latter's full fields are
  local presentability, both small generating families and both functorial factorizations.
- `Mathlib.CategoryTheory.Monoidal.Category`: `CategoryTheory.MonoidalCategory`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `CategoryTheory.Limits.colimit`,
  `Cocone`, `IsColimit`; Mathlib supplies the initial maps and all colimit-size conventions.
- `Sheaf.CategoryTheory.AssociativeWordFiltration`:
  `CategoryTheory.AssociativeWordFiltration.Construction`, `power`, `concat`, and
  `CategoryTheory.tensor_word_free_associative_filtration`. Its recorded module, including
  the full construction fields, was read. This already-landed node is added to stmt_deps
  because its construction occurs in the signature.
- Proof imports: `Sheaf.CategoryTheory.AccessibleMonadPresentability`
  (`CategoryTheory.accessibleMonadPresentability`),
  `Sheaf.CategoryTheory.PresentableSmallObjectFactorization`
  (`CategoryTheory.MorphismProperty.hasFunctorialFactorization_of_isLocallyPresentable`),
  `Sheaf.CategoryTheory.PresentableCellularFactorization`
  (`CategoryTheory.SmallObject.exists_cellular_factorization_of_isLocallyPresentable`),
  Mathlib's lifting-class closure and transfinite-left-lifting modules. Their signatures and
  proof docstrings were read. The theorem docstring follows all eight proof steps.

Edge cases checked before finalization:

- `l = []` in the monoid generators means a single factor, which must be a trivial
  cofibration. A zero-factor generator is excluded, as in Muro's `n ≥ 1` definition.
- A list of initial maps with no trivial cofibration fails the explicit existential
  trivial-factor condition. If an initial map itself is trivial it is legitimately allowed.
- A noncofibrant auxiliary `X` is still allowed; no `IsCofibrant X` occurs in the definition.
- Factor ordering is retained by `List.foldl`; no symmetry or permutation is used.
- Continuous chains include the identity/zero-length case and arbitrary small limit
  ordinals through Mathlib's continuous transfinite-composition interface.
- Empty I or J families are quantified without a `Nonempty` condition. Their lifting
  equality is required only when they actually generate the indicated system.
- The zeroth word is present; the free algebra at an initial object includes the unit
  summand rather than an empty coproduct.
- Object and Hom universes remain independent. `Mon M : Type (max u v)` is reflected in
  the transferred combinatorial structure; the small generators and colimits still use `v`.
- Zero/degenerate algebra objects and the initial algebra are not excluded.

Searches performed with `msearch.py NB lem-coef-associative-algebra-model-transfer`:

- LeanFinder: “Associative unital algebras in a nonsymmetric monoidal model category
  satisfying the monoid axiom have a transferred combinatorial model structure” returned
  eight hits about homological-complex tensors, simplicial monoidal structures and
  module/algebra equivalences; no transfer theorem.
- Loogle: `ModelCategory, Mon` returned zero hits, unknown unqualified `ModelCategory`.
- Mathlib grep: `monoid.?axiom|transfer.*model.?structure` returned three irrelevant
  ordinary monoid-axiom comments in `Mon.lean` and `Skeleton.lean`.
- Source and side-library rg for the same terms and the exact item id found no source
  declaration and only the unrelated sorted-simplicial-algebra transfer statement in the
  side-library. Searches by the exact new definition names returned no hits.
- The new definition node contains verbatim msearch results for LeanSearch, LeanFinder,
  and Mathlib grep. Extra DAG/source/side-library searches are recorded there too.
- `blueprint_refs.py search 'monoid axiom'` returned zero blueprint nodes;
  `ancestor` returned `prop-coef-integral-exceptional-adjoint`.

Both delivered modules compile cleanly through `scompile.py`, separately in dependency
order. The sole postponed theorem is the item's theorem. Both definition declarations
have real bodies, and the conclusion bundle is a structure of the advertised data and
properties. No statement correction, disputed statement, or dependency repair is needed.

## New nodes

`def-coef-nonsymmetric-monoid-axiom` defines the hypothesis absent as a standalone notion
from the DAG and Lean libraries. Its module is
`Sheaf.CategoryTheory.NonsymmetricMonoidAxiom`. It defines the finite generators and the
axiom using existing Mathlib pushout products and closure predicates. The witness-class
formulation is precisely the generated-closure formulation: the least closed class is
contained in any witness K, and conversely it itself is a witness when contained in W.
The source is Muro Definition 9.1, printed p. 1591. Muro states cellular acyclicity;
adding retracts is equivalent since model weak equivalences are retract closed. The
three semantic/text search kinds produced no existing definition. DAG hits mention the
axiom as a hypothesis but do not supply its definition. The new node is cited directly
from the item, with ancestry inherited from the finite-level model transfer substep.

## Source error

Opened [Haugseng Section 3.2](https://arxiv.org/html/1312.3881v4) and
[Muro Definition 9.1](https://msp.org/agt/2011/11-3/agt-v11-n3-p13-p.pdf).
Haugseng's printed Definition 3.11 restricts auxiliary objects to cofibrant ones, whereas
the proof of Corollary 3.14 attaches words involving the arbitrary target algebra.
The DAG already specifies the arbitrary-object version from Muro and explicitly rejects
that printed restriction. This delivery keeps the DAG's version unchanged.

## Second reading by NB

Independent maintainer second reading of the NB delivery at immutable commit
`c69ef78711fcd2a552011bffa3cf955acc297ccc`, performed on 2026-10-17. This reader
did not write the delivery or its worker self-check. The complete worker report above
is retained. I read the packet, immutable node records and both delivered modules,
then the exact dependency declarations in the read-only group clone and Mathlib.

All rows of the hypothesis/conclusion table above were independently verified:

- `M : Type u`, `Category.{v} M`, `ModelCategory M`, `HasLimits M`, `HasColimits M`
  and `CombinatorialModelCategory.{u,v,v} M` express the stated complete,
  cocomplete, locally presentable, set-generated, functorially factored model category.
  The latter structure's five fields were read in ModelColimitLocalizationComparison.
- `MonoidalCategory M` is the nonsymmetric structure with associator, unitors,
  pentagon and triangle; both partial tensor functors are left adjoints. There is
  no symmetry, properness, tractability, simplicial enrichment or cofibrant-domain
  hypothesis. The unit and inclusive-or pushout-product hypotheses are exact.
- `NonsymmetricMonoidAxiom` has real definitional content. Its generators are
  nonempty finite left-associated products, every factor permitted by the node,
  with an explicit existential trivial factor. Arbitrary `X : M` are permitted.
  The witness class is closed under pushouts, v-small continuous transfinite
  compositions and arrow retracts, and lies in the weak equivalences. This is
  equivalent to the specified generated-closure formulation.
- Mathlib `Mon M`, `MonObj` and `Mon.Hom` give exactly strict associative unital
  algebras and operation-preserving maps. `Mon.forget M` is the stated U.
- The existential `Construction M` supplies the tensor-word coproduct, the
  zeroth unit summand, concatenation multiplication and the free-forgetful
  adjunction. I read `power`, `concat`, `Construction.coproduct`, `freeUnderlying`,
  `free_one`, `free_mul`, `adjunction` and `adjunction_unit`, as well as its
  filtered-colimit and actual pushout-filtration fields. These characterize the
  free algebra; they do not hide arbitrary data chosen from mere existence.
- `AssociativeAlgebraTransfer` supplies the algebra model structure, all small
  limits and colimits, combinatoriality, exact inverse-image fibrations and weak
  equivalences, and both free-functor preservation clauses. Its two generating
  clauses quantify over every v-small generating family, not just chosen ones.
- `underlying_cofibrant` uses the map from the specified initial canonical unit
  algebra. Mathlib `isCofibrant_iff_of_isInitial` identifies this with ordinary
  cofibrancy in the transferred model. The result is `IsCofibrant A.X` in the
  original model structure, exactly the final conclusion.

Edge cases independently checked: one-factor generators (`l = []`); exclusion of
zero factors and of all-initial-map lists lacking a trivial factor; noncofibrant
auxiliary objects; ordered nonsymmetric factors; identity and limit-ordinal
composites; empty generating families whenever they generate; the empty tensor
word and the initial algebra; zero/degenerate objects. Object and Hom universes
are independent, `Mon M` has object universe `max u v`, and generators, colimits
and transfinite closure all use `v`. No silent universe equality is imposed.

Sources opened: Haugseng, Definitions 3.2 and 3.6, Theorem 3.10, Corollaries 3.14
and 3.15, at https://arxiv.org/html/1312.3881v4; Muro, Definition 9.1 and
Proposition 9.2 through Lemma 9.4, printed pp. 1591-1593, at
https://msp.org/agt/2011/11-3/agt-v11-n3-p13-p.pdf. Muro permits arbitrary auxiliary
objects, unlike Haugseng's printed cofibrant-only version. The immutable node
already chooses Muro's version: there is no stage-2 statement correction or
required correction/citer audit. The blueprint ancestor proof paragraph 2 was
also read; this remains generic algebra transfer supporting that route, with no
pro-etale replacement theorem.

I checked the new definition node's fields, ancestry, dependencies and recorded
LeanSearch/LeanFinder/grep searches. Independent text searches in the group
library, upstream WeilConjectures, Mathlib CategoryTheory/AlgebraicTopology, and
the DAG found no existing nonsymmetric monoid axiom definition or this general
transfer theorem. Ordinary monoids and special simplicial-algebra transfer do
not duplicate this result. Existing notions are reused. The item differs from
the context clone only in `lean` and the permitted `stmt_deps` additions; the
new node supplies the genuinely missing definition. Both delivered
`lean.statement` fields are verbatim signatures from their respective modules.

The source/blueprint module and declaration docstrings are present; the main
theorem docstring follows all eight node proof steps. Both definitions have
real bodies, and the sole theorem's entire proof is `sorry`. There are no
lines over 100 characters, unbound universes, private copies or local instances.

Reproduction command (immutable inputs):

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py NB lem-coef-associative-algebra-model-transfer snapshot/lean/Sheaf/CategoryTheory/NonsymmetricMonoidAxiom.lean snapshot/lean/Sheaf/CategoryTheory/AssociativeAlgebraModelTransfer.lean
```

Exit status 0, no errors or warnings. The prescribed wrapper compiled the
private sibling overlay and each module separately with a 60-second limit.
Final library checks took 0.9 seconds for NonsymmetricMonoidAxiom and 1.8 seconds
for AssociativeAlgebraModelTransfer; overlay/preliminary/sandbox checks also
passed. No global build, live Lean write, direct SSH, Git mutation, delivery or
landing was performed by this reader.

Finding and repair: H11 documentation gap only. The original section openly
recorded a worker self-check rather than an independent reading. This complete
replacement report preserves the worker report and supplies the independent
reading here. No mathematical, Lean-module or node-record correction is needed.
