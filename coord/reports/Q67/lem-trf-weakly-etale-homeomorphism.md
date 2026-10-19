## Worker report

The earlier sandbox attempt was checked against the current shared node, its three
statement dependencies, and their exact source signatures. No existing declaration
states the item, so this delivery supplies the statement module
`lean/Sheaf/AlgebraicGeometry/WeaklyEtaleUniversalHomeomorphism.lean` and the item's
`lean` record. No statement, dependency, proof, source, or split metadata is changed.
The module states
`AlgebraicGeometry.isIso_of_weaklyEtale_of_universalHomeomorphism` with proof `sorry`.

The node's objects and clauses render as follows.

- The schemes `V` and `W` are `{V W : Scheme.{u}}`, with the universe `u` explicitly
  bound. A morphism is `(f : V ⟶ W)`, using `AlgebraicGeometry.Scheme.Hom`.
- The hypothesis that `f` is weakly etale is the typeclass binder `[WeaklyEtale f]`,
  exactly the recorded Mathlib declaration
  `AlgebraicGeometry.WeaklyEtale`; its two fields are flatness of `f` and flatness of
  `pullback.diagonal f`.
- The hypothesis that `f` is a universal homeomorphism is
  `(hf : (topologically IsHomeomorph).universally f)`. Here `topologically` is the
  recorded construction on scheme morphisms and `universally` quantifies over every
  pullback square, so the underlying map of every base change is a homeomorphism.
  This is the exact interface recorded by `def-weil-universal-homeomorphism`, rather
  than the separate upstream class with the same mathematical name.
- The conclusion that `f` is an isomorphism is `IsIso f`.

Dependency declarations read and used:

- `def-pc-scheme`: Mathlib's `AlgebraicGeometry.Scheme` and `Scheme.Hom`, imported
  through the morphism modules.
- `def-weil-weakly-etale-morphism`: Mathlib's
  `AlgebraicGeometry.WeaklyEtale` in
  `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`; the source signature is the
  class with fields `flat : Flat f` and `flat_diagonal : Flat (pullback.diagonal f)`.
- `def-weil-universal-homeomorphism`: Mathlib's
  `CategoryTheory.MorphismProperty.universally`,
  `AlgebraicGeometry.topologically`, and `IsHomeomorph`, imported from
  `Mathlib.CategoryTheory.MorphismProperty.Limits` and its public dependencies.
  The node records `(topologically IsHomeomorph).universally f` as the exact
  declaration-level rendering.

The module has no definitions with data and no auxiliary theorem; the one statement
has the expected `sorry`. Its docstring records the seven proof steps and all proof
nodes from the stage-1 split: weak etale flatness and universal-homeomorphism base
changes give flatness, surjectivity, and universal injectivity; the affine and
separatedness consequences give a flat surjective quasi-compact diagonal; the
fibre-product monomorphism calculation and fpqc descent make the diagonal an
isomorphism; the same calculation and descent then make `f` an isomorphism.

Edge cases checked before writing:

- Empty schemes are admitted; no nonemptiness or surjectivity assumption is added to
  the statement (surjectivity is a consequence used by the proof).
- Identity morphisms satisfy both hypotheses and the conclusion.
- `Spec k → Spec (k[ε]/(ε²))` is a closed underlying homeomorphism and hence fits the
  universal-homeomorphism interface, but is not flat, so it is correctly excluded by
  `[WeaklyEtale f]`.
- A nontrivial purely inseparable field extension is a universal homeomorphism but its
  diagonal is not flat, so it is excluded by weak etaleness.
- No Noetherian, finite-presentation, reducedness, characteristic, or field
  hypothesis is introduced, and `u` is arbitrary.

Searches for an existing declaration or duplicate notion:

- `msearch.py leanfinder` query `A weakly etale morphism of schemes which is a universal
  homeomorphism is an isomorphism`: eight hits (stalkwise/isomorphism and etale facts),
  no exact item theorem.
- `msearch.py loogle` query `WeaklyEtale, IsHomeomorph, universally, IsIso`: zero hits;
  Loogle reports unknown identifier `WeaklyEtale`.
- `msearch.py grep` query
  `WeaklyEtale.*universally.*IsHomeomorph|isIso.*WeaklyEtale` in
  `Mathlib/AlgebraicGeometry`: zero hits.
- `msearch.py leansearch` query `A weakly etale universal homeomorphism of schemes is an
  isomorphism`: eight hits about isomorphisms inducing homeomorphisms and etale
  morphisms; no exact item theorem.
- Direct `rg` over `lean/Sheaf` and the read-only upstream
  `WeilConjectures` checkout for the item id and weakly-etale/homeomorphism/isomorphism
  vocabulary found no declaration. The existing upstream class
  `AlgebraicGeometry.IsUniversalHomeomorphism` was not used because the dependency
  node explicitly records the inline Mathlib universal construction.

## Worker self-check

I reopened the shared item node, the three dependency nodes, the exact Mathlib source
signatures, and the newly written module. The theorem has exactly the node's two
hypotheses and one conclusion: `Scheme.{u}` objects `V,W`, a morphism `f`, weak
etaleness, the recorded universal-homeomorphism property, and `IsIso f`. No clause,
object, universe case, or hypothesis was added or dropped. The `lean` record's
statement is verbatim the declaration signature, with `existing: false`, module,
file, declaration, branch, worker, and UTC date fields. The file compiles cleanly with
`scompile.py`; the only postponed proof is the expected `sorry`.


The recorded Mathlib proof-dependency modules are imported non-publicly, including
`FlatDescent`, `Affine`, `Separated`, `Proper`, `ClosedImmersion`, `Integral`,
`UniversallyClosed`, `UniversallyInjective`, `UnderlyingMap`, and scheme `Limits`.
They provide the exact proof plan while the theorem remains `sorry`.
The source statement and proof were read both in local Stacks
`more-morphisms.tex`, label `lemma-weakly-etale-universal-homeomorphism` (Tag 0F6V),
and in the current `main-20261015` blueprint lemma and proof files.
No statement dispute, new node, or dependency interface repair is needed.

## Completion check by the resumed worker

The shared node and the delivered copy differ only in `lean`. The UTC date is
2026-10-17. There is no repair note for this item. I reread Stacks
`more-morphisms.tex`, lines 19190ff., and the current blueprint statement and proof
under `main-20261015/blueprint/sec-six-functors-basics/`. Both state exactly the
theorem above. The seven-step docstring follows the reviewed DAG proof, which
implements the same diagonal-then-descent argument. No correction is needed.

I repeated the duplicate search with `msearch.py`:

- LeanFinder, `A weakly etale universal homeomorphism of schemes is an isomorphism`:
  eight auxiliary etale declarations; no exact theorem.
- Loogle, `AlgebraicGeometry.WeaklyEtale, CategoryTheory.IsIso`: zero hits.
- Grep, `isIso.*[Ww]eakly|[Ww]eakly.*[Hh]omeomorph`, restricted to
  `AlgebraicGeometry`: zero hits.
- Direct `rg` for the item id, the proposed declaration name, and both orderings
  of weakly-etale/homeomorphism wording over Mathlib algebraic geometry, upstream
  `WeilConjectures`, and shared `lean/Sheaf`: no hits.

The prescribed `scompile.py` command compiled both its sandbox check and the
library-path check successfully, with no compiler messages. The independent
second reader is still to complete their reading before delivery.


## Second reading by Q67

I independently read the shared node and sandbox node, the complete Lean module,
all three statement-dependency nodes and their actual Mathlib declarations. I read
`literature/stacks-project/more-morphisms.tex`, the section beginning at line 18863,
Definition `definition-weakly-etale` (094P), and Lemma
`lemma-weakly-etale-universal-homeomorphism` at line 19190 (0F6V), including its proof.
I also read `morphisms.tex`, Definition `definition-universal-homeomorphism` (04DD),
and the current `main-20261015` blueprint statement and proof in
`sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/`.
The Stacks section imposes no base, characteristic, Noetherian, finite-presentation,
separatedness, or other standing assumption. Its lemma and the blueprint agree
with the unchanged node.

The complete object/hypothesis/conclusion list, matched independently:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Arbitrary schemes V and W | `{V W : Scheme.{u}}`, with `universe u` | Exact. |
| A scheme morphism f from V to W | `(f : V ⟶ W)` | Exact. |
| f is flat | `[WeaklyEtale f]`, field `WeaklyEtale.flat` | Exact. |
| Its diagonal into V ×_W V is flat | Same hypothesis, field `WeaklyEtale.flat_diagonal` | Exact. |
| Every base change of f is a homeomorphism on underlying spaces | `(hf : (topologically IsHomeomorph).universally f)` | Exact. |
| f is an isomorphism of schemes | `IsIso f` in the category `Scheme.{u}` | Exact. |

For `def-pc-scheme`, I opened `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`
extends `LocallyRingedSpace` with the local affine condition, `Scheme.Hom`
extends the locally ringed space morphism, and the category instance uses these
morphisms. These are the node's schemes and morphisms, not topological spaces or
affine schemes alone. For `def-weil-weakly-etale-morphism`, I opened
`Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`: its class has exactly the two
flatness fields above; it does not require finite presentation or ordinary etaleness.
For `def-weil-universal-homeomorphism`, I opened all recorded declarations:
`CategoryTheory.MorphismProperty.universally` (Limits.lean:872) quantifies over
all pullback squares with arbitrary schemes X',Y'; `AlgebraicGeometry.topologically`
(Constructors.lean:259) applies the property to the underlying function; and
`IsHomeomorph` (Homeomorph/Defs.lean:511) requires continuity, openness and bijectivity.
Thus it is a homeomorphism, not merely a continuous bijection. Quantification over
all choices of pullback is equivalent to the source's canonical base changes,
since homeomorphism is invariant under isomorphism. The identity base change is
included, so the hypothesis also implies surjectivity of f itself.

I additionally opened upstream
`WeilConjectures/AlgebraicGeometry/Morphisms/UniversalHomeomorphism.lean`.
Its class uses integral, universally injective, surjective morphisms and supplies
a comparison into the universal topological predicate. This is an existing
alternative interface, not an exact theorem for this item. The delivery correctly
uses the dependency node's already recorded inline predicate without defining a
second notion or adding an integrality assumption.

The quantifiers are in the same order: arbitrary V,W and f, the two properties of
that f, then its invertibility. Universal base changes occur inside the second
hypothesis, as in the source. There are no additional inferred structure binders.
`set_option autoImplicit false` and the explicit universe declaration rule out
unbound variables. The common arbitrary scheme universe is Mathlib's category
encoding, not a fixed small universe or an unrelated test universe; base changes
range over the same `Scheme.{u}` category and include f's own source and target.

Edge cases: both empty schemes and their unique isomorphism are included. A map
from the empty scheme to a nonempty scheme fails the universal-homeomorphism
hypothesis already at the identity base change; a map to the empty scheme forces
its source empty. Affine schemes of the zero ring are therefore covered. Identities
are covered. Non-surjective open immersions show that weak etaleness alone is
insufficient; nilpotent closed thickenings such as Spec k → Spec k[epsilon]/(epsilon²)
show why an underlying universal homeomorphism alone is insufficient. Nontrivial
purely inseparable field extensions fail flatness of the diagonal. Arbitrary
characteristic and non-Noetherian schemes are admitted. There is no index family,
cohomological degree, or natural-number parameter, so the empty-index and n=0
checks impose no additional condition.

Independent duplicate searches, using vocabulary beyond the first worker's:

- `msearch.py leanfinder`: "A universally bijective integral morphism that is flat
  and has flat diagonal is an isomorphism". Eight results, including
  `AlgebraicGeometry.Flat.isIso_of_surjective_of_mono`, fpqc descent and universal
  injectivity of the diagonal; none states this item. The flat-monomorphism theorem
  assumes monicity, which is a substantive intermediate conclusion here.
- `msearch.py loogle`: `AlgebraicGeometry.WeaklyEtale, CategoryTheory.IsIso`.
  Zero results.
- `msearch.py leansearch`: "A weakly etale radicial surjective morphism of schemes
  is an isomorphism". Eight results about flat monomorphisms, open immersions and
  reduced-target closed immersions; no exact item.
- Direct `rg` over the pinned Mathlib, upstream `WeilConjectures`, shared
  `lean/Sheaf`, and `dag/lean_names_upstream.json` for the proposed declaration,
  tag 0F6V, weakly-etale/isomorphism, and weakly-etale/homeomorphism or radicial
  combinations; also a multiline search with up to three intervening lines.
  The hits concern site invariance, unrelated ring statements or comparison
  modules, not this theorem. The proposed full declaration name is absent.

No new definition node or dependency module is delivered, so there is no new-node
or dependency-interface repair to audit. No maintenance repair note exists for the
item. Comparing the two JSON records shows that only `lean` changes; there is no
statement correction and hence no correction-citer audit is required. I checked
by eye that `lean.statement` is verbatim the theorem signature in the module.

The module and theorem docstrings both name Stacks 0F6V and the correct blueprint
id. I matched each of its seven numbered proof paragraphs to the corresponding
DAG proof step: flatness and universal injectivity/surjectivity; affine and separated
consequences; quasi-compact monic diagonal; the elementary self-pullback calculation;
fpqc descent for the diagonal; monicity of f; and fpqc descent for f. Each paragraph
records the relevant node ids. The non-public proof imports implement those DAG
leaves, as stage 2 requires. There is one theorem with proof `sorry`, no proved
auxiliary result and no definition containing postponed data. The namespace,
imports and line widths follow the conventions.

Mismatches found: none. I preserved the Lean source, signature, node statement and
dependency list; the only second-reader edit is this independent review report.

Validation: the prescribed `scompile.py Q67 lem-trf-weakly-etale-homeomorphism`
command with the sandbox module's absolute path succeeded for both its sandbox
and library-path checks (1.5 s and 1.6 s). There were no compiler messages.
A literal signature comparison and a 100-character Lean line-width check also pass.
