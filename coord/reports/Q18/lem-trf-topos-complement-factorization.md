## Worker report

The module `Sheaf.CategoryTheory.Sites.ToposComplementFactorization` defines the full-subcategory
predicate `CategoryTheory.closedComplementObjects` and states
`CategoryTheory.topos_complement_factorization`. The sole theorem has proof `sorry`.
The predicate is a real definition using Mathlib's binary product and `IsIso`; no datum is
postponed. These are two declarations of the same node's explicitly specified construction,
listed in `lean.declarations`. No new DAG notion or dependency repair is needed.

The statement is unchanged. Its hypotheses and conclusions correspond as follows:

| Node text | Lean rendering |
| --- | --- |
| E is a Grothendieck topos | `E : Type u`, `[Category.{v} E]`, `hE : IsGrothendieckTopos.{w} E` |
| u is subterminal, equivalently a mono into the terminal object | `u : E`, `hu : IsSubterminal u` (Mathlib's mono/terminal characterization was read) |
| E_c is the full subcategory where A × u → u is an isomorphism | `(@closedComplementObjects E _ products u).FullSubcategory`; the predicate is `IsIso (prod.fst : u ⨯ A ⟶ u)`, the same projection after product symmetry |
| E_c is a Grothendieck topos | first `IsGrothendieckTopos.{w}` conjunct |
| j is the slice geometric morphism | `j : GeometricMorphism (Over u) E` and `Nonempty (j.inverse ≅ @Over.star E _ u products)`; Mathlib's `Over.star u` sends A to `(u × A → u)` |
| the slice is a topos | `IsGrothendieckTopos.{w} (Over u)` |
| k has inclusion as direct image | `k : GeometricMorphism ... E` and `Nonempty (k.direct ≅ (...).ι)` |
| both are geometric embeddings | `Nonempty j.direct.FullyFaithful ∧ Nonempty k.direct.FullyFaithful` |
| j is the open subtopos of u | the canonical slice inverse image and full faithfulness, precisely Stacks 08LW and the immediately following open-subtopos definition |
| k is its complementary closed subtopos | the specified full subcategory, inclusion direct image and full faithfulness, precisely 08LY/08LZ/08M0 |
| every Grothendieck topos H | `∀ (H : Type uH) [Category.{vH} H], IsGrothendieckTopos.{w} H → ...` |
| closed essential image is exactly a with inverse image of u initial | the first `∀ a`, its `∃ b` and direct-image natural isomorphism, equivalent to `Nonempty (IsInitial (a.inverse.obj u))` |
| closed identification includes all 2-morphisms | for every closed `b d`, bijectivity of `τ ↦ Functor.whiskerRight τ k.direct` |
| open essential image is exactly a with inverse image of u terminal | the second `∀ a`, its `∃ b` and direct-image natural isomorphism, equivalent to `Nonempty (IsTerminal (a.inverse.obj u))` |
| open identification includes all 2-morphisms | for every slice `b d`, bijectivity of `τ ↦ Functor.whiskerRight τ j.direct` |
| uniqueness up to unique compatible isomorphism | the two Hom bijections uniquely lift an isomorphism between composites; lift its inverse as well, and injectivity forces both inverse identities |

Binary products are supplied by an existential in the conclusion, not an extra hypothesis.
This makes the displayed product projection meaningful without requiring a new global instance
derived from the topos presentation. The source already guarantees these products. There are
no chosen initial/terminal objects or extra existence hypotheses on H: being initial/terminal
is equivalent to being isomorphic to its initial/terminal object. All object, morphism and
presentation universes (`u`, `v`, `uH`, `vH`, `w`) are explicitly bound and independent.

The equivalence of categories is rendered by its exact criterion: full faithfulness on every
Hom set and the specified essential image. Right whiskering preserves identities and
composition by Mathlib's `Functor.whiskerRight_id` and `Functor.whiskerRight_comp`. Thus this
does not weaken the categorical assertion to a bijection of objects. A direct-image natural
isomorphism is precisely an isomorphism under the dependency's 2-morphism convention; its
inverse mate and unit compatibility come from that dependency's adjunction API. No arbitrary
map replaces a canonical construction: j is constrained by the canonical slice inverse image,
k by the actual full-subcategory inclusion, and the 2-morphism maps are actual whiskering.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.Sites.GrothendieckTopos`, `CategoryTheory.IsGrothendieckTopos`,
  imported publicly through `GeometricMorphism`. Its full small-site-presentation definition
  was read, including the independent presentation universe.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`, `CategoryTheory.GeometricMorphism` and
  `CategoryTheory.GeometricMorphism.comp`. Both full signatures and docstrings were read,
  as were `inverseMate` and `inverseIso`. Composition uses the recorded composite adjunction.
- Mathlib: `IsSubterminal`, `Over`, `Over.star`, `ObjectProperty.FullSubcategory`,
  `ObjectProperty.ι`, `Functor.FullyFaithful`, `Functor.whiskerRight`, `IsInitial`, `IsTerminal`.

Proof dependencies already stated in Mathlib are available through the imported geometric
morphism module: `Adjunction.mkOfHomEquiv`, `unit_conjugateEquiv_symm`, and
`Adjunction.rightAdjoint_preservesLimits`. Their source signatures were read. The three
site-presentation proof dependencies currently have no Lean record and supply no imports;
they are not statement prerequisites. All eleven proof steps, including those future inputs,
are preserved in the theorem's source/blueprint docstring. No other module is edited.

Source read: `literature/stacks-project/sites.tex`, from the subtopos definition through
Tags 08LW, 08LY, 08LZ, 08M0 (lines 10100–10265). The closed projection is exactly the one
in 08LY, and its product-order reversal is explicitly documented.

Edge cases checked before writing:

- u initial: E/u is the degenerate topos, the closed subcategory is all of E; the closed
  criterion holds for every a, and the open criterion only for degenerate H.
- u terminal: E/u is E and the closed subcategory is the terminal-object category; the
  open criterion holds for every a, while the closed one requires degenerate H.
- Degenerate E/H and empty presenting site are permitted; no nonemptiness or `0 ≠ 1`
  hypothesis appears. The two essential-image conditions may coincide in the degenerate case.
- Arbitrary topos presentations and independent object/morphism universes remain allowed.
- The maps on 2-morphisms are not restricted to invertible transformations.

Searches made (all through the prescribed `msearch.py` where applicable):

- LeanFinder: `Closed complement of a subterminal object in a Grothendieck topos and
  universal factorization of geometric morphisms`: eight results, mostly classifier
  constructions and sheaf factorization; none asserts the node's statement.
- Loogle: `CategoryTheory.Over, CategoryTheory.Functor.FullyFaithful`: eleven hits including
  `Functor.FullyFaithful.over`, mono-over and scheme forgetful functors. These are general
  tools, not the two complementary topos embeddings or factorization criteria.
- LeanSearch: `Grothendieck topos subterminal open closed complement universal factorization
  geometric morphisms`: eight hits, including `Subterminals` and its terminal-mono
  equivalence, sheaf epi/mono factorization, and topological complements; none matches.
- Mathlib grep: `subtopos|closedComplement|GeometricMorphism` in `CategoryTheory`: zero hits.
- Project grep: `GeometricMorphism|ClosedComplement|closedComplement|sliceGeometric` in
  `lean/Sheaf/CategoryTheory` and the upstream `WeilConjectures/CategoryTheory`: existing
  geometric morphism datum and unrelated oriented/coherent constructions, no complement API.
- Upstream grep for the exact item id: zero hits in `WeilConjectures`.
- Additional Mathlib source search located `Over.star` in `Comma/Over/Pullback.lean` and
  `ObjectProperty.FullSubcategory`/`ι`; their definitions and docstrings were read and reused.
- Duplicate-name searches for `closedComplementObjects` and
  `topos_complement_factorization` in upstream and `lean/Sheaf`: no prior declarations.

No statement dispute or node fault was found. No statement correction, new node or
dependency module is delivered.

Validation: prescribed `scompile.py Q18 lem-trf-topos-complement-factorization <module>`
passed for the sandbox and library-path probes, with no errors or warnings. The first compile
identified the namespace-qualified spelling `Functor.whiskerRight`; the final source uses it.

## Second reading by Q18

A separate reading pass in this worker session reopened the node and the final module; no
sub-agent was started, as required by the dispatch brief. The maintainer performs the
independent review. The hypothesis/clause table above records this pass's comparison.

I checked the existential products binder is a conclusion, the actual full subcategory is
used for k's domain, the slice functor is `Over.star` rather than `Over.forget`, and the
initial and terminal criteria have the correct closed/open directions. I checked that both
Hom bijections quantify over every pair of factors and every natural transformation, so
they imply the stated unique compatible isomorphism, including the compatibility with a
chosen composite comparison. Isomorphisms rather than literal equality of functors encode
the canonical embeddings without changing the mathematical statement. No mismatch was found
on this pass and no mathematical change was needed.
