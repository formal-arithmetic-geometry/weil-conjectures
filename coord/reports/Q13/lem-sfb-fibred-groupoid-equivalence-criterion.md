## Worker report

The module `Sheaf.CategoryTheory.FibredGroupoidEquivalenceCriterion` states
`CategoryTheory.Functor.exists_cartesian_quasiInverse_of_fibrewise_equivalence`
with a single `sorry`. It also defines the canonical
`CategoryTheory.Functor.mapFiber` by specializing Mathlib's
`Functor.Fiber.inducedFunctor` to the inclusion of the source fibre. This helper
has actual functor data, no choices and no postponed theorem. It belongs to the
induced fibre functor already introduced by the item, and is listed in
`lean.declarations`. No new independent notion or dependency repair is needed.
The original statement and all DAG dependencies are unchanged.

Hypothesis and clause correspondence, checked against the node and Stacks
`categories.tex`, Tag 003Z (`lemma-equivalence-fibred-categories`):

- The larger universe is the explicit `universe u`; `C A B : Type u` with
  `Category.{u}` structures means all objects and Hom sets are small in this
  common universe. `def-weil-size-convention` has a convention-only Lean record
  with no declaration/module; it instructs citers to state the universe choices
  themselves. No coefficient or scheme hypothesis occurs in this abstract node.
- The base category is `C`; the projections are `p : A ⥤ C` and `q : B ⥤ C`.
- Cartesian lifts with prescribed target are given by `[p.IsFibered]` and
  `[q.IsFibered]`. Mathlib defines these using existence of weak cartesian
  lifts and stability under composition, and its
  `Functor.IsFibered.isStronglyCartesian_of_isCartesian` gives exactly the
  arbitrary-base-arrow factorization in this node. Conversely, the node's
  strong cartesian lifts imply that composition stability automatically.
  Thus this does not add a fibration hypothesis beyond the node's definition.
- The fibres are the actual `Functor.Fiber p T` and `Functor.Fiber q T`, whose
  objects are pairs with projection equal to `T` and whose arrows are total
  category arrows satisfying `IsHomLift` over `𝟙 T`. The hypotheses `hp` and
  `hq` assert `IsGroupoid` of each such fibre, which says every fibre arrow is
  invertible. This uses Mathlib's existing notion, not a new private predicate.
- The functor is `G : A ⥤ B`. The equality `hG : G ⋙ q = p` is precisely
  `qG=p` in Lean's diagrammatic composition order, including arrow maps.
- `hcart` quantifies over every base arrow and every total arrow and preserves
  `IsStronglyCartesian`. The adjective strong is necessary: Mathlib's plain
  `IsCartesian` only tests arrows lying over the same base arrow, whereas the
  node quantifies over an additional arbitrary `h : R ⟶ S`. The full strong
  predicate contains uniqueness, not merely existence of a factorization.
- `mapFiber G hG T` is the stated `G_T`. Its object map sends `a` to `G.obj a`
  and its arrow map sends a vertical `v` to `G.map v`. Its equality argument
  is built from associativity, `hG` and `fiberInclusion_comp_eq_const`.
- `hfull` says each fibre Hom map is surjective, and `hfaithful` says it is
  injective. These are exactly the stipulated bijections on fibre morphisms.
- `hessSurj` is `EssSurj` of each actual fibre functor, so its witnesses are
  isomorphisms in the fibre, hence vertical, as required. The orientation of
  the chosen fibre isomorphism is immaterial since it is invertible.
- The conclusion first supplies `H : B ⥤ A` and `H ⋙ p = q`, including strict
  equality on both objects and arrows over the base.
- The next conjunct preserves strong cartesian arrows under `H` for all base
  arrows and all `B` arrows, exactly the cartesian quasi-inverse requirement.
- `e : G ⋙ H ≅ 𝟭 A` is `HG ≅ 1_A`, and `i : H ⋙ G ≅ 𝟭 B` is `GH ≅ 1_B`.
  No triangle identities or uniqueness conditions have been added.
- The last two universal conjuncts state `IsHomLift` of `e.hom.app a` over
  `𝟙 (p.obj a)` and of `i.hom.app b` over `𝟙 (q.obj b)`. This explicitly
  expresses verticality even when object equalities are not definitional.
  The inverse components are also vertical, since a vertical isomorphism has
  vertical inverse; no independent extra hypothesis is required.

Dependency declarations and imports:

- `def-weil-size-convention`: the existing convention record has no declaration
  or module, so there is no import; explicit universes implement it. Read the
  latest blueprint's size-convention statement as well as the node record.
- Proof dependency `lem-sfb-chosen-object-quasi-inverse` is imported as a plain
  proof import `Sheaf.CategoryTheory.ChosenObjectQuasiInverse`; its full
  declaration `CategoryTheory.Functor.exists_quasiInverse_with_objIso` and
  docstring were read. The delivered theorem docstring explains use of its
  prescribed-object and comparison formulas to obtain strict equality over
  the base and the two vertical comparisons.
- Public Mathlib imports: `CategoryTheory.FiberedCategory.Fiber` (`Fiber`,
  `Fiber.fiberInclusion`, `Fiber.inducedFunctor`,
  `Fiber.fiberInclusion_comp_eq_const`); `CategoryTheory.FiberedCategory.Fibered`
  (`Functor.IsFibered`, `Functor.IsStronglyCartesian`, `Functor.IsHomLift`);
  `CategoryTheory.Groupoid` (`IsGroupoid`); `CategoryTheory.Equivalence`
  (natural isomorphisms, `Functor.Full`, `Functor.Faithful`, `Functor.EssSurj`).

Edge cases checked before writing: empty base (both total categories then have
no objects); empty source/target fibres (essential surjectivity excludes an
unmatched nonempty target fibre); terminal base (ordinary groupoid equivalence);
nontrivial base arrows (strong cartesianness is retained rather than checking
vertical arrows alone); multiple objects with equal images (no injectivity on
objects is imposed); non-definitional object equalities (handled by `Fiber` and
`IsHomLift`); nontrivial automorphisms (full faithfulness uses all Hom sets).
No nonemptiness, chosen cleavage, skeleton, discrete-fibre, or finite-size
hypothesis is imposed. There is no statement dispute or statement correction.

Searches performed with the prescribed `msearch.py` (2026-10-24):

- LeanFinder: "A cartesian functor between categories fibred in groupoids that
  is fully faithful and essentially surjective on each fibre has a quasi
  inverse over the base". Eight hits, mainly `HasFibers` and special
  Grothendieck-construction fibre equivalences; none states the criterion.
- Loogle: `CategoryTheory.Functor.IsFibered,
  CategoryTheory.Functor.IsEquivalence`. Zero hits.
- Mathlib grep: `equivalence|IsEquivalence|isEquivalence` in
  `CategoryTheory/FiberedCategory`. Six hits in `HasFibers.lean` and
  `Grothendieck.lean`; these compare a particular fibre model with the actual
  fibre and do not provide a base-preserving inverse for an arbitrary functor.
- LeanSearch: "A fibrewise fully faithful essentially surjective cartesian
  functor between categories fibred in groupoids admits a base preserving
  quasi inverse". Eight hits; ordinary equivalence constructions,
  `HasFibers` and Grothendieck constructions, no exact match.
- `rg` of `lean/WeilConjectures/CategoryTheory`, project
  `lean/Sheaf/CategoryTheory`, Mathlib's fibre API, and the upstream declaration
  index found no theorem giving the required inverse and vertical comparisons.
  A direct search for this node id under `lean/WeilConjectures` found no match.
  Project-wide searches also located the existing `IsFibredInGroupoids` in
  `StablePointedModuliGroupoids.lean`; it uses the equivalent all-arrows-strong-
  cartesian formulation. The present signature directly uses the Mathlib
  fibration and groupoid-of-each-fibre predicates matching the node's own
  formulation; it introduces no competing definition of fibred groupoids.
- Name searches across Mathlib, the project and `dag/lean_names_upstream.json`
  found neither `CategoryTheory.Functor.mapFiber` nor the proposed theorem name.

## Second reading by Q13

I reread the node, the source Tag 003Z, and the complete module after drafting.
This is a second pass by the assigned worker, not a claim of a second agent;
the dispatcher explicitly forbids starting another agent, and the maintainer
provides the independent review. In particular I checked the order of the
composites: Lean `G ⋙ H` has source `A` and is `HG`, while `H ⋙ G` has source
`B` and is `GH`. Both component conditions use the projection of that same
source category. I checked that `hG` and the resulting `H ⋙ p = q` are strict
functor equalities, not merely isomorphisms of projections. I checked that the
fibre helper uses `Fiber p T`, not a chosen equivalent model, and that `EssSurj`
is taken there, so its comparison is vertical. The most significant potential
mismatch was the word "cartesian": the node's factorization matches Mathlib's
`IsStronglyCartesian`, which the draft uses on both input and inverse functors.
The full/faithful/essential-surjectivity clauses and the two vertical natural
isomorphisms all match. No statement correction, dependency repair, or new node
was needed. Only the theorem proof is postponed.

Validation: the prescribed `scompile.py Q13
lem-sfb-fibred-groupoid-equivalence-criterion <module>` completed successfully
on the server for both the sandbox check and the library module, with no errors
or unexpected warnings. The required delivery dry run supplies the separate
record/layout preflight and repeats the per-file compile.
