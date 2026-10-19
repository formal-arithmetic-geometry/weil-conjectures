## Worker report

Repaired the returned stage-2 packet for `lem-trf-coherent-object-approximation`
(returned immutable head `53d4790c3978`, H3). The declaration is
`CategoryTheory.coherentObjectApproximation` in
`Sheaf.CategoryTheory.Sites.CoherentObjectApproximation`. Its only proof is
`sorry`; no definition or additional theorem was introduced.

The saved packet was inspected first and passed the required initial
`deliver2.py NH lem-trf-coherent-object-approximation --no-push`
(commit `21cea47cda`, nothing pushed). That mechanical success did not resolve
the two semantic faults in the return. This repair changes the actual signature
for both faults. The sandbox node was compared with the current shared node;
only `lean` differed. Its natural statement and all other fields remain those
of the current shared node. No statement correction is needed.

Clause-by-clause correspondence:

- The containing category is `E : Type u` with `Category.{v} E`,
  `HasCoproducts.{w} E`, and `HasFiniteLimits E`; the coherent Grothendieck
  topos hypothesis is `hE : IsCoherentTopos.{w} E`. The latter unfolds to the
  recorded Grothendieck-topos and coherent-generator conditions. Explicit
  universes `w u v` and `I : Type w` implement `def-weil-size-convention`.
- Finite coproducts: `n : ℕ` and `X : Fin n → E` range over finite families,
  now explicitly assuming `(∀ i, IsCoherentObject (X i))`. The conclusion is
  coherence of `∐ (fun i : ULift.{w} (Fin n) => X i.down)`. The lift puts the
  index in the coproduct universe without changing the finite family.
- Finite limits: for every `J : Type` with `SmallCategory J` and
  `FinCategory J`, `ObjectProperty.IsClosedUnderLimitsOfShape
  (fun X : E => IsCoherentObject X) J` asserts closure of coherent objects
  under limits of coherent diagrams. The definition of that Mathlib property
  supplies the coherent-diagram hypothesis; this includes the empty diagram.
- Images: for every `f : A ⟶ B`, coherence of both `A` and `B` implies
  existence of `I`, `e : A ⟶ I`, and `m : I ⟶ B`, with `Epi e`, `Mono m`,
  `e ≫ m = f`, and `IsCoherentObject I`. For every mono `d : D ⟶ B`
  through which `f` factors, the conclusion supplies `q' : I ⟶ D` with
  `q' ≫ d = m`. This is precisely the least-subobject characterization.
  Monicity of `d` makes that factorization unique.
- Approximation: for every `G : E`, the hypothesis is
  `IsQuasiSeparatedObject G`. The index is explicitly `I : Type w` with
  `PartialOrder I`, `Nonempty I`, and `IsDirected I (· ≤ ·)`. Mathlib's
  `Preorder.smallCategory` supplies the category of this very order; no
  independent arbitrary category structure is quantified over. A diagram
  `F : I ⥤ E` has `(∀ i, IsCoherentObject (F.obj i))`. Each order transition
  is explicitly an inclusion through
  `(∀ (i j : I) (h : i ≤ j), Mono (F.map (homOfLE h)))`.
  The cocone `c : Cocone F` has `c.pt = G` and monic legs
  `(∀ i, Mono (c.ι.app i))`. Its naturality supplies
  `F.map (homOfLE h) ≫ c.ι.app j = c.ι.app i`, so the transitions are
  inclusions over the common object `G`. The monic legs identify each value
  as a coherent subobject of `G`; no choice of unrelated maps is involved.
  `Nonempty (IsColimit c)` asserts the colimit universal property. A colimit
  cocone with point equal to `G` is equivalent to a colimit isomorphism to
  `G`, with the given inclusions as structure maps.
- The final conjunct quantifies over `m : G ⟶ F`, assumes `Mono m` and
  `IsCoherentObject F`, and gives the same small nonempty directed-poset
  colimit of coherent subobjects of `G`, with monic order transitions.
  It assumes neither quasi-compactness nor coherence of `G`.

The two repairs therefore address every part of H3: coherent summands are
required in the coproduct clause, and both approximation clauses now contain
a partial order, nonemptiness, directedness, its associated category, and
inclusion transitions compatible with the coherent subobjects.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.Sites.CoherentTopos`:
  `CategoryTheory.IsCoherentTopos`, `IsCoherentObject`, and
  `IsQuasiSeparatedObject`, including their full signatures and docstrings.
- `def-weil-size-convention` is recorded as a metatheoretic convention;
  it has no module or declaration. The universes are explicit in this file.
- `def-weil-pbc-category-colimit` records Mathlib's
  `CategoryTheory.Limits.Cocone`, `IsColimit`, `colimit`, `colimit.desc`, and
  `CategoryTheory.IsFiltered`. The statement uses `Cocone` and `IsColimit`
  directly, via `Mathlib.CategoryTheory.Limits.HasLimits`, with filteredness
  expressed by the specified nonempty directed poset.

`Mathlib.CategoryTheory.Category.Preorder` supplies `Preorder.smallCategory`
and `CategoryTheory.homOfLE`; Mathlib's `IsDirected` says any two indices
have a common upper bound. The recorded proof-dependency modules are imported
without `public`; the docstring now spells out all eleven steps of the node's
proof, including least images, finite covers, finite limits, finite extensivity,
finite-subset indexing, local gluing, and the subobject specialization.

Edge cases checked: `n = 0` gives coherence of the empty coproduct with a
vacuous summand hypothesis; `n = 1` requires coherence of the one summand
(the missing hypothesis in the returned packet). Arbitrary noncoherent
summands no longer satisfy the premise. The finite-limit clause includes the
terminal object. Identity and already-monic image maps obey the stated least
property. The directed index cannot be empty, even though directedness alone
would allow that; the proof's finite-subset poset contains the empty subset.
All order arrows, including identities, are addressed by the monic-transition
clause. The empty `G` case can use the singleton poset and the empty coherent
object. A subobject of coherent `F` is never asserted to be coherent itself.

Search evidence from the retained packet: `msearch.py` LeanFinder queried
“In a coherent Grothendieck topos every quasi separated object is a directed
union of coherent subobjects” and returned coherent-topology and directed-cover
results, with no exact theorem. Loogle queried `"coherent", "Subobject"`
and returned no hits. Mathlib grep queried
`coherent.*object|quasi.?separated|quasi.?compact` in `CategoryTheory`, with
no match. LeanSearch queried “Every quasi separated sheaf on a coherent
Grothendieck topos is the filtered union of its coherent subsheaves”; the hits
were generic sheaf and filtered-colimit APIs, not this theorem. The saved
investigation also searched the project `lean/Sheaf` and read-only
`WeilConjectures` sources for coherent-object and image declarations; no
existing exact statement was found. This repair retains that investigation.
For the repair interface I additionally used `rg` and read
`Mathlib/CategoryTheory/Category/Preorder.lean`, `Order/Directed.lean`,
`CategoryTheory/Presentable/Directed.lean` (the analogous existential
partial-order syntax), `Limits/Cones.lean`, and
`ObjectProperty/LimitsOfShape.lean` to verify the exact definitions used.

Validation: the repaired module, including the proof imports and expanded
proof docstring, compiled cleanly through `scompile.py NH
lem-trf-coherent-object-approximation` in both the sandbox and library checks.
Every Lean line is at most 100 characters. `lean.statement` is extracted
verbatim from the theorem signature; `lean.date` is from `date -u +%F`.
No new nodes, dependency modules, natural-statement change, or
`STATEMENT-DISPUTED` issue is introduced.

## Second reading by NH

I reread the current natural node statement, all three statement-dependency
records, the coherent-topos definitions, the complete repaired module, and
the extracted signature. The old finite-coproduct statement had no premise
on `X`; it now has the pointwise coherent premise, including the vacuous
empty-family case. The old approximation statement bound an arbitrary
category with `IsFiltered`; both occurrences now bind a `PartialOrder` and
require nonemptiness and directedness. Their functors use the category of
that order, every order transition is monic, and cocone naturality identifies
it as the inclusion over `G`. Thus the repaired conclusion supplies the exact
directed family requested by the node. The finite-limit, least-image, and
subobject-specialization clauses retain their full hypotheses and conclusions.
Only `lean` changes in the node copy; the proof remains `sorry`.
