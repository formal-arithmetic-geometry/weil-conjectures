## Worker report

Repair of returned stage-2 head `791d049fd0f9`, H3. The retained packet was first
checked with `deliver2.py ND lem-coef-walking-module-weight-cells --no-push`:
it passed mechanically as `2a8b14149c`, but still had the mathematical defects
identified in the return. This delivery replaces its existential action,
vertex-only characterization of the map, and simplicial-set cell-complex
predicate. The node's mathematical statement, dependencies and proof are
unchanged; only its `lean` record changes.

The module `Sheaf.CategoryTheory.WalkingModuleWeightCells` defines the canonical
ordinal-sum action, the adjoining-last map on complete nerve chains, the regular
and empty module arrows, and the free module boundary cells. Its main theorem
`SSet.Enhanced.walking_module_weight_cells` has `sorry` as required at stage 2.
Named auxiliary theorems postpone precisely the well-definedness, naturality,
equivariance and module laws needed by the concrete constructions. They have
source/blueprint and natural-language proof docstrings and are all listed in
`lean.declarations`. No definition chooses unspecified data from a postponed
existence theorem.

Clause-by-clause comparison with the node:

- There are no external mathematical hypotheses. `universe u` is explicit and
  `autoImplicit` is false. The finite ordinal nerves are the dependency's
  `coherentMonadIndex.{u}` and `coherentAlgebraWeight.{u}`; the latter uses exactly
  `CoherentAlgebraOrdinals`, the wide subcategory of nonempty ordinals whose
  maps preserve the last element.
- The simplicial monoid structure is `coherentOrdinalMonoid`: its unit is
  `SSet.const coherentMonadEmpty` and its multiplication is the recorded
  `coherentMonadMultiply`. The named `coherentOrdinalMonoid_laws` supplies its
  unit and associativity proof fields.
- The specified left action is `coherentAlgebraAction`, not an existential
  variable. `coherentActionObj` concatenates the first ordinal with the second,
  and `coherentActionHom` concatenates their maps. Its empty-first-block cases
  are explicit, including the right block inclusion when that block grows from
  empty to nonempty. `coherentActionComposable` applies this to every object and
  arrow of a chain, and `coherentAlgebraActionApp` lifts the resulting chain to
  the recorded nerves. Naturality is a named theorem. The concrete action is
  installed by `coherentWeightModObj`, with its unit and associativity laws.
- The specified map j is `coherentAdjoinLast`. `adjoinLastSimplexFunctor` reuses
  the dependency's `appendLast`, which acts by the old map on old points and
  sends the new last point to the new last point. `adjoinLastFunctor` extends
  it to the empty ordinal, sending it to the singleton and its outgoing maps
  to the singleton selecting the new last point. Applying `nerveMap` and the
  existing `SSet.uliftFunctor` fixes j in every degree, on all arrows as well
  as vertices.
- `coherentAdjoinLast_equivariant` states the exact action-compatibility square.
  It makes `walkingRegularToWeight` a morphism from `Mod.regular D` to
  `walkingWeightModule`, with underlying map the fixed j. There is no arbitrary
  map or action to choose.
- The vertex-bijection clause is
  `Function.Bijective (coherentAdjoinLast.{u}.app (op ⦋0⦌))`.
- The absolute arrow is `walkingEmptyToWeight`, from `walkingEmptyModule` to
  `walkingWeightModule`. The former is the empty simplicial set with its unique
  action, using Mathlib's `Mod.trivialAction`; `walkingEmptyModule_laws` states
  its initiality and the required equivariance of `initial.to W`.
- `walkingFreeCell n` now reuses the existing `CategoryTheory.Mod.free D` functor:
  it is `(Mod.free D).map (SSet.boundary n).ι`. Its source and target are the
  free modules on the boundary and standard simplex. The upstream action is
  multiplication on the first factor, so the map is precisely
  `D × ∂Δⁿ → D × Δⁿ`, for every `n : ℕ` including zero.
- Both cellularity conclusions use `IsWalkingProjectiveCellComplex`, whose
  source and target are objects of `CategoryTheory.Mod SSet D`. It asserts
  `Nonempty (RelativeCellComplex ... f)` with the constant family of these
  `walkingFreeCell n` arrows. The well-ordered stage type and coproduct index
  sizes are `Type u`, retaining small transfinite compositions. Mathlib's
  structure supplies a well-order-continuous diagram, its colimit identified
  with the target, its bottom identified with the source, and an `AttachCells`
  structure at each successor. These are pushouts of coproducts in the module
  category itself. The two final conjuncts apply it respectively to
  `walkingEmptyToWeight` and `walkingRegularToWeight`.
- The concluding cellular-weight assertion is this absolute free-module
  cell-complex condition: weights for the specified one-object simplicial
  category are left D-modules. The main docstring also explains the actual
  dimension filtration: the absolute case begins with the empty module and
  its zero-cell, while the relative case begins with j(D), the dimension-zero
  stage, and uses the remaining positive-dimensional cells.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.CoherentMonadModules`:
  `SSet.Enhanced.coherentMonadIndex`, `coherentMonadEmpty`,
  `coherentMonadMultiply`, `coherentTopMaps`, `CoherentAlgebraOrdinals`,
  `coherentWeightInclusion`, `coherentAlgebraWeight`. Their objects and
  ordinal-sum implementation are reused, not redefined.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`, imported transitively by the
  preceding recorded dependency: `SSet.Enhanced.appendLast` supplies the full
  finite ordinal-map extension. The recorded `coneCategory` signature and
  docstring were read; this item does not require choosing an enhanced diagram
  or cone and imposes no such additional parameter.
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Mod` and its imported
  `Mathlib.CategoryTheory.Monoidal.Mod`: `MonObj`, `ModObj`, `Mod`,
  `Mod.Hom.mk'`, `Mod.regular`, `Mod.trivialAction`. These give the existing
  category of modules and equivariant morphisms.
- `Mathlib.AlgebraicTopology.RelativeCellComplex.Basic`:
  `HomotopicalAlgebra.RelativeCellComplex`; its `TransfiniteCompositionOfShape`
  and `AttachCells` interfaces were inspected to check continuity, small
  coproducts and pushouts. No private replacement category was introduced.

Edge cases checked: the empty ordinal acts as the unit; an empty first block
can map to a nonempty one; the impossible reverse map is eliminated, not
silently invented. The empty ordinal maps under j to the singleton, and j
sends a k-element ordinal to a (k+1)-element ordinal, giving the stated vertex
bijection. The singleton and all last-preserving maps are retained. The
zero-dimensional cell uses `boundary 0`, and the relative filtration is
permitted to use only positive-dimensional cells. A countable filtration and
finite/countable coproduct families fit `Type u` even at `u = 0`.

A finite-ordinal model in sandbox `scratchpad/ordinal_edge_check.py` checked
428 adjoining-last composition equations, 1,225 adjoining-last equivariance
equations, 665 action top-preservation equations, and 5,220 action composition
equations, with ordinal sizes up to three (and unit/identity checks through
size four). Every check passed, including empty blocks. This checks the
construction's edge cases, not the postponed cellularity proof.

Searches made before adding these constructions:

- `msearch.py ... leanfinder` with “Relative projective cell complex in left
  simplicial modules over a simplicial monoid with free boundary simplex
  attaching maps” returned generic `RelativeCellComplex`, `AttachCells`, and
  unrelated Dold–Kan/classifying-space interfaces, with no exact theorem.
- `msearch.py ... loogle` with
  `CategoryTheory.Mod, HomotopicalAlgebra.RelativeCellComplex` returned zero hits.
- `msearch.py ... grep` with `ModObj|RelativeCellComplex|appendLast` in
  `CategoryTheory/Monoidal` located the existing `ModObj` and `Mod.trivialAction`
  interfaces; these are used. The maintainer's independent search additionally found the general constructor
  `CategoryTheory.Mod.free` in upstream `WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian`.
  Its free section does not assume additivity or abelianness. The corrected file
  imports and uses it, removing the duplicate construction.
- `rg` in Mathlib, upstream `WeilConjectures/`, and project `lean/Sheaf/`
  located the dependency's existing `appendLast`, which replaced a draft
  duplicate. Searches for the new walking-weight names and the item id found
  no existing exact result. The original packet's LeanSearch queries likewise
  found generic nerve and simplicial-object declarations only.

The online source was opened and checked:
[Riehl–Verity, Homotopy coherent adjunctions and the formal theory of monads](https://emilyriehl.github.io/files/adjunctions.pdf),
Definition 6.1.6 specifies the ordinal-sum module; Lemma 6.1.8 treats its
cofibrancy. Corollary 6.2.3 and Observation 6.2.4 assert the relative projective
cell presentation; Remark 6.2.5 identifies adjoining the terminal singleton.
Proposition 5.3.3 supplies the free-cell interpretation. These agree with the
node and the repaired module. No statement correction or dispute is needed.

The final module was compiled through the required `scompile.py` wrapper:
clean, with no errors or unexpected warnings. The node's recorded signature
matches the file verbatim; all 28 retained declarations are listed. Scratchpad
checks are not delivered as Lean modules.

## Second reading by ND

This is a substantive second pass in this worker session, with the node,
returned packet and repaired file open. The dispatcher explicitly forbids
starting another agent; this section does not claim another worker reviewed
it. The maintainer's independent delivery review remains separate.

The returned version had three concrete mismatches. First, its relative cell
complex lived in `SSet`, allowing non-equivariant stage maps and pushouts. The
new predicate has binders `A X : Mod SSet coherentMonadIndex`, and each basic
cell is constructed by `Mod.Hom.mk'`. Following the types through
`RelativeCellComplex.attachCells` now places the entire filtration in that
category, including its continuity and target colimit. Second, the old action
was existential: the new action has fixed ordinal-sum data on all arrows,
including the empty-to-nonempty case. Third, the old j was constrained only on
vertices: it is now the nerve of the explicit adjoining-last functor, whose
map is the existing `appendLast` on nonempty ordinals and the last-point
singleton map on the empty-source case. Equivariance refers to these fixed
constructions.

I also checked that the free-cell action multiplies the two D factors and
leaves K unchanged; using a trivial action on D × K would have reproduced a
different projective-cell notion. The empty module's trivial action is valid
because its underlying set is empty. The relative source is the regular
module with the recorded multiplication, not merely the same underlying
simplicial set endowed with another action. The monoid laws and action laws
all share the explicit universe u; a draft's unconstrained law universes were
replaced with explicit `.{u}` arguments. Every data field of a definition is
concrete; only named proposition-valued laws are postponed.

Finally I checked the main theorem against each clause above and reread the
normal-form proof in the node: maximal compatible cuts, reduction under
Eilenberg–Zilber factorization, dimension-bounded submodules, earlier
boundaries, the identification j(D) = X₀, and the union at ω are all covered
in the main proof docstring. The statement asserts the existence of the
module filtrations using Mathlib's full structure, rather than merely
simplicial monomorphisms or cofibrancy as an unspecified retract. I found no
remaining mismatch requiring a node statement change.


## Maintainer independent second reading, 2026-10-17

Reviewed immutable head `58e8a253b39da4f4ee060301752487fd80d4b903` from its
snapshot, independently of the worker's self-review above. The original worker
report and its clause-by-clause reading are retained, with free-cell references
updated for this correction.

Finding H4: the original `walkingFreeAction`, `walkingFreeAction_laws`,
`walkingFreeModule`, and `walkingFreeCell_equivariant` duplicated the existing
upstream free-module construction. Removed those four declarations. The
remaining `walkingFreeCell` is just the upstream free functor on the boundary
inclusion. The node's mathematical statement, dependencies, main signature,
and canonical monoid/action/adjoining-last map are unchanged. Added a module
API list and updated the complete declaration record.

Read the node and both statement-dependency records; opened
`CoherentMonadModules` and `EnhancedDiagramsCones` and the exact ordinal-sum,
append-last, module and relative-cell APIs. The action is the left prepend
action in all degrees, j is adjoining the last point in all degrees, the
relative source is the regular module, and all stages and colimits are in
`Mod SSet D`. `RelativeCellComplex` includes well-order continuity, source
identification, target colimit, and successor pushouts of small coproducts.
No extra mathematical hypothesis or universe equality is imposed.

Checked empty ordinals and empty sources, singleton targets, zero cells,
empty coproducts, the regular submodule X₀, and continuity at ω. The maximal-cut
normal form and its compatibility with degeneracies and proper faces justify
the advertised dimension filtration; no pro-etale notion is used. Every
retained theorem body is exactly `by sorry`; all definitions supply real data
and named law theorems. The main proof docstring carries all five proof stages.
The proof-only orbit-filtration node has no Lean record in the read-only group
clone and therefore has no module import to add at this stage.

Source checked online: Riehl--Verity, Definition 6.1.6, Lemma 6.1.8,
Proposition 5.3.3, Corollary 6.2.3 proof, Observation 6.2.4, and Remark 6.2.5
(for the explicit adjoining-last identification). No statement correction or
citer audit is required.

Compiler reproduction: the prescribed `scompile.py ND
lem-coef-walking-module-weight-cells <file>` returned exit 0 for both the
immutable snapshot and the corrected complete module, with sandbox and library
checks each clean (original: 1.6 s / 1.8 s; final corrected file: 1.7 s / 6.8 s). The installed wrapper uses a
server-side private overlay rather than the older local-overlay route in the
brief. No direct SSH command, global build, live Lean write, clone edit, Git
mutation or delivery command was run by the reviewer.
