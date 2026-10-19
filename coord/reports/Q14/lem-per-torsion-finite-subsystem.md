## Worker report

The module `Sheaf.DeligneLaumon.TorsionFiniteSubsystem` states
`AlgebraicGeometry.Scheme.torsion_local_system_finite_subsystem`. Its sole theorem has
proof `sorry`. No definition or helper theorem is introduced, and the source node is
changed only in `lean`.

Source checked directly: ILO, Travaux de Gabber, Exposé XVII, Definition 7.2.1 and
Proposition 7.2.3 (printed p. 301), and the proof of Lemma 7.2.6 (printed p. 303).
The latter indexes finite local subgroup systems by inclusion when extending the
structural group of a torsor. The theorem here states the subgroup exhaustion used
there. The docstring carries the node's four `proof` steps with the nodes they use
(lem-per-set-local-system-calculus, lem-galois-flc-representable,
lem-per-finite-torsion-generated-subgroup, lem-weil-pbc-finite-local-abelian-forget);
no proof imports are added at stage 2.

Hypothesis and clause correspondence:

| Node text | Lean |
| --- | --- |
| Noetherian scheme X | `(X : Scheme.{u}) [IsNoetherian X]`; Mathlib's class extends exactly `IsLocallyNoetherian X` and `CompactSpace X`. |
| Abelian sheaf on the small etale site | `G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`. |
| Underlying set sheaf is a local system | `hG : IsIndFiniteEtaleSheaf ((sheafCompose ... (forget AddCommGrpCat)).obj G)`, using the recorded ind-finite definition, not ordinary locally constant sheaves. |
| Each element of each geometric stalk is torsion | `htorsion` quantifies over every `Ω : Type u`, its `Field` and `IsAlgClosed` structures, every `t : Spec (.of Ω) ⟶ X`, and every element `g` of `pointedEtaleStalk G t`; it asks for `∃ n : ℕ, 0 < n ∧ n • g = 0`. |
| All finite locally constant subgroup sheaves | The biconditional quantifies over **every** `H : Subobject G`. Its left side is exactly an etale cover with each restriction isomorphic to a constant finite abelian group. Its right side is `∃ i : I, S i = H`. Both directions are required, so neither a smaller cofinal family nor extra nonfinite objects can serve. |
| Finite locally constant means etale locally constant finite abelian group | `𝒰 : Cover.{u} etalePrecoverage X`; for every cover member, `A : AddCommGrpCat.{u + 1}` with `Finite A` and an isomorphism of the restricted **abelian** sheaf with `(constantSheaf (X.smallEtaleTopology.over ...) AddCommGrpCat).obj A`. The constant group may vary across cover members, so disconnected bases are included. |
| Ordered by inclusion, a poset | `[PartialOrder I]` and `S : I ↪o Subobject G`; this order embedding preserves and reflects the canonical subobject inclusion order and excludes duplicate indices for the same subgroup. The category on I is the canonical preorder category, with no independently chosen categorical arrows. |
| Small | `I : Type (u + 1)`, the universe of coefficient sets and the ind-finite diagram, rather than a possibly larger class of presentations of monomorphisms. |
| Filtered | `IsFiltered I`, including nonemptiness. |
| Their union is G | The diagram is `S.monotone.functor ⋙ Subobject.underlying`; the cocone has tip G, and `∀ i, ι.app i = (S i).arrow` fixes every leg to the actual inclusion. The two colimit properties express this union in the respective sheaf categories. |
| Abelian-sheaf colimit identifies with G | `Nonempty (IsColimit (Cocone.mk G ι))`, with the actual inclusion maps, so the canonical comparison is an isomorphism. |
| Underlying set-sheaf colimit identifies with G | `Nonempty (IsColimit ((sheafCompose ... (forget AddCommGrpCat)).mapCocone (Cocone.mk G ι)))`. This is the colimit in set **sheaves**, not a sectionwise presheaf colimit. |

Dependency declarations used (source signatures and docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, with `IsNoetherian`
  bundling it with quasi-compactness.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (no Hausdorff assumption).
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`, specialized to abelian groups.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` and `Scheme.Etale`.
- `Sheaf.AlgebraicGeometry.IndFiniteEtaleLocalSystem`:
  `Scheme.IsIndFiniteEtaleSheaf` (small filtered diagram of finite-etale representables).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points are written
  inline as in the recorded dependency. Also read `Scheme.SpecToEquivOfField` in
  `Mathlib.AlgebraicGeometry.ResidueField` for the geometric-point convention.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`: `pointedEtaleStalk` and its
  `pointedEtaleStalkDiagram`, the opposite pointed-neighbourhood colimit.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`,
  sheafification of the constant presheaf, here on the localized small etale site.
- `Mathlib.CategoryTheory.Limits.HasLimits`: colimit conventions;
  `Cocone`, `IsColimit` and `Functor.mapCocone` express the universal property directly.
- `Mathlib.CategoryTheory.Filtered.Basic`: `CategoryTheory.IsFiltered`.
- `Mathlib.CategoryTheory.Subobject.Basic`: `Subobject`, its partial order,
  `Subobject.underlying` and `Subobject.arrow`. Subobjects quotient monomorphisms by
  commuting isomorphisms, so this is the set of subgroup sheaves, not their presentations.
- `WeilConjectures.ConstructibleSheaf.Defs`: existing
  `Cover.etalePrecoverageToEtale` (through the ind-finite dependency).

Edge cases checked: X may be empty (the zero subgroup still gives a nonempty singleton
poset), G may be zero, and finite trivial groups are allowed. X need not be connected:
cover constants vary, and no single global group or geometric point is required.
There is no common torsion exponent, no finite-generation assumption on G, and no
characteristic restriction. The order on the full finite-subgroup family has zero as
least element and sums as upper bounds. The coefficient and index universes match the
recorded ind-finite local-system universe. Universal quantification over stalk elements
includes zero, which is killed by 1; the positive condition excludes n = 0 as a
vacuous witness.

Searches made (2026-10-19):

- `msearch.py ... leanfinder "a torsion abelian etale local system on a Noetherian scheme is the filtered union of finite locally constant subgroup sheaves"`: eight hits about finite-type sheaves and condensed modules, none matching.
- `msearch.py ... loogle "Subobject, IsFiltered, IsColimit"`: no hits; service reports unknown identifier `Subobject`. The actual subobject and colimit APIs were then read directly.
- `msearch.py ... grep "finite.*subsystem|torsion.*local.system|FiniteLocallyConstant" CategoryTheory`: zero hits.
- `msearch.py ... leansearch "torsion abelian local system filtered union finite locally constant subgroup sheaves"`: eight hits, including `AddCommGroup.finite_of_fg_torsion`, `Module.finite_of_fg_torsion` and condensed-colimit facts. The ordinary group lemmas can aid the future proof but do not state the sheaf exhaustion.
- `rg` for finite subsystems, torsion local systems and finite locally constant sheaves in Mathlib, the upstream `WeilConjectures` source and `lean/Sheaf`: no existing exhaustion statement; the downstream `TorsionTorsorDescent` module refers to this item in its proof docstring. The upstream `IsFiniteLocallyConstantSheaf` uses finitely **generated** stalks for abelian groups, so it is not used as a bare synonym for finite abelian-group stalks. The statement instead spells out the node's local finite-constant condition using the already-recorded constant-sheaf functor; no new predicate is defined.
- `rg`/the prescribed node-id search in upstream sources: no occurrence of `lem-per-torsion-finite-subsystem`; `dag/lean_names_upstream.json` has no declaration with the chosen name.

No node fault, statement correction, new node or dependency module was necessary.
No `STATEMENT-DISPUTED` concern remains.

## Second reading by Q14

Author self-check under the dispatcher brief; the maintainer supplies the independent
review. Reopened the node and the final module side by side. An initial draft merely
indexed a family and supplied an unrelated category and partial order; it would not
have asserted all finite subgroups with their inclusion order. Replaced this with an
order embedding into `Subobject G`, an exact image biconditional, and the canonical
preorder category. Also corrected the local constant-sheaf topology to the localized
site and used `Functor.mapCocone` for forgetting to sets. Checked every row above,
especially finiteness as a finite underlying group, pointwise torsion with positive
exponent, and the canonical legs of both colimits. The final theorem has exactly the
hypotheses of the node and all its conclusions. No helper definitions, added
hypotheses, or altered dependency records are concealed by the encoding.

Validation: the final declaration compiled through `scompile.py` as both a sandbox
module and its library module, without errors or warnings. Delivery preflight and
per-file compilation are run again by `deliver2.py --no-push` before the push.

## Maintainer review fix

The delivered docstring gave a different proof route (connected components and
fundamental-group modules) and the report said the node's `proof` was empty; the node has
four proof steps. The docstring now carries those steps; the statement is unchanged.
