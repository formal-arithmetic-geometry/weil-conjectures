## Worker report

The module `Sheaf.AlgebraicGeometry.AmpleAffineLimitDescent` states
`AlgebraicGeometry.exists_stage_isAmple_of_limit_isAmple`, the Stacks Project
Limits Tag 09MT descent of absolute ampleness along an inverse system of
quasi-compact quasi-separated schemes with affine transition maps.

The Lean binders render the node as follows. `I : Type v` with
`[Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]` is the small nonempty
directed index set. `D : Iᵒᵖ ⥤ Scheme.{u}` is the inverse system, and `c : Cone D`
with `hc : IsLimit c` supplies its limit and projections `c.π.app (op i)`.
The two instance binders `CompactSpace (D.obj (op i))` and
`QuasiSeparatedSpace (D.obj (op i))` state quasi-compactness and
quasi-separatedness of every stage. `haff` states that every transition
`D.map (homOfLE h).op` for `h : i ≤ j` is affine. `i₀` is the fixed stage and
`L₀` is its invertible module, with `[L₀.IsInvertible]`. The hypothesis `hL`
packages invertibility of the tensor pullback to the limit together with
`@IsAmple c.pt ((tensorPullback (c.π.app (op i₀))).obj L₀) h`, exactly the
assumption that the limit pullback is ample. The conclusion gives an index `j`
and `hij : i₀ ≤ j`, then packages invertibility and ampleness of the tensor
pullback along `D.map (homOfLE hij).op` to the stage `j`.

The statement dependencies used are `AlgebraicGeometry.Scheme` from
`Mathlib.AlgebraicGeometry.Scheme`,
`AlgebraicGeometry.Scheme.Modules.IsInvertible` from
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
`AlgebraicGeometry.Scheme.Modules.tensorPullback` from
`WeilConjectures.AlgebraicGeometry.TensorPullback`, `CompactSpace` from
`Mathlib.Topology.Defs.Filter`, `AlgebraicGeometry.QuasiSeparated` from
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`, `AlgebraicGeometry.IsAffineHom`
from `Mathlib.AlgebraicGeometry.Morphisms.Affine`,
`CategoryTheory.Limits.colimit`/`CategoryTheory.IsFiltered` from
`Mathlib.CategoryTheory.Limits.HasLimits`, and
`AlgebraicGeometry.Scheme.Modules.IsAmple` from
`WeilConjectures.AlgebraicGeometry.Ample`. The proof-only imports are `Sheaf.AlgebraicGeometry.LimitAffineTransition` and
`Sheaf.AlgebraicGeometry.ValuationLimitQcohSectionDescent`. The Mathlib proof leaves
`Scheme.exists_isAffine_of_isLimit`, `exists_map_eq_top` and `exists_preimage_eq`
are available through `Mathlib.AlgebraicGeometry.AffineTransitionLimit`, imported by
the first proof module. No proof-dependency import is omitted for a cycle.

Edge cases checked: `Nonempty I` excludes an empty inverse system as required;
`IsDirected` permits a singleton index and `j = i₀`; tensor powers in
`IsAmple` retain the positive-power condition, so `n = 0` is excluded by the
ampleness definition; the explicit existential invertibility witnesses avoid
adding an unmentioned typeclass hypothesis while expressing the same
invertibility condition.

Searches for an existing declaration: `msearch.py leanfinder` query
“Ampleness of an invertible sheaf descends from an affine transition inverse
limit of quasi-compact quasi-separated schemes to a later stage” returned only
generic affine-limit declarations and no ampleness theorem; `msearch.py loogle`
query `IsAmple, IsLimit, IsAffineHom` returned no match; `msearch.py grep`
query `IsAmple|ample|lemma-limit-ample` in Mathlib algebraic geometry found no
absolute ampleness declaration; `rg` over `WeilConjectures` and `lean/Sheaf`
found no theorem for Tag 09MT. The existing `AlgebraicGeometry.Scheme.Modules.IsAmple` is the
absolute ampleness definition used here, while the upstream
`AlgebraicGeometry.IsAmple` in `Modules.VeryAmple` is a different relative
projective-over-a-field notion.


## Second reading by Q113

Author self-check only; the maintainer supplies the independent review, as required
by the remote-worker brief. Reading the node and signature together confirms the
same index, inverse diagram, qcqs stages, affine transitions, limit cone, fixed
stage and invertible module. Both ampleness occurrences use absolute
`Scheme.Modules.IsAmple`, with the exact tensor pullbacks and the bound `i₀ ≤ j`.
The existential proof of invertibility is solely the typeclass argument needed by
`IsAmple`; invertibility is automatic for a pullback of `L₀`, and proof irrelevance
ensures this packaging makes no extra mathematical choice or assumption. The empty
limit scheme remains permitted: ampleness is then the compactness condition with
its pointwise clause vacuous, and eventual emptiness is compatible with the theorem.
The index universe `v` is independent of the scheme universe `u`, as requested
by the maintainer; no equality or inequality of these universes is imposed. No characteristic, nonemptiness of a scheme,
Noetherianity, or finite-type condition was introduced. No statement correction or
new/dependency node is needed.

The source was checked in `literature/stacks-project/limits.tex`, Situation
`situation-descent` and `lemma-limit-ample` (Tag 09MT). The proof docstring applies
section descent to the tensor powers, as required when the finite ample cover uses
different powers. The original node's step 2 informally writes `F = L₀` for all
sections, a proof-plan shorthand which must be interpreted with these tensor powers.
The recorded `IsAmple` source was read in the shared upstream overlay, and the
current `tensorPullback` source was read with `scompile.py --source` because it is
absent in the older local upstream checkout. All uses retain those exact interfaces.
The theorem has one `sorry`, as prescribed by stage 2; no data definitions are added.

Validation: the statement compiles cleanly through `scompile.py`. The signature
record is exact, only `lean` differs from the base node, and all Lean lines are at
most 100 characters. There is no disputed mathematical statement.

## Repair of return L

The immutable returned head `57c2925496f7` restricted both the directed index
and schemes to universe `u`. The saved packet retained that restriction, and
its initial dry run passed at `fcbab311a5`; this mechanical pass did not fix
the return. The current shared base has the same natural statement and no
landed Lean record for this item. The repair declares `universe u v` and uses
`{I : Type v}` with `D : Iᵒᵖ ⥤ Scheme.{u}`. The node's `lean.statement` is
extracted verbatim from the revised signature. This renders the same small
directed set without identifying its universe with that of the schemes; the
other binders, pullbacks, and conclusion are unchanged. No natural statement
correction is necessary.

Author self-check: both universes are explicitly bound, and the signature
contains no equation or order constraint relating them. The earlier case
`v = u` remains an instance, and indices in a different universe are allowed.
All previous edge-case and hypothesis checks still apply.
