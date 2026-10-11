## Worker report

The module `lean/Sheaf/AlgebraicGeometry/FiniteUnramifiedOnePointClosed.lean` states
`AlgebraicGeometry.finite_unramified_one_point_closed` from Stacks Project, Etale Morphisms,
Lemma 04DG. The binders `X S`, `π`, `s`, and `x` render the schemes, morphism, base point,
and fibre point. `hx : π x = s` says that `x` lies over `s`; `hunique` says every point over
`s` equals `x`, rendering the unique underlying fibre point. `hfinite : IsFinite π` is the
finite hypothesis. `hunramified` is the Mathlib rendering of the node's unramified notion:
`LocallyOfFiniteType π` together with an open-immersion diagonal. The `hpure` `letI` installs
the algebra structure induced by `π.residueFieldMap x`; its conjunction states that the residue
field extension is purely inseparable and finite (`Module.Finite`). The conclusion quantifies
an open `U : S.Opens` containing `s` and states `IsClosedImmersion (π ∣_ U)`, the restricted
morphism to that neighbourhood.

Dependency declarations used are Mathlib's `AlgebraicGeometry.Scheme`,
`Scheme.Hom.fiber`/scheme opens and restriction (`morphismRestrict`),
`AlgebraicGeometry.IsFinite`, `AlgebraicGeometry.LocallyOfFiniteType`,
`AlgebraicGeometry.IsOpenImmersion`, `AlgebraicGeometry.IsClosedImmersion`,
`AlgebraicGeometry.Scheme.residueField` and `Scheme.Hom.residueFieldMap`, and
`IsPurelyInseparable` with `Module.Finite`, as recorded by the dependency nodes.

Edge cases checked: the unique point condition allows arbitrary schemes and empty fibres are
excluded by the explicit point `x` and `hx`; no finiteness, characteristic, or universe cases
are silently restricted, and `U` may be any open neighbourhood. The induced residue-field
algebra is taken over `S.residueField (π x)` because this is the domain of the canonical map;
`hx` identifies it with `S.residueField s` in the node's formulation.

Searches made: `msearch.py leanfinder "finite unramified scheme morphism with one fibre point and purely inseparable residue extension is a closed immersion near that point"` (generic finite/unramified/closed-immersion declarations, no local theorem); `msearch.py loogle "AlgebraicGeometry.IsFinite -> AlgebraicGeometry.IsClosedImmersion"` (finite/monomorphism characterization only); `msearch.py grep "IsClosedImmersion.iff_isFinite_and_mono|FormallyUnramified|IsFinite"` (generic declarations only); `rg` over `WeilConjectures` and `lean/Sheaf` for one-point fibre and residue-field patterns (no matching theorem).

No `STATEMENT-DISPUTED` issue found.

## Earlier second reading (a previous round; superseded)

Reading the node and module side by side: `hx` and `hunique` exactly encode the named point
and uniqueness over `s`; `hfinite` and `hunramified` retain both hypotheses; `hpure` retains
pure inseparability and finite extension data using the canonical residue-field map; and the
existential open neighbourhood and closed-immersion restriction match the conclusion clause by
clause. The only elaboration adjustment was expressing the source residue field as
`S.residueField (π x)`, the actual domain of `residueFieldMap`; `hx` supplies the node's
identification with `κ(s)`. The file compiles cleanly with the expected `sorry`.

## Second reading by K1

Read the sandbox node, its seven proof steps, its module, and all seven statement dependency
nodes independently. The repository has no Stacks checkout; I read the available checkout at
`/home/ubuntu/c1-stacks-review/etale.tex`, lines 706–743, including the chapter conventions
(lines 39–56). The conventions explicitly reiterate Noetherian hypotheses when needed;
04DG has none. Its four conditions are finiteness, unramifiedness, a singleton topological
fibre, and pure inseparability. It does not separately assume finite residue-field degree.
The node agrees exactly with this source and needs no statement correction.

Object, hypothesis, and conclusion inventory, with the final Lean rendering and verdict:

- Schemes X and S: `{X S : Scheme.{u}}`. Correct: Mathlib Scheme is locally ringed with
  affine neighbourhoods; its Hom is a morphism of locally ringed spaces (Scheme.lean:74).
  This is `def-pc-scheme`, not an affine or Noetherian specialization.
- Morphism π: `(π : X ⟶ S)`. Correct: the category is the recorded scheme category.
- Base point s and named fibre point x: `(s : S) (x : X)`. Correct: coercion to a scheme's
  type means its underlying points, not geometric points or field-valued lifts.
- Membership in the fibre: `(hx : π x = s)`. Correct, and supplies nonemptiness.
- Uniqueness of that point: `(hunique : ∀ y : X, π y = s → y = x)`. Correct: together with
  hx it says the underlying inverse image of {s} is {x}. The alternative scheme-theoretic
  formulation is equivalent via `Scheme.Hom.fiberHomeo`; I opened Fiber.lean:38–46,103,
  where fiber is `pullback π (S.fromSpecResidueField s)` and fiberHomeo has codomain
  `π ⁻¹' {s}`. There is no need to introduce a second fibre notion or import an unused module.
- Finiteness: `(hfinite : IsFinite π)`. Correct: Finite.lean:39 requires IsAffineHom and
  finite ring maps on affine opens, exactly `def-weil-finite-integral-morphism`.
- Unramifiedness: `(hunramified : LocallyOfFiniteType π ∧
  IsOpenImmersion (pullback.diagonal π))`. Correct: precisely the conjunction recorded
  by `def-weil-unramified-morphism`. I opened FiniteType.lean:43, OpenImmersion.lean:38,
  and Limits/Shapes/Diagonal.lean:38–43; diagonal is the map X → pullback π π induced by
  the two identity maps. No finite-presentation, flatness, or etaleness assumption is added.
- Residue-field extension: hpure installs `(π.residueFieldMap x).hom.toAlgebra`, then asserts
  `IsPurelyInseparable (S.residueField (π x)) (X.residueField x)`. Correct after repair.
  ResidueField.lean:45 defines the local-ring residue field and :123 defines the induced
  map from the stalk map. Its domain is κ(π x); hx identifies this with κ(s), so this is
  the canonical extension in `def-weil-residue-field`, not an arbitrary field action.
  PurelyInseparable/Basic.lean:107,211 gives the recorded pure-inseparability notion.
  The dependency `def-weil-pbc-finite-purely-inseparable-extension` defines pure inseparability
  and finiteness separately: citing it does not add finiteness to the node's hypothesis.
- Open neighbourhood: `∃ U : S.Opens, s ∈ U ∧ ...`. Correct: an arbitrary open containing
  the original s, after the fixed X,S,π,s,x and their hypotheses.
- Closed immersion of the restricted morphism: `IsClosedImmersion (π ∣_ U)`. Correct:
  Restrict.lean:569 types morphismRestrict as `(π ⁻¹ᵁ U).toScheme ⟶ U.toScheme` and defines
  the notation; ClosedImmersion.lean:45 is a closed embedding with surjective stalk maps,
  the recorded definition of `def-weil-closed-immersion`.

Edge cases: empty X, empty S, or an empty fibre cannot provide x,s,hx, exactly as the source's
singleton fibre cannot be empty. There is no index set or integer n in this statement. The
zero-ring affine scheme is empty and is handled by the same binders. Pure inseparability
includes all characteristics: exponential characteristic 1 makes every element belong to
the base field, and positive characteristic gives p-power membership (Basic.lean:211).
No characteristic, nontriviality, Noetherianity, connectedness, or base-field instance is
assumed. Universe u is explicitly bound and arbitrary; both schemes live in the ordinary
Mathlib scheme category in a common universe, with no independent test-object universe or
smallness restriction. Opens may be any open neighbourhood, including all of S.

Independent searches (actual invocations recorded in searches.jsonl):

- LeanSearch: "A finite morphism with unramified diagonal and a singleton fibre with radicial
  residue field is a closed embedding on a neighbourhood". Service returned Internal Server
  Error; no conclusion drawn from this unavailable search.
- LeanFinder: "Restriction to a neighbourhood of a point of a finite unramified morphism is
  a closed immersion if the fibre is one point with purely inseparable residue field".
  Eight hits: residue maps being closed immersions/preimmersions, closed-singleton criterion,
  finite residue-field instances, and fibre projection preimmersions. None states 04DG.
- Loogle: `AlgebraicGeometry.IsClosedImmersion, AlgebraicGeometry.morphismRestrict`.
  Two hits: preservation of an already closed immersion under restriction and a restricted
  diagonal criterion, neither giving 04DG from its four conditions.
- Mathlib grep via msearch: `purelyInseparable|residueField.*[Cc]losed|[Cc]losed.*residueField`
  in AlgebraicGeometry. Found residue-field, universal-injectivity, and closed-immersion
  facts, no local singleton-fibre theorem. I opened the relevant definitions rather than
  treating their names as evidence of equivalence.
- Direct rg of Mathlib, the whole WeilConjectures tree, and repository lean/Sheaf for
  `04DG|finite.unramified.one.point|one.point.*closed.immersion|singleton.*IsClosedImmersion`,
  and broader one-point/pure-inseparability searches in AlgebraicGeometry: no exact statement.
  Existing ClosedFibreSingleton and EtaleLocalFiniteMultiplePoints concern different
  hypotheses and conclusions. No occurrence of the proposed name in lean_names_upstream.json.

Mismatches and repairs: the first worker's hpure conjoined Module.Finite with pure
inseparability, although only pure inseparability is stated by the node and 04DG. Removed
Module.Finite and the corresponding phrase in the declaration docstring. This finiteness
is a consequence of the other geometric hypotheses, not a premise to expose to callers.
The short proof docstring compressed seven steps and named no dependency nodes; replaced
it by all seven steps, with every cited dependency, including nonzero fibre and prime
contraction for one factor, characteristic cases, Nakayama, annihilator spreading, and the
principal-open closed-immersion conclusion. Updated lean.statement verbatim from the final
signature. No node statement, proof, or dependencies changed; no new definition nodes or
dependency modules were needed. No private or hollow definitions, extra theorem, or proof
was introduced. The sole theorem still has `by sorry`. Imports serve the actual signature;
all source and blueprint docstrings, namespace, explicit universe, and 100-character lines
checked. Compilation by scompile.py succeeded on the server (exit 0, 1.7 seconds), with no
errors or warnings. This reading supersedes the earlier report's approval of Module.Finite.
