## Worker report

The module `Sheaf.GroupTheory.ProfiniteRestrictionFullFaithful` states
`ContAction.surjective_iff_bijective_finite_res`, with its proof entirely `sorry`.
There are no new definitions, helper theorems, dependency repairs, or statement
corrections. The node's accepted split and every field outside `lean` are preserved.

Source read: `literature/stacks-project/pione.tex`, lines 736–794,
Tag 0BN6, `lemma-functoriality-galois-surjective`. The theorem formalizes
(1) equivalent to (2), in the finite-action categories under that diagram.
The proof docstring includes all five accepted DAG steps, including the
closed-image argument, construction of the proper open subgroup, and fixed-coset
contradiction. The source's last paragraph has a condition-number slip; the
accepted node already gives the complete fixed-point/fullness argument.

Hypotheses and clauses, individually:

- `H : Type u` and `G : Type v`, each with `Group`, `TopologicalSpace`, and
  `IsTopologicalGroup`, introduce the two topological groups without identifying
  their carrier universes.
- `[CompactSpace H]` and `[CompactSpace G]` express compactness of both groups.
- `[T2Space H]` and `[T2Space G]` express their Hausdorff hypotheses.
- `hH` and `hG` say that the neighbourhood filter at the identity has a basis
  consisting of the carriers of all `OpenNormalSubgroup`s. `Filter.HasBasis`
  says a set is a neighbourhood iff it contains one of these carriers.
  `OpenNormalSubgroup` bundles exactly an open subgroup and its normality.
  Hence these binders express precisely the node's identity-neighbourhood basis.
- `h : H →ₜ* G` is the specified continuous group homomorphism.
- `ContAction FintypeCat.{w} G`, with the public scoped instances
  `FintypeCatDiscrete`, is exactly the finite discrete continuous left-action
  category used by the dependency, with equivariant functions as morphisms.
  There is no nonemptiness restriction on its objects.
- `ContAction.res FintypeCat.{w} h` is Mathlib's actual canonical restriction
  functor. Its object action is precomposition by `h`, so `t` acts as `h t`.
  Its map is unchanged on underlying functions, as is visible in `Action.res`
  and `ObjectProperty.lift`; no replacement or arbitrary functor is introduced.
- `Function.Surjective h` expresses the left side of the equivalence.
- `∀ E D : ContAction FintypeCat.{w} G, Function.Bijective
  ((ContAction.res FintypeCat.{w} h).map (X := E) (Y := D))` is the node's exact
  final Hom-set formulation of full faithfulness. It includes both injectivity
  and surjectivity for every ordered pair of finite continuous actions.
- `↔` expresses both directions. No extra conclusion or hypothesis is added.

Dependency declarations and source signatures read:

- `Sheaf.CategoryTheory.FiniteContinuousModule`: the entire dependency module
  was read, including `CategoryTheory.FiniteContinuousModule`, its category and
  forgetful functor, and `finiteContAction_hasFiniteProducts`,
  `finiteContActionFiniteProducts`, `finiteContActionForget`. For this item the
  dependency's explicit finite-set comparison convention is the relevant clause:
  `ContAction FintypeCat G`, with `FintypeCatDiscrete`. Importing that owning
  module reuses the convention without reintroducing any notion.
- `Mathlib.CategoryTheory.Action.Continuous`: `ContAction`, `Action.IsContinuous`,
  and `ContAction.res` at lines 96–110; the latter has signature
  `(f : G →ₜ* H) : ContAction V H ⥤ ContAction V G`.
- `Mathlib.Topology.Algebra.OpenSubgroup`: `OpenNormalSubgroup` at lines 366–370
  and its normality/carrier instances; used in the statement.
- Proof dependency `lem-dl-a1-compact-hausdorff-closed-map` has the exact Mathlib
  match `Continuous.isClosedMap`, read at `Topology/Separation/Hausdorff.lean`
  lines 672–674: compact domain, Hausdorff target, continuous map implies closed
  map. Its module is a plain proof import.
- Proof dependency `lem-dl-a1-open-subgroup-finite-cosets` has exact matches
  `Subgroup.quotient_finite_of_isOpen` (OpenSubgroup.lean:287–290),
  `QuotientGroup.discreteTopology` (Group/Quotient.lean:115–117), and
  `QuotientGroup.instContinuousSMul` (Group/Quotient.lean:68–72). All three full
  signatures were read; none assumes normality. OpenSubgroup is already public
  for the basis hypothesis; Group.Quotient is a plain proof import.

Edge cases checked before writing:

- Empty actions are admitted by `FintypeCat`; maps from the empty action and
  maps into it have the expected injectivity/surjectivity behaviour. No
  `Nonempty E` or `Nonempty D` binder is present.
- Trivial source and/or target groups are allowed. Into the trivial target the
  homomorphism is onto and both action-equivariance notions coincide. A trivial
  source into a nontrivial finite group fails fullness on the singleton-to-coset
  test, as required.
- The proof uses cosets of an open subgroup that need not be normal; only the
  auxiliary basis subgroup is normal. This agrees with the exact Mathlib leaves.
- The action universe `w` is independent of `u` and `v`. Every finite set has a
  representative in any universe, e.g. a lifted `Fin n`; thus the finite coset
  obstruction is still available even when the carrier of `G` is larger.
  There is no lower-universe quantification over arbitrary groups or schemes.
- Compactness of `H` ensures its image is closed; the dense proper image
  counterexamples for general topological groups are excluded by precisely
  the node's compact/Hausdorff assumptions.

Searches actually run (the search wrapper log is in `searches.jsonl`):

- leanfinder: "A continuous homomorphism of profinite groups is surjective if
  and only if restriction on finite continuous actions is fully faithful".
  Eight hits, including `Action.full_res`, `ProfiniteGrp.toLimit_surjective`,
  and Galois-category fundamental-group results. None is the equivalence here.
- loogle: `ContAction, CategoryTheory.Functor.Full`. One hit: fullness of the
  canonical Galois fibre-functor construction in `Galois.Equivalence`. Its
  declaration, read at lines 42–49, is not restriction along arbitrary `h`.
- grep through Mathlib CategoryTheory:
  `res.*[Ff]ull|[Ff]ull.*res|[Ss]urjective.*[Ff]ull`. Twenty-five hits;
  `Action.full_res` is the relevant forward implication only. Read its full
  statement and proof at `Action/Basic.lean:402–419` and restriction definition
  at lines 345–359. There is no converse match.
- leansearch: "A continuous homomorphism between profinite groups is onto
  exactly when restriction of finite continuous sets is fully faithful".
  Eight hits concerning `ProfiniteGrp.ofHom`, its limit comparison, and fully
  faithful finite-set inclusions; no matching criterion.
- Project searches: `rg` for restriction/fullness/surjectivity combinations in
  both `lean/WeilConjectures` and `lean/Sheaf`, followed by narrower
  `ContAction.res` and criterion-name searches in their GroupTheory and
  CategoryTheory directories; no statement of this equivalence found.
  `grep -rn` for the exact node id in `lean/WeilConjectures`, and `rg` for it in
  `dag/lean_names_upstream.json`, gave no match. No existing declaration was
  replaced or duplicated.

Validation: the prescribed `scompile.py` compiled this file both as sandbox
`Sheaf.Stage2.Sandbox0` and as its intended library module. Both passed with no
errors or warnings (5.7 s and 5.2 s). No direct compiler or global build was run.

## Second reading by Q98

A second reading in this worker compared the node's literal statement to the
finished signature and the canonical restriction definition. The dispatcher
explicitly forbids starting another agent; this is a self-review, and the
maintainer's independent review remains the delivery review.

Both groups retain compactness, Hausdorffness, group topology, and the open
normal identity basis. The two basis hypotheses use all open normal subgroups,
which is equivalent to existence of a neighbourhood basis of such subgroups:
each open normal subgroup is itself a neighbourhood, and any given basis is
cofinal in this family. The restriction has the correct direction from
`G`-actions to `H`-actions. Its Hom map has source `E ⟶ D` and target the Hom
between their actual restrictions. The equivalence uses bijectivity, not merely
fullness. The finite-action category includes empty objects and the singleton.
All three universes are explicitly bound. No mismatch or statement correction
was found, and no change was needed in this pass.
