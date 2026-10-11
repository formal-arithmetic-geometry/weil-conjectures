## Worker report

The module states `AlgebraicGeometry.nagataMorphismEqEventually` for the full inverse
system, limit cone, base index, qcqs and finite-presentation hypotheses, two morphisms
over the base, and the recorded `NagataMorphismEqualityStageData`. Its conclusion
quantifies every `lambda` with `i₀ ≤ lambda` and assumes
`nagataMorphismEqualityStage data ≤ lambda`; it equates the underlying scheme maps
obtained by applying `Over.pullback (D.map (homOfLE hlambda).op).map` to
`Over.homMk phi hphi` and `Over.homMk psi hpsi`. Thus the two maps are exactly the
base changes of `phi` and `psi` to the stage `lambda`.

The hypotheses render the node as follows: `I`, its preorder, directedness and
nonemptiness are the first binders; `D`, `c`, `hc`, and affine transition instances
render the inverse system and limit; `i₀` and the compact/quasi-separated instance
render the base stage; `X₀`, `Y₀`, their compact/quasi-separated instances and `p`,
`q` with locally finite presentation, quasi-compactness and quasi-separatedness
render the finite-presentation base schemes; `phi`, `psi`, `hphi`, and `hpsi`
render the two morphisms over the base; and `d`, `r`, and `data` render the selected
stage construction [def-nagata-morphism-equality-stage]. The conclusion's two
clauses are the lower-bound hypothesis `i₀ ≤ lambda` and the stage bound followed by
the equality of the two pulled-back morphisms.

Dependency declaration used: `Sheaf.AlgebraicGeometry.NagataMorphismEqualityStage`,
`AlgebraicGeometry.NagataMorphismEqualityStageData` and
`AlgebraicGeometry.nagataMorphismEqualityStage`. The upper-bound lemma and qc-open
eventual-equality lemma occur only in the proof described by the node and are not
statement dependencies, so no additional imports are needed.

Edge cases checked: the index is only required to be a nonempty directed preorder;
no finiteness or linearity of `I` is added. The lower-bound binder permits every
stage in the indexing tail, including the selected stage itself. Empty finite cover
index types and zero generators remain permitted by the dependency data. Universes
use the same `u` for the index and schemes as the dependency declaration.

Searches made: `msearch.py E1 lemma-nagata-morphism-eq-eventually leanfinder
"eventual equality of two scheme morphisms after base change in a directed inverse
system"` (only broad `ExistsHomHomCompEqCompAux` and locally finite-presentation
results); `msearch.py ... loogle "Scheme.Hom, equal after pullback, directed inverse
system"` (no hits); grep of Mathlib AlgebraicGeometry for eventual morphism equality
(no matching declaration); `rg` over `WeilConjectures/` and `lean/Sheaf` for the node
and declaration name (no existing statement). No exact existing declaration was found.

## Earlier second reading (a previous round; superseded)

Read the node, dependency module, and this file independently. Every node hypothesis
is present with the same objects and instances. The conclusion uses the canonical
`Over.pullback` base-change functor and compares the underlying maps, which is the
explicit Lean rendering of equality of the two base changes. No hypothesis or clause
was added or omitted; no statement correction was needed.


## Second reading by E1

Read the item's node and proof, the recorded dependency node and its whole module,
the upstream `baseChangeDiagram`, `Over.homMk` and `Over.pullback` declarations,
and the selected finite-upper-bound and compact-open equality-stage definitions.
Read the blueprint source files on the server (not present locally) and Stacks
`limits.tex`, label `lemma-descend-finite-presentation`, Tag 01ZM, lines 2370–2446,
including the standing hypotheses and proof of (3).

Object/hypothesis/conclusion checklist (all verdicts: exact):

- Directed index set: `{I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  [Nonempty I]`. Nonemptiness is already forced by the fixed base index.
- Inverse system and its limit: `{D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D}
  {hc : IsLimit c}`. The limit scheme is `c.pt`; no separate choice of an
  unrelated limit object occurs.
- Affine transition morphisms: the instance quantified over every arrow of
  `Iᵒᵖ` asserts `IsAffineHom (D.map f)`, in the correct inverse direction.
- Fixed stage and qcqs base: `{i₀ : I}`, `CompactSpace (D.obj (op i₀))`
  and `QuasiSeparatedSpace (D.obj (op i₀))`. Stacks assumes all base stages
  qcqs; the dependency node uses only this stage, and affineness makes every
  stage in its tail qcqs. No assumptions on unused earlier stages are needed.
- Finite-presentation schemes over that base: `{X₀ Y₀ : Scheme.{u}}`,
  `{p : X₀ ⟶ D.obj (op i₀)}` and `{q : Y₀ ⟶ D.obj (op i₀)}` with
  `LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated` for each.
  This is Stacks finite presentation. The explicit qcqs instances on X₀
  follow from these properties and the qcqs base; they impose no extra case
  restriction. The dependency does not need a separate qcqs instance on Y₀.
- Two base morphisms: `{phi psi : X₀ ⟶ Y₀}` and
  `{hphi : phi ≫ q = p} {hpsi : psi ≫ q = p}` express exactly being over the base.
- Equality after limit base change: `data.equalLimitBaseChange` compares the
  composites of `pullback.fst p (c.π.app (op i₀))` with phi and psi.
  This is equivalent to equality of the pulled-back morphisms, since their
  other projections to the limit base coincide.
- Choices determining the specified stage: `{d : I → I → I}` and
  `{r : LinearOrder I}` are explicit choice data, not an extra linear-order
  instance on the directed preorder. `data.boundData` supplies the common
  upper-bound property of d. `NagataMorphismEqualityStageData` contains the
  finite affine covers T/V, finite algebra generators G, compact inverse-image
  opens with equal limit pullbacks, `selectedLambda` equating lambdaJK to the
  recorded compact-open equality stage, the finite affine intersection covers U,
  factorizations phiU/psiU, and later coefficient witnesses mu. Read each field;
  none assumes the theorem's eventual morphism equality. The dependency's
  `nagataMorphismEqualityStage data` is the actual `directedFiniteUpperBound`
  of i₀, every lambdaJK, and every mu, exactly the node's finite set.
- Universal later stage and bound: `∀ (lambda : I) (hlambda : i₀ ≤ lambda),
  nagataMorphismEqualityStage data ≤ lambda → ...`. The additional proof
  binder hlambda merely types the transition arrow: the selected bound
  dominates i₀, so it is derivable from the stated bound and drops no stage.
- Equality conclusion: the two `.left` morphisms of
  `(Over.pullback (D.map (homOfLE hlambda).op)).map (Over.homMk ... phi hphi)`
  and its psi analogue. The transition is S_lambda → S_i₀; these are precisely
  the two base changes X_lambda → Y_lambda, and equality of underlying maps
  is equivalent to equality of the morphisms over S_lambda. No weaker equality
  on points or on the limit is substituted.

Edge cases: empty I cannot have i₀, exactly as in the source. Empty schemes,
empty finite covers J/K/L, and empty generator lists are permitted. The finite
set defining the bound always includes i₀, even if the covers are empty.
The bound stage itself is included. No positive dimension, nonzero ring,
Noetherian, separated, characteristic or field hypothesis occurs. There is no
numeric n. Index and schemes share arbitrary universe u, as required for limits;
there is no independent smaller test universe and every variable is bound.

Independent searches: LeanFinder query "A chosen finite upper bound of affine
chart coefficient witnesses makes two descended scheme maps equal at every later
index" returned the generic existential equality theorem and cover extensionality.
Loogle query "AlgebraicGeometry.Scheme, CategoryTheory.Over.pullback" returned
five pullback/flat-descent results, no exact statement. LeanSearch query
"Equality of two descended scheme morphisms at all stages above a fixed finite
bound of generator equality witnesses" was unavailable (Internal Server Error).
Grep of Mathlib `AffineTransitionLimit.lean`, upstream `WeilConjectures/`,
project `lean/Sheaf/`, and `dag/lean_names_upstream.json` with
`exists_hom_hom_comp_eq_comp`, `NagataMorphismEquality`, and
`morphism.*equality.*stage` found no exact existing statement. Opened
`Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType` and
`Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType`: both assert existence
of some refinement; neither asserts equality at every stage above this specified
finite bound. Thus recording either as existing would lose the node's conclusion.

Mismatch repaired: H8, the proof docstring omitted the node's detailed three-step
argument and dependency ids. Expanded it to include domination of each witness,
equality and coverage of transported inverse-image opens, transport of coefficient
equalities from mu to lambda, agreement on the base ring and generators, the
fibre-product universal property and open-cover extensionality; added Stacks
Tag 01ZM (3) as a source. The theorem signature and node statement needed no
change; the node's `lean.statement` remains verbatim the file signature.
No new nodes or dependency modules were necessary, no definitions were added,
and the sole theorem proof remains `by sorry`. Local single-file compilation
passed (exit 0, 1.8 seconds), with no errors or warnings.
