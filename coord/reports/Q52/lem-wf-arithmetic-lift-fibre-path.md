## Worker report

Repair of the immutable returned head `49a227fccd8b`. The retained packet was first
checked with `deliver2.py Q52 lem-wf-arithmetic-lift-fibre-path --no-push`; it passed
mechanical preflight and compilation (dry-run commit `f26e7e77e9`). That did not
repair the mathematical omissions in the return, so this packet adds the clauses
below. Only the item's `lean` and its permitted added statement dependency change.
The natural-language statement, source and proof are unchanged.

The module states `AlgebraicGeometry.Scheme.FiniteEtale.arithmeticLiftFibrePath`.
Its only postponed theorem is that theorem, with proof `sorry`. Its twelve-step
docstring follows all twelve DAG proof steps, including the torsor argument for
bijectivity. All helper definitions contain real data: chosen fibre products,
composition of scheme maps, existing fibre comparisons, and existing Yoneda/point
comparisons. They are the canonical arrows appearing in this node, not independent
notions or replacement fibre functors.

Hypotheses, in source order:

- `K` is `[Field K] [PerfectField K]`; `L` is `[Field L] [Algebra K L]
  [IsAlgClosure K L]`. The displayed `[Algebra.IsAlgebraic K L]` is already a
  field of `IsAlgClosure`, hence imposes no further restriction.
- The separated finite-type K-scheme is `X₀ : Over (Spec (.of K))` with
  `[IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]`.
- `Y` is precisely `fieldExtensionBase X₀ L`, the existing chosen pullback;
  `[ConnectedSpace (fieldExtensionBase X₀ L)]` includes nonemptiness.
- The geometric point is `s : Spec (.of Ω) ⟶ fieldExtensionBase X₀ L`, with
  `[Field Ω] [IsAlgClosed Ω]`. Its arithmetic point is `s ≫ arithmeticBaseProjection X₀`.
  The constants embedding is `i : L →ₐ[K] Ω`; `hi` identifies its Spec map with
  `s` followed by the second projection. The Ω algebra and scalar-tower instances
  can always be obtained from that embedding; they do not restrict geometric points.

Conclusion, clause by clause:

- `j` and `r` have exactly the groups `Aut (fiber s)`, `Aut (fiber (s ≫ ...))`
  and `L ≃ₐ[K] L`. `Continuous j ∧ Continuous r` uses Mathlib's evaluation-product
  topology on fibre automorphisms and `krullTopology K L`. For this normal separable
  algebraic extension, `InfiniteGalois.continuousMulEquivToLimit` identifies the latter
  with the requested inverse limit over finite Galois subextensions.
- The equality `j a = fiberAutBaseChange ... s a` fixes the structure-map homomorphism
  using the existing first-projection fibre comparison; an arbitrary injection would
  not satisfy this requirement.
- The constant-cover clause quantifies over each finite intermediate field `E`,
  embedding `τ : E →ₐ[K] L`, and labelled fibre element `z`. Through the existing
  `fiberConstantCoverEquiv`, the input label is `i ∘ τ` and the output label is
  `i ∘ r(g) ∘ τ`. This characterizes the required arithmetic restriction `r`.
  The implication only expresses that `z` has the specified label; these labels
  exhaust the fibres because E/K is algebraic and L is algebraically closed.
- `Function.Injective j`, `Function.Surjective r`, and `Set.range j = {g | r g = 1}`
  give precisely the short exact sequence. Identifying P with its image is expressed
  by writing its action inside G as `j a`.
- `arithmeticLiftMap X₀ σ` is the existing `fieldExtensionBaseMap X₀ σ`, hence
  `id × Spec σ`. `Φ` is an `Equiv` from the fibre of `r` over σ to natural isomorphisms
  `fiber (s ≫ arithmeticLiftMap X₀ σ) ≅ fiber s`.
- For every finite E and cover Q_E, `arithmeticModelCover X₀ E Q_E` is its composite
  finite étale arithmetic cover. `arithmeticModelFiber ... s s rfl` is iota_1 and
  `arithmeticMovedModelFiber ... s σ` is iota_sigma. Their definitions postcompose
  with the actual first projection of the base-change cover.
- Both `Function.Injective` assertions and both `Set.range` equalities state that these
  are injections onto exactly the scalar-labelled fibres. The labels are respectively
  `Spec (i ∘ E.val)` and `Spec (i ∘ σ ∘ E.val)`; no embedding convention is implicit.
- The next equality is exactly `iota_1 ((Φ t)_Q z) = t⁻¹ iota_sigma(z)`, with t acting
  on the arithmetic model. It is required for every finite model, not one chosen model.
  Each `Φ t` is already a natural isomorphism on the entire finite étale category,
  so it includes every cover morphism. Naturality at model comparison isomorphisms
  identifies the evaluation rule under different models; finite-model descent covers
  every cover and every morphism.
- `arithmeticFibreAut X₀ σ s a` is the action through `pullbackFiberIso`, the specified
  first-projection identification. The c equation is `j c = t⁻¹ * j a * t`, followed
  by the requested equality on every fibre element. The same c works for all covers;
  injectivity of j makes it unique. No extra choice of conjugate is introduced.
- The last finite-cover equality is `Φ (j a * t) = arithmeticFibreAut ... (a⁻¹) ≪≫ Φ t`,
  so it has the required inverse action and order of composition.
- The final conjunct quantifies over every Yoneda-compatible equivalence `e` of the
  existing FEt and FLC categories, with its identification `α`. Such data exist by the
  imported `exists_finiteEtale_flc_equivalence_sheaf`; this is not an empty condition.
  `arithmeticStalk` is an abbreviation for the existing sheaf stalk restricted to FLC.
  `arithmeticStalkComparison` composes α with the existing point/Yoneda comparison,
  rather than choosing an arbitrary stalk identification.
- `Ψ` is the corresponding bijection with natural isomorphisms of those actual stalk
  functors. Its whiskering equation identifies it with Φ through precisely those
  canonical comparisons (the `ULift` is the size convention of the recorded equivalence).
  A and B are the corresponding automorphisms on the ordinary and moved stalk functors;
  their whiskering equations fix them. C corresponds to the same geometric conjugate c.
  `B ≪≫ Ψ t = Ψ t ≪≫ C` and `Ψ (j a * t) = B.symm ≪≫ Ψ t` are the two required identities
  on every FLC sheaf. Equality of natural isomorphisms includes all their components.

Dependency declarations read and used:

- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosure`, `IsAlgClosed` (algebraic
  closure and geometric point); `Mathlib.AlgebraicGeometry.ResidueField`:
  `Scheme.SpecToEquivOfField` (the recorded inline geometric-point convention).
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded pullback
  convention, using Mathlib's `Limits.pullback`, `fst`, `snd`, `map` directly. Its
  module-pullback declaration is not relevant to this coefficient-free statement.
- `WeilConjectures.AlgebraicGeometry.GaloisCategories`: `Scheme.FLC`;
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`: `Scheme.FiniteEtale`,
  `FiniteEtale.fiber`, `fiber_left_comp`.
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality`: `pullback`;
  `...Restriction`: `pullbackFiberIso`, and the signatures and characterization of
  `fundamentalGroupMap`, `fundamentalGroupMap_smul`, `continuous_fundamentalGroupMap`.
  That abstract-model map expects small fundamental groups; the existing generic
  `fiberAutBaseChange` from `Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleWeilTransport`
  gives its canonical full-Aut form without imposing any small-model hypothesis.
  The Weil-transport theorem itself is not used.
- `...ConstantCover`: `constantCover`, `fiberConstantCoverEquiv`;
  `Mathlib.RingTheory.Etale.Field`: `Algebra.FormallyEtale.of_isSeparable`, with
  `Algebra.FinitePresentation.of_finiteType.mp` packaging the finite constant algebra.
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleFieldLimitDescent`:
  `fieldExtensionBase`, `fieldExtensionBaseMap`, `finiteEtale_fieldLimit_descent`.
  Its already-landed node is added to `stmt_deps` because the finite-model clause now
  directly uses its field-system interface. No dependency node or new node is delivered.
- `Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence`:
  `exists_finiteEtale_flc_equivalence_sheaf`; its full source was also checked with
  `scompile.py --source`. The canonical point comparisons are
  `uliftSheafFiberIso`, `uliftYonedaIsoShrinkYoneda`, and
  `shrinkYonedaCompPresheafFiberIso`.
- `Mathlib.CategoryTheory.Galois.Topology`: `autEmbedding` and its induced topology;
  `Mathlib.FieldTheory.KrullTopology`: `krullTopology`. The inverse-limit identification
  was checked in `Mathlib.FieldTheory.Galois.Profinite`, `continuousMulEquivToLimit`.

Edge cases checked before the repair: the empty scheme is excluded by ConnectedSpace,
which matches the node. Empty covers and zero-cardinality fibres remain allowed: the
injection/image/evaluation clauses allow empty sets and are then vacuous on elements.
For σ = 1, the label and evaluation are the original label and t⁻¹ action; at t = 1
this forces the identity path. For K = L algebraically closed, r has trivial codomain
and the path bijection reduces to inversion on fibre automorphisms. E = K and nonnormal
finite intermediate E are both allowed; the constant-cover rule uses every embedding,
not a nonexistent restriction automorphism of a nonnormal E. Arbitrary finite-model
isomorphisms and refinements are covered by naturality and the universal model clause.
Universes are explicit throughout (`autoImplicit false`); sheaf stalks use Type (u+1)
and finite fibres use FintypeCat u with the canonical universe lift.

Searches: the retained searches.jsonl records the original LeanFinder query
`arithmetic lift semilinear paths finite fibre functors` (eight unrelated path hits)
and Loogle query `AlgebraicGeometry.Scheme.FiniteEtale fiber, Aut, Gal` (unknown constant,
no hit). Repair searches used `msearch.py` with LeanFinder query
`Finite model normalization of arithmetic fundamental group paths by inverse action on
finite etale geometric fibres` (eight generic Galois-category/fundamental-group hits,
no arithmetic normalization); Loogle `CategoryTheory.PreGaloisCategory.autEmbedding`
(six exact existing topology API hits, reused); and Mathlib grep
`semilinear|arithmeticLift|arithmetic.*fibre` in AlgebraicGeometry (four unrelated
StructureSheaf semilinear-map hits). `rg` searches of upstream WeilConjectures and
project lean/Sheaf found generic transport and coefficient semilinearity, with no
existing declaration of this arithmetic path statement or finite-model normalization.
The existing finite-field Weil-transport construction and generic fibreAutBaseChange
were read and reused where applicable. All objects introduced here are canonical
arrows of this node; no independent notion needs a new definition node.

No STATEMENT-DISPUTED finding or source correction. The current main node was compared
with the saved node: all fields outside `lean` initially agreed. The only additional
field change is the permitted addition of the already-landed field-limit node to stmt_deps.

## Second reading by Q52

This is a fresh clause-by-clause self-check in the dispatcher worker session; no second
agent was started, as the dispatcher explicitly forbids that. It does not claim an
independent worker review. The maintainer performs the independent delivery review.

With the DAG statement and revised Lean file open, I checked the field, algebraic-closure,
separatedness, finite-type, connectedness, geometric-point and constants binders against
the first paragraph. They match as listed above; ConnectedSpace excludes the empty base.
I checked that both structure maps now have their required characterization, that their
continuity uses the evaluation and Krull topologies, and that all three exactness clauses
remain present. These were genuine omissions in the returned version, now repaired.

I checked the finite-model paragraph against the actual helper definitions, not only their
names. The forgetful maps compose with pullback.fst, and their image equations specify
i and i-sigma on constants. The normalized evaluation equation uses t inverse, on the
arithmetic model Q_E, for every finite intermediate E. NatIso naturality covers all cover
morphisms, and the rule is universal over finite models. The returned version had none
of these clauses; all are now explicit.

I checked the conjugation formula by first projecting a moved pullback fibre: the action
is arithmeticFibreAut, and the conjugate is t inverse times j(a) times t. The lift-change
formula precomposes Φ t with the inverse action on that moved fibre. The revised c binder
precedes Q and z, so it denotes a single group element on all fibres, as required.

I then checked the last paragraph against Ψ and its actual stalk functors. Its comparison
is canonical from α and the point/Yoneda isomorphism. The Ψ comparison square identifies
these very paths with Φ; the A, B, C comparison equations identify all three actions.
The final two natural-isomorphism equalities therefore express conjugation and lift
change for every FLC sheaf. Merely importing an equivalence, as the saved version did,
would not state this conclusion.

Finally I reread every proof-docstring step against the twelve DAG steps. Step 11 now
constructs a lift of each path as t j(b) inverse and proves injectivity using exactness,
lift change, and the equivalence h_sigma pullback. Thus it supplies the bijectivity
argument omitted in the return. No theorem is proved at stage 2 and no definition's
data is postponed. Every helper is listed in lean.declarations with source/blueprint
docstrings; the main lean.statement is extracted verbatim from the final file.


## Maintainer review correction (2026-10-18)

The independent immutable-head review found H6: the original `arithmeticModelFiber`
definition proved its over-base equality by a local `calc`, and
`arithmeticMovedModelFiber` proved its basepoint equality by local `simp`.
The replacement module postpones those two proof obligations as the named theorems
`arithmeticModelFiber_over` and `arithmeticLiftMap_basepoint`, both with `sorry`,
source/blueprint docstrings and explicit proof plans. They are well-definedness
clauses of the finite-model injection already specified in the item's statement
and proof step 5, not independent notions or additional DAG prerequisites.
Both helpers are registered in the replacement lean record. All definition data
remain the original canonical projection/comparison constructions. There are now
three postponed theorem proofs, each exactly `sorry`; the earlier assertions that
only the main theorem is postponed are superseded by this correction.

The main theorem signature, and therefore `lean.statement`, is unchanged verbatim.
No natural-language statement correction or citer audit is required. All ten
statement dependencies, source conventions, inverse-action normalization,
finite-model images, conjugation, lift-change and stalk comparison were checked
independently. There is no dropped route-pivot citation or pro-etale substitute.

Compiler evidence for the immutable module: prescribed `scompile.py Q52
lem-wf-arithmetic-lift-fibre-path <immutable-file>` exited 0, with side-overlay
sandbox compilation 7.4 s and library-path confirmation 40.9 s, without diagnostics.
The installed wrapper delegates to the server overlay/confirmation; no direct SSH
command, global build or live source edit was performed by the reviewer.

Compiler evidence for the complete replacement: `scompile.py Q52
lem-wf-arithmetic-lift-fibre-path <review-dir>/fixes/ArithmeticLiftFibrePath.lean`
exited 0, with sandbox compilation in the side overlay 58.6 s and confirmation
21.8 s, without Lean diagnostics. Because the replacement is stored in the
merge tool's flat basename format, the wrapper assigns its confirmation module
name `Sheaf.Stage2.Check`; it compiled the complete replacement bytes. All runs
kept the default 60-second per-file limit. The initial SSH multiplexing transport
message did not prevent the successful wrapper run.
