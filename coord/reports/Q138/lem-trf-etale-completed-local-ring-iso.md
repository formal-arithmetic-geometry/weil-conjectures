## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleCompletedLocalRingIso` states
`AlgebraicGeometry.etale_completedLocalRing_iso`, with one theorem and one `sorry`.
No definitions, dependency repairs, new nodes, or statement corrections are needed.
The node copy changes only its `lean` field.

Hypotheses, with the original node and the declaration open:

- An algebraically closed field k is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The schemes are `{C D : Scheme.{u}}`.
- The specified k-scheme structure of C is `(f : C ⟶ Spec (.of k))`.
  D's structure morphism is exactly `e ≫ f`; no unrelated algebra structure is used.
- Locally finite type over k is `[LocallyOfFiniteType f]`, with no quasi-compactness,
  global finite type, separatedness, reducedness, smoothness, or dimension assumption.
- The actual etale map is `(e : D ⟶ C) [Etale e]`.
- The point is `(y : D)`, and x is written everywhere as `e y`.
- The first alternative in `hres` is bijectivity of the ring map
  `((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ C.Γevaluation (e y)).hom`.
  Its three factors are constants `k → Γ(Spec k, ⊤)`, structural pullback to
  `Γ(C, ⊤)`, and the actual evaluation into `C.residueField (e y)`.
  This is precisely the specified structural field map, rather than an abstract
  field equivalence or an independently chosen k-algebra structure.
- The second alternative is the identical construction using `(e ≫ f).appTop`
  and `D.Γevaluation y`. Thus it refers to D's induced structure over k.
  Bijectivity of these ring maps is exactly their being isomorphisms.

Conclusions, clause by clause:

- `e y ∈ closedPoints C`: x is a closed point of C.
- `y ∈ closedPoints D`: y is a closed point of D.
- `IsIso (e.residueFieldMap y)`: the induced residue-field map itself is an
  isomorphism, not merely that its domain and codomain happen to be isomorphic.
- The last conjunct is existence of a bijective ring homomorphism `ehat` between
  the maximal-ideal-adic completions of the actual stalks at x and y, with its
  value prescribed on every quotient level. For all `n : ℕ`, all compatible
  sequences z and all representatives a of z's nth coordinate, its nth image
  coordinate equals the class of `(e.stalkMap y).hom a`. This is exactly the
  induced completed local homomorphism in the node. It is the same representation
  of this canonical map as the recorded `RingHom.flat_local_completion_iso`.
  The coordinate condition determines the homomorphism uniquely: each quotient
  projection is surjective from the original ring, and equality at every quotient
  coordinate is equality of compatible sequences. Thus this does not substitute
  an arbitrary bijective ring map. No choice of map or hollow construction is made.
  The usual commutation with the canonical maps from the stalks follows from
  the formula at every n, without adding another conclusion.

Dependency declarations read and reused:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`.
- `def-weil-algebraic-closure`: Mathlib `IsAlgClosed`, in
  `Mathlib.FieldTheory.IsAlgClosed.Basic` (the node's mathlib_match explicitly names
  this predicate alongside `AlgebraicClosure` and `IsAlgClosure`).
- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, its morphisms and `Spec`, in
  `Mathlib.AlgebraicGeometry.Scheme`; `Scheme.ΓSpecIso` identifies constants.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`, in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale` (the local checkout's actual class).
- `def-weil-residue-field`: `Scheme.residueField`, `Scheme.Hom.residueFieldMap`,
  `Scheme.evaluation` and `Scheme.Γevaluation`, in
  `Mathlib.AlgebraicGeometry.ResidueField`. Evaluation is germ followed by residue.
- `def-weil-closed-points`: `closedPoints`, in `Mathlib.Topology.JacobsonSpace`.
- `def-weil-pbc-adic-completion`: `AdicCompletion`, in
  `Mathlib.RingTheory.AdicCompletion.Basic`, with its ring structure and canonical
  quotient projections `AdicCompletion.evalₐ` from
  `Mathlib.RingTheory.AdicCompletion.Algebra`.

The module also imports the stated proof dependencies, non-publicly: the recorded
`AlgebraicGeometry.IsUnramified` from `Sheaf.AlgebraicGeometry.UnramifiedMorphism`;
`AlgebraicGeometry.Flat` and its stalk criterion from Mathlib's `Morphisms.Flat`;
`AlgebraicGeometry.unramified_neighbourhood_iff_maximalIdeal_residue` from
`Sheaf.AlgebraicGeometry.UnramifiedMaximalIdealResidueCriterion`;
`Scheme.Hom.isClosed_singleton_asFiber_of_finiteDimensional` from
`Sheaf.TraceFormula.FiniteResiduePointClosedInFibre`; `Scheme.Hom.fiber` and its
projections from Mathlib's `Fiber`; `IsLocallyNoetherian` and
`LocallyOfFiniteType.isLocallyNoetherian` from Mathlib's `Noetherian`;
`IsAffineOpen.isLocalization_stalk` and the affine-stalk interfaces from Mathlib's
`AffineScheme`; `IsLocalization.isNoetherianRing` from Mathlib's
`RingTheory.Localization.Submodule`; and `RingHom.flat_local_completion_iso` from
`Sheaf.RingTheory.FlatLocalCompletionIso`. The algebraically closed subfield lemma
`IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic` is already available from
the public `IsAlgClosed.Basic` import. Scheme, Spec and residue-field proof
prerequisites are likewise already public imports. No proof import was omitted.
The theorem docstring follows all seven proof steps and names their DAG inputs.

Source checks: read Stacks `morphisms.tex` at
`lemma-algebraic-residue-field-extension-closed-point-fibre` (01TE) and
`lemma-etale-over-field` (02GL), `more-algebra.tex` at `lemma-flat-unramified`
(0AGX), and `etale.tex` at `lemma-characterize-etale-completions` (039M), including
its residue-degree remark. They agree with the node; no statement fault was found.
No stage-2 repair-note file exists for this item.

Edge cases checked before drafting:

- Empty D admits no y, so the quantified statement covers it vacuously. A map to
  empty C similarly supplies no point y with an image. No nonemptiness is added.
- The identity morphism satisfies the conclusion with identity residue and
  completed maps whenever the residue hypothesis holds.
- The generic point of a positive-dimensional integral k-scheme normally has
  transcendental residue field, so neither structural bijectivity hypothesis
  is spuriously inferred there.
- The second residue-field alternative really suffices: writing j = alpha i,
  surjectivity of j and injectivity of alpha force surjectivity of i.
- Arbitrary characteristic is retained; no characteristic-zero or invertibility
  hypothesis is introduced. Etaleness already rules out inseparable ramification.
- For the quotient level n = 0, the power is the unit ideal, and both quotients
  are the zero ring. The coordinate formula is still valid. All positive powers
  are included; there is no loss of first-order or higher-order information.
- Locally finite type, rather than global finite type, suffices for Noetherian
  stalks; infinite disjoint unions of finite-type charts are not excluded.
- A nonreduced C is allowed: the stalk completion and induced map are unchanged
  notions, and the flat-local completion theorem applies without reducedness.
- Every variable and the universe u is explicitly bound (`autoImplicit false`).

Searches for an existing exact statement:

- `msearch.py ... leanfinder` with "An etale morphism of schemes over an
  algebraically closed field induces isomorphic completed local rings at rational
  points": eight hits, only etale definitions, loci and basic properties.
- `msearch.py ... loogle 'AdicCompletion, RingEquiv'`: zero hits.
- `msearch.py ... leansearch` with "Etale morphisms induce isomorphic completions
  of local rings when the residue field map is an isomorphism": eight hits,
  ring-etale definitions and the open-immersion residue-field isomorphism, no match.
- `msearch.py ... grep 'etale.*complet|complet.*etale|completedLocal|completion.*residue'`:
  six hits, the local-completion residue-field lemma and unrelated etale
  idempotent constructions.
- `rg` of the same expression plus the item id in the upstream
  `WeilConjectures` and side-project `lean/Sheaf`: no exact theorem. Read the
  nearby `CompletedStalkIsomorphismEtale` (the converse implication),
  `NodalPointEtaleLocality` (a nodal specialization consuming this item), and
  `FlatLocalCompletionIso` (the local-ring proof input). None states this node.
- `rg` for `etale_completedLocalRing_iso` and `completedLocalRing_iso` in Mathlib,
  upstream `WeilConjectures`, side-project `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no name collision.

Validation: the prescribed `scompile.py Q138 lem-trf-etale-completed-local-ring-iso`
compiled this file as both sandbox and library module, cleanly (2.5 s and 2.2 s),
with no errors or warnings. No project or global build was run.

## Second reading by Q138

Author's separate self-check for this direct worker delivery; the maintainer
provides the independent review, as specified in the dispatcher brief. Reopened
the node and the final module and checked the binders and each conjunct. The
algebraically closed field, locally finite type C over k, actual etale map e,
point y and x = e(y) occur with exactly the node's assumptions. Both sides of
`hres` use the appropriate structure morphism, rather than abstract residue-field
isomorphisms. The closed-point conclusions name C and D respectively, and the
residue isomorphism refers to `e.residueFieldMap y`. The completion coordinate
formula uses the actual `e.stalkMap y` and the maximal ideals of the corresponding
stalks in the correct contravariant direction C to D. Bijectivity is required of
that uniquely determined coordinatewise map. The existential formulation includes
existence, so no implication about a nonexistent map can make it vacuous.
No extra Noetherian, dimension, finite-type, or coefficient-splitting hypothesis
was introduced. No mismatch was found and no mathematical change was needed.
