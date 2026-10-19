## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.BirationalDenseOpenIso` states
`AlgebraicGeometry.exists_dense_open_isIso_of_generic_stalks`, with proof `sorry`.
It introduces no definitions, new nodes, dependency replacements or statement changes.

The source is `literature/stacks-project/morphisms.tex`,
`lemma-birational-isomorphism-over-dense-open` (Tag 0BAJ), choosing separatedness
in alternative (1) and local finite presentation in alternative (2). I read the
statement and proof there, and `lemma-birational-birational` (Tag 0BAC).

Hypothesis and conclusion correspondence:

- Schemes and the given morphism `f:Y → X` are `{X Y : Scheme.{u}} (f : Y ⟶ X)`.
  The universe `u` is explicitly declared; no auto-implicit binders are used.
- Separatedness is `[IsSeparated f]`, the Mathlib diagonal-closed-immersion class.
- Local finite presentation is `[LocallyOfFinitePresentation f]`, the recorded
  Mathlib affine-local finite-presentation class. No global finite presentation,
  quasi-compactness or Noetherian assumption is introduced.
- Finitely many components of the target and source are respectively
  `(hX : (irreducibleComponents X).Finite)` and
  `(hY : (irreducibleComponents Y).Finite)`.
- Mapping the generic points of the source components bijectively onto those of
  the target is `(hgeneric : Set.BijOn f (genericPoints Y) (genericPoints X))`.
  Mathlib's `genericPoints Z` is `{η | closure {η} ∈ irreducibleComponents Z}`.
  Thus these are exactly generic points in the recorded `IsGenericPoint` sense;
  `genericPoints.isGenericPoint` records that fact. `BijOn` includes mapping into
  the target set, injectivity on the source set and surjectivity onto the target
  set. It refers to the actual point map of `f`, not an unrelated bijection.
- The specified generic local-ring isomorphism is
  `(hstalk : ∀ η ∈ genericPoints Y, IsIso (f.stalkMap η))`.
  I read `Scheme.Hom.stalkMap` in `Scheme.lean`: its type is precisely the map
  `X.presheaf.stalk (f η) ⟶ Y.presheaf.stalk η` in `CommRingCat`.
  This includes nilpotents and is not a condition merely on residue fields.
- The dense open is `∃ V : X.Opens, Dense (V : Set X) ∧ ...`.
- The isomorphism of the whole inverse image is `IsIso (f ∣_ V)`.
  I read `morphismRestrict` in `Mathlib.AlgebraicGeometry.Restrict`: its domain
  is `(f ⁻¹ᵁ V).toScheme` and its codomain is `V.toScheme`, and it is the
  canonical base-change restriction. No arbitrary source open substitutes for
  the full inverse image.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsSeparated`, reexported by its
  recorded module `Mathlib.AlgebraicGeometry.Morphisms.Proper`; the definition
  itself is in `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- `def-sbc-locally-finite-presentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` in
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `def-weil-irreducible-components`: `irreducibleComponents` in
  `Mathlib.Topology.Irreducible`, exactly maximal irreducible subsets.
- `def-sc-generic-point`: `IsGenericPoint` in `Mathlib.Topology.Sober`, together
  with its existing component-generic-point set `genericPoints`.
- `def-weil-locally-ringed-space-morphism`:
  `AlgebraicGeometry.LocallyRingedSpace.Hom` in
  `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`, underlying `Scheme.Hom`.
  Its `prop` field says the stalk maps are local homomorphisms.

The module also imports the recorded proof-dependency module
`Sheaf.AlgebraicGeometry.SeparatedLqfBaseChange`; I read its
`AlgebraicGeometry.separated_lqf_base_change` declaration and docstring, and only
its separatedness clause is needed by the natural-language proof. The remaining
stated proof dependencies are Mathlib open and closed immersions and
`IsClosedImmersion.of_comp`, already available through the public imports.
`lem-per-birational-common-dense-opens` has no Lean binding or Mathlib match in
the base, so no import can yet be added for that proof-only dependency. It is
named in the full proof docstring for stage 3. All three DAG proof steps are
included there, including the density argument on open subschemes that avoids
the false inference that every surjective closed immersion is an isomorphism.

Edge cases checked before writing:

- Empty schemes: a bijection of component generic-point sets forces the two
  schemes to be simultaneously empty. The empty open is dense in the empty
  target and the restriction is an isomorphism. No nonempty hypothesis is used.
- Identity maps, including nonreduced schemes and finite unions of components,
  satisfy the hypotheses and allow `V = ⊤`.
- A cusp normalization illustrates a restriction which becomes an isomorphism
  after removing a proper closed subset; the conclusion does not assert that
  `f` itself is an isomorphism.
- The doubled-origin line map shows why separatedness matters for replacing a
  pair of common dense opens by the entire inverse image. That map fails the
  separatedness hypothesis.
- Nilpotent structure is retained in generic stalks; reducedness, normality,
  integrality and residue-field substitutes have not been introduced.

Searches (all run before writing the declaration):

- `msearch.py ... leanfinder`: "A separated locally finitely presented
  birational morphism of schemes with finitely many irreducible components is
  an isomorphism over a dense open" returned local-isomorphism, normalization
  and general isomorphism criteria; none states the desired construction.
- `msearch.py ... leansearch`: "A separated morphism locally of finite
  presentation that is birational on generic points is an isomorphism over a
  dense open" returned separatedness, properness and openness criteria;
  none gives this theorem.
- `msearch.py ... loogle`: `AlgebraicGeometry.Scheme.Hom, IsGenericPoint, IsIso`
  reported unknown identifier `IsIso`, so it is not negative evidence.
  The corrected query `AlgebraicGeometry.Scheme.Hom, CategoryTheory.IsIso`
  succeeded with zero hits.
- `msearch.py ... grep` in `AlgebraicGeometry/`:
  `birational|isIso.*[Dd]ense|[Dd]ense.*isIso` found the Birational modules.
  I read the declaration `Scheme.Birational`: it packages existence of a
  partial isomorphism and does not construct a saturated inverse-image open
  for the given morphism from generic stalk hypotheses.
- `rg` with the same expression in upstream `WeilConjectures/` and side
  `lean/Sheaf` found normalization and Chow modifications and statements
  using dense-open birationality as an input, not this generic-stalk theorem.
  `NormalModificationCodimensionOne.lean` cites this item in its proof
  docstring but does not state it. Its stronger geometric hypotheses also
  differ from this item.
- Searching the upstream sources for this exact node id found nothing.
  Searching `dag/lean_names_upstream.json`, Mathlib, upstream and side sources
  for the proposed full declaration's short name found no declaration.

No statement dispute or mathematical fault was found. The previous worker's
blocker confused the Q45 stage-1 landing (ledger line 41500) with a stage-2
statement landing: the base node is split and independently reviewed, but its
`lean` field is absent. This delivery preserves that reviewed split and adds
only its stage-2 binding.

Validation: prescribed `scompile.py` compiled both the sandbox form and actual
library module path successfully, with no errors or warnings (2.2 s and 1.9 s).

## Second reading by Q111

Author's self-check; no separate agent was started, as required by this brief.
The maintainer supplies the independent review. I reopened the node and source
signatures and matched each clause as listed above. In particular `Set.BijOn`
is on generic-point sets of the given point map; stalk `IsIso` is at every
source generic point and has the contravariant local-ring direction; and
`morphismRestrict` uses the full inverse image of the target open. The finite
component hypotheses cover both schemes. No mismatch or correction was found.
The node copy changes only `lean`; its recorded statement is extracted verbatim
from the theorem signature. No new or dependency nodes need second reading.
