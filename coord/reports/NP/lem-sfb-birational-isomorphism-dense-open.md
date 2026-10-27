## Worker report

The module `Sheaf.AlgebraicGeometry.BirationalIsomorphismDenseOpen` states
`AlgebraicGeometry.exists_dense_open_isIso_of_separated_birational`, with its only proof
`sorry`. No definitions or additional statements are introduced. The item node changes only
in `lean`.

Source read: `literature/stacks-project/morphisms.tex`, lines 13370–13397,
Tag 0BAJ, `lemma-birational-isomorphism-over-dense-open`; also lines 13072–13117,
Tag 0BAC, `lemma-birational-birational`. The item is precisely the separated alternative
of 0BAJ(1) and locally-of-finite-presentation alternative of 0BAJ(2), with the source's
X and Y exchanged to match this node. The node's three proof steps are preserved in the
Lean docstring, including the closed-section argument replacing the source's finite-map
shrinking argument. There is no statement correction or dispute.

Clause-by-clause correspondence:

- Schemes and the specified morphism `f : Y → X` are `{X Y : Scheme.{u}} (f : Y ⟶ X)`.
  The arbitrary explicitly bound universe `u` is Mathlib's universe for schemes and does not
  impose a size, integrality, reducedness or nonemptiness restriction.
- Separatedness is `[IsSeparated f]`, meaning that the diagonal is a closed immersion.
- Local finite presentation is `[LocallyOfFinitePresentation f]`.
- Finitely many irreducible components of X and Y are respectively
  `(hX : (irreducibleComponents X).Finite)` and
  `(hY : (irreducibleComponents Y).Finite)`.
- The generic points of irreducible components are Mathlib's `genericPoints Y` and
  `genericPoints X`. Their definition in `Topology/Sober.lean:277` is
  `{x | closure {x} ∈ irreducibleComponents _}`. Thus membership means precisely that
  `IsGenericPoint x Z` for an irreducible component Z, using the recorded generic-point
  definition, with no newly chosen generic point or duplicate notion.
- Mapping those generic points bijectively onto those of X is
  `(hgeneric : Set.BijOn f (genericPoints Y) (genericPoints X))`.
  `BijOn` includes mapping into that set, injectivity on the source set, and surjectivity
  onto the target set. It concerns this given f.
- The induced homomorphism of local rings is the canonical `f.stalkMap η`, of type
  `X.presheaf.stalk (f η) ⟶ Y.presheaf.stalk η` in `CommRingCat`.
  `(hstalk : ∀ η : Y, η ∈ genericPoints Y → IsIso (f.stalkMap η))` states exactly that
  each required homomorphism is an isomorphism. It does not identify a local ring with a
  residue field or function field, which would lose the nonreduced cases.
- Existence of an open subset of X is `∃ V : X.Opens`; density is `Dense (V : Set X)`.
- The map from its full inverse image to V is Mathlib's `f ∣_ V`, namely
  `morphismRestrict f V : (f ⁻¹ᵁ V).toScheme ⟶ V.toScheme`. The conclusion
  `IsIso (f ∣_ V)` therefore supplies precisely the stipulated isomorphism for this map.
  It does not merely assert that some dense source open maps isomorphically to V.

Dependency declarations and interfaces read:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`, lines 42–46 and 74–77. The canonical
  `Scheme.Hom.stalkMap` is at lines 235–238.
- `def-weil-proper-morphism`: recorded module `Mathlib.AlgebraicGeometry.Morphisms.Proper`;
  the separatedness clause uses `AlgebraicGeometry.IsSeparated` from its public imports,
  `Morphisms/Separated.lean:42–47`. No properness hypothesis is imposed.
- `def-sbc-locally-finite-presentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:42–48`.
- `def-weil-irreducible-components`: the exact Mathlib match `irreducibleComponents`,
  `Mathlib.Topology.Irreducible:105–108` (maximal irreducible subsets).
- `def-sc-generic-point`: `IsGenericPoint`, `Mathlib.Topology.Sober:37–40`;
  `genericPoints` at line 277 and `genericPoints.isGenericPoint` at line 285 use that
  same closure-of-singleton definition. Both are in the recorded module.
- `def-weil-locally-ringed-space-morphism`: `AlgebraicGeometry.LocallyRingedSpace.Hom`,
  `Mathlib.Geometry.RingedSpace.LocallyRingedSpace:77–83`, with the locality field on stalk
  maps; used through the scheme morphism and its canonical stalk map.
- The conclusion uses `AlgebraicGeometry.morphismRestrict`,
  `Mathlib.AlgebraicGeometry.Restrict:568–570`, defined using the canonical pullback.
- Already stated proof dependencies are imported non-publicly: `IsOpenImmersion` from
  `Mathlib.AlgebraicGeometry.OpenImmersion`; `IsSeparated.instSndScheme` and
  `IsClosedImmersion.of_comp` from `Mathlib.AlgebraicGeometry.Morphisms.Separated`;
  and `IsClosedImmersion` from `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
  `lem-sfb-birational-common-dense-opens` has neither a Lean record nor a Mathlib match
  in the read DAG. It is used only in the future proof, so it supplies no import yet and
  no missing statement interface here. No statement depends on a downstream result.

Edge cases checked before writing and on rereading:

- Empty X and Y have empty generic-point and component sets. `Set.BijOn` and the stalk
  condition are then vacuous, and the empty open is dense in the empty space. No
  `Nonempty` hypothesis is introduced. If exactly one scheme is empty, either there is
  no such morphism or the bijection on generic points fails.
- The identity of any scheme with finitely many components, including a nonreduced scheme
  such as the spectrum of dual numbers, satisfies the statement with V the whole scheme.
  Stalks remain the full local rings, not residue fields.
- A dense open immersion with finitely many components fits the hypotheses; take its
  image as V. There is no quasi-compactness assumption hidden in local finite presentation.
- Reducible schemes are allowed; the generic-point set is not replaced by a single point
  or by an integral scheme's `genericPoint`.
- The doubled-origin morphism fails separatedness, as expected; the statement does not
  assume that generic information alone gives a global isomorphism.
- The localization example preceding 0BAC (Z localized at the odd integers) shows why
  one may not discard the finite-presentation hypothesis. It is not a counterexample
  to the stated lemma.

Searches run through `msearch.py NP lem-sfb-birational-isomorphism-dense-open`:

- LeanFinder: `A separated locally finitely presented morphism with bijective generic
  points and isomorphic generic local rings is an isomorphism over a dense open of its
  target`. Eight hits, including `isomorphisms_eq_stalkwise`, `IsLocalIso`,
  `isomorphisms_eq_isOpenImmersion_inf_surjective`, and `IsPreimmersion`; none proves
  the desired generic-stalk shrinking statement.
- Loogle: `"Birational", "IsIso"`. Zero hits.
- LeanSearch: `Birational separated morphism locally of finite presentation is an
  isomorphism over a dense open`. Eight hits, including properness descriptions,
  `locallyOfFinitePresentation_of_isOpenImmersion`, `Scheme.RationalMap.dense_domain`,
  `IsLocalIso`, and `IsOpenImmersion.isIso`; none is this statement.
- grep: `birational|generic.*[Ii]so|[Ii]so.*generic` in `AlgebraicGeometry`.
  Thirteen hits in Birational/Dominant, Birational/Birational, RationalMap, and
  FunctionField. `Scheme.Birational` says that some partial isomorphism exists;
  it does not assert the conclusion for the specified f.
- Direct `rg` searches for `birational|Birational` and dense-isomorphism patterns in
  `lean/WeilConjectures` and `lean/Sheaf`, plus the exact node id in
  `lean/WeilConjectures`, found no matching theorem. Relevant candidate signatures read:
  `exists_dense_open_isIso_component_modifications` requires reducedness and a coproduct
  of component modifications; `isIso_fromNormalization_denseOpen` concerns a relative
  normalization. Neither states this node. `dag/lean_names_upstream.json` has no match
  for this item or the new declaration name. The exact new declaration name was also
  searched in Mathlib, WeilConjectures and Sheaf, with no hit.

Validation: `scompile.py NP lem-sfb-birational-isomorphism-dense-open` compiled the delivered
file in both sandbox form (4.9 s) and its intended library module (4.4 s), with no errors
or warnings. All variables and the universe are explicit, the theorem has only `sorry`
as its proof, and every Lean line has at most 100 characters.

## Second reading by NP

The dispatcher-run worker reread the final node and module together; no additional agent
was started, as instructed. The maintainer supplies the independent review of this delivery.
On this rereading, `{X Y : Scheme.{u}} (f : Y ⟶ X)` keeps the node's direction;
`[IsSeparated f]` and `[LocallyOfFinitePresentation f]` match the two selected source
alternatives; hX and hY retain both finite-component hypotheses. `Set.BijOn` renders all
three parts of the generic-point bijection, and hstalk applies to every generic point of Y
with the correct contravariant local-ring map. `V : X.Opens` with `Dense` and
`IsIso (f ∣_ V)` gives the full inverse-image conclusion. In particular, no reducedness,
quasi-compactness, single-component, nonempty or function-field hypothesis has slipped in.
The source lines, definition of `genericPoints`, and type of `morphismRestrict` were read
again to check these points. No mismatch was found and no statement change was required.
