## Worker report

The node is stated exactly by the existing declaration
`AlgebraicGeometry.ProEtale.condensedPushforwardHom_comp_map_coefficientMap`, in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`, lines 122–132 of
the published framework. The delivery changes only the item's `lean` record, with
`existing: true`, and introduces no Lean module. The branch label `slopmaster2` refers to
the published upstream root, including the framework overlay described in
`coord/pefw-upstream-framework.md`. I read the exact current source through
`scompile.py --source` as well as the shared overlay. The old local upstream checkout lacks
this module; that absence does not imply absence from the published library.

Source read: the current blueprint's
`sec-six-functors-basics/sk-def-sfb-coefficient-change/lem-sfb-coefficient-pushforward-square.md`
and its proof file, together with the current DAG's expanded statement and three proof steps.
The upstream theorem's proof uses comparison naturality, functoriality of pushforward,
associativity, and unit naturality, exactly as those steps specify.

Hypothesis-by-hypothesis and clause-by-clause match:

- Condensed abelian groups Λ and Λ' are
  `{Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}`. This is precisely the coherent
  topology on profinite sets, not a discrete coefficient ring or a different sheaf category.
- An arbitrary condensed abelian-group morphism is `(a : Λ ⟶ Λ')`. The theorem explicitly
  has `omit [MonObj Λ] [MonObj Λ'] [IsMonHom a] in`. The compiler-printed full type confirms
  that no ring structure or multiplicativity condition remains. The ring-oriented module
  docstring does not restrict this theorem's actual type.
- Arbitrary schemes and a scheme morphism are `{X Y : Scheme.{u}} (f : X ⟶ Y)`; there is
  no properness, finite-type, nonemptiness, or weakly-étale hypothesis on f.
- For T = X,Y, `upperStarFromPoint T` is the recorded `p_T^*`, defined as
  `pointUpperStar ⋙ (toSpecZ T)^*[Ab.{u + 1}]`. `condensedRingObj Λ T` is definitionally
  `(upperStarFromPoint T).obj Λ`, even without a ring structure. The same holds for Λ'.
- `coefficientMap a T` is definitionally `(upperStarFromPoint T).map a`, giving exactly
  the node's `a_T`, at both X and Y.
- `upperStar Ab.{u + 1} f`, `lowerStar Ab.{u + 1} f` and
  `upperStarLowerStarAdjunction Ab.{u + 1} f` are the recorded pullback, pushforward,
  and their adjunction. The unit is that adjunction's `.unit.app`.
- `upperStarFromPointComp f` is the recorded `c_f`: associativity, followed by whiskering
  `pointUpperStar` with `(upperStarComp Ab f (toSpecZ Y)).symm`, followed by the
  identification induced by `comp_toSpecZ f`. Thus its direction is precisely
  `upperStarFromPoint Y ⋙ upperStar Ab f ≅ upperStarFromPoint X`.
- `condensedPullbackHom Λ f` is definitionally `(upperStarFromPointComp f).hom.app Λ`:
  `Functor.compAlgHom` is an abbreviation of `.app`. It gives exactly α_f, and similarly
  for Λ' and α'_f. No unspecified comparison map is introduced.
- `condensedPushforwardHom Λ f` is definitionally the adjunction unit at Λ_Y followed by
  `(lowerStar Ab f).map (condensedPullbackHom Λ f)`; `Adjunction.unitAlgHom` abbreviates
  `.unit.app`. This gives precisely η_f, and similarly η'_f.
- The equality is
  `condensedPushforwardHom Λ f ≫ (f)_*[Ab].map (coefficientMap a X) =
  coefficientMap a Y ≫ condensedPushforwardHom Λ' f`.
  Since Lean's `≫` writes composition in execution order, this is exactly
  `f_*a_X ∘ η_f = η'_f ∘ a_Y`, with source Λ_Y and target f_*Λ'_X.
- The conditional ring-specialization clause uses these very same declarations.
  Supplying `[MonObj Λ] [MonObj Λ'] [IsMonHom a]` makes `coefficientMap` the recorded
  ring-object morphism and the coefficient-morphism instances give the recorded ring maps.
  Forgetting their structures changes none of the underlying arrows. This is definitional
  compatibility, not an extra assumption on the abelian-group theorem.

Dependency declarations read and used (all eight current statement/proof dependencies):

- `def-sfb-upper-star-from-point`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.upperStarFromPoint` and its monoidal/braided instances.
- `def-sfb-finite-upper-star`, `def-sfb-finite-lower-star`, and
  `def-sfb-finite-upper-lower-star-adjunction`:
  `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.ProEtale.upperStar`, `.lowerStar`, `.upperStarLowerStarAdjunction`.
  Read their complete declaration contexts and docstrings: the coefficient category is
  Grothendieck abelian and the scheme morphism is arbitrary; specialize to `Ab.{u+1}`.
- `def-sfb-pullback-from-point-comp-iso` and proof dependency
  `sk-def-sfb-pullback-from-point-comp`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.upperStarFromPointComp`, with the latter node also recording
  `.isMonoidal_upperStarFromPointComp`. The same comparison gives both underlying arrows.
- `def-sfb-coefficient-map`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`,
  `AlgebraicGeometry.ProEtale.coefficientMap`, and its functor-induced ring-map structure.
- `sk-def-sfb-coefficient-morphisms`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.condensedPullbackHom`, `.coefficientPullbackIso`,
  `.condensedPushforwardHom`, `.isMonHom_condensedPullbackHom`,
  `.isMonHom_condensedPushforwardHom`.

Edge cases checked: coefficients without any ring structure (compiler-validated), arbitrary
zero/noninjective/nonsurjective a, zero coefficient objects, a = identity, f = identity,
and empty schemes. None is excluded by a binder or a typeclass. The equality is naturality
for every a and f, including these cases. The scheme universe u and coefficient universe u+1
are exactly the dependency interfaces' size convention; no site universes were equated.
There is no index set, degree bound, or characteristic restriction.

Searches performed on 2026-10-18 (recorded by msearch.py in the sandbox's searches.jsonl):

- LeanFinder: "Coefficient changes of condensed abelian groups commute with the mate from
  pullback from the point to pushforward". Eight results, including light-condensed
  internal-Hom naturality and `SheafOfModules` adjunction formulas; no exact Mathlib match.
- Loogle: `CategoryTheory.NatTrans.naturality`. Nine results, including the general
  naturality square and unrelated pullback/pushout constructions; the general square
  alone is not this coefficient pushforward identity.
- Mathlib grep: `condensedPushforwardHom|coefficientMap`, entire Mathlib. Zero hits.
- LeanSearch: "naturality of condensed coefficient changes with pushforward and the
  adjunction unit". Eight results, including `CategoryTheory.Adjunction.unit_naturality`
  and sheaf-of-modules adjunction formulas; no exact Mathlib match.
- `rg` in the old upstream source and `lean/Sheaf` for `coefficientMap`,
  `condensedPushforwardHom`, and the exact theorem name. Old upstream has no module-object
  match; side Sheaf hits are unrelated coefficient maps, not this declaration.
- `grep -rn` for the node id in old upstream: no hit.
- Exact-name `rg` in the shared published `lean/WeilConjectures` framework finds the
  theorem at ChangeOfCoefficients.lean:126. Opened that theorem, its explicit `omit`,
  full section parameters, docstring and proof, and all definitions used above.

Validation: a scratch-only file `scratch/Check.lean` imports the existing module and prints
its complete type and axioms. It also checks the existing proof term against the node's
fully expanded equation, using only explicitly bound Λ, Λ', a, X, Y, f, u, and no MonObj
or IsMonHom hypotheses. `scompile.py Q56 lem-sfb-coefficient-pushforward-square
scratch/Check.lean` passed both sandbox and library checks without errors or warnings.
`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound` for this theorem.
The scratch file is outside `lean/` and is not delivered. No proofs or definitions were
added, no node statement was corrected, and there are no statement disputes or new nodes.

## Second reading by Q56

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
