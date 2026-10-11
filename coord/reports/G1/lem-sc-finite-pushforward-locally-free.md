## Worker report

Module: `Sheaf.AlgebraicGeometry.FinitePushforwardLocallyFree`.
Declaration: `AlgebraicGeometry.Scheme.Modules.exists_locally_constant_rank_pushforward_unit`.
This is a theorem statement with `sorry`, not a proof or a new definition. The node is
unchanged except for its `lean` record; no statement correction, new node, or dependency
module is needed. All notions in the signature are already defined by Mathlib.

Hypothesis and clause matching:

- Schemes X and Y: `{X Y : Scheme.{u}}`, for arbitrary universe `u`.
- Their morphism f: `(f : X ⟶ Y)`.
- Finite: `[IsFinite f]`.
- Flat: `[Flat f]`.
- Locally of finite presentation: `[LocallyOfFinitePresentation f]`.
- The actual O_Y-module f_*O_X:
  `(pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)`.
  The Mathlib `pushforward` is restriction of scalars along the structure-sheaf map,
  with sections O_X(f inverse-image U); `unit` is O_X as a module over itself.
- Finite locally free, with a trivializing open cover: for every `y : Y`,
  `∃ U : Y.Opens, y ∈ U` and an isomorphism of its restriction with
  `SheafOfModules.free (ULift.{u} (Fin (d y)))`. These neighbourhoods cover Y.
  `Nonempty` states existence of the module isomorphism without choosing one.
  Mathlib's `over U` restricts a sheaf to the slice of opens contained in U,
  which is precisely the open-subscheme restriction. Mathlib's `free` is the
  coproduct of copies of the structure module. The lifted finite index type
  has exactly d(y) elements and fits the structure-module universe.
- The rank is finite: `∃ d : Y → ℕ`, and the trivialization has exactly d(y) summands.
- The rank is locally constant: `IsLocallyConstant d`, together with
  `∀ z : Y, z ∈ U → d z = d y` on each chosen trivializing neighbourhood.
  This latter clause is redundant but explicitly relates the rank on the
  whole neighbourhood to the number of summands in its trivialization.
- Equivalent disjoint clopen decomposition: the sets `{y | d y = n}`, n in ℕ,
  are disjoint and cover Y; each is open by `IsLocallyConstant d`, and closed
  because its complement is likewise a preimage of a set and is open.
  On each piece the displayed local trivializations have constant rank n.
  This renders the parenthetical equivalence, not an extra conclusion.

Dependency declarations read and used:

- `def-pc-scheme`: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-finite-integral-morphism`: Mathlib.AlgebraicGeometry.Morphisms.Finite,
  `AlgebraicGeometry.IsFinite`; also read the node's other recorded declaration
  `AlgebraicGeometry.IsIntegralHom` in Morphisms.Integral (not needed in this signature).
- `def-weil-flat-morphism`: Mathlib.AlgebraicGeometry.Morphisms.Flat,
  `AlgebraicGeometry.Flat`; its docstring and `Flat.iff_flat_stalkMap` give the
  equivalence between the affine-local and stalk-wise definitions.
- `def-sbc-locally-finite-presentation`:
  Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation,
  `AlgebraicGeometry.LocallyOfFinitePresentation` (its affine-local definition is
  equivalent to the node's pointwise affine-neighbourhood condition).

Other existing Mathlib definitions used, not copied:
`Scheme.Modules.pushforward` (AlgebraicGeometry.Modules.Sheaf),
`SheafOfModules.unit` (Algebra.Category.ModuleCat.Sheaf),
`SheafOfModules.over` (Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous),
`SheafOfModules.free` (Algebra.Category.ModuleCat.Sheaf.Free),
`IsLocallyConstant` (Topology.LocallyConstant.Basic).

Source checks: local `literature/stacks-project/morphisms.tex` is absent on this
machine, so opened the authoritative pages
[Tag 02KB](https://stacks.math.columbia.edu/tag/02KB) and
[Tag 04MH](https://stacks.math.columbia.edu/tag/04MH).
02KB identifies finite local freeness with finite + flat + local finite presentation;
04MH supplies the disjoint clopen rank decomposition. The declaration docstring
contains both proof steps from the node, including the restriction/direct-image
identification and the degree-zero case, with the three proof dependency ids.
No node fault or statement dispute was found.

Edge cases checked before writing:

- Empty Y: the unique rank function on the empty space is locally constant and
  the neighbourhood requirement is vacuous; no nonemptiness hypothesis occurs.
- Empty X over nonempty Y: take constant zero rank, and free on `Fin 0` is zero;
  no positive-rank or surjectivity hypothesis is imposed.
- Identity morphism: constant rank one and usual structure-module trivializations.
- Disconnected bases: different components can have different ranks; there is no
  global constant-rank or uniform bound assumption.
- Arbitrary characteristic and non-Noetherian bases are permitted. Local finite
  presentation is retained, so the finite flat non-finitely-presented exception
  is not mistakenly included.

Searches performed:

- `msearch.py ... leansearch "finite flat morphism pushforward structure sheaf locally free"`:
  UNAVAILABLE, Internal Server Error. No mathematical verdict assigned to this service.
- `msearch.py ... leanfinder "finite flat locally finitely presented morphism pushforward
  structure sheaf finite locally free module locally constant rank"`: eight results,
  including Flat's ring-hom property, flat_appLE, finitePresentation_appLE, and
  sheaf finite-presentation/finite-type APIs; no exact whole statement.
- `msearch.py ... loogle "SheafOfModules.IsFiniteLocallyFree, AlgebraicGeometry.Flat"`:
  zero hits, unknown identifier SheafOfModules.IsFiniteLocallyFree.
- `msearch.py ... grep "IsFiniteLocallyFree|isLocallyConstant_finrank" AlgebraicGeometry`:
  three hits in Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean, including
  `Scheme.Hom.isLocallyConstant_finrank`; rank-function theorem only.
- `rg` of IsFiniteLocallyFree, LocallyFree and pushforward in upstream
  WeilConjectures/AlgebraicGeometry found Modules/FinitePushforward.lean.
  Read the whole module: `isFiniteLocallyFree_pushforward` treats an arbitrary
  finite locally free input module and concludes finite local freeness; it does
  not state the explicit locally constant rank function/trivializations.
  `isFiniteLocallyFreeOfRank_pushforward_unit` assumes a prescribed globally
  constant degree d, and does not give this varying-rank statement.
  These are related existing results, not exact declarations of this node.
  Also read the existing finite-locally-free classes in
  WeilConjectures/Mathlib/Algebra/Category/ModuleCat/Sheaf/LocallyFree.lean.
- `rg` for the item id in upstream WeilConjectures: no hit.
- `rg` for IsFiniteLocallyFree, finite_pushforward and rank/local-constancy in
  project lean/Sheaf: no exact statement or corresponding module.
- `rg` for the new full-name suffix in dag/lean_names_upstream.json, Mathlib,
  upstream WeilConjectures and lean/Sheaf: no collision.

Validation: prescribed `scompile.py` compiled the 51-line module on the server
in 2.1 seconds, exit code 0, with no errors or warnings. All universes and
variables are explicitly bound. Only the theorem proof is `sorry`.

## Second reading by G1

I independently opened the base node, its sandbox copy and the 51-line Lean module,
all four statement dependency nodes and their Mathlib declarations. The only node
change is the Lean record; there are no new nodes, dependency modules, or statement
corrections to audit. The recorded signature agrees verbatim with the file.

Source reading: I fetched and read the actual `morphisms.tex` source from
https://raw.githubusercontent.com/stacks/stacks-project/master/morphisms.tex,
including `lemma-finite-flat` (02KB) and `lemma-finite-locally-free` (04MH), and
checked the authoritative tag pages. The former applies to arbitrary schemes;
local Noetherianity is assumed only for the separate equivalence with finite flat
without local finite presentation. The latter includes all degrees d >= 0.
No standing field, characteristic, separation, or Noetherian assumption applies.

Object/hypothesis/conclusion checklist and verdicts:

- Objects X and Y are arbitrary schemes: `{X Y : Scheme.{u}}`. I read
  Mathlib's `Scheme` and `Scheme.Hom` in AlgebraicGeometry/Scheme.lean; they are
  locally ringed spaces locally isomorphic to affine spectra and their morphisms,
  matching `def-pc-scheme`. PASS.
- Morphism f from X to Y: `(f : X ⟶ Y)`, in the category of those schemes. PASS.
- Finite hypothesis: `[IsFinite f]`. Finite.lean:39 extends `IsAffineHom f`
  and requires finiteness of `(f.app U).hom` for each affine U. This is exactly
  the finite clause of `def-weil-finite-integral-morphism`; integrality is not
  an additional hypothesis. PASS.
- Flat hypothesis: `[Flat f]`. Flat.lean:42 uses flat affine-section maps;
  `Flat.iff_flat_stalkMap` at line 106 identifies this with flatness at every
  point, exactly `def-weil-flat-morphism`. PASS.
- Locally of finite presentation: `[LocallyOfFinitePresentation f]`, whose
  affine-section condition at FinitePresentation.lean:45 is the affine-local
  equivalent of `def-sbc-locally-finite-presentation`. This does not demand
  global finite presentation or introduce a separate compactness hypothesis. PASS.
- The module is the actual f_*O_X, not a presheaf or a constant sheaf:
  `(pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)`. I read
  Modules/Sheaf.lean:166 and its section formula at line 170, and the unit
  definition in ModuleCat/Sheaf.lean:173. Sections over V are O_X(f^-1 V),
  with the O_Y action induced by f. PASS.
- Finite rank on local trivializations: `∃ d : Y → ℕ` and
  `SheafOfModules.free (ULift.{u} (Fin (d y)))`. I read Sheaf/Free.lean:39:
  free is the coproduct of structure modules. Fin(d y) has d y elements;
  ULift only changes the universe. The inferred ring sheaf on the right is
  `Y.ringCatSheaf.over U`, not the ring sheaf of X. PASS.
- Open cover and module isomorphisms: `∀ y : Y, ∃ U : Y.Opens, y ∈ U` and
  the displayed `Nonempty (... .over U ≅ free ...)`. A neighbourhood for each
  point gives a cover, and every pointwise trivializing cover gives these
  neighbourhoods. I read `overFunctor`/`over` in PushforwardContinuous.lean
  and `Scheme.Modules.overEquiv` in Modules/Sheaf.lean:558: sheaves on the slice
  over U are equivalent to O_U-modules. Thus this is exactly the restriction
  of f_*O_X to the open subscheme U. Nonempty asks for existence of an
  isomorphism, without selecting one. PASS.
- Locally constant rank: `IsLocallyConstant d` with
  `∀ z : Y, z ∈ U → d z = d y`. The latter condition lets each trivialization
  use the rank throughout its neighbourhood; it imposes no stronger condition
  because any trivializing neighbourhood can be intersected with the open
  fibre of d through y. I read IsLocallyConstant in Basic.lean, including its
  open/closed fibre lemmas. The fibres d^-1(n) partition Y into disjoint clopen
  rank pieces, exactly the node's parenthetical equivalent conclusion. PASS.
- Quantifier order: the function d is chosen once on Y before the neighbourhood
  and isomorphism for each y. The cover is not assumed finite, nor is the
  varying rank uniformly bounded. All hypotheses are precisely the node's. PASS.

Edge cases: empty Y gives a vacuous neighbourhood condition and the empty rank
function. Empty X over a nonempty Y allows d = 0; Fin 0 is empty and the coproduct
is the zero module. Identity morphisms allow rank one. Disconnected schemes may
have different ranks on different components, including unbounded ranks. No
nonemptiness, surjectivity, positive rank, field, characteristic, Noetherianity,
or separatedness instance is present. Universe u is arbitrary; Mathlib's scheme
category uses one universe for both schemes, into which any pair of scheme sizes
can be placed, and the finite-index ULift imposes no size restriction.

Independent searches (different wording from the first reader):

- `msearch.py G1 lem-sc-finite-pushforward-locally-free leanfinder
  "A finite flat morphism of finite presentation has a structure sheaf direct
  image trivial on neighbourhoods with finite rank varying locally constantly"`:
  eight hits. Module.isLocallyConstant_rankAtStalk is a ring-module rank fact;
  the remaining hits concern flatness/finite presentation. No exact theorem.
- `msearch.py ... loogle "IsLocallyConstant, SheafOfModules.free"`: zero hits.
- `msearch.py ... grep
  "exists_locally_constant_rank_pushforward_unit|finite_pushforward_locally_free"`:
  zero upstream/Mathlib hits.
- Direct `rg` with `locally_constant.*rank|rank.*pushforward|locally_free.*pushforward`
  on upstream WeilConjectures, project lean/Sheaf and Mathlib/AlgebraicGeometry,
  and `exists_locally_constant|IsLocallyConstant d` on the project DAG/library:
  no exact existing declaration. I also independently opened the upstream
  FinitePushforward.lean signatures at lines 214 and 254 and the locally free
  classes at LocallyFree.lean:133,156. The first theorem takes an arbitrary module
  and its finite-local-freeness instance; the second prescribes global degree d.
  Neither is the whole pointwise locally constant-rank existential statement.
  The worker's LeanSearch failure remains documented above, not treated as a hit.

H5/H6/H8/H9: no definitions or instances are introduced, no data are sorry,
and the only theorem has precisely `by sorry`. Its docstring cites 02KB/04MH,
the blueprint id, and both node proof steps with all three dependency ids,
including the restricted pushforward identification and rank zero. Every import
supplies a notion in the signature; the namespace and explicit universe/binders
follow project conventions, and all lines are at most 100 characters.

Mismatches found: none. Changes: appended this independent second-reading report;
kept the correct Lean source and node record unchanged. Clean compilation and the
prescribed delivery preflight are run after this reading.
