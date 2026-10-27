## Worker report

Item: lem-sfb-cartesian-groupoid-pushforward-adjunction.
Module: Sheaf.AlgebraicGeometry.CartesianGroupoidPushforwardAdjunction.
Main declaration: AlgebraicGeometry.Scheme.exists_cartesian_groupoid_pushforward_adjunction.

This states Tags 03LJ and 09VH with the ordinary module-adjunction restriction specified
in both directions. There is one postponed theorem, with the eight-step DAG proof in its
docstring. The four helper definitions contain actual canonical operations, no chosen map
or existence-only replacement. No statement correction or new node is needed.

Hypotheses, individually:

- `S : Scheme.{u}` and `U R U' R' : Scheme.{u}` give the base, object and arrow schemes.
- `p q p' q'` are their structure morphisms to S. `_hsS`, `_htS`, `_hsS'`, `_htS'`
  assert source and target are over S. The groupoid identities imply that identity,
  inversion and composition are over S as well; no extra assumption is imposed.
- `s t e i c`, `s' t' e' i' c'` are all the groupoid operations, with composition
  on the recorded `pullback s t` and `pullback s' t'`.
- `hG : IsGroupoid ...` and `hG' : IsGroupoid ...` are exactly the recorded laws.
- `f₀`, `f₁` are the specified object and arrow maps. `_hfS`, `_hfS'` make them over S.
- `hs`, `ht` express commutation with source and target. `_he`, `_hi` express identity
  and inversion. `_hc` uses `pullback.map` to express commutation with composition.
- `[QuasiCompact f₀]` is quasi-compactness of affine inverse images, equivalently of
  all compact open inverse images, and `[QuasiSeparated f₀]` is compactness of its diagonal.
- `[Flat s']`, `[Flat t']` are the two required flat morphisms; no flatness of f₀,
  or source/target of the unprimed groupoid, is assumed.
- `_hcart : IsPullback f₁ t t' f₀` is exactly the target square, with no extra source-square
  hypothesis. Inversion gives the latter in the proof.

Conclusions, individually:

- The existing `GroupoidModule` gives precisely QCoh of each groupoid: `moduleObj`,
  `quasiCoherent`, `beta`, `unit`, `cocycle`; its Hom subtype is exactly the displayed
  intertwining equation. It uses the recorded tensor pullback with canonical comparisons.
- Existential `F` has the direction QCoh(R') to QCoh(R), and `G` the reverse direction.
- `hF` is equality of underlying functors with tensor pullback by f₀; it specifies both
  the underlying objects and every underlying morphism, including identities/composition.
- The first conjunct specifies F's descent map as f₁-pullback of beta, with the canonical
  target and source square comparisons inserted by `groupoidMorphismPullbackDescent`.
- `hP` is equality of underlying functors with `Modules.pushforward f₀`, specifying
  f₀,*N and f₀,*a exactly. Existence of `G.obj N` includes quasi-coherence.
- For every N the second conjunct asserts `IsIso` for the actual target and source
  base-change maps. `groupoidMorphismBaseChange` is the existing `moduleBaseChangeMap`
  expressed through the opaque-but-equal `groupoidModulePullback` interface.
- The following equality is b_t followed by f₁,*(gamma) equals delta followed by b_s.
  Since b_s is explicitly invertible, this specifies exactly
  delta = b_t; f₁,*(gamma); b_s inverse. `eqToHom` only transports along the exact
  equality `hP` of underlying functors. Identity/cocycle conditions are the `unit`
  and `cocycle` fields of the returned object `G.obj N`.
- `adj : F ⊣ G` supplies the natural Hom bijections and all adjunction laws.
- The final two clauses require its forward and inverse Hom equivalence to have exactly
  the ordinary module transposes on underlying maps. Thus ordinary transposition of
  every equivariant map is equivariant in each direction. No arbitrary Hom equivalence
  is substituted. `groupoidModuleOrdinaryAdjunction` is literally the already recorded
  section-normalized ordinary adjunction in the existing groupoid coordinates.
- Naturality of the descent construction is encoded by F/G being functors, equality
  of their underlying functors, and the existing natural canonical base-change maps.
  Naturality of the Hom bijections is part of `Adjunction`.

Dependency declarations used and read (full signatures and docstrings):

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Sheaf.AlgebraicGeometry.SchemeGroupoidLaws: `Scheme.IsGroupoid`, all its fields.
- Sheaf.AlgebraicGeometry.CoherentFiniteType: exposes Mathlib
  `SheafOfModules.IsQuasicoherent`; only this clause of pqf-def-coherent is needed.
- Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction: `Modules.tensorPullback`,
  `tensorPullbackSectionAdjunction`, `tensorPullbackSectionComp`, `tensorPullbackSectionId`.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`, `pullback.map`,
  projections, universal property; scheme pullbacks are supplied by the groupoid import.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: `AlgebraicGeometry.Flat` and its stalkwise
  equivalence, the exact interpretation of def-weil-flat-morphism.
- Sheaf.AlgebraicGeometry.SchemeGroupoidModule: `GroupoidModule`, `Hom`, `category`,
  `forgetToModules`, and `groupoidModulePullback`. This landed node is newly cited in
  stmt_deps, so its notion is reused rather than copied.
- WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction:
  `Scheme.Modules.moduleBaseChangeMap`. The live definition node
  `def-sfb-module-base-change-map` owns this plain canonical map and is cited in stmt_deps;
  the open-restriction theorem node is not used by this statement.

Public dependencies already expose schemes, pullback and quasi-coherence transitively.
The stated proof-dependency modules imported privately are
WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde,
WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs,
WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar, and
Sheaf.Paper.IntegralResidueMatePasting. Mathlib's mate and transpose-square lemmas are
already exposed by the canonical-base-change dependency, and the qcqs and flat
base-change permanence declarations by the morphism imports. The recorded degree-zero
flat-base-change proof will require the full flat-base-change theorem at proof stage:
its existing EulerChar binding is only a special case; no such special-case hypothesis
has been inserted in this statement. GroupoidCoinductionAdjunction is downstream and
is not imported (it cites this item).

Edge cases checked before writing: the identity groupoid morphism (both ordinary
transposes and base-change maps normalize to identity comparisons); zero modules and
zero equivariant maps; empty object/arrow schemes; arbitrary possibly non-flat f₀;
non-Noetherian/nonseparated object schemes with f₀ still qcqs. No finite-type,
coherence, properness, flatness of f₀, nonemptiness or surjectivity restriction appears.
The single universe u follows the recorded `GroupoidModule` and `Scheme.Modules`
universes and includes every scheme in the chosen ambient size.

Searches performed:

- msearch.py leanfinder: "Pushforward of quasi coherent modules along a cartesian
  morphism of scheme groupoids is right adjoint to pullback": 8 hits, ordinary module
  adjunctions/pseudofunctor, no equivariant groupoid theorem.
- msearch.py loogle: "Groupoid, Adjunction": 0 hits (unknown identifier Groupoid).
- msearch.py grep, AlgebraicGeometry: "equivariant|GroupoidObject": 0 hits.
- msearch.py leansearch: "The ordinary module sheaf adjunction restricts to equivariant
  quasi coherent modules on a cartesian scheme groupoid morphism": 8 hits, ordinary
  sheafification and pullback adjunctions, no match.
- rg of project WeilConjectures and Sheaf for Groupoid/equivariant modules located the
  existing SchemeGroupoidModule and the downstream GroupoidCoinductionAdjunction.
  rg for this item's id found only the downstream proof citation, not a statement.
- rg for moduleBaseChangeMap located the exact canonical ordinary map upstream; read
  its definition and naturality before reusing it. No second base-change map is defined:
  the helper merely changes to the already established groupoid pullback coordinates.
- DAG filename/content searches found def-sfb-scheme-groupoid-module and the recorded
  base-change-map node; these are reused. No new definition node is needed.

Validation: prescribed scompile.py compiled both sandbox and named library module
cleanly under the 60-second limit. The initial probe exposed a mismatch between the
irreducible groupoid pullback and tensorPullback; the ordinary-adjunction coordinate
helper fixes it without changing any mathematical object or hypothesis.

## Second reading by NR

Author's second reading, not an independent review: the dispatcher explicitly forbids
starting other agents; the maintainer supplies the independent reading. I reopened the
node and final module and matched every hypothesis and clause as listed above.
The source and target orientations agree with the node: beta goes t-star to s-star,
and `pullback.fst s t` is the later arrow. The direct-image equation has b_t on the
left and b_s after delta on the right, hence gives precisely the stated inverse-b_s
composite. Both ordinary Hom transpose directions are present, with transports in
opposite directions. Groupoid laws, quasi-coherence and identity/cocycle conditions
are carried by the existing objects rather than weaker substitute predicates.
The added ordinary-adjunction helper fixes only opacity in elaboration. No source
statement correction, hypothesis change or disputed mathematical assertion remains.
