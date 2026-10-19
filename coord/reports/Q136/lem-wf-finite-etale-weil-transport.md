## Worker report

Item: lem-wf-finite-etale-weil-transport. The delivery contains one module,
`Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleWeilTransport`, and changes only
this item's `lean` record. There is no statement correction, new node, or dependency repair.

The theorem `AlgebraicGeometry.Scheme.FiniteEtale.finiteEtaleWeilTransport` has exactly
one postponed proof, `sorry`. Its docstring gives all nine finite-stage proof steps from
the node, including descent of arbitrary morphisms and independence from the model.
The two accompanying definitions have real data:

- `covariantTransport a` is the lift of the existing postcomposition functor
  `MorphismProperty.Over.map` through the finite-cover full subcategory. Thus its object
  has exactly P's underlying scheme and structure map `P.obj.hom ≫ a.hom`; its map has
  exactly the original underlying morphism. Étaleness and finiteness come from the
  existing composition/isomorphism instances. It introduces precisely the T in this node.
- `fiberAutBaseChange f s g` is
  `(pullbackFiberIso f s).symm ≪≫ Functor.isoWhiskerLeft (pullback f) g ≪≫
  pullbackFiberIso f s`. This is the canonical base-change map on the actual natural
  automorphism groups, without any chosen path, arbitrary map or extra hypothesis.
  It is the construction of Stacks 0BND(3). The existing `fundamentalGroupMap` is packaged
  for groups in the scheme universe; the full `Aut (fiber s)` lives one universe higher.
  The helper uses the existing fibre identification and whiskering directly, so does not
  constrain universes or choose another fundamental group. Both helpers belong to this
  node's transport construction and are listed in `lean.declarations`.

Hypothesis and clause correspondence (write i for `fiberAutBaseChange` only in this report):

| Node | Lean |
| --- | --- |
| Global k0 = Fq and fixed closure k | `D : WeilConjectures.FiniteFieldDatum.{u}`; fields `D.k₀`, `D.k`, existing algebra and closure instances |
| U0 a k0-scheme | `U₀ : Over (Spec (CommRingCat.of D.k₀))` |
| Geometrically connected | `[GeometricallyConnected U₀.hom]` |
| Separated | `[IsSeparated U₀.hom]` |
| Finite type | `[LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]` |
| U = U0 times k | `(D.geometricFiber U₀).left`, exactly the recorded geometric fibre |
| Chosen geometric point | `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and `s : Spec (.of Ω) ⟶ ...` |
| F and Pi = Aut(F) | Existing `fiber s : U.FiniteEtale ⥤ FintypeCat.{u}` and `Aut (fiber s)` |
| W with arithmetic base point | Existing `weilGroup U₀.hom (s ≫ Limits.pullback.fst ...) (Aut (fiber (s ≫ Limits.pullback.fst ...)))` |
| n = deg(w) | `w.val.2.toAdd`, definitionally the projection `weilGroupDeg ... w` converted from `Multiplicative ℤ` |
| Phi = id times Spec(gamma) | Existing `D.geometricFrobenius U₀`, not the relative or absolute Frobenius |
| T_n on covers/maps | `covariantTransport ((D.geometricFrobenius U₀) ^ w.val.2.toAdd)`; real postcomposition data as above |
| Natural finite-set isomorphism tau | First existential `τ : covariantTransport ... ⋙ fiber s ≅ fiber s` |
| Conjugation by w | `∃! h : Aut (fiber s), i h = w.val.1 * i g * w.val.1⁻¹ ∧ ...` |
| tau(gx) = (wgw^-1)tau(x) | `τ.hom.app P (g.hom.app _ x) = h.hom.app P (τ.hom.app P x)`, for every cover P and every x in F(T_n P) |
| T_-n is isomorphic to (Phi^n)^* | Middle conjunct `Nonempty (covariantTransport (Phi ^ (-n)) ≅ pullback (Phi ^ n).hom)` |
| Natural fibre bijection lambda | Last existential `lam : pullback (Phi ^ n).hom ⋙ fiber s ≅ fiber s` |
| Conjugation by w^-1 | `∃! h : Aut (fiber s), i h = w.val.1⁻¹ * i g * w.val.1 ∧ ...` |
| lambda(gx) = (w^-1gw)lambda(x) | `lam.hom.app P (g.hom.app _ x) = h.hom.app P (lam.hom.app P x)` for all P and all x in F((Phi^n)^*P) |
| Naturality for every cover morphism | Both bijections and the comparison are categorical natural isomorphisms on the full `Scheme.FiniteEtale` category, whose arrows are all base-scheme morphisms |
| No action on P, coefficient group or cohomology | None occurs in the binders; natural automorphisms are evaluated directly, without a supplied action |

The unique-h formulation spells out the node's identification of Pi as its geometric
subgroup: it asserts existence of the conjugate in that subgroup and uses its unique
preimage. It adds no assumption of an unspecified conjugation operation. In particular,
it does not assume the theorem's transport or its equivariance as input. The topology
is the existing natural-automorphism topology; no topological or continuity hypothesis
needs to be introduced for these finite-fibre identities.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and
  `FiniteFieldDatum.geometricFiber`, through the Frobenius import.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `WeilConjectures.FiniteFieldDatum.geometricFrobenius`; read also `galoisMap`, its inverse,
  projection equations, and affine formula to check the geometric convention.
- `WeilConjectures.AlgebraicGeometry.GaloisCategories`: `Scheme.FLC`; this records the
  dependency's other category. For the category used here it explicitly reuses
  `Scheme.FiniteEtale` and its fibre, rather than introducing a second category.
  Its current source was read with `scompile.py --source`, because it is absent locally.
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`:
  `Scheme.FiniteEtale`, `FiniteEtale.fiber`; the latter is the dependency's exact recorded
  declaration and has finite sets as target.
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup`:
  `constantCover`, `arithmeticFrobenius`, `constantCoverAction`, `geometricFrobenius`,
  `weilGroup`, `weilGroupDeg`; full signatures and docstrings were read. The Weil group
  accepts the actual arithmetic Aut group, and its degree is the second projection.
- `def-weil-pbc-scheme-conventions` is explicitly a convention-only record: it defines
  no extra declaration. Its existing `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact`, `IsFinite`, `Etale` meanings are used.
- The recorded proof dependency `lem-galois-pi1-functoriality` uses source declarations
  now split between `FundamentalGroup.Functoriality` (`pullback`) and
  `FundamentalGroup.Restriction` (`pullbackFiberIso`, `fundamentalGroupMap`). The latter
  is publicly imported because the statement's canonical helper uses its fibre iso.
- Stated proof dependencies are imported: `AlgebraicGeometry.GroupScheme.Defs` for
  `etale_SpecMap_algebraMap_tfae`; `WeilConjectures.GroupTheory.WeilGroup` for
  `MonoidHom.exact_weilGroupDeg`; Mathlib finite-field Galois theory and universal
  injectivity for the finite/separable and finite-radicial facts. Pullback, finite and
  étale composition/base-change definitions and the finite-field Frobenius declarations
  arrive through the public imports. The currently unstated proof-only node
  `lem-wf-finite-etale-field-limit-descent` has no module to import; it is explicitly
  named in the proof docstring, not assumed as an added hypothesis or newly stated here.

Source checks: opened local Stacks `pione.tex` at lemma-functoriality-galois (0BN5),
theorem-fundamental-group (0BND), lemma-limit (0BTV), and lemma-ses-field (0BTX).
Opened the current `main-20261015` proof of `lem-wf-finite-constant-h1-pi1`, particularly
the penultimate paragraph's `s⁻¹ g s` pullback formula. The two conjugation orientations
are exactly those of the node. No node fault or disputed statement was found.

Edge cases checked: degree zero is permitted; positive and negative degrees are integers
and use `Aut` integer powers. The degree-zero lift need not be the identity, so its
conjugation has not been discarded. Empty and disconnected finite covers are included:
neither `P` nor its finite fibre has a nonempty, connected or torsor assumption.
The base scheme cannot be empty once the chosen geometric point exists; no additional
nonemptiness hypothesis is introduced. The global datum covers every allowed p, a and
chosen algebraic closure. All scheme, field and group universes are explicit; Pi and
the arithmetic Aut group retain their actual higher universe. No small-group equality
or extra connected-space assumption is needed.

Existing-declaration searches:

- `msearch.py ... leanfinder "Weil group transport finite etale fibre functor conjugation
  geometric Frobenius"`: eight results, including `evaluationEquivOfIsGalois`,
  `instIsFundamentalGroupAutFunctorFintypeCat`, and arithmetic ring Frobenius facts;
  none states the arithmetic-lift transport.
- `msearch.py ... loogle "FiniteEtale, weilGroup, fiber"`: zero results; the service
  reports `unknown identifier 'FiniteEtale'`. Compensated by exact source searches.
- `msearch.py ... loogle "CategoryTheory.Aut, FintypeCat"`: twelve results, including
  `instMulActionAutFunctorFintypeCatObjFiniteObj`, `mulAction_def`,
  `mulAction_naturality`, and Galois-object automorphism lemmas. These confirm that
  evaluation is the standard action; none identifies transport by an arithmetic lift.
- `msearch.py ... grep "weilGroup|covariantTransport" CategoryTheory`: zero Mathlib hits.
- `msearch.py ... leansearch "A Weil element induces a natural finite etale fibre functor
  transport intertwining geometric fundamental group conjugation"`: eight results,
  including `toAutMulEquiv_apply`, `toAutHomeo` and abstract `FiberFunctor` declarations;
  no exact match.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for `weilGroup`, transport
  and conjugation: found the existing Weil-group infrastructure, Frobenius-point
  transport, and the downstream finite-constant-H1 theorem. These do not state this
  general finite-cover theorem. The downstream theorem's proof invokes this item;
  it is not used as an input here.
- Exact node-id search in upstream `WeilConjectures`: no match. Exact declaration-name
  searches for `covariantTransport`, `fiberAutBaseChange`, `finiteEtaleWeilTransport`
  across Mathlib, upstream and `lean/Sheaf`: no match.

Validation: single-file compilation uses only the prescribed `scompile.py` wrapper.
The initial elaboration errors were repaired by making postcomposition's morphism
explicit, qualifying `Functor.isoWhiskerLeft`, and using `lam` as an identifier.
The delivered declaration has no auto-bound implicits, file-local notation, local
instances, or lines over 100 characters. The dry run with `deliver2.py --no-push` passed: commit `d19adb7f44` passed
server preflight and compilation. The final delivery uses `deliver2.py`; no direct
Git operation or live-file edit is used.

## Second reading by Q136

No second reading by a worker: since 2026-10-17 the worker delivers directly and the
maintainer's independent review is the only review.
