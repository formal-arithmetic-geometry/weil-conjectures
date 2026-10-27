## Worker report

The module `Sheaf.AlgebraicGeometry.CubicalFibrewiseAmpleCriterion` states
`AlgebraicGeometry.CubicalRigidifiedLine.isAmple_over_affine_of_fibrewise`, with
proof `sorry`. There are no new definitions, dependency repairs, new nodes, or
statement corrections. The copied node changes only in `lean`. The source of the
proof is the accepted agent-written seven-step split, not a claimed numbered
Raynaud theorem: the original Raynaud XI remains locally WANTED. I read the
current blueprint section and the node's source/proof_origin and proof in full.
The declaration docstring gives all seven steps and their mathematical arguments.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| A base scheme T | `{T : Scheme.{u}}` |
| T locally Noetherian | `[IsLocallyNoetherian T]` |
| Every local ring is an integrally closed domain | `hnormal : ∀ t : T, IsDomain (T.presheaf.stalk t) ∧ IsIntegrallyClosed (T.presheaf.stalk t)` |
| A group scheme p : H → T, with addition, inverse and identity over T satisfying group identities | `H : Grp (Over T)`; the scheme is `H.X.left`, and p is `H.X.hom`. `Grp` supplies the actual group object, rather than arbitrary operations. |
| Commutativity | `[IsCommMonObj H.X]`; with the given group object this supplies the `CommGrpObj H.X` used by the cubical-line definition. |
| Smooth | `[Smooth H.X.hom]` |
| Separated, meaning closed-immersion diagonal | `[IsSeparated H.X.hom]`, whose defining field is `isClosedImmersion_diagonal` |
| Finite presentation | `[QuasiCompact H.X.hom]` together with smoothness, which implies `LocallyOfFinitePresentation`, and separatedness, which implies `QuasiSeparated`. These are precisely the three parts of finite presentation in the node's dependency. |
| Semiabelian geometric fibres | `hsemi : HasSemiabelianGeometricFibres H`; the recorded definition quantifies over algebraically closed fields and the actual base-changed group law, allowing torus rank zero. |
| A cubical rigidified line (B,r,tau) | `B : CubicalRigidifiedLine H.X`; `B.line`, `B.invertible`, `B.rigidification`, `B.sectionIso`, and `B.compatible` are exactly the line, local rank-one property, identity rigidification, nowhere-vanishing cube section, and permutation/normalization/cocycle laws. |
| All line pullbacks are tensor inverse images | Every pullback in the signature is `Scheme.Modules.tensorPullback`. Its source construction is change of rings on the abelian inverse image, not bare inverse image or an arbitrary map. |
| Residue-field fibre H_t = H ×_T Spec kappa(t) | `H.X.hom.fiber t`, definitionally the canonical pullback along `T.fromSpecResidueField t` |
| B_t is the pulled-back line | `(tensorPullback (H.X.hom.fiberι t)).obj B.line`; `fiberι` is the first pullback projection. |
| Ample for every t in T | `hample : ∀ t : T, ∃ hBt : (...).IsInvertible, @IsAmple (H.X.hom.fiber t) (...) hBt` |
| Every affine open V of T | `∀ V : T.Opens, IsAffineOpen V → ...` |
| B restricted to p^{-1}(V) is ample | `∃ hBV : (...).IsInvertible, @IsAmple (H.X.hom ⁻¹ᵁ V).toScheme ((tensorPullback (H.X.hom ⁻¹ᵁ V).ι).obj B.line) hBV` |

The existential witnesses `hBt` and `hBV` merely supply the proof-valued
invertibility parameter required by the recorded `IsAmple`. Invertibility of
these actual tensor pullbacks follows already from `B.invertible` and
`invertible_pullback_tensor`; it adds no mathematical condition or additional
conclusion. Proof irrelevance makes `IsAmple` independent of the witness. This
avoids hidden local instances and `let`/`have` in the signature. The theorem has
no properness, generic ampleness, symmetry, connected-base, or characteristic
assumption.

Recorded statement-dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, with morphisms `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `AlgebraicGeometry.LocallyOfFinitePresentation` (the local part of finite presentation, supplied by smoothness).
- `Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres`: `AlgebraicGeometry.HasSemiabelianGeometricFibres`.
- `Sheaf.AlgebraicGeometry.CubicalRigidifiedLine`: `AlgebraicGeometry.CubicalRigidifiedLine`, including the exact cube and compatibility predicate.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the recorded normalized adjunction; its public upstream functor `AlgebraicGeometry.Scheme.Modules.tensorPullback` is the functor used here. I read its full construction in `WeilConjectures.AlgebraicGeometry.TensorPullback`: `tensorPullbackObj` is the specified tensor inverse image.
- `WeilConjectures.AlgebraicGeometry.Ample`: `AlgebraicGeometry.Scheme.Modules.IsAmple`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, with `IsDomain`, exactly the recorded inline normal-domain convention on stalks.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `CategoryTheory.Limits.pullback`; it underlies Mathlib's canonical `Scheme.Hom.fiber` and its projection, from `Mathlib.AlgebraicGeometry.Fiber`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and `Scheme.fromSpecResidueField`.

Every currently stated proof dependency has its module imported (Mathlib
matches are used even when a node has no `lean` record). In particular the
strict-henselian density, affine-cap-section, ample-limit descent, affine
strict-local comparison, affine ample pullback, and algebraic-space ample-local
modules are regular proof imports. The sole unstated proof dependency
`lem-sfb-cubical-strict-local-affine-seed` has neither a Lean record nor a
Mathlib match, so has no import yet. It is a proof input, not a missing notion
needed to type this statement; its full use is recorded in step 2.

Edge cases checked before drafting:

- T may be empty or disconnected: no `Nonempty` or irreducibility assumption
  is imposed. Normality is stated pointwise, so also makes sense on the empty base.
- Empty affine opens are included. The inverse-image scheme is empty; the
  absolute ample definition has its compactness clause and a vacuous pointwise clause.
- Rank-zero tori and abelian fibres are retained by the supplied semiabelian definition.
- Nonproper smooth groups, including split tori, are not excluded. For a torus
  the structure line is ample on the affine fibres, as expected.
- No symmetry of the underlying line is assumed: the permutation invariance
  is solely that in the cubical structure, as the node requires.
- Every residue-field fibre is tested, including generic and nongeneric points.
  Neither testing only closed points nor only geometric fibres replaces `hample`.
- `u` is explicit and arbitrary; both schemes and residue fields live in this
  universe. No smaller independent universe is used for geometric fibre tests;
  the recorded semiabelian definition uses fields in the scheme universe.
- No positive degree or characteristic is fixed in the signature. Positive
  tensor exponents are quantified inside the recorded ampleness definition.

Searches for an existing statement (all returned types were checked):

1. `msearch.py leanfinder`, query “Fibrewise ample cubical rigidified line on a
   semiabelian group scheme over a normal locally Noetherian base is ample over
   every affine open of the base”: eight hits on affine-space fibres,
   affine-morphism fibres, affine transition limits, and diagonals. None concerns
   cubical lines or this ampleness criterion.
2. `msearch.py loogle`, query
   `AlgebraicGeometry.Scheme.Modules.IsAmple, AlgebraicGeometry.CubicalRigidifiedLine`:
   zero hits; the remote Mathlib search reports the project-specific `IsAmple`
   identifier unknown. This is a search limitation, not a positive match.
3. `msearch.py grep`, query
   `cubical|semiabelian|fibrewise.*ample|fiberwise.*ample`, restricted to
   `AlgebraicGeometry`: zero hits.
4. `msearch.py leansearch`, query “An ample line bundle on every fibre of a
   semiabelian group scheme with a cubical rigidification is relatively ample
   over a normal locally Noetherian base”: eight hits on local Noetherian
   structures, affine fibres, and formally unramified structures; none matches.
5. `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
   `cubical.*[Aa]mple|[Aa]mple.*cubical|fibrewise.*ample|fiberwise.*ample`:
   only the proper-fibrewise-projectivity theorem and its trace-formula citation;
   that result has properness hypotheses and does not state this criterion.
   `grep -rn` of the exact item id in `lean/WeilConjectures` found no declaration.
   `rg` of `dag/lean_names_upstream.json` for cubical/ampleness combinations
   found no existing statement. The current blueprint section had no independently
   matching cubical ampleness statement. Dependency definitions found by these
   searches were reused, not copied.

Validation: the theorem passed both the isolated sandbox and actual library-module
checks through `scompile.py` on the live published build, about two seconds each,
without errors or warnings. All variables and the sole universe are explicitly
bound with `autoImplicit` and `relaxedAutoImplicit` disabled; every Lean line is
at most 100 characters. The only proof is the requested named theorem with `sorry`.

The prescribed `deliver2.py --no-push` dry run passed server preflight and
both per-file compilation checks (`OK (dry run)`, commit `9025fb96e77`).

## Second reading by Q102

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
