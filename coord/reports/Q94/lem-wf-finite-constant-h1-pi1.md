## Worker report

The module `Sheaf.Paper.FiniteConstantH1Pi1` states
`WeilConjectures.finiteConstantH1Pi1`. Its only proof is `sorry`. It uses the canonical
upstream torsor-monodromy equivalence and asserts that it is an additive isomorphism,
natural under every pointed automorphism and under pullback for every Weil degree.
No data definitions, duplicate fundamental groups, arbitrary comparison maps, or
additional mathematical conjectures are introduced. The natural-language statement,
proof, and proof dependencies of the item are unchanged.

The source read was the current blueprint
`literature/blueprint/main-20261015/blueprint/sec-purity-real-sheaves/sk-p-real-rankone/lem-wf-finite-constant-h1-pi1.md`,
including equation (3.1) and both naturality clauses. The seven-step DAG proof is
included in the theorem docstring, with each of its named inputs.

Hypotheses and conclusions are rendered as follows.

- The globally fixed finite field and its arbitrary fixed algebraic closure are
  `D : FiniteFieldDatum.{u}`. The datum contains the prime, exponent, cardinality,
  finite base field, closure, inclusion, and algebraic-closure structure.
- The scheme over that field is `U₀ : Over (Spec (CommRingCat.of D.k₀))`.
  Its structure morphism has `GeometricallyConnected`, `IsSeparated`,
  `LocallyOfFiniteType`, and `QuasiCompact`. The last two together are finite type.
- The geometric base change is literally `(D.geometricFiber U₀).left`, constructed
  by the recorded dependency, with the first projection to `U₀.left` expressed by
  `pullback.fst U₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))`.
- Connectedness of the model and geometric fibre is exposed as the two
  `ConnectedSpace` instances required by the fundamental-group API. These are
  consequences, not extra restrictions: apply
  `GeometricallyConnected.connectedSpace_of_subsingleton` to the model map and
  its base change to `Spec D.k`. Both spectra are nonempty singleton spaces.
  Equivalently, the geometric-fibre assertion is the defining geometric
  connectedness condition applied to the closure embedding.
- The geometric point is `s : Spec (.of Ω) ⟶ (D.geometricFiber U₀).left` for an
  explicitly bound field `Ω : Type u` with `IsAlgClosed Ω`. It need not have
  values in the particular chosen closure. This is the recorded convention for
  geometric points, allowing arbitrary algebraically closed field extensions.
- `G` and `G₀` are compact topological group models of the fibre functors at `s`
  and its composite with the first projection. Their `MulAction` and
  `IsFundamentalGroup` instances give precisely the geometric and arithmetic
  étale fundamental groups. This is the project's required small-universe
  encoding, canonically identified with `Aut F` by `toAutContinuousMulEquiv`.
- The coefficients are `M : Type (u + 1)` with `AddCommGroup M` and `Finite M`.
  `TopologicalSpace M` with `DiscreteTopology M` supplies exactly the discrete
  coefficient topology. This size is required by the recorded constant-sheaf
  interface; finite groups in smaller universes can be lifted into it.
- The constant étale abelian sheaf is
  `(constantSheaf (D.geometricFiber U₀).left.smallEtaleTopology
  AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)`.
  Its first cohomology is `Sheaf.H ... 1`, the accepted Ext spelling documented
  in `def-weil-pbc-etale-cohomology.lean.note`. The public mathematical meaning
  is the same cohomology of derived global sections; the dependency records
  their stage-3 comparison. No group cohomology is substituted.
- Equation (3.1) is `∃ e : Sheaf.H ... 1 ≃+ Additive (G →ₜ* Multiplicative M), ...`.
  `Additive` and `Multiplicative` only change notation for the group laws:
  multiplication of characters is pointwise addition in M. Thus `≃+` asserts
  both bijectivity and preservation of the abelian group law. The first conjunct,
  `(e c).toMul = EtaleTorsor.sheafHEquivContinuousMonoidHom M s G c`, fixes the
  map for every cohomology class to the existing canonical torsor character.
  It does not leave an arbitrary group isomorphism unspecified.
- Pointed naturality is the second conjunct. It quantifies over every
  `a : Aut (D.geometricFiber U₀).left` and `ha : s ≫ a.hom = s`, every torsor P,
  and every g. Its left side is e of the canonical class of `P.pullback a.hom`.
  Its right side evaluates e of the class of P on the induced map of g.
  That induced map is exactly `fundamentalGroupMap` for the canonical
  `pullbackFiberIso a.hom s`, followed by the `eqToIso` induced by ha.
  There is no arbitrary fibre transport hypothesis. Canonical torsor classes
  exhaust cohomology by `EtaleTorsor.bijective_classH1`, so quantification over
  P is equivalent to the full cohomological naturality square.
- Weil naturality is the third conjunct. The element w belongs to the recorded
  `weilGroup U₀.hom (s ≫ pullback.fst ...) G₀`, with the recorded
  `weilGroupDeg`. Its pullback is literally along
  `((D.geometricFrobenius U₀) ^ (weilGroupDeg ... w).toAdd).hom`, using the
  recorded geometric coefficient Frobenius for the arbitrary chosen closure.
  In particular this is pullback, with no assumption of a transport theorem.
- The geometric subgroup inclusion is the canonical
  `fundamentalGroupMap (pullbackFiberIso (pullback.fst ...) s) G G₀`.
  `w.val.1` is the arithmetic fundamental-group component of the actual Weil
  element. For every g the conclusion gives a unique h whose image is
  `w.val.1⁻¹ * image(g) * w.val.1`, and evaluates the pulled-back character at g
  as the original character at h. This is exactly inverse conjugation in the
  geometric subgroup. The unique-preimage formulation spells out the subgroup
  identification implicit in the node, without an unspecified conjugation map.

Dependencies read and used:

- `def-wf-weil-group`: upstream
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup`, including
  `FiniteEtale.constantCover`, `constantCoverAction`, `geometricFrobenius`,
  `weilGroup`, and `weilGroupDeg`. The theorem uses the latter two directly.
- `def-galois-fibre-functor`: upstream
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`, `FiniteEtale.fiber`.
  Its full source and the project's prescribed fundamental-group convention were read.
- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`,
  `WeilConjectures.FiniteFieldDatum` and `FiniteFieldDatum.geometricFiber`.
- `def-weil-pbc-etale-cohomology`: upstream
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `Etale.rightDerivedGlobalSections` and `Etale.cohomology`; imported for the
  proof bridge. The existing node expressly permits the `Sheaf.H` convention here.
- Added statement dependency `def-weil-frobenius-detailed`:
  `Sheaf.AlgebraicGeometry.FrobeniusDetailed`,
  `WeilConjectures.FiniteFieldDatum.geometricFrobenius`. Its construction, inverse,
  projection identities, and coefficient-Frobenius specialization were read.
- Added statement dependency `cor-galois-abelian-h1`: upstream
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor`,
  `EtaleTorsor.sheafHEquivContinuousMonoidHom`. The prerequisite's missing Lean
  record is supplied as an existing declaration, described below.
- Canonical pullback objects and maps:
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback`,
  `EtaleTorsor.pullback`, and the upstream `Restriction` module's
  `FiniteEtale.pullbackFiberIso` and `FiniteEtale.fundamentalGroupMap`.
- Recorded proof inputs are imported: `Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence`
  (`Scheme.exists_finiteEtale_flc_equivalence_sheaf`),
  `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence`
  (`FiniteEtale.exists_fiber_flc_equivalence` and its base-change clauses),
  `WeilConjectures.CategoryTheory.Sites.Torsor`
  (`Sheaf.Torsor.classH1`, `Sheaf.Torsor`, and `Sheaf.nonempty_equiv_H_one_torsor`),
  and `WeilConjectures.GroupTheory.WeilGroup` (`MonoidHom.exact_weilGroupDeg`).
  `lem-wf-finite-etale-weil-transport` currently has no recorded Lean module;
  its proof import is consequently absent. The theorem does not assume that
  transport as data or as a hypothesis: it asserts the resulting Weil formula.

Edge cases checked before writing: the empty scheme is excluded already by
geometric connectedness and the chosen geometric point; it has not been removed
by a new hypothesis. The trivial coefficient group gives trivial groups on both
sides. For a simply connected geometric scheme both sides are zero. No coprimality
condition on the order of M is used, including characteristic-p coefficients.
Degree zero, arbitrary negative degrees, and positive degrees are all included by
integer powers of the actual Frobenius automorphism. An inner geometric element
of degree zero acts trivially on abelian characters, as required. Changing the
lift of a degree leaves the pullback unchanged and changes only an inner
conjugation, so the formula includes lift independence. Pointed automorphisms
include the identity and are not restricted to automorphisms over the closure.
No site-universe equality or curve/smoothness assumption is imposed.

Searches performed through `msearch.py Q94 lem-wf-finite-constant-h1-pi1`:

- LeanFinder: "First etale cohomology finite constant abelian group continuous
  homomorphisms fundamental group Weil conjugation". Eight hits, chiefly
  `IsFundamentalGroup`, the absolute Galois group abelianization, and abstract
  group-cohomology H1. No full étale statement with the two naturality clauses.
- Loogle: `ContinuousMonoidHom, CategoryTheory.Sheaf.H`. Zero hits.
- Mathlib grep: `etale.*fundamental|WeilGroup|H1IsoOfIsTrivial|torsor.*cohomology`.
  Five hits, all in `RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`.
  They concern abstract group cohomology and do not state the item.
- LeanSearch: "First etale cohomology of a finite constant abelian group is
  continuous characters of the etale fundamental group naturally under Weil descent".
  Eight hits on abstract H1, the cyclotomic character, fundamental group models,
  and zeroth continuous cohomology. No exact full match.
- Source grep for `lem-wf-finite-constant-h1-pi1` found `FundamentalGroup/Frobenius.lean`
  and `EtaleCohomology/Purity/RealSheaves/FundamentalGroup.lean`. Read their relevant
  declarations: `monodromy_mapIso` takes a transport and its intertwining law as
  hypotheses, and the latter file treats a curve quotient with an extra
  `IsEtaleQuotient` interface. Neither asserts the full item, in particular
  additive group isomorphism and actual all-degree Weil pullback without such
  hypotheses. They are not exact existing bindings for this node.
- Source search for `sheafHEquivContinuousMonoidHom` found the canonical bijection
  and its torsor-evaluation theorem in `FundamentalGroup/Torsor.lean`; these are
  reused, and the corresponding corollary node is bound to them.
- Mathlib and side-project searches for `finiteConstantH1Pi1`,
  `finite_constant_h1_pi1`, and `sheafHEquivContinuousMonoidHom` found no conflicting
  declarations. A side-project search for the blueprint id found no module.

Validation: prescribed `scompile.py` file-only compile passed with no errors or
warnings. The file contains no auto-bound variables, local notation, private
abbreviations, local instances, or hidden `let` statements. All lines are at most
100 characters. The only postponed theorem is the named statement carrying this
item's complete proof plan. No statement is disputed and no source correction
was necessary. The worker delivers directly; the maintainer performs independent
review, as required by the current brief.

## Dependency modules

`cor-galois-abelian-h1`: no new module. The node had neither a Lean record nor a
Mathlib match, but the exact upstream declaration already exists. Its record is
set, changing only `lean`, to
`AlgebraicGeometry.Scheme.EtaleTorsor.sheafHEquivContinuousMonoidHom` in
`WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor`, with `existing: true`.
This is a canonical bijection for every connected scheme, geometric point and
finite abelian group, constructed from the canonical class map and monodromy.
`sheafHEquivContinuousMonoidHom_classH1` says that the class of P goes to its
monodromy, and `fiber_map_vaddHom_monodromy` says that this character is precisely
`g p = p + f(g)`. The latter is independent of p, and the construction is on
isomorphism classes. Its hypotheses and topology are exactly those in the node;
there is no coefficient restriction. These declarations are recorded together.
The main item gains this existing prerequisite and the already landed geometric
Frobenius definition in its statement dependencies. No new definition node is
needed, and no other node fields change.

## Second reading by Q94

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
