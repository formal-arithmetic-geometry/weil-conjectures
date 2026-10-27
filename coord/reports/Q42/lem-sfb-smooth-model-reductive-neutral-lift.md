## Worker report

Module `Sheaf.AlgebraicGeometry.GroupScheme.SmoothModelReductiveNeutralLift` states
`AlgebraicGeometry.smoothModel_reductive_neutral_lift`, with one `sorry` and no new definitions.
The source is Prasad--Yu, https://arxiv.org/pdf/math/0405381, read online: the neutral-component
paragraph before Lemma 3.5, Lemma 3.5, Section 3.6 and Proposition 4.3 first paragraph
(printed pp.6--8). The paragraph defines precisely the union used here; Lemma 3.5 gives
its smooth affineness; Section 3.6 explains splitting over a strictly henselian ring.
The current blueprint direct-images statement and proof, part (3), were read at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`.
No statement correction or disputed statement is needed.

Hypothesis and conclusion correspondence:

- Henselian DVR: `R : Type u`, `[CommRing R]`, `[IsDomain R]`,
  `[IsDiscreteValuationRing R]`, `[HenselianLocalRing R]`. The nonfield condition belongs
  to the DVR class. The residue field F is the canonical `IsLocalRing.ResidueField R`,
  with `[IsAlgClosed (IsLocalRing.ResidueField R)]`; using the canonical residue field
  makes no choice of a different residue map or extra hypothesis.
- Fraction field L: `L : Type u`, `[Field L]`, `[Algebra R L]`, `[IsFractionRing R L]`.
- Smooth affine finite-type R-group scheme: `N : Grp (Over (Spec (.of R)))`,
  `[Smooth N.X.hom]`, `[IsAffine N.X.left]`, `[LocallyOfFiniteType N.X.hom]`,
  `[QuasiCompact N.X.hom]`. The bundled group object includes all group diagrams.
- Geometrically connected generic fibre: `GeometricallyConnected` of
  `pullback.snd N.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R L)))`.
- Reductive special identity component: `hH : ReductiveTorusCentralizer.IsReductive`
  of `Grp.mk (GrpObj.identityComponent ...)`, applied to the pullback along
  `IsLocalRing.residue R`. The `CategoryTheory.Obj` scope supplies the transported
  group structure on this pullback. Explicit `inferInstanceAs` terms supply its
  finite-type and quasi-compactness instances using `pullback.snd`. These are derived
  instances, not extra hypotheses, new instances, or postponed facts.
- Open subgroup with induced open structure: existential `D : Grp (Over (Spec (.of R)))`,
  group homomorphism `i : D ⟶ N`, and `IsOpenImmersion i.hom.hom.left`.
- Its prescribed underlying union: `Set.range i.hom.hom.left` equals the union of
  the range of the generic `pullback.fst` and the range of the special
  `GrpObj.identityComponentι` followed by the special `pullback.fst`. Together with
  the open immersion this gives exactly the induced open subscheme, including its
  structure sheaf. It does not replace that subscheme with an arbitrary group model.
- D is smooth affine of finite type: `Smooth D.X.hom`, `IsAffine D.X.left`,
  `LocallyOfFiniteType D.X.hom`, and `QuasiCompact D.X.hom` in the conclusion.
- D_L = N_L: `IsIso` of the actual base-changed inclusion, via `mapGrp.map i`.
- D_F = N_F^0: existential isomorphism `e` in `Over (Spec F)`, with
  `e.hom ≫ GrpObj.identityComponentι ... = (Over.pullback ...).map i.hom.hom`.
  Thus this is an identification as subschemes over the specified inclusion.
- Reductive geometric fibres: for every algebraically closed field `Ω : Type u`
  and ring map `φ : R →+* Ω`, the pulled-back group has the existing `IsReductive`
  predicate. That predicate is smooth, geometrically connected, affine finite type,
  and forbids nontrivial smooth connected normal geometric unipotent subgroups;
  the existing unipotence predicate uses a faithful matrix representation.
- Split maximal torus: `∃ (r : ℕ) (j : RingGroupSchemes.splitTorus R r ⟶ D)`,
  `IsClosedImmersion j.hom.hom.left`, and `IsMaximalTorus` of the actual base-changed
  `j` for every `Ω, φ` as above. Giving the inclusion from the standard split torus
  states the same existence as a subgroup T isomorphic to that torus. The existing
  maximality predicate compares every containing closed torus subgroup and requires
  the factor to be an isomorphism, exactly maximality under subgroup inclusion.

Dependency declarations read and used:

- `IsDiscreteValuationRing`, `Mathlib.RingTheory.DiscreteValuationRing.Basic`;
  `HenselianLocalRing`, Mathlib's Henselian module, reexported by the recorded
  `WeilConjectures.Mathlib.RingTheory.Henselian` (whose strictly henselian class and
  docstring were also read); `IsAlgClosed` and `AlgebraicClosure`, the recorded
  Mathlib field-theory modules.
- `CategoryTheory.GrpObj` and `Grp`, `Mathlib.CategoryTheory.Monoidal.Grp`;
  transported by `Functor.mapGrp` and `Functor.grpObjObj`.
- `AlgebraicGeometry.Smooth`, `Mathlib.AlgebraicGeometry.Morphisms.Smooth`;
  `ConnectedSpace`, `Mathlib.Topology.Connected.Basic`;
  `AlgebraicGeometry.IsOpenImmersion`, `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `AlgebraicGeometry.GrpObj.identityComponent` and `identityComponentι`,
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`, with their full signatures,
  canonical restricted group structure and inclusion. The already-recorded
  `def-wf-algebraic-components` is added to stmt_deps to expose this shared API.
- `AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive` and `IsMaximalTorus`,
  `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`;
  `AlgebraicGeometry.RingGroupSchemes.splitTorus` and `multiplicative`,
  `Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing`. The two corresponding
  already-landed definition nodes are added to stmt_deps; no duplicate definition
  nodes or dependency modules are introduced.
- The field-torus and matrix-unipotence definitions used by these predicates were
  read in `ToriMultiplicativeType.lean` and `SolvableGroupStructure.lean`.
- The mathematical proof dependencies that have modules are plain imports, including
  `HasRingHomProperty.Spec_iff`, smooth-flatness, flat torsion-freeness,
  the prime-spectrum clopen/idempotent correspondence, affine-localization facts,
  `reductive_borel_pair_structure`, `smooth_and_fibre_dimension_zero_of_etale`,
  and `Algebra.Smooth.exists_lift_of_henselianRing`.
  The three currently unstated proof inputs (finite-type identity subgroup,
  reductive-torus fibre openness, and split-torus etale subgroup lift) are described
  in the proof docstring; no imports are invented for them.

Edge cases checked: rank zero is included by `r : ℕ` and the existing recursive
split-torus definition, whose zero case is the trivial group. The trivial group
satisfies the intended hypotheses and conclusion. No residue-characteristic restriction
is imposed, including characteristic two and mixed characteristic. Disconnected special
fibres are allowed; only their identity component is assumed reductive. No completeness,
normality or excellence is assumed. Empty total schemes cannot be group schemes over
this nonempty base because they have a unit section. The generic fibre is nonempty and
geometrically connected as stipulated. Tests for geometric fibres run in the ambient
scheme universe, just as Mathlib's `GeometricallyConnected`; the algebraic closure
construction stays in that same universe. No independent smaller test universe occurs.

Searches made (2026-10-24):

- `msearch.py ... leanfinder` query "A smooth affine group scheme over a henselian
  discrete valuation ring with connected generic fibre and reductive special identity
  component has split reductive neutral model": eight hits, including
  `WeierstrassCurve.IsGoodReduction`, `HenselianLocalRing`, and formal-smoothness
  lemmas; none states this result.
- `msearch.py ... leansearch` query "neutral component smooth affine group scheme
  reductive special fibre split reductive": eight hits on smoothness, affine schemes,
  and algebra smoothness; none states this result.
- `msearch.py ... loogle` query `IsDiscreteValuationRing, GrpObj, IsSmooth`: no hits;
  the service reports unknown `GrpObj`.
- `msearch.py ... grep` query `reductive|neutralComponent|identityComponent` in
  Mathlib/AlgebraicGeometry: zero hits. Direct source inspection found the upstream
  identity-component interface and the relevant Mathlib geometric-connectedness API.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for reductivity, neutral components,
  split tori and the proposed theorem name: no existing theorem; the shared definitions
  listed above were found and reused. The required search for the item id in
  `lean/WeilConjectures` returned no match. `blueprint_refs.py search reductive neutral`
  returned zero blueprint-node matches. DAG keyword searches located the existing
  reductivity and split-torus nodes, rather than creating new nodes.

Validation: every delivered Lean file was compiled with the prescribed `scompile.py`
wrapper against the live build. Module mode is used, all variables and universes are
explicit, and both auto-implicit options are disabled. Only the theorem proof is `sorry`.
The compiler issue with typeclass synthesis for an opaque pullback expression was
resolved using explicit existing pullback instances, with no mathematical strengthening.

## Second reading by Q42

Author's second reading, with both the node and final module open; independent review
is the maintainer's under the dispatcher brief. I rechecked every hypothesis and every
clause against the correspondence above. The range equality refers to N's actual two
fibres, not just a complement described on rational points. The special isomorphism
commutes with the special inclusion, while the generic assertion is about the actual
base-changed inclusion. Both reductivity and maximality quantify over all geometric
points of Spec R. The existential torus inclusion uses the Laurent Hopf group law,
and does not assume a torus lift in the hypotheses. Rank zero and all characteristics
remain allowed. Explicit pullback instances change elaboration only. No semantic
mismatch, statement correction, new definition or dependency replacement was found.
