## Worker report

The module states `AlgebraicGeometry.exists_normal_line_bundle_tensorPow_linearization`
with one postponed proof and no new definitions. The accepted stage-1 split is preserved.
The inherited NOANSWER concerned stage 1; the current queue has this item at stage 2,
its live record has no Lean, and there is no released repair note. The explicit stage
handoff paragraph of coord/brief-stage2.md authorizes the present statement delivery.

The source was checked in the latest blueprint's direct-images proof, part (3), and in
Brion, Algebraic group actions on normal varieties, arXiv:1703.09506v3, Lemma 2.9
(https://arxiv.org/html/1703.09506v3). Brion's smooth case cites Brion 2015 Theorem 2.14.
The node's extension to a finite disjoint union and the empty scheme is unchanged.
Its eight proof steps and their exact named dependencies are in the theorem docstring.

Hypothesis and clause correspondence:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The k-group scheme is `G : Over (Spec (.of k))` with `[GrpObj G]`.
  This is the dependency's recorded internal group object, including its multiplication,
  inverse and identity diagrams. No commutativity is assumed.
- Smoothness is `[Smooth G.hom]`; connectedness is `[ConnectedSpace G.left]`;
  affineness is `[IsAffine G.left]`. ConnectedSpace includes nonemptiness.
- Finite type of G is exactly `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`.
- The k-scheme is `X : Over (Spec (.of k))`. Separatedness and finite type are
  `[IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]`.
- Normality is `hX : ∀ x : X.left, IsDomain (X.left.presheaf.stalk x) ∧
  IsIntegrallyClosed (X.left.presheaf.stalk x)`. Both domain and integral-closure
  conditions are present. There is no integrality or connectedness assumption on X.
- The arbitrary action is `[ModObj G X]`. Its data is a morphism of k-schemes,
  and its `one_smul` and `mul_smul` fields are precisely unit and associativity
  as morphism equalities; no action is restricted to geometric points.
- The arbitrary line bundle is `(L : X.left.Modules) [L.IsInvertible]`, using
  Scheme.Modules.IsInvertible from the dependency, not an unrelated invertibility class.
- The positive integer is `∃ m : ℕ, 1 ≤ m ∧ ...`; `L.tensorPow m` is the existing
  sheaf tensor power, canonically isomorphic to the iterated positive tensor power
  of the node. The existing convention has a tensor unit at exponent zero, which
  is excluded by `1 ≤ m`, and a canonical right unitor at exponent one.
- `source G X` is the second scheme-fibre-product projection, and `target G X`
  is the given action. `Scheme.groupoidModulePullback` is the existing opaque
  wrapper for exactly `Scheme.Modules.tensorPullback`, not another pullback.
  The existential `theta` therefore has exactly the requested direction p₂* → a*.
- `D : ActionGroupoidModel G X` presents this action's canonical groupoid.
  It is an existential output, not a hypothesis. Its identity and inverse arrows
  are fixed as (e,x) and (g⁻¹,gx), and its `group_coordinate` field fixes composition
  to (g,h,x) ↦ (gh,x) on every test scheme. Together with `source_comp`, this
  uniquely determines D.comp by the product universal property. Thus the extra
  binder only names the canonical composable-arrow pullback and its equations;
  it does not replace a specified construction by an arbitrary map.
- `groupoidModuleUnitLaw ... theta.symm` says that the inverse isomorphism is the
  identity after pulling back along (e,x), with the canonical section-normalized
  pullback comparisons. This is equivalent to the same assertion for theta.
- `groupoidModuleCocycleLaw ... theta.symm` uses the actual pullback of composable
  arrows. Its first arrow is the later arrow (g,hx), second is (h,x), and composite
  is (gh,x). Its equation for beta=theta⁻¹ is beta_(gh)=beta_g;beta_h; taking inverses
  is precisely theta_(gh)=theta_h;theta_g, or theta_(gh,x)=theta_(g,hx)∘theta_(h,x).
  Thus the order of the node's forward-action formula is preserved.
- Both laws are equalities of sheaf maps with canonical comparisons. Applying
  any scheme tensor-pullback functor preserves these equations, compositions and
  inverses. This renders the arbitrary-base-change clause structurally, including
  nonreduced bases: there is no reduced/closed-point test in either law.
- No quasi-projectivity, ampleness, connectedness or nonemptiness of X is assumed.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: Field; Mathlib.FieldTheory.IsAlgClosed.Basic:
  IsAlgClosed (the algebraic-closure dependency explicitly records this predicate).
- Mathlib.CategoryTheory.Monoidal.Grp: CategoryTheory.GrpObj, as specialized to
  Over (Spec k) in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- Mathlib.CategoryTheory.Monoidal.Mod and .Cartesian.Mod: ModObj and its full laws.
- Mathlib.AlgebraicGeometry.Scheme: Scheme, Spec; .AffineScheme: IsAffine;
  .Morphisms.Smooth: Smooth; .Morphisms.FiniteType: LocallyOfFiniteType;
  .Morphisms.QuasiCompact: QuasiCompact; .Morphisms.Proper: IsSeparated;
  Mathlib.Topology.Connected.Basic: ConnectedSpace.
- Mathlib.RingTheory.IntegralClosure.IntegrallyClosed: IsIntegrallyClosed, with
  IsDomain as required by def-weil-pbc-normal-ring's recorded inline convention.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: pullback and its
  projections. In Over S the cartesian tensor is the existing scheme pullback.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible:
  Scheme.Modules.IsInvertible and Scheme.Modules.tensorPow.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses:
  SheafOfModules.cochainModulesMonoidal, the existing sheaf tensor structure.
- Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction:
  Scheme.Modules.tensorPullbackSectionAdjunction, tensorPullbackSectionComp,
  tensorPullbackSectionId, on the upstream explicit tensorPullback functor.
- Sheaf.AlgebraicGeometry.EquivariantCoherentGZero: source, target, identityArrow,
  inverseArrow, ActionGroupoidModel. This already recorded definition node was
  added to stmt_deps to use its canonical action-groupoid interface.
- Sheaf.AlgebraicGeometry.SchemeGroupoidModule: groupoidModulePullback,
  groupoidModuleUnitLaw, groupoidModuleCocycleLaw, and the canonical unit/composition
  comparison definitions. Its already recorded definition node was added to stmt_deps.
  No new notion, dependency module or statement correction is needed.

Proof imports include every already stated non-Mathlib proof dependency:
Geometrically.Connected (of_connectedSpace_of_section),
SmoothConnectedGenericGeometryCore (Scheme.smooth_connected_generic_geometry_core),
and FlatSmoothPointBaseChange (smooth_at_point_pullback_snd_iff_of_flat).
Mathlib.Noetherian, Topology.NoetherianSpace, and AlgebraicGeometry.AlgClosed.Basic
supply the recorded Noetherian/component/Jacobson/residue-field tools. Smooth and
finite-type permanence are already public imports. The four proof-only prerequisites
normal-locally-finite-components, affine-group-picard-stable-exponent,
normal-noetherian-generic-line-pullback, and rosenlicht-product-unit-factorization
have no Lean record or Mathlib match at the time of writing; there is no module to
import yet. They are not statement dependencies and are not restated in this delivery.

Edge cases checked before writing: X empty (normality is vacuous and the sheaf category
has its unique linearization; m=1), X disconnected (no IsIntegral/ConnectedSpace X),
trivial G (all action-groupoid equations reduce to identity), arbitrary characteristic,
nonreduced test/base schemes (all equations are sheaf-map equations), and m=1.
The standard PGL₂ action on P¹ with O(1) confirms that m=1 must not be forced;
allowing some positive tensor power accommodates m=2. The group need not be commutative.
All variables and the universe are explicit, with autoImplicit and relaxedAutoImplicit false.
There are no node faults or STATEMENT-DISPUTED flags.

Searches for reuse (2026-10-24):

- msearch.py leanfinder: “A positive tensor power of a line bundle on a normal scheme
  admits a linearization for any smooth connected affine algebraic group action”.
  Eight hits: Rep's free-module linearization, projective section powers, and ring
  Picard tensor/base-change operations; none is this statement.
- msearch.py loogle: `"Linearization"`. Nine Rep.linearization declarations only,
  which linearize an abstract group action on a type, not an algebraic line bundle.
- msearch.py grep: `lineariz|Lineariz|Sumihiro` in Mathlib/AlgebraicGeometry:
  zero hits.
- msearch.py leansearch: “A line bundle on a normal variety admits a positive tensor
  power linearizable under a connected affine group scheme action”. Eight hits,
  concerning Rep linearization, normalization and topological vector bundles; no match.
- rg on lean/WeilConjectures/AlgebraicGeometry and lean/Sheaf/AlgebraicGeometry:
  `lineariz|Lineariz|SchemeAction|GroupSchemeAction` and `tensorPow|tensorPower`.
  Found the reusable EquivariantCoherent action-groupoid and SchemeGroupoidModule
  laws, the existing tensor power, specialized PGL polarizations, trivial-base torus
  linearizations, and affine Hopf coactions. None states this theorem.
- rg for the item id in lean/WeilConjectures: no match. rg for the new theorem name
  in dag/lean_names_upstream.json, lean/WeilConjectures and lean/Sheaf: no match.
- blueprint_refs.py search “linearization” was run to check existing blueprint notions.
  No new definition node is proposed.

Validation: scompile.py checked the complete module against the live server build.
The first compile had only a docstring-ending style warning, which was repaired.
The final clean compile and deliver2.py dry-run outcomes are recorded below.

## Second reading by Q120

A second clause-by-clause pass compared the node, the final theorem signature, and
the full source definitions of ActionGroupoidModel, groupoidModuleUnitLaw and
groupoidModuleCocycleLaw. It checked in particular the inverse orientation and the
later-arrow-first convention: taking inverses of the recorded descent equation
recovers exactly the forward cocycle of the node. It also checked that D.comp is
pinned by actual group-valued test-scheme morphisms and the source equality,
so the existential D is a presentation of the fixed action rather than a second
hypothesis or a different action. All field, finite-type, separatedness, smoothness,
affineness, normal-domain and invertibility assumptions correspond individually
as listed above. No mismatch was found. The only edit was the docstring ending.
This was a second pass by the assigned worker; no other agent was started under
the dispatcher's explicit isolation instruction. Independent review is the
maintainer's delivery review described in the current brief.

Final validation: scompile.py completed cleanly in sandbox (9.9 s) and library
(5.1 s). deliver2.py --no-push returned OK: preflight passed and the module
compiled; only the theorem module, item node and worker report were staged.
