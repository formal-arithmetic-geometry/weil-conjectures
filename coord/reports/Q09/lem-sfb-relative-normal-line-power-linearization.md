## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeNormalLinePowerLinearization` states
`AlgebraicGeometry.exists_relative_normal_line_tensorPow_linearization`, with its
whole proof `sorry`. It adds no definition or instance and changes no mathematical
statement. The node copy changes only `lean` and adds three already landed definition
nodes to `stmt_deps`, so the exact constructions appearing in the signature are recorded.

Source read: Thomason, *Equivariant resolution, linearization, and Hilbert's fourteenth
problem over arbitrary base schemes*, Adv. Math. 65 (1987), §§1.1–1.2 and proof of
Theorem 3.3, printed p.32, first paragraph. The primary article's full text is available at
[ResearchGate](https://www.researchgate.net/publication/243015730_Equivariant_resolution_linearization_and_Hilbert%27s_fourteenth_problem_over_arbitrary_base_schemes).
The paragraph invokes a positive-power linearization before selecting coherent sections.
The declaration docstring contains all five steps of the accepted split-torus proof.
The latest blueprint search contains no separate occurrence of this newly split node;
the node itself records its ancestor route and the agent proof.

Every hypothesis and conclusion clause is rendered as follows:

| Node clause | Lean rendering |
| --- | --- |
| A commutative ring A; S = Spec A | `(A : Type u) [CommRing A]`, and `Over (Spec (.of A))` |
| A Noetherian | `[IsNoetherianRing A]` |
| r ≥ 0, including r = 0 | `(r : ℕ)` with no positivity binder |
| C = A[t_1^±1,…,t_r^±1] and T its specified Hopf spectrum | `ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))`; its actual coordinate algebra is `AddMonoidAlgebra A (ULift.{u} (Fin r → ℤ))`, with the finite-support monomial basis and coproduct, counit, and antipode prescribed in the node |
| f : X → S | `X : Over (Spec (.of A))`, with `f = X.hom` |
| f separated and finite type | `[IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]`; locally finite type plus quasi-compact is the recorded finite-type convention |
| Every local ring of X is an integrally closed domain | `hnormal : ∀ x : X.left, IsDomain (X.left.presheaf.stalk x) ∧ IsIntegrallyClosed (X.left.presheaf.stalk x)` |
| An S-action with morphism-level unit and associativity | `[ModObj (ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))).X X]`; `ModObj` packages the action on the fibre product in `Over S` and its action diagrams |
| L an O_X-module, invertible | `(L : X.left.Modules) [L.IsInvertible]` |
| L relatively very ample over S | `hL : Scheme.Modules.IsRelativelyVeryAmple X.hom L`, without restricting the projective-bundle coefficient module |
| There exists an integer m ≥ 1 | `∃ m : ℕ, 1 ≤ m ∧ …`; positive natural numbers are exactly the permitted positive integers |
| Tensor power L^{⊗m} | `L.tensorPow m`, the existing scheme-module tensor power, canonically isomorphic to the node's left-associated positive-power convention |
| θ : p₂*L^{⊗m} ≅ a*L^{⊗m} | `theta` is the displayed isomorphism between `groupoidModulePullback (source …)` and `groupoidModulePullback (target …)` applied to `L.tensorPow m` |
| θ restricts to 1 along the identity | `Scheme.groupoidModuleUnitLaw … D.laws.source_id D.laws.target_id (L.tensorPow m) theta.symm` |
| θ_{gh,x} = θ_{g,hx} θ_{h,x} | `Scheme.groupoidModuleCocycleLaw … D.comp D.laws.source_comp D.laws.target_comp (L.tensorPow m) theta.symm` |
| Equations are equations of pulled-back sheaf maps | Both law predicates expand to equality of module morphisms with the section-normalized composition and identity comparison isomorphisms |

The existing descent convention uses beta = theta inverse, from action pullback to
projection pullback. Its cocycle is beta_(gh,x) = beta_(h,x) beta_(g,hx), exactly the
inverse of the stated forward cocycle. The scheme of composable arrows
`pullback (source G X) (target G X)` is canonically T ×_S T ×_S X: its first arrow
is (g,hx), its second (h,x). The existential `D : ActionGroupoidModel G X` is a
presentation of this given action, not an additional hypothesis or an arbitrary
composition. `D.group_coordinate` pins the group coordinate of composition to gh
on every test scheme, and `D.laws.source_comp` pins its X-coordinate to x. Those
two coordinates determine composition uniquely. The remaining groupoid laws express
the already assumed action and group identities.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, and `Spec.map`; imported transitively by the group-scheme modules.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; the products in `Over S` and the composable-arrow
  scheme use these chosen fibre products.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: the recorded `multiplicative`
  and `multiplicativeGroup` interfaces were read. They are field-only, so they
  cannot define the arbitrary-base torus here. Their module is retained as the
  original definition dependency. No private replacement is introduced.
- `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`:
  `AlgebraicGeometry.ringDiagonalizableGroup`; its landed definition node
  `def-sfb-ring-diagonalizable-group` is added to `stmt_deps`. This already gives
  the exact arbitrary-ring Laurent Hopf spectrum on the rank-r free lattice.
- `Sheaf.AlgebraicGeometry.EquivariantCoherentGZero`:
  `EquivariantCoherent.source`, `target`, `identityArrow`, and `ActionGroupoidModel`;
  its landed owner `def-sfb-equivariant-coherent-gzero` is added to `stmt_deps`.
- `Sheaf.AlgebraicGeometry.SchemeGroupoidModule`: `Scheme.groupoidModulePullback`,
  `groupoidModuleUnitLaw`, and `groupoidModuleCocycleLaw`, with
  `groupoidModuleCompComparison` and `groupoidModuleUnitComparison`; its landed
  owner `def-sfb-scheme-groupoid-module` is added to `stmt_deps`. These implement
  the linearization notion already spelled out in the item's own statement.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSectionComp`, and
  `tensorPullbackSectionId`. The opaque `groupoidModulePullback` is defined to be
  exactly `tensorPullback`, and its comparison maps use these normalized isomorphisms.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible` and `tensorPow`. Tensor power uses the existing
  sheaf tensor and unit, without a second tensor construction. Its right-associated
  recursion with degree-zero unit is canonically the node's positive recursion.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  the recorded `SheafOfModules.cochainModulesMonoidal` interface was read and its
  module imported for the tensor dependency.
- `Sheaf.AlgebraicGeometry.RelativelyVeryAmple`:
  `Scheme.Modules.IsRelativelyVeryAmple`, with its normalized tautological quotient.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`;
  `IsDomain` is retained separately as required by the normal-domain convention.
- Scheme-conventions node: a conventions-only record with no module or declaration.
  Its actual Mathlib `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`
  declarations were read and their owning modules imported.
- Proof imports: `Mathlib.AlgebraicGeometry.Noetherian` gives both
  `AlgebraicGeometry.IsLocallyNoetherian` and
  `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`.
  `lem-sfb-normal-laurent-line-invariance` has no Lean record, so it has no import
  to include yet. This is only a proof prerequisite: no notion or object in the
  present signature depends on a missing declaration. The live-source query for
  `Sheaf.AlgebraicGeometry.NormalLaurentLineInvariance` also reported unavailable.

Edge cases checked before writing:

- A = 0 is permitted: there is no `Nontrivial A` hypothesis, and a scheme mapping
  to its empty spectrum is empty. Unit and cocycle are still equations of sheaf maps.
- Nonreduced A is permitted: no reducedness, domain, field, or normality binder on A.
- Empty X: normality is vacuous, invertibility is point-local, and no point or
  connected component is selected; m = 1 is the intended witness.
- Disconnected X: normality is imposed pointwise without integral or connected-space
  assumptions. The accepted Laurent-support argument is local on X.
- r = 0: the exponent lattice is the zero group and the existing Hopf spectrum is
  the trivial group. No finite nonempty family of torus generators is assumed.
- The positive bound excludes m = 0 and the tensor-unit loophole. m = 1 is allowed.
- The `ULift` of the finite-rank lattice changes only its size presentation and gives
  an explicit group canonically isomorphic to Z^r; it imposes no algebraic restriction.
- The equalities use universal scheme and sheaf morphisms, so infinitesimal/nonreduced
  test schemes are included, rather than only geometric points.

Searches for existing statements and notions:

- `msearch.py`, LeanFinder: “A split torus action on a normal scheme over a
  Noetherian ring linearizes a positive tensor power of a relatively very ample
  invertible sheaf”. Eight hits, all unrelated affine section or limit results;
  no linearization theorem.
- `msearch.py`, Loogle: `"AlgebraicGeometry", "lineariz"`: zero hits.
- `msearch.py`, Mathlib grep in `AlgebraicGeometry`:
  `linearization|linearisation|Sumihiro|Thomason`: zero hits.
- `rg` in `lean/WeilConjectures/AlgebraicGeometry` for linearization and
  `lem-sfb-relative-normal-line-power-linearization`: no matching theorem.
- `rg` in `lean/Sheaf` found `NormalLineBundlePowerLinearization`: its exact
  signature assumes an algebraically closed field and a different group family,
  so it is not this arbitrary-base statement. It confirms the usable existing
  action-groupoid/descent presentation. `GroupSchemeLinearization.Linearization`
  assumes a field and uses `Modules.pullback`, so it was not used.
- DAG and project searches found the three landed owner nodes listed above;
  their full statements, records, and defining modules were read. Hence no new
  definition node or dependency-module replacement is needed.

No statement correction, disputed statement, or hollow definition is present.
The final module compiled through `scompile.py` both as its sandbox and library
module, each in 1.7 seconds, with no errors or warnings.

## Second reading by Q09

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
