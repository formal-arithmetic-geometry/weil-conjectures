## Worker report

The module `Sheaf.AlgebraicGeometry.CubicalStrictLocalAffineSeed` states
`AlgebraicGeometry.cubical_strict_local_affine_seed`, with its entire proof `sorry`.
There are no new definitions, dependency repairs, statement corrections, or disputed
statements. Only the item's `lean` field changes. The theorem docstring carries all nine
proof steps and their dependency ids, including the noncircular norm-reflection route.
The source is explicitly the node's agent-formulated input; it makes no numbered claim
about the unavailable Raynaud original.

Hypothesis-by-hypothesis correspondence:

- The commutative normal Noetherian local ring is `A : CommRingCat.{u}`, with
  `[IsLocalRing A]`, `[IsNoetherianRing A]`, and `hnormal`, the recorded inline condition
  that every prime localization is an integrally closed domain. No characteristic
  restriction or additional domain assumption is imposed.
- Its residue field is `(Spec A).residueField (IsLocalRing.closedPoint A)`. This is
  canonically the ordinary residue field of the local ring, using the scheme residue
  field definition named by the node. `K : Type u`, `[Field K]`, its `Algebra` over that
  field, and `IsSepClosure` give the chosen separable closure with its embedding.
- `c` is a cocone on `Scheme.etaleResidueTriplesRingDiagram` at the closed prime with
  exactly that embedding, and `hc : IsColimit c`. Its apex `c.pt` is the chosen strict
  henselization R. `[IsLocalRing c.pt]` supplies its local-ring structure for the closed
  point. `ρ : A ⟶ c.pt` and `hρ : ∀ t, t.α ≫ c.ι.app t = ρ` identify the structural
  map, rather than allowing an arbitrary map A → R. These are presentation data, not
  stronger mathematical hypotheses: `Scheme.strictHenselization_triples` supplies all
  these data for the given K, and colimit uniqueness transports them to any presentation.
- `H : Grp (Over (Spec A))` is the given group scheme, with its own group operations;
  `[IsCommMonObj H.X]` says commutative. Its structure map p is `H.X.hom`.
- `[Smooth H.X.hom]` says smooth. `[IsSeparated H.X.hom]` literally means its diagonal
  is a closed immersion in Mathlib. `[LocallyOfFinitePresentation H.X.hom]` and
  `[QuasiCompact H.X.hom]` say finite presentation: separatedness supplies the remaining
  quasi-separatedness condition. No properness or total-space ampleness is assumed.
- `hsemiabelian : HasSemiabelianGeometricFibres H` uses the recorded full definition,
  including every geometric fibre, the given group law, fppf quotient and rank zero.
- `B : CubicalRigidifiedLine H.X` is the given (B,r,τ), including its invertible module,
  identity rigidification, and symmetric normalized cocycle section. No cubical structure
  is chosen independently of the supplied B.
- `hfibre : ∀ p : Spec A, ...` ranges over EVERY prime, not only the generic or closed
  prime. The morphism `(Spec A).fromSpecResidueField p` is the canonical Spec κ(p) → Spec A.
  `B.baseChange` is termwise base change of the supplied cubical line, with underlying
  module the actual tensor pullback. `@Scheme.Modules.IsAmple ... ... .invertible`
  applies the existing absolute ampleness predicate using its stored invertibility proof.

Conclusion clause-by-clause:

- `CubicalLine.baseChangedGroup (Spec.map ρ) H.X` is the existing canonical base-changed
  group with underlying scheme the actual pullback H ×_A Spec R (as `Over.pullback`
  defines it); its identity is the transported group identity, not an arbitrary section.
- `(B.baseChange (Spec.map ρ)).line` is L, the tensor pullback of B to X.
- `∃ n : ℕ, 0 < n ∧ ...` is precisely an integer n ≥ 1.
- `s` belongs to `.val.presheaf.obj (Opposite.op ⊤)` of its `tensorPow n`, namely
  Γ(X,L^{⊗n}). No tensor power zero is substituted.
- `U` is an open of that same X, and `IsAffineOpen U` says the corresponding open
  subscheme is affine.
- `(η[CubicalLine.baseChangedGroup (Spec.map ρ) H.X]).left
  (IsLocalRing.closedPoint c.pt) ∈ U` is the closed identity e_R(m_R) ∈ U.
- The final set equality identifies U with `Scheme.Modules.nonvanishingLocus` of that
  exact section, so membership means nonzero residue-fibre value s(e_R(m_R)).
  U is the entire nonvanishing locus, not merely an affine neighbourhood inside it.
  There is one existential chart, no assertion that such charts cover X.

Dependency declarations read and used:

- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, with
  `IsDomain` and `Localization.AtPrime`, using the recorded inline normal-ring form.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap` (read), and the canonical `Scheme.fromSpecResidueField`.
- `WeilConjectures.RingTheory.StrictHenselizationTriples`:
  `Scheme.strictHenselization_triples`, and its public
  `WeilConjectures.AlgebraicGeometry.EtaleResidueTriples` diagram
  `Scheme.etaleResidueTriplesRingDiagram`; c, hc, ρ, hρ present exactly that colimit.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `IsSeparated`, whose field is
  `isClosedImmersion_diagonal`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `Grp`, `GrpObj`, `IsCommMonObj`.
- `Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres`:
  `AlgebraicGeometry.HasSemiabelianGeometricFibres`.
- `Sheaf.AlgebraicGeometry.CubicalRigidifiedLine`: `CubicalRigidifiedLine`, its fields
  `line` and `invertible`, `CubicalRigidifiedLine.baseChange`,
  `CubicalLine.baseChangedGroup` and its transported group-law instances.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible` and `Scheme.Modules.tensorPow`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its universal
  projections and `Over.pullback` (used through the existing base-changed-group notion).
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the normalized pullback
  interface, publicly importing `WeilConjectures.AlgebraicGeometry.TensorPullback` and its
  actual `Scheme.Modules.tensorPullback` construction. No private pullback is defined.
- `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.IsAmple` and
  `Scheme.Modules.nonvanishingLocus`.

Every recorded available proof-dependency module is imported (plain imports for proof-only
uses); the proof also imports the Mathlib affine-permanence and Noetherian modules and the
recorded upstream smooth-flat module. The proof nodes with neither a module nor a Mathlib
match (generic torus quotient, smooth connected-fibre integrality, generic-line pullback,
and cubical ample-norm reflection) have no import to add yet; their complete uses remain
in the proof docstring. They are not prerequisites for stating this item.

Edge cases checked before writing: rank-zero tori and the trivial group are admitted;
A a field is admitted; the tensor exponent is strictly positive; all residue primes,
including generic and closed, occur in hfibre. There is no added characteristic condition
or connectedness hypothesis. Empty H cannot occur because a group has an identity over
the nonempty local base, and the closed identity forces the resulting chart nonempty.
The zero ring is already excluded by the node's local-ring and residue-field assumptions.
All ring, scheme, residue-field and diagram-stage rings live in universe u, in accord with
the recorded triples and geometric-fibre interfaces; no smaller independent test universe
makes a hypothesis vacuous. A separable closure can be realized in the same universe.

Searches performed:

- `msearch.py leanfinder`: "A fibrewise ample cubical line on a smooth semiabelian group
  over a normal Noetherian local ring admits an affine nonvanishing chart at the closed
  identity after strict henselization". Eight hits, all affine-transition limit/local
  neighbourhood or ring-map results; no matching theorem.
- `msearch.py loogle`: `"IsAmple", "IsLocalRing"`. Zero hits.
- `msearch.py grep`: `cubical|cubist|semiabelian|ample.*hensel|hensel.*ample` in
  Mathlib/AlgebraicGeometry. Zero hits.
- `msearch.py leansearch`: "An ample cubical invertible module on semiabelian geometric
  fibres has an affine section nonvanishing locus through the identity over a strict
  henselization". Eight hits on invertible ring modules, affine limits, ordinary basic
  opens and stalk units; no match for the supplied cubical line statement.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`:
  `cubical.*strict|strict.*cubical|affineSeed|affine_seed`. No existing theorem.
- `grep -rn lem-sfb-cubical-strict-local-affine-seed lean/WeilConjectures` and `rg` in
  `dag/lean_names_upstream.json`: no recorded upstream statement.
- Read the existing cubical and semiabelian modules, strict-henselization triples module,
  tensor-pullback module and ampleness module in full at their defining declarations.
  Reused their notions rather than defining a second version.

Validation: scompile.py compiled this module in sandbox and library module modes without
errors or unexpected warnings. The only postponed proof is the named theorem above.

## Second reading by Q01

Independent second reading by the maintainer reviewer (the delivered section stated that no
second reading was made). Read the node, its source place (agent-formulated, no numbered
Raynaud claim), the nine proof steps, the fourteen stmt_dep records and the declarations
`IsAmple`, `nonvanishingLocus` (WeilConjectures.AlgebraicGeometry.Ample),
`CubicalRigidifiedLine`, `.baseChange`, `CubicalLine.baseChangedGroup` (Sheaf.AlgebraicGeometry.CubicalRigidifiedLine),
`HasSemiabelianGeometricFibres` and `Scheme.strictHenselization_triples`.

Node clause → Lean → verdict:

- A normal Noetherian local → `A : CommRingCat.{u}`, `[IsLocalRing A]`, `[IsNoetherianRing A]`,
  `hnormal` = recorded inline normal-ring form of def-weil-pbc-normal-ring. Exact.
- k, chosen k^sep, R = A^sh with that embedding → `K`, `IsSepClosure`, colimit cocone `c`, `hc`
  on `etaleResidueTriplesRingDiagram` at the closed point, `ρ` with `hρ` pinning the structural
  map; `[IsLocalRing c.pt]` is a Prop (true by the triples theorem, transported along colimit
  uniqueness). Same presentation as the landed StrictHenselizationComparison and
  SmoothStrictLocalFieldModelCore modules. Exact; no arbitrary map A → R.
- p : H → Spec A smooth separated commutative group of finite presentation → `H : Grp (Over (Spec A))`,
  `IsCommMonObj`, `Smooth`, `IsSeparated` (diagonal closed immersion), `LocallyOfFinitePresentation`
  + `QuasiCompact` (quasi-separated follows from separated). Exact, nothing stronger.
- semiabelian geometric fibres → `HasSemiabelianGeometricFibres H`. Exact.
- (B,r,τ) → `B : CubicalRigidifiedLine H.X`. Exact.
- for EVERY prime p, B_p ample on H ×_A Spec κ(p) → `hfibre : ∀ p : Spec A`, `IsAmple` of
  `(B.baseChange (fromSpecResidueField p)).line` (actual `tensorPullback`) on
  `(Over.pullback _).obj H.X`. Exact (absolute ampleness of def-weil-pbc-ample-invertible-module).
- X = H ×_A Spec R, L = B|_X, e_R → `baseChangedGroup (Spec.map ρ) H.X`, `(B.baseChange (Spec.map ρ)).line`,
  `η[…].left`. Exact.
- ∃ n ≥ 1, s ∈ Γ(X, L^n), X_s affine, s(e_R(m_R)) ≠ 0 → `∃ n, 0 < n ∧ ∃ s ∃ U, IsAffineOpen U ∧
  e_R(closedPoint) ∈ U ∧ U = nonvanishingLocus (L.tensorPow n) s`. U is the whole X_s, so X_s is
  affine and membership is the residue-value nonvanishing. Exact; one chart, no covering claim.

Edge cases: A a field (R = k^sep), rank-zero tori, trivial group: all admitted; n = 0 excluded
as in the node; no characteristic or connectedness hypothesis added; one universe u throughout
as in the recorded triples and cubical interfaces, no restriction beyond the dependencies'.

One definition per notion: no new definitions; all notions are the recorded dependency
declarations. Searched side-live lean/Sheaf and lean/WeilConjectures for
`affine_seed|strict_local.*ample|cubical.*hensel`: nothing existing.

Gates: module and theorem docstrings carry the source place and `(blueprint: …)`; the theorem
docstring carries all nine steps with their dependencies; proof is `sorry` only; `lean.statement`
is verbatim in the file. Mismatches found: none in the Lean; only this section was replaced.
