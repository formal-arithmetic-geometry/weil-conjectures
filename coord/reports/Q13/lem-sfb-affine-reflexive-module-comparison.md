## Worker report

The module `Sheaf.AlgebraicGeometry.AffineReflexiveModuleComparison` states exactly
`lem-sfb-affine-reflexive-module-comparison` in two declarations. Both proofs are `sorry`;
there are no new definitions, dependency repairs, or statement corrections.

Clause-by-clause correspondence:

- Integral scheme: `(Y : Scheme.{u}) [IsIntegral Y]`.
- Locally Noetherian scheme: `[IsLocallyNoetherian Y]`.
- Coherent structure-module sheaf: `(F : Y.Modules)` and
  `(hF : RingedSpace.IsCoherent Y.toRingedSpace F)`. This is the exact finite-type and
  finite-type-kernel predicate exposed by the dependency, not merely quasi-coherent finite type.
- The dual `Hom(F,O_Y)` is the existing `SheafOfModules.homObj` into
  `SheafOfModules.unit Y.ringCatSheaf`; both occurrences in the target of
  `SheafOfModules.bidual (R := Y.sheaf) F` are these internal Hom sheaves.
- Algebraic reflexivity is `Module.IsReflexive R N`. Its field is exactly bijectivity
  of `Module.Dual.eval R N`, whose value on `m` and `phi` is `phi m`. For modules,
  this is precisely invertibility of the linear evaluation map.
- Clause (i): `IsIso (SheafOfModules.bidual (R := Y.sheaf) F)`.
  Reading the upstream sheaf and presheaf bidual modules confirms this is the canonical
  evaluation, not an arbitrary isomorphism of the double-dual objects.
- Clause (ii): `∀ (W : Y.Opens), IsAffineOpen W → Module.IsReflexive Γ(Y, W) Γ(F, W)`.
  These are sections over the same open, with their canonical section-ring action.
- Clause (iii): `∀ (y : Y), Module.IsReflexive (Y.presheaf.stalk y)
  ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj F)`.
  The stalk functor uses precisely the abelian-group stalk and its canonical stalk-ring
  action from the recorded presheaf module-stalk dependency.
- Equivalence of all three clauses is the conjunction `(i ↔ ii) ∧ (i ↔ iii)`.
- The final affine specialization is `isIso_bidual_tilde_iff_isReflexive`:
  `(A : CommRingCat.{u}) [IsNoetherianRing A] [IsDomain A]`,
  `(M : ModuleCat.{u} A) [Module.Finite A M]`, and
  `IsIso (SheafOfModules.bidual (R := (Spec A).sheaf) (tilde M)) ↔ Module.IsReflexive A M`.
  The tilde object is the dependency's actual Mathlib associated sheaf. Its coherence
  follows from these assumptions and is not added as a separate hypothesis.

Statement dependencies used, with their actual declarations read:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: publicly exposes the exact
  `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `WeilConjectures.AlgebraicGeometry.Coherent`; the module's finite-type conjunction
  is not substituted for coherence.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor` and `stalkObj`; for sheaves the same carrier
  and action are bundled by `RingedSpace.moduleStalkFunctor` from
  `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`, as the dependency's note prescribes.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: `AlgebraicGeometry.tilde`,
  `tilde.toOpen`, `tilde.toOpen_res`. The declaration is also exposed under the
  `ModuleCat.tilde` interface, but the node's recorded `AlgebraicGeometry.tilde` works.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Bidual` supplies the existing
  canonical `SheafOfModules.bidual`; `Mathlib.LinearAlgebra.Dual.Defs` supplies
  `Module.IsReflexive`. No duplicate reflexivity predicate or evaluation map is introduced.

Every already-stated proof dependency is imported, with proof-only imports kept non-public.
The tilde module supplies the free-module comparisons and tilde/global-sections adjunction;
the coherence, gluing, stalk-Hom, stalk detection, affine finite-type, and Spec-domain
modules supply the remaining proof interfaces. The theorem docstrings reproduce all seven
DAG proof steps, separating the first six from the final affine specialization.

Edge cases checked before writing: `W = ⊥` is not excluded by a nonemptiness assumption;
its section ring and module are zero, so the evaluation is invertible. `F = 0` and `M = 0`
likewise give zero-module evaluations. An empty scheme is excluded exactly by the node's
integrality hypothesis. A field, an arbitrary nonregular Noetherian domain, and a coherent
module that is not locally free all remain allowed: there is no extra normality, projectivity,
finite locally free, or smoothness assumption. Universes and variables are explicit,
`set_option autoImplicit false` is enabled, and no local notation or instance is introduced.
The standard `Scheme.{u}` / `Modules.{u}` / `ModuleCat.{u}` size convention matches the
recorded tilde and stalk interfaces; `u` is arbitrary.

Searches for an existing result (2026-10-24):

- `msearch.py ... leanfinder`: “A coherent module on an integral locally Noetherian scheme
  is reflexive iff its sections on every affine open and all its stalks are reflexive
  modules”. Eight hits concern reduced stalks, Noetherian stalks, tilde, and reflection
  of isomorphisms. None is this theorem.
- `msearch.py ... leansearch`: “A coherent sheaf is reflexive if and only if its affine
  sections and stalks are reflexive modules”. Eight hits supply `Module.IsReflexive`
  and its algebraic properties; none compares sheaf reflexivity.
- `msearch.py ... loogle`: `Module.IsReflexive, SheafOfModules.bidual`.
  Zero hits; Loogle reports unknown identifier `SheafOfModules.bidual` (upstream,
  not a Mathlib declaration). The local upstream source does contain that map.
- `msearch.py ... grep`: `IsReflexive|reflexive|bidual` in `AlgebraicGeometry`.
  Zero Mathlib hits. Direct `rg` of Mathlib AlgebraicGeometry and ModuleCat likewise
  found no reflexive-sheaf theorem. Reading `LinearAlgebra/Dual/Defs.lean` located
  the exact algebraic predicate and evaluation.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the proposed declaration
  names and `IsReflexive`: algebraic flat base-change results exist, but no statement
  matching this node. Searching the item's id in `lean/WeilConjectures` found no match.
  Searches for biduality located the existing sheaf evaluation and invertible/finite
  locally free biduality results; their hypotheses do not state the coherent theorem.
- The source was read locally in `literature/stacks-project/divisors.tex`,
  `definition-reflexive`, `lemma-check-reflexive-on-affines` (0AY0), and
  `lemma-check-reflexive` (0AY3). The latter has an additional closed-point equivalent
  condition, which this DAG node does not claim and the Lean does not add.

No statement dispute or node fault was found.

Validation: the prescribed `scompile.py Q13 lem-sfb-affine-reflexive-module-comparison`
compiled both its sandbox and library views cleanly, 2.8 seconds each. The only postponed
proofs are the two theorems recorded in `lean.declarations`.

## Second reading by Q13

This is a separate self-reading of the node, source and finished module, not an independent
agent review: the dispatch brief forbids starting another agent and assigns independent
review to the maintainer. Rechecked all binders and conclusions against the open node.
`IsIntegral` and `IsLocallyNoetherian` match the two scheme hypotheses; `hF` uses exact
coherence, including finite-type kernels. The two iff statements share the same canonical
sheaf evaluation, and the affine quantifier includes every affine open. The point quantifier
uses module stalks over the actual stalk rings. The second declaration retains both the
Noetherian-domain and finite-module hypotheses and uses the recorded tilde construction.
Checked the upstream presheaf evaluation formula: on a smaller open it evaluates the
functional on the restricted section, so the sheaf map is the source's evaluation.
Checked Mathlib's algebraic reflexivity field against the module double dual. Neither
condition means merely existence of an unrelated isomorphism. The pair of iff statements
is exactly the three-way equivalence. No mathematical mismatch or change was needed.
