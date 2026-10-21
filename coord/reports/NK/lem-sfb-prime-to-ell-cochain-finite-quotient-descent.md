## Worker report

Stage 2 only. The module `Sheaf.CategoryTheory.PrimeToEllCochainFiniteQuotientDescent`
states `Profinite.ContinuousScalarCochains.prime_to_ell_cochain_finite_quotient_descent`,
with the sole new postponed proof `by sorry`. The reviewed stage-1 split, statement,
source, proof and proof dependencies are retained. The previous attempt confused an
already-reviewed stage-1 split with an already-completed stage-2 statement: the live
item had no `lean` record. This delivery adds that record and its actual module.

The module has two complete auxiliary Prop definitions belonging to the explicit notions
introduced by this item. `FactorsThroughFiniteQuotient` spells out precisely the defining
finite-quotient property. `HasFiniteQuotientComparison` states existence of the two specified
complexes with exact coordinates, the prescribed subpresheaf, its sheafification, the
specified arrow, and its invertibility after localization. No definition chooses objects
from that existence statement, and neither definition contains sorry.

The coordinate presentation determines the mathematical objects up to unique compatible
isomorphism. It is not a hypothesis assuming an arbitrary comparison map. Existence of
all the presentation data is part of the conclusion. Additive coordinates, restrictions,
scalar action and differential determine C. Componentwise injectivity and the exact image
condition determine P and its inclusion. The sheafification isomorphism determines L, and
the counit equation determines iota. Since sheafification preserves monomorphisms, its
underlying inclusion is monic, so the compatible internal scalar action on L is determined
as well. Consequently invertibility of this arrow is the statement about the canonical
inclusion between the node's explicit complexes, independent of their presentation.

Hypothesis and clause correspondence:

| Node | Lean rendering |
| --- | --- |
| A prime ell | `(ell : ℕ) [Fact ell.Prime]`. |
| Omega an algebraic closure of Q_ell | `(Ω : Type u) [IsAlgClosure ℚ_[ell] Ω]`. |
| Its extended norm topology, with no completeness assumption | `[NormedField Ω] [NormedAlgebra ℚ_[ell] Ω]`; continuity uses precisely these induced topological instances. There is no `CompleteSpace Ω` binder. |
| A finite intermediate field E | `(E : IntermediateField ℚ_[ell] Ω) [FiniteDimensional ℚ_[ell] E]`; its subtype norm and topology are inherited from Ω. |
| F=E and F=Omega | The two conjuncts `HasFiniteQuotientComparison E K` and `HasFiniteQuotientComparison Ω K`. |
| A_F(S)=all continuous functions | `A := Profinite.continuousMapRingObjOfUniverse.{u,u} F` with the recorded monoid and commutativity structures; its sections are the canonical universe lift of `C(S,F)`. |
| Coherent small profinite site and size convention | `coherentTopology Profinite.{u}`, coefficient groups `AddCommGrpCat.{u+1}`, internal module objects in universe `u+2`, and standard derived localization in universe `u+2`. A common universe bound may contain both the chosen group and field; there is no independent smaller test-object universe. |
| Profinite group K | `[Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]`. |
| Every finite continuous quotient has order prime to ell | `hK` quantifies over every discrete finite group Q and surjective continuous homomorphism `q : K →ₜ* Q`, and asserts `Nat.Coprime (Nat.card Q) ell`. All quotient types K/U lie in the quantified universe. |
| Trivial K-action on F | The first differential term is plain evaluation, with no multiplication by a group action. There is no representation parameter to alter it. |
| Nonnegative cochain complexes of internal A_F-modules | `C L : CochainComplex M ℕ`, where `M := Mod (Sheaf ... AddCommGrpCat) A`, using Mathlib's actual internal module category. |
| C^n(S)=C(S times K^n,F) | Additive bijections `e n S : (C.X n).X.obj.obj (op S) ≃+ C(S × (Fin n → K),F)`; these are onto all continuous maps, not a locally constant or finite-field-valued subspace. |
| Restriction in S and A_F-linearity | The first conjunction gives `e` under every `f : S' ⟶ S`; the second gives `(r • x)(s,g)=r(s)*x(s,g)` using the recorded `sectionRings` and `sectionModuleFunctor`. |
| The full displayed inhomogeneous differential | The third conjunction evaluates `C.d n (n+1)` as deletion of the first coordinate plus the sum over `j : Fin (n+1)` of `(-1:ℤ)^(j.val+1)` times `Fin.contractNth j (·*·) g`. For j<n this multiplies adjacent coordinates; j=n deletes the last one, supplying the displayed endpoint term with its sign. |
| Degree-zero differential zero | For n=0 both tuple arguments are the unique empty tuple and the formula is x-x. No positive-degree restriction is imposed on the differential clause. |
| The finite-quotient subpresheaf | `P` is a presheaf cochain complex and `i : P ⟶ U.mapHomologicalComplex.obj C` is componentwise injective. Its sectionwise image is exactly `FactorsThroughFiniteQuotient`. Thus its restriction and differential are precisely the restrictions of C's, not other maps on the same groups. |
| One open normal U for all group coordinates of a function | `∃ U : OpenNormalSubgroup K, ∃ b : C(S × (Fin n → K ⧸ U.toSubgroup),F), ∀ s g, ...`; pullback is along `QuotientGroup.mk' U.toSubgroup` in every coordinate. |
| Unrestricted continuous dependence on S | The descended `b` is continuous on the whole product; there is no finite quotient of S, local constancy in S, or common finite scalar subfield condition. |
| L is the sheafification of that subpresheaf complex | `a : T.mapHomologicalComplex.obj P ≅ V.mapHomologicalComplex.obj L`, for the actual `T := presheafToSheaf ...` and `V := Mod.forget A`. |
| Canonical inclusion iota | `iota : L ⟶ C`, with `V.map (iota.f n) = a.inv.f n ≫ T.map (i.f n) ≫ (sheafificationAdjunction ...).counit.app (C.X n).X` in every degree. This is exactly sheafification of the prescribed inclusion and the canonical counit at the already-sheaf C. |
| This map is invertible in unbounded D(Mod_A) | `IsIso (DerivedCategory.Q.{u+2}.map (HomologicalComplex.extendMap iota ComplexShape.embeddingUpNat))`; extension by zero supplies all negative degrees. This is the derived statement itself and is equivalent to being a quasi-isomorphism. |
| No identification with derived invariants | The objects in the conclusion are just the continuous-function complexes and their canonical map; no invariants model occurs. |

Dependency declarations read and used:

- `Sheaf.Topology.ContinuousMapCondensedRing`: the full definitions and docstrings of
  `Profinite.continuousMapRingPresheafOfUniverse`, `continuousMapRingSheafOfUniverse`,
  `continuousMapRingObjOfUniverse`, `continuousMapRingObjOfUniverseMonObj`, and
  `isCommMonObj_continuousMapRingObjOfUniverse`. These supply the real scalar sheaf and
  its canonical tensor monoid, rather than a second scalar-ring definition.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj` and `Mod.Hom`
  are the generic category, action axioms and module-compatible maps recorded on
  `sk-def-sfb-module-objects`. The main predicate uses that category directly.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: read the recorded
  right-derived-functor convention module, and the `DerivedCategory`/`DerivedCategory.Q`
  definitions in `Mathlib.Algebra.Homology.DerivedCategory.Basic` it exports. This item
  needs only unbounded localization, not derived functors. `HasDerivedCategory.standard`
  provides the standard size without an added existence hypothesis.
- `def-weil-size-convention` is the recorded metatheoretic convention, with no module or
  declaration; the explicit universes above implement it.
- Added the already-landed `def-weil-pbc-internal-abelian-sheaf-module-equivalence` to
  `stmt_deps`, using `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`,
  `CategoryTheory.InternalAbelianSheafModule.sectionRings` and `sectionModuleFunctor`.
  I read the whole recorded `sectionModuleEquivalence` signature/docstring and the
  section-ring and forward-functor constructions. The forward functor keeps underlying
  groups and restrictions definitionally, which permits the scalar law on the same x.
  This adds a landed dependency, not a new definition or a dependency repair.

Proof-only imports retain the stated parts of the twelve-step plan:
`Sheaf.NumberTheory.Padics.CountableClosedFiniteCover`,
`Mathlib.Analysis.Normed.Unbundled.SpectralNorm`, `Mathlib.Topology.Baire.Lemmas`,
`Mathlib.Analysis.Normed.Module.Completion`, and
`Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`.
The complete integral, metric-function quotient, norm-one projection and rectangle
replacement nodes have no recorded Lean module in the read snapshot, so no invented
import was made. Their proof steps are nevertheless included in the theorem docstring.

Edge cases checked before finalizing:

- Empty S: continuous-function groups and the represented finite-quotient subgroups have
  one element, and the section/image clauses still apply.
- n=0: K^0 is the one-point empty tuple, every function factors through the top open
  normal subgroup, and d=x-x=0. Thus both degree-zero sheaves are A_F and iota is the
  identity under the canonical coordinates and counit.
- n=1: the differential is c(g2)-c(g1*g2)+c(g1); the averaging primitive formula in the
  docstring gives c=0 for a degree-one cocycle, consistent with zero outgoing d from
  degree zero.
- K=1: d is zero in even degree and identity in odd positive degree; no nontrivial-group
  hypothesis was introduced. Finite K is included by the same quotient quantification.
- Negative degrees: extension by zero, not a bounded-below derived category substituted
  for the unbounded category.
- E=Q_ell and arbitrary finite E: both retain their induced norm, including ell=2.
- Omega: no completeness, discrete topology, or bounded/finite-subextension image
  condition is present in either the coordinates or the theorem's binders.

Searches actually run with `msearch.py` (their exact results are in the sandbox search log):

- LeanFinder query: “Continuous finite quotient cochains include quasi isomorphically
  into all continuous cochains for pro prime to ell groups with algebraic ell adic
  scalars”. Eight hits, including `continuousCohomology`, homogeneous cochains, standard
  representation resolutions and unrelated quasi-isomorphisms; no exact comparison.
- Loogle query: `"ContinuousCohomology"`. Twelve hits on cohomology, cocycles, maps and
  their functoriality. No parameterized condensed finite-quotient comparison.
- Mathlib grep query: `(finiteQuotient|finite_quotient).*(cochain|Cochain)`. Zero hits.
- LeanSearch query: “finite quotient cochains compare quasi isomorphically to continuous
  cochains with algebraic p adic scalars”. Eight hits, including MultiInd complexes,
  homogeneous cochains and unrelated localizations/completions; no exact statement.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for finite-quotient cochains and
  prime-to-ell names found `Rep.baseFieldContinuousCochains_finiteQuotients`. I read its
  full signature: it uses discrete representations and locally constant cochains and
  asserts filtered colimits, not this all-continuous scalar comparison. It is not a match.
- The item's id has no declaration in `lean/WeilConjectures`; its occurrence in
  `PrimeToEllCondensedAcyclicity` is a proof-plan citation, not a Lean statement of this
  item. That downstream module was not imported, avoiding a future proof-import cycle.
- Searches of both project roots and `dag/lean_names_upstream.json` found no existing
  names `FactorsThroughFiniteQuotient`, `HasFiniteQuotientComparison`, or
  `prime_to_ell_cochain_finite_quotient_descent`.

There is no statement correction, new DAG node, dependency module, or statement dispute.
The source's WANTED reference is retained; its analytic argument is explicitly the
agent-formulated reviewed twelve-step proof, not a claim that the blueprint paragraph
itself contains that analytic proof.

Validation: `scompile.py NK lem-sfb-prime-to-ell-cochain-finite-quotient-descent` compiled
both sandbox and module-name forms cleanly, approximately four seconds each. All variables
and universe parameters are explicitly bound. No proof other than the main theorem is
postponed. The dry-run and delivery results are recorded by the prescribed wrapper.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
