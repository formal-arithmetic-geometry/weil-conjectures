# Affine profinite family Serre cohomology bound

## Worker report

This is a stage-2 statement delivery, not another stage-1 split. The current item has
status split and no lean record. NC's reviewed stage-1 delivery remains unchanged.
The earlier worker's stale-assignment response confused the two stages; its sandbox
contained no statement, node copy or report when this work began.

The module `Sheaf.Paper.AffineProfiniteFamilySerreCd` states
`AlgebraicGeometry.ProEtale.CondensedRing.affine_profinite_family_serreHeart_cohomology_vanishes`.
Its sole theorem has proof `sorry`. There are no new definitions, helper theorems,
new nodes, dependency repairs, statement corrections or proofs. Only the item's
`lean` field is changed. The six-step proof docstring preserves the reviewed proof plan.

Hypothesis and clause matching:

| Node text | Lean rendering |
| --- | --- |
| Prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| Commutative condensed coefficient ring | `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`, `[MonObj Λ] [IsCommMonObj Λ]` |
| Finite commutative A killed by a power of ell, discrete topology | First disjunct of `hΛ`: a commutative topological discrete ring `A : Type`, `Finite A`, and `∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0` |
| Z_ell | Second disjunct: ring-object isomorphism with `Profinite.continuousMapRingObj ℤ_[ℓ]` |
| O_E in the fixed algebraic closure | Third disjunct: `∃ E : PadicAlgCl.FiniteIntermediateField ℓ`, ring-object isomorphism with `Profinite.padicIntegersRingObj ℓ E` |
| Q_ell | Fourth disjunct: ring-object isomorphism with `Profinite.continuousMapRingObj ℚ_[ℓ]` |
| Finite subextension E/Q_ell | Fifth disjunct: `∃ E : PadicAlgCl.FiniteIntermediateField ℓ`, ring-object isomorphism with `Profinite.continuousMapRingObj E` |
| Omega with all continuous maps for its induced norm topology | Last disjunct: ring-object isomorphism with `Profinite.continuousMapRingObj (PadicAlgCl ℓ)` |
| Affine reduced C | `{C U : Scheme.{u}} [IsAffine C] [IsReduced C]` |
| w-contractible C | `[IsWContractibleRing Γ(C, ⊤)]`, the recorded affine coordinate-ring definition |
| Every prime of its coordinate ring maximal | `hCdim : ∀ p : PrimeSpectrum Γ(C, ⊤), p.asIdeal.IsMaximal` |
| Separably closed residue fields | `hCres : ∀ c : C, IsSepClosed (C.residueField c)` |
| Affine U | `[IsAffine U]` |
| Finite-type g:U -> C | `(g : U ⟶ C) [LocallyOfFiniteType g] [QuasiCompact g]`, the dependency's recorded conjunction |
| Nonnegative integer e | `(e : ℕ)`; every nonnegative integer is represented uniquely |
| Every algebraically closed geometric point | `he : ∀ (K : Type u) [Field K] [IsAlgClosed K] (c : Spec (CommRingCat.of K) ⟶ C), ...` |
| Geometric fibre dimension at most e | `topologicalKrullDim (pullback g c : Scheme.{u}) ≤ (e : WithBot ℕ∞)` |
| Lambda_U = p_U^* Lambda and ordinary internal module heart | `N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)` |
| P_U is the replete weak Serre coproduct intersection on constant-model constructibles | `hN : ObjectProperty.weakSerreCoproductClosure.{u + 1} (IsConstantModelConstructible Λ U) N` |
| Zero belongs to P_U | Empty ambient coproduct is included in the existing closure; its source supplies the `ContainsZero` instance |
| Kernels and cokernels of maps between members | The closure quantifies over `IsClosedUnderKernels` and `IsClosedUnderCokernels`, not closure under arbitrary subobjects |
| Extensions with both ends in the class | The closure's `IsClosedUnderExtensions` tests the two end objects of a short exact sequence |
| All small ambient coproducts | Its `∀ J : Type (u + 1), IsClosedUnderColimitsOfShape (Discrete J)` is the fixed indexing universe |
| N placed in degree zero | `(DerivedCategory.singleFunctor _ 0).obj N` |
| R Gamma of the internal module category into D(Ab) | `(condensedModuleSections Λ U).rightDerivedFunctor.obj ...` |
| Every integer q > e+2 | `(r : ℤ) (hr : (e : ℤ) + 2 < r)` |
| H^q vanishes | `IsZero ((DerivedCategory.homologyFunctor _ r).obj ...)` in `AddCommGrpCat.{u + 1}` |

All coefficient isomorphisms use `Mon.mk`, so they preserve the ring structure.
The coefficient list is spelled out because `IsLocalizingAdmissibleCoefficient`
now also includes the different finite-subextension-valued algebraic-closure object.
That additional disjunct is not in this item. We use the existing continuous ring
construction, not a duplicate predicate or a modified dependency. Quantifying E in
the two relevant disjuncts is equivalent to the node's fixed arbitrary finite E:
in the other cases the chosen E is unused. Small finite rings in `Type` exhaust
finite ring isomorphism classes, and the statement is invariant under the displayed
ring-object isomorphisms.

`condensedModuleSections` is the full composite from the internal module category:
forget the module action, include the underlying sheaf as a presheaf, and evaluate
at `Scheme.ProEt.mk (𝟙 U)`. Its total right derived functor derives that composite,
not a separately derived forgetful functor. The module category and its derived
category are ordinary, with no completion or solidification predicate. No properness,
Noetherianity, finite presentation, invertibility of ell or completeness hypothesis
occurs. No `let`, `show ... from`, local notation or local instance is used. All
universes and variables are explicit, and `autoImplicit` is false.

Dependency declarations read and used:

- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingAdmissibleCoefficients`,
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`; read the full
  disjunction and its distinction of the two algebraic-closure coefficients.
  Its imported coefficient-ring constructions are reused in `hΛ`.
- `sk-def-sfb-module-derived-pushpull`: `Sheaf.Paper.CondensedModuleDerivedPushpull`,
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward` and
  `moduleObjectDerivedPullback`; these specialize the same total derived functors
  on ordinary `Mod` categories. The statement uses the imported
  `CategoryTheory.Functor.rightDerivedFunctor` for absolute sections.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `HasFiniteConstantLocalModel`, `IsFiniteConstantStratified` and
  `IsConstantModelConstructible`. Their exact finite scalar presentations, finite
  constructible locally closed strata and affine-local fallback were read.
- `def-weil-size-convention`: metatheoretic convention, no declaration. Here schemes
  are `Scheme.{u}`, site objects are in `Type (u+1)`, abelian groups and module
  coefficients in universe `u+1`, and coproduct indexing is `Type (u+1)`.
- `sk-def-pe-wlocal`: `WeilConjectures.RingTheory.ProEtale.WContractible`,
  `IsWContractibleRing`, inheriting `IsWStrictlyLocalRing` and `IsWLocalRing`.
  The field `extremallyDisconnected_connectedComponents` supplies the final clause.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.ProEt` and `ProEt.topology`, the weakly etale small site
  with fpqc covers.
- `def-weil-geometric-fibre`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, applied to `g` and the bound geometric point.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim : WithBot ℕ∞`, whose bottom is the empty-space dimension.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `LocallyOfFiniteType`, together with `QuasiCompact` from its recorded interface.

Further existing constructions reused: `CategoryTheory.ObjectProperty.weakSerreCoproductClosure`
from `WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure`,
and `AlgebraicGeometry.ProEtale.CondensedRing.condensedModuleSections` from
`Sheaf.Paper.CondensedQcqsPushforwardContinuity`. Their definitions were read in full.
All recorded proof-dependency modules with declarations are imported privately.
`lem-sfb-torsion-cd-topological-serre-transfer` has no recorded Lean declaration,
so its import is omitted; it is a proof dependency, not a notion needed to state
this theorem. Its obligation stays explicit in the docstring and existing DAG.
The downstream proper-family theorem is not imported; importing it here would
reverse the mathematical dependency.

Edge cases checked before writing: empty C forces empty U, with no nonempty
binder imposed; empty fibres have bottom dimension and satisfy `he`; e=0 gives
exactly the bound r>2; the zero coefficient ring is included; N=0 belongs by
zero/empty-coproduct closure; finite A may be the zero ring; no characteristic
restriction excludes characteristic ell; separably closed imperfect residue fields
are not replaced by algebraically closed residue fields. Geometric point fields
use the same scheme universe u, avoiding a vacuous independently smaller universe.
The fixed bound applies to every N and r; no per-object bound is introduced.

Sources read: the exact current main-20261015 refinement proof (2); the complete
item and its statement-dependency node records; NC's merged stage-1 report; Stacks
`etale-cohomology.tex`, proposition-cd-affine, Tag 0F0V (including its torsion scope).
The exact reference for the topological transfer is still WANTED, as already
recorded in the node. This delivery neither supplies its proof nor attributes it
to Stacks. No explicit counterexample or new statement fault was found.

Searches performed with msearch.py for this item (2026-10-22):

- LeanFinder: "Affine pro etale cohomology vanishes above fibre dimension plus two
  for weak Serre coproduct closure of constructible continuous ell adic modules".
  Eight hits: Nobeling exactness, affine-transition-limit section lemmas, etale locus,
  projective derived/Tor vanishing and singular homology; no statement match.
- Loogle: `AlgebraicGeometry.IsAffine, DerivedCategory.IsLE`. Zero hits.
- Mathlib grep: `proetale.*cohomological|weakSerreCoproductClosure|affine.*Artin`.
  Two Artinian-affine instances; neither is this cohomology statement.
- LeanSearch: "Affine finite type schemes over a zero dimensional separably closed
  profinite base have pro etale cohomology zero above relative dimension plus two
  for constructible topological coefficients and their weak Serre coproduct closure".
  Eight hits about affineness, properness, etale morphisms/sites and affine spaces;
  none asserts the required vanishing.
- rg in `lean/WeilConjectures` and `lean/Sheaf`: `weakSerre|profinite.*(heart|serre)|affine.*profinite|AffineProfinite|affine_profinite|WeakSerre`.
  Found the existing closure and downstream proper-family theorem, but no affine
  family theorem. The latter has bound 2e+2 and properness, and cites this item.
- Node-id search in `lean/WeilConjectures`: no hits. Exact new declaration-name
  search in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`:
  no hits. Mathlib rg for weakSerre/affine profinite found no statement.

Validation: scompile.py compiled both sandbox and library module forms cleanly
on the server in 3.7 and 3.6 seconds, within the 60-second limit. The statement
record is the exact multiline theorem signature before `:=`. Source line widths
are at most 100 characters. The prescribed deliver2.py --no-push wrapper reported OK: commit d04ef644559
passes preflight and compiles; nothing was pushed by that dry run.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
