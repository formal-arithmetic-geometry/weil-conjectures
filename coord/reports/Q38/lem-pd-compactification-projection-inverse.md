## Worker report

The module `Sheaf.Paper.CompactificationProjectionInverse` states
`AlgebraicGeometry.ProEtale.CondensedRing.compactification_projection_inverse`.
There is exactly one postponed theorem, with proof `sorry`; all five auxiliary
definitions have complete data. The node statement and all DAG dependencies are unchanged.
The four clause predicates package this node's displayed assertions, not additional
geometric objects. Isomorphism witnesses fix their forward maps by equality, so their
inverses are uniquely determined and no arbitrary comparison is substituted.

Hypotheses and clauses, checked against the current node:

- Prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`. Positive prime characteristic distinct from ell:
  `{k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`.
- The two separated finite-type k-schemes are `X Y : Over (Spec (.of k))`, each with
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on its structure map.
  The k-morphism is `f : X ⟶ Y`. The arbitrary compactification is
  `c : Compactification f.left`; its `i`, `g`, `comm`, `overObj`, `overI`, `overG`,
  and `overI_overG` give precisely j, q, their factorization, the middle k-scheme,
  and its k-morphisms. The existing instances supply the middle scheme's
  separated finite-type structure.
- The theorem fixes Lambda to `Profinite.padicAlgClRingObj ℓ`, not the sheaf of all
  continuous maps into the algebraic closure. The general coefficient variable
  of the auxiliary predicates is absent from the main theorem's parameters.
- `K`, and every quantified `B` and `N`, belong to the actual internal-module
  `ProEtale.BoundedConstructible (condensedRingObj ... T)` full subcategory. There
  is no completeness, finite-stage, perfectness, or Tor-amplitude condition.
- The `alpha` family in `compactification_projection_inverseClauses` has forward
  map exactly `(boundedConstructibleUpperStarLowerStarAdjunction ...).projectionMorphism`
  evaluated at `j_!K,B`. This is the adjunct of the actual oplax tensorator followed
  by counit tensor identity. The equality fixes the actual map, not its endpoints only.
- The `Q` family has forward map exactly the restricted open adjunction's
  `projectionComparison K N`, for EVERY bounded constructible N on Z. That definition
  is extension of unit tensor identity, followed by extension of the actual lax
  pullback tensorator, followed by the open counit, with the node's orientation.
- Both families are isomorphisms, rendering invertibility of alpha and Q without
  imposing it as a hypothesis.
- `compactificationProjectionPullbackIso` is the inverse of the recorded
  `boundedConstructibleUpperStarComp`, followed by `eqToIso` of `c.overI_overG`.
  It is precisely the specified a: Lj* Lq* to Lf*, including the factorization equality.
- `(P B).hom` is fixed to alpha, then `Rq_*((Q (Lq*B)).inv)`, then
  `F_c.map (K ◁ a.hom.app B)`. This is the displayed P in Lean's left-to-right
  composition notation, in the restricted category itself.
- `(P B).inv` is fixed to `F_c.map (K ◁ a.inv.app B)`, then `Rq_*(Q.hom)`,
  then alpha inverse, exactly R in the node. Both identity equations are also
  explicitly asserted as `(P B).hom ≫ (P B).inv = 𝟙 _` and its reverse.
- For arbitrary B, B' and h, the naturality clause is
  `F_c.obj K ◁ h ≫ (P B').hom = (P B).hom ≫ F_c.map (K ◁ Lf*.map h)`.
  This is exactly the node's equation with Lean's composition convention.
- For every B, `c = compactificationOverField f` implies heterogeneous equality
  of `(P B).hom` with `((boundedConstructibleExceptionalProjection ... f).app K).app B`.
  HEq only allows the compactification-dependent endpoints to be compared before
  transporting along that equality; at the chosen c it is ordinary map equality.
- `compactification_projection_ambient_normalizationClauses` asserts equality of
  the underlying restricted alpha and Q with `internalProjection` and
  `internalOpenProjection`. These are the actual ambient adjunction mates.
- `compactification_projection_proper_normalizationClauses` states the full
  `D(E_Y)` image square, with derived-push, tensor, and derived-pull comparisons
  inserted, equating that alpha with the precise ringed `projection` used by
  `derivedProjectionFormulaMate` and `lem-weil-pbc-ringed-projection-mate-exact`.
- `compactification_projection_open_normalizationClauses` states the analogous
  full `D(E_Z)` image square, with tensor, extension and pull comparisons inserted,
  equating Q with the ringed `openProjection`, the adjoint of unit tensor identity
  followed by inverse delta. These last two predicates reproduce the comparison
  dependency's exact normalization equations, specialized by the theorem to j,q,K,B,N.
- The binder `∀ T, HasDerivedCategory.{u+1,u+1,u+2} (ModuleRingedComparison.modules ... T)`
  is the existing section-module realization's chosen derived localization. It
  specifies the categorical infrastructure used by D(E_T), not a new geometric,
  coefficient, or isomorphism hypothesis. The coefficient and site universes are
  retained exactly. It neither identifies site universes nor chooses an Abelian
  structure from a Nonempty proof.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `compactificationOverField`, `boundedConstructibleUpperStar`,
  `boundedConstructibleLowerStar`, both restricted adjunctions,
  `boundedConstructibleUpperStarComp`, `boundedConstructibleLowerShriekOfCompactification`,
  and the inherited monoidal structure. The `bcoOpenAdjunction` recorded for
  def-sfb-dc-open-lower-shriek-adjunction is a transparent alias of the exact full
  adjunction name used here; its node's lean.note explicitly names that declaration.
  No replacement adjunction is defined.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClRingObj`, with finite-subextension-valued sections.
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale` publicly
  retains `ProEtale.boundedConstructible`, `BoundedConstructible`, and
  `mem_boundedConstructible_iff`; the general internal-module form is used here.
- `Sheaf.Paper.BoundedConstructiblePushforwardRestriction` publicly retains the
  recorded restricted operations and their ambient structures. The named coefficient
  specialization is used, so its arbitrary-preservation variant is unnecessary.
- `Sheaf.Paper.ModuleRingedToposDerivedComparison`: `internalProjection`,
  `internalOpenProjection`, `projection`, `openProjection`, `projection_comparison`,
  `openProjection_comparison`, and their specified section-derived comparisons.
- `Sheaf.Paper.ProjectionMateExact`: `SheafOfModules.ringedProjectionMateExact` and
  its `derivedProjectionFormulaMate` canonical-mate interface; the map used by the
  comparison module is this same specified mate.
- `WeilConjectures.PoincareDuality.ProjectionFormula`:
  `boundedConstructibleExceptionalProjection`, whose actual component, ambient
  inclusion, and compactification composition map occur in the final clause.
- Proof imports: `Sheaf.PoincareDuality.ProperProjectionFormulaBounded`, with
  `isIso_properProjection_bounded`; `Sheaf.Paper.CondensedOpenExceptionalProjectionFormula`,
  with `condensed_open_exceptional_projection_formula` (also publicly imported for
  its shared ambient module structures). The module docstrings carry the node's
  five-step assembly proof, including normalization, inversion, naturality, and
  the final component calculation.

Edge cases checked: no nonempty scheme hypothesis excludes empty X, Y or Z; zero K,
B, N and h are allowed; j or q may be identities; arbitrary and chosen compactifications
are both included, with the latter compared using the actual composition isomorphism.
The coefficient is the algebraic-closure case, not an assumed common finite extension.
An independent universe for a test category is not introduced. Inverse arrows are
specified only after isomorphism witnesses whose forward arrows are fixed, avoiding
an unjustified `inv` of an arbitrary morphism. No statement fault or dispute remains.

Searches for existing declarations:

- msearch LeanFinder: "The compactification projection formula is invertible with
  inverse the composite of proper projection inverse and open extension by zero
  projection comparison". Eight hits on Stone-Cech extensions, OnePoint and abstract
  completion comparisons; none states the geometric canonical-map assertion.
- msearch Loogle: `CategoryTheory.Adjunction, CategoryTheory.IsIso`. Twelve hits on
  adjunction-to-equivalence and fully faithful functors; none matches this statement.
- msearch grep: `exceptionalProjection|properProjectionMorphism|openImmersionProjectionComparison`.
  No Mathlib hits. Additional repeated queries and service digests are retained in
  sandbox `searches.jsonl` from the interrupted work.
- msearch LeanSearch: "The exceptional projection of a compactification is a natural
  isomorphism with explicit inverse". Eight hits on explicit cokernels, Grothendieck
  constructions, Proj and CompHaus; none matches.
- Direct rg of Mathlib CategoryTheory found no geometric exceptional projection.
  Direct rg of WeilConjectures and Sheaf for `compactificationProjection`,
  `exceptionalProjectionMorphismOfCompactification`, `internalOpenProjection`, and
  the node id found the upstream constituent arrows and the section comparison,
  but no theorem assembling the restricted normalization, specified reverse composite,
  both identities, naturality and target component. The upstream isIso instance alone
  does not assert these clauses. Separate etale/integral compactification maps use
  different coefficient categories and do not match.

Compilation: the complete module passed scompile.py in sandbox mode and its actual
library module mode with no warnings. A proof dependency brings the unrelated global
`WeilConjectures.integralCoefficientAbLocallyBijective` instance into the elaborator;
its unconstrained max-universe parameter caused a stuck size constraint. Removing
that imported instance from the active instance table makes Lean select the section
comparison's original instances. This changes no object, definition or hypothesis.
All delivered lines are at most 100 characters. There are no diagnostic commands,
auto-bound implicits, local definitions, new nodes, or dependency record repairs.

## Second reading by Q38

No second reading by another worker: this dispatcher brief explicitly forbids starting
other agents and directs the worker to deliver; the maintainer supplies independent
review. I reread the current node and completed module clause by clause above. In the
saved draft I found unfinished inverse/normalization clauses and obsolete instance
priority names; these are replaced by the complete exact clauses and current published
interfaces. The final statement has the node's fixed coefficient, arbitrary N, explicit
reverse composite, both identities, every h, and the chosen target component. No DAG
statement was changed.
