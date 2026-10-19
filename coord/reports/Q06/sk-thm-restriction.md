## Worker report

The item module is `Sheaf.Paper.RationalExceptionalRestriction`, with main theorem
`AlgebraicGeometry.ProEtale.CondensedRing.rationalExceptional_preserves_constructibleFiniteTor`.
Its sole theorem proof is `sorry`. The helper
`AlgebraicGeometry.ProEtale.constantModelFiniteTorToLocalizing` is the actual full inclusion
from the dependency's Dctf category into its localizing closure. It uses Mathlib
`ObjectProperty.ιOfLE` and the defining intersection, with no chosen data or postponed proof.
No statement correction and no new definition node are needed.

Hypothesis and clause matching:

- “Fix a prime ell”: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- “A field k of characteristic p > 0 with p different from ell”:
  `(k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`.
  The characteristic of a field is zero or prime; requiring it prime is exactly positive
  characteristic, and does not choose a second characteristic parameter.
- “A finite extension E/Q_ell”: `(E : PadicAlgCl.FiniteIntermediateField ℓ)`. This is
  a finite intermediate field in the fixed algebraic closure. Every finite extension can
  be embedded there; its norm is the induced ell-adic norm, as in the dependencies.
- “Lambda = E or Qbar_ell, with its condensed coefficient ring”:
  `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`, with `[MonObj Λ]`
  and `[IsCommMonObj Λ]`, together with `_hΛ`, the disjunction of ring-object isomorphisms
  to `Profinite.continuousMapRingObj E` and
  `Profinite.continuousMapRingObj (PadicAlgCl ℓ)`.
  These are all continuous maps for the specified topologies. Ring-object isomorphism
  permits representations of the same condensed coefficient ring. In the Qbar case the
  separately fixed E is allowed to be any finite intermediate field and is unused in
  the second disjunct, exactly as in the natural statement.
- “X,Y separated schemes of finite type over k”: `{X Y : Scheme.{u}}`, their two
  `Over (Spec (.of k))` instances, and `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`
  on each structure morphism. No smoothness, properness or nonemptiness is imposed.
- “f a separated finite-type k-morphism”: `(f : X ⟶ Y)`,
  `[f.IsOver (Spec (.of k))] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]`.
- “In the standing setting”: the displayed scheme/morphism binders express that setting
  directly. `c : Compactification.BoundaryCompactification f` specifies the chosen
  compactification, with its quasi-compact open immersion. It is the same type used by
  the recorded adjoint-existence interface; the theorem works for every such choice.
- “Dctf”: `ConstantModelConstructibleFiniteTor Λ X` and its Y version, defined in
  the recorded constructibility module from `constantModelBoundedConstructible` and
  `DerivedCategory.finiteTorAmplitude`. These are full subcategories of the ordinary
  derived category of internal modules over `condensedRingObj Λ X`; no completeness
  condition and no alternate category of constant discrete-module sheaves is used.
- “Loc(Dctf)”: `(localizingClosureProEtale Λ X).FullSubcategory` and its Y version.
  These use exactly the recorded intersection in the same ambient derived category.
- “The right adjoint f! of sk-prop-sf-existence”: the binder `h` specifies preservation
  of the localizing closures by the canonical ambient
  `rightDerivedLowerShriekOfCompactification Λ c.obj.obj`. The functor `G` and
  `_adj : localizingLowerShriek Λ c.obj.obj h ⊣ G` specify its right adjoint.
  This does not assume constructibility preservation or replace f! by an arbitrary
  map: the adjunction fixes precisely the right adjoint already named by the node.
  The repaired existence dependency supplies such data for these coefficients.
- “f! Dctf(Y) is contained in Dctf(X)”: the first conjunct quantifies over all objects
  `K` of the Y localizing closure and assumes the conjunction of bounded constant-model
  constructibility and finite Tor amplitude of `K.obj`. It concludes both corresponding
  conditions for `(G.obj K).obj`. This includes every Dctf input since the helper
  inclusion sends every such object into the localizing closure.
- “Its restriction is right adjoint to Rf! on Dctf”: existential functors `F₀`, `G₀`
  have exactly the two Dctf domains/codomains. The two equalities after
  `constantModelFiniteTorToLocalizing` identify them on objects and morphisms with the
  original lower shriek and G. `Nonempty (F₀ ⊣ G₀)` states their adjunction, including
  its natural Hom equivalences. The equalities prevent unrelated adjoint functors
  from satisfying this clause. They express the restrictions strictly using proof
  irrelevance for the full-subcategory membership fields.

Dependency declarations read and used:

- `sk-def-sfb-dc-setting`: module
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  declaration `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`.
  Its full source signature uses the same field, scheme-over-base and finite-type
  hypotheses; its chosen compactification supplies the standing convention.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `AlgebraicGeometry.ProEtale.HasFiniteConstantLocalModel`,
  `IsFiniteConstantStratified`, `IsConstantModelConstructible`,
  `constantModelBoundedConstructible`, `ConstantModelConstructibleFiniteTor`.
  These declarations use finite scalar presentations before pullback and the
  affine-local convention for general schemes.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`, with `IsSeparated` and `UniversallyClosed`.
  In this theorem separatedness is used; no properness hypothesis on f is added.
- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingAdmissibleCoefficients`,
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`, and its public
  import `Sheaf.Paper.LocalizingClosure`, declarations
  `CategoryTheory.localizingClosure`, `AlgebraicGeometry.ProEtale.localizingClosureProEtale`.
- `sk-prop-sf-existence`: original module `Sheaf.Paper.LocalizingExceptionalAdjoint`,
  `AlgebraicGeometry.ProEtale.CondensedRing.localizingLowerShriek` and
  `localizingLowerShriekCommShift`; the repaired theorem is
  `exists_localizingExceptionalAdjoint_admissible` in
  `Sheaf.Paper.LocalizingExceptionalAdjointAdmissible` (see below).

The module also imports the recorded stated proof dependencies
`Sheaf.Paper.CompactificationLocalizing` and
`Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible`, and the Mathlib proof leaves for
closed immersions, affine space, constructible subsets, quasi-separatedness and finite
presentation. Mathlib `Adjunction.restrictFullyFaithful` supplies the final formal step.
The other geometric proof nodes have no recorded Lean module to import. Their full
proof plan, including all eight steps, is in the theorem docstring.

Edge cases checked before writing: empty X or Y is allowed, no affine chart or minimum
is chosen in the statement, and the proof docstring treats the empty-cover case. The zero
complex is allowed. The identity morphism and any chosen compactification are allowed.
The extension E = Q_ell (the bottom intermediate field) is included. Both disjuncts allow
all representations isomorphic as condensed ring objects. No truncation bound is fixed,
so every bounded complex with any finite Tor interval is allowed. The indexing universe
of the recorded closure is unchanged; the small pro-etale site still has distinct
object and morphism universes and its additive sheaves are in Ab.{u+1}.

Searches for an exact existing statement (all on 2026-10-18):

- msearch LeanFinder: “The exceptional inverse image right adjoint to compact support
  preserves bounded constructible complexes with rational l-adic coefficients”. Eight
  hits, including LightCondMod.LocallyConstant.adjunction,
  CondensedMod.LocallyConstant.adjunction, CondensedSet.compactlyGeneratedAdjunction,
  CompHausLike.LocallyConstantModule.functor and HomologicalComplex.map_isStrictlySupported;
  none states this geometric preservation theorem.
- msearch Loogle: `CategoryTheory.Adjunction, "restrict"`. Nine hits, including
  `CategoryTheory.Adjunction.restrictFullyFaithful` and its unit/counit/Hom lemmas.
  This only covers the formal last step; it does not prove constructibility preservation.
- msearch grep of Mathlib:
  `upperShriek|exceptionalInverse|constructible.*[Aa]djoint|[Aa]djoint.*constructible`:
  no hits.
- msearch LeanSearch: “Exceptional inverse image preserves bounded constructible
  rational l-adic sheaves”. Eight hits, including sheaf pullback finite-limit preservation,
  scheme constructible-preimage lemmas and inverse-image weak Serre predicates; no match.
- rg of upstream WeilConjectures and project lean/Sheaf for the item id and
  `localizing.*[Rr]estrict|[Rr]ational.*[Aa]djoint|[Ee]xceptional.*[Cc]onstructible`:
  the recorded localizing-adjoint module and other etale/rational coefficient frameworks
  occur, but none states this theorem for the recorded module-object Dctf and closure.
- rg of Mathlib, upstream, project lean/Sheaf and dag/lean_names_upstream.json for the
  three new declaration names: no preexisting declaration. The helper reuses
  `ObjectProperty.ιOfLE`; it is not a second constructible or localizing category.

Validation: both delivered files are compiled separately with scompile.py in dependency
order; dry-run preflight and final delivery use deliver2.py. The results are recorded by
those tools. No Lean source, git state, launcher script or compiled live artifact was
edited directly outside the sandbox.

## Dependency modules

`sk-prop-sf-existence`: the former theorem's Qbar disjunct used
`Profinite.padicAlgClRingObj`, whose own docstring explicitly specifies continuous
functions with image in a finite subextension, and explicitly distinguishes it from
all continuous maps to Qbar. The item's recorded `sk-def-localizing-closure` convention
uses all continuous maps in the valuation topology. This is an actual missing case in
the old existence interface, so §1(B) applies. The repair module
`Sheaf.Paper.LocalizingExceptionalAdjointAdmissible` imports the old module unchanged and
states `exists_localizingExceptionalAdjoint_admissible`, replacing only the expanded
coefficient hypothesis by the existing `IsLocalizingAdmissibleCoefficient ℓ Λ`.
That predicate has all six coefficient classes, including all continuous Qbar maps.
All conclusion clauses of the dependency are retained: preservation of the closures,
triangulated structures and exactness, small coproducts, an exact right adjoint preserving
those coproducts, and unique counit-compatible isomorphism to any other right adjoint.
The existing canonical lower shriek and its shift comparison are reused without copies.
The dependency node is changed only in `lean`, with the required explanatory `note`.

There is a related mismatch in the unstated geometric proof interfaces: some detail
nodes explicitly choose finite-subextension-valued Qbar coefficients. They are not
statement prerequisites or changed in this delivery. A later proof worker must reconcile
those interfaces with the all-continuous coefficient convention before applying them
to the Qbar branch. This does not change either delivered statement or introduce an
additional hypothesis; the discrepancy is reported rather than silently identified.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
