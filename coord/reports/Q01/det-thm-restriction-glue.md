## Worker report

The delivery states `AlgebraicGeometry.ProEtale.CondensedRing.rationalRestrictionGlue`
in `Sheaf.Paper.RationalRestrictionGlue`. Its only postponed theorem is this node's
statement. Two concrete helper definitions, `restrictionGlueLowerShriek` and
`restrictionGlueUpperShriek`, restrict the existing compactification composite and
supplied exceptional inverse image using `ObjectProperty.lift`. Neither contains
postponed data or a postponed proof. No node statement is changed.

Hypotheses, matched against the node:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The fixed finite subextension is
  `(E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) [FiniteDimensional ℚ_[ℓ] E]`.
  This keeps the embedding in the fixed algebraic closure.
- `(k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)`
  is exactly a field of positive prime characteristic distinct from ℓ.
- `X Y : Scheme.{u}`, their `Over (Spec (.of k))` instances, and
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on both structure maps
  express separated finite-type k-schemes. The same three properties on `f`,
  together with `f.IsOver`, express the stated separated finite-type k-morphism.
  Finite type is the conjunction of local finite type and quasi-compactness,
  exactly as in the recorded Mathlib dependency.
- `Λ` is a sheaf of abelian groups on the coherent profinite site equipped with
  `MonObj` and `IsCommMonObj`, the recorded internal condensed commutative-ring
  encoding. `hΛ` identifies it, as a ring object, with the underlying ring object
  of `Profinite.padicSubfieldCondensedRing ℓ E` or with
  `Profinite.padicAlgClRingObj ℓ`. The former is continuous functions into E
  with the induced adic topology; the latter has finite-subextension-valued
  sections, not all continuous maps into the algebraic closure. Ring-object
  isomorphism allows equivalent representations of the same specified coefficient.
- `condensedRingObj Λ X` is the actual inverse image of Λ from the point, with
  its transported multiplication. `DerivedCategory (Mod … (condensedRingObj Λ X))`
  is the unbounded internal-module derived category from the statement, rather
  than a category of discrete field-module sheaves.
- `c : Compactification.BoundaryCompactification f` names the compactification
  fixed in the standing setting. `h`, `G`, and
  `adj : localizingLowerShriek Λ c.obj.obj h ⊣ G` name exactly the lower-shriek
  restriction and right adjoint supplied by `sk-prop-sf-existence`. They are
  parameters for that supplied adjunction, not assumptions that it preserves
  constructibility. The assertion holds for each such supplied choice. Its
  existence and uniqueness are already in the recorded dependency; the present
  node does not choose a different functor from a bare existence statement.

Clauses, matched against the node:

1. The first conjunct quantifies over every `I : Type w` with `[Finite I]` and
   every `U : I → X.Opens`. The equation `iSup U = ⊤` says the opens cover X.
   The ambient object `M` is unrestricted. Its local hypotheses are
   `constantModelBoundedConstructible Λ (U i).toScheme
   (((upperStar Λ (U i).ι).mapDerivedCategory).obj M)` for every i.
   Exact coefficient pullback makes this the prescribed restriction M|Ui.
   The conclusion is `constantModelBoundedConstructible Λ X M`, the dependency's
   precise Dbc predicate.
2. The existential inequalities `hX`, `hY` place Dbc inside the recorded
   `localizingClosureProEtale`; these are conclusions, not extra assumptions.
   They are the typing witnesses for using the supplied adjunction on all A,K
   from Dbc, since the rational heart identifies Dctf with Dbc. The existential
   `hG` says for every localizing object K with bounded constructible underlying
   object, `(G.obj K).obj` is bounded constructible. Thus it covers every
   K ∈ Dbc(Y,Λ), using `hY`. The existential `hF` records Rf!A ∈ Dbc(Y,Λ),
   which the displayed Hom set in the source already requires.
3. `adjbc` is an adjunction between the two concrete lifts on the exact recorded
   `ConstantModelBoundedConstructible` categories. Its `homEquiv A K` is the
   displayed bijection and is natural in both variables by the `Adjunction`
   interface. The final equality, for every A,K and every arrow t, identifies
   its underlying ambient arrow with `adj.homEquiv` applied to the same t.
   Thus the equivalence is the restriction of the supplied one, not an
   unrelated bijection or a new adjunction with arbitrary normalization.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `compactificationOverField`, `HasCompactification.of_isOver`, and the existing
  compactification composite interface, for the standing setting. No older
  upstream bounded-constructibility predicate replaces the corrected recorded one.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `constantModelBoundedConstructible`, `ConstantModelBoundedConstructible`,
  and their cohomological and finite-constant-model definitions.
- `Sheaf.Paper.LocalizingAdmissibleCoefficients`, publicly importing
  `Sheaf.Paper.LocalizingClosure`: `localizingClosureProEtale` and
  `CategoryTheory.localizingClosure`. The admissibility predicate is not used
  to identify Qbar coefficients: the node explicitly specifies the different
  finite-subextension-valued coefficient, and the closure construction accepts it.
- `Sheaf.Paper.LocalizingExceptionalAdjoint`: `localizingLowerShriek` and
  `exists_localizingExceptionalAdjoint`; read the entire supplied adjunction
  signature and its proof plan. `h,G,adj` instantiate its object/adjunction data.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `.QuasiCompact`, `.Proper`,
  `.Separated`: `LocallyOfFiniteType`, `QuasiCompact`, `IsProper`, `IsSeparated`.
- `Sheaf.Topology.ProfiniteCondensedRing`, retaining the continuous constructors;
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `padicSubfieldCondensedRing`, `padicAlgClCondensedRing`, `padicAlgClRingObj`.
  The algebraic-closure dependency has no lean record but has a closed upstream
  audit naming these exact declarations; its existing construction is reused.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, and its commutativity instance, with
  their actual inverse-image formulas. The read-only shared framework sources
  are used as instructed in `coord/pefw-upstream-framework.md`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`:
  exact `upperStar Λ U.ι` and its `mapDerivedCategory` restriction.
- `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`: `lift`, `ιOfLE`,
  `homMk`, and the induced-category `.hom`; these are the existing full-subcategory
  constructions and supply real helper data without a duplicate categorical notion.
- Proof-only imports include the recorded `coefficientHeart`, `cartesianCoefficients`,
  `coefficientHeart_commonStratification`, `reduced_induced_closed_subscheme`, and
  `compactification_localizing`, as well as the Mathlib permanence interfaces.
  `det-thm-restriction-local` has no Lean binding in the read snapshot; it is
  a proof prerequisite only and is recorded in the proof docstring. No statement
  prerequisite is missing and no arbitrary substitute for that local theorem is used.

Edge cases checked before writing: an empty finite indexing type is allowed and
its cover condition forces X empty; empty opens and the zero complex are allowed;
there is no nonempty-cover assumption or chosen global cohomological interval.
The full-subcategory Hom equation works for zero objects and identities. All
finite extensions, including E = Q_l, are admitted. Qbar always uses the exact
finite-subextension construction. The finite indexing universe w is independent
and arbitrary; the coefficient/site universe u follows the published framework,
with Ab in u+1. No equality of object and morphism universes is imposed.

Searches for an existing whole statement and helper interfaces:

- msearch leanfinder, query `bounded constructible complexes glue on a finite open
  cover and exceptional inverse image preserves constructibility`: eight results,
  all about constructible subsets of topological spaces, including
  `Topology.IsLocallyConstructible.of_isOpenCover'`; no module-sheaf theorem.
- msearch leansearch, query `bounded constructible complexes finite open cover
  gluing exceptional adjunction`: eight results on scheme gluing and locally
  constructible subsets; no matching derived constructibility theorem.
- msearch loogle, query `CategoryTheory.Adjunction, "restrict"`: nine results,
  notably `Adjunction.restrictFullyFaithful`. Read its full signature and
  docstring: it assumes the functor restrictions and supplies neither geometric
  gluing nor exceptional inverse-image preservation. Its constructions inform
  the exact restricted adjunction, rather than replace the node's assertions.
- msearch grep, query `boundedConstructible|rightDerivedUpperShriek|rightDerivedLowerShriek`:
  zero Mathlib hits.
- rg of upstream WeilConjectures and the shared Sheaf and framework sources,
  query `restrictionGlue|restriction_glue|constructible.*[Gg]lu|[Gg]lu.*[Cc]onstructible|det-thm-restriction-glue`:
  only unrelated constructibility proof comments and an unrelated private
  relative-Mayer-Vietoris restriction lemma; no exact whole theorem.
- rg of Mathlib and both source roots for `rationalRestrictionGlue`,
  `restrictionGlueLowerShriek`, `restrictionGlueUpperShriek`: no existing names.
  The existing generic `ObjectProperty.lift` is reused for both helpers.

No statement correction, new node, unusable statement dependency, or disputed
assertion is introduced by this delivery. The old split-report dispute concerns
omitted standing hypotheses that are already restored in the current node; the
Lean explicitly includes them. Validation uses scompile.py and deliver2.py only.

Initial validation: scompile.py compiled the sandbox statement and the library-path
module successfully, with no errors or warnings. A local structural read confirms
that the node differs only in `lean`, every universe is explicit, all Lean lines
have at most 100 characters, and the theorem is the sole `sorry`.

## Second reading by Q01

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
