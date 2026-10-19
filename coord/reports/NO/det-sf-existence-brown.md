## Worker report

The new module `Sheaf.Paper.BrownExceptionalAdjoint` states
`AlgebraicGeometry.ProEtale.CondensedRing.exists_brownExceptionalAdjoints` with `sorry`.
It introduces one data-bearing helper, `brownCompactificationRefinementMap`, whose value
is the actual pushforward of the recorded open-adjunction refinement map, followed by the
inverse canonical derived direct-image compositor and transport along the refinement's
proper triangle. There is no choice of an arbitrary comparison and no sorried definition.

Hypotheses, individually:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- The field and positive characteristic are `(k : Type u) [Field k] (p : ℕ)
  [CharP k p] (_hp : 0 < p)`; `_hpℓ : p ≠ ℓ` is the unequal-characteristic condition.
- `X` and `Y` are `Scheme.{u}`. Their `Over (Spec (.of k))` structures are the specified
  k-scheme structures. `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on each
  structure map mean separated finite type over k; finite type includes quasi-compactness.
- `(f : X ⟶ Y) [f.IsOver (Spec (.of k))]` is a k-morphism, and the three corresponding
  instances on f impose exactly separated finite type.
- `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}` with `MonObj` and
  `IsCommMonObj` is a commutative condensed ring, and
  `_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ` is exactly the recorded six-case
  coefficient convention. In particular the algebraic closure uses all continuous maps,
  not the finite-subextension-valued condensed object.
- `localizingClosureProEtale Λ Z` is precisely the recorded Loc(Dctf(Z,Λ)). Its ambient
  category is the ordinary unbounded derived category of internal modules over
  `condensedRingObj Λ Z`. It publicly imports the recorded constant-model constructibility
  and finite-Tor definitions. No completed category or bounded category is substituted.
- The source Brown assumptions appear as
  `[(localizingClosureProEtale Λ X).IsTriangulated]`,
  `[LocallySmall.{u + 1} ...FullSubcategory]`, and
  `[HasCoproducts.{u + 1} ...FullSubcategory]`. The first supplies the canonical ambient
  shifts and distinguished triangles on the full subcategory.
- `_hgen` exhibits `I : Type (u + 1)` and objects `E` in the source full subcategory.
  Its first conjunct puts each underlying object in bounded constant-model constructibles
  and finite Tor amplitude, exactly Dctf; its second says `IsCompactObject (E i)`;
  its last is the recorded `IsTriangulatedGeneratingFamily E`. These are the witnesses
  unpacking the recorded `IsCompactlyGeneratedTriangulated`, with the source's additional
  requirement that the generators belong to Dctf. The universe is the same fixed indexing
  universe used by the landed Brown-hypotheses interface.
- Compactifications are quantified as `Compactification.BoundaryCompactification f`.
  The existing type includes the quasi-compact open immersion and proper map, with the
  factorization equality. No density is imposed on the compactification itself.
  Packaging the assertion simultaneously for all c also supplies it for any chosen c.

Conclusions, clause by clause:

1. The existential family `h` proves that every actual ambient compactification composite
   preserves the two recorded closures. `localizingLowerShriek Λ c.obj.obj (h c)` is the
   existing canonical full-subcategory lift of that composite; it has the same objects
   and maps as `Rp_* D(j_!)`. The existential `G` and `adj` give an exceptional functor
   for each c and an adjunction. `Adjunction.homEquiv` is the required bijection on
   every pair of objects and contains both naturality laws. The existential target
   triangulation `hY` is a consequence of the standing geometry, not an assumption.
2. For every c, the installed shift structure is exactly
   `(adj c).rightAdjointCommShift ℤ`, rather than an independently chosen shift.
   Under that structure, `(G c).IsTriangulated` is exactness, and
   `(adj c).CommShift ℤ` states compatibility of the unit and counit. Mathlib's
   `rightAdjointCommShift` includes the zero and addition coherence identities.
3. For every c, every J and every adjunction `adjJ`, `∃! e : G c ≅ J` with
   `F_c.map (e.hom.app N) ≫ adjJ.counit.app N = (adj c).counit.app N` gives exactly
   uniqueness compatible with the adjunction. It does not assert uniqueness among
   arbitrary natural isomorphisms. For different c,d the existential `phi` compares
   the actual restricted lower shrieks. For every dense refinement d→c its components
   under the inclusion equal `brownCompactificationRefinementMap`. Thus phi is the
   canonical comparison, normalized by the recorded refinement construction; the
   identity and cocycle equations determine comparisons through every common dense
   refinement and ensure independence of its choice. The family `gamma` compares G c
   and G d with the exact transferred-counit equation
   `F_d(gamma) ≫ epsilon_d = phi.inv ≫ epsilon_c`. The following universally quantified
   clause makes it the unique such natural isomorphism. The final two clauses are
   `gamma c c = Iso.refl _` and `gamma c d ≪≫ gamma d e = gamma c e`.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and the documented
  explicit geometric setting. Its actual local signature uses schemes with Over
  structures; no new standing-setting predicate is introduced.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `IsConstantModelConstructible`, `constantModelBoundedConstructible`,
  `ConstantModelConstructibleFiniteTor`, and their documented finite scalar models.
- `Sheaf.Paper.LocalizingAdmissibleCoefficients` and its public import
  `Sheaf.Paper.LocalizingClosure`: `IsLocalizingAdmissibleCoefficient`,
  `localizingClosureProEtale` (all under AlgebraicGeometry.ProEtale).
- `Sheaf.CategoryTheory.CompactlyGenerated`: `IsCompactlyGeneratedTriangulated`,
  unpacked using its imported `IsCompactObject` and `IsTriangulatedGeneratingFamily`.
- `Sheaf.SixFunctorsBasics.BrownHypotheses`: `CategoryTheory.BrownHypothesesFor` and
  `brownHypotheses`. The theorem supplies the target structures in the proof route;
  no extra target Brown hypothesis is imposed.
- `Sheaf.Compactification.BoundaryRefinement`:
  `AlgebraicGeometry.Compactification.BoundaryCompactification` and
  `DenseBoundaryCompactification`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`, exactly the two separately derived factors.
- `Sheaf.Paper.LocalizingExceptionalAdjoint`: the already defined
  `localizingLowerShriek` and `localizingLowerShriekCommShift`. These are reused as
  constructions, not copied. Its larger theorem does not state compactification
  comparisons or their cocycle and is not recorded as an exact existing match.
- `Sheaf.Paper.CompactificationRefinementLocalizing`: `localizingRefinementMap`,
  `refinementTheta`, `refinementDerivedLowerStarComp`, and their normalized constructions.
  The existing constructions are referenced through the new definition record
  `def-sf-comp-refinement-data`; no second Lean owner is introduced.
- Proof imports use `compactification_localizing`, `brownRepresentabilityRightAdjoint`,
  `Yoneda.fullyFaithful`, `Adjunction.isTriangulated_rightAdjoint`, and
  `Adjunction.rightAdjointUniq`. Their signatures and docstrings were read. The
  proof dependency det-sf-comp-coherence-cocycle currently has no recorded Lean
  declaration; no import for that unstated theorem is possible. The source normalization
  needed for the item's own statement is rendered directly using the already landed
  refinement construction, with no postponed extra theorem and no prerequisite wait.
- def-weil-size-convention is the recorded metatheoretic convention, rendered by
  explicit universes; it deliberately has no Lean declaration.

Import-cycle note for future proof imports: the existing restriction helper lives with
sk-prop-sf-existence, whose natural-language proof uses this item. This module imports
that helper's existing owning module. The reverse proof-only import must therefore be
omitted by the normal cycle check; do not duplicate the restriction definition to remove
that cycle. This delivery changes neither the parent module nor its statement.

Edge cases checked before and after writing: no nonemptiness is imposed on schemes or
on I; the zero category may have an empty generating family. Empty schemes, the zero
object, the empty coproduct, and the zero coefficient ring (allowed by the finite ring
case) are retained. Arbitrary integers, including zero and negative shifts, are covered
by CommShift ℤ. Compactifications need not be dense; only the common-refinement
normalization uses a dense source, exactly as in the source construction. Self-comparison
and repeated compactifications are explicit identity cases. All six coefficient cases,
all separated finite-type k-schemes, and arbitrary chosen compactifications are retained.
No STATEMENT-DISPUTED flag and no mathematical statement correction is needed.

Searches made:

- msearch.py leanfinder: “Brown representability gives an exact right adjoint to compact
  support pushforward on the localizing closure of constructible complexes”. Eight
  results concerned sheaf adjunctions and condensed adjunctions; no complete match.
- msearch.py leansearch: “right adjoint of compact support pushforward Brown
  representability localizing constructible”. Eight results on generic adjoint criteria
  and sheaf/module pushforward; no match for all three clauses.
- msearch.py loogle: `CategoryTheory.Adjunction, CategoryTheory.Functor.IsTriangulated`.
  Seven results including `Adjunction.isTriangulated_rightAdjoint`; these supply only
  the exact-adjoint component, not the geometric assertion and independence clauses.
- msearch.py grep: `Brown|brown|rightAdjointUniq` in CategoryTheory/Triangulated: zero hits.
- Direct rg in the allowed Mathlib checkout inspected Shift/Adjunction, Adjunction/Unique,
  Triangulated/Adjunction, Yoneda, and full-subcategory lifting interfaces. These give
  the generic shifts, uniqueness, and exactness constructions, not this full statement.
- Direct rg in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id and
  Brown/localizing compact-support patterns: no declaration for this item; the older
  ExceptionalAdjoint module instead concerns the ambient FullCD hypothesis.
- Direct rg in `lean/Sheaf` found the exact localizing closure, source Brown hypothesis,
  refinement maps, and restriction helper reused above. The existing parent adjoint
  theorem lacks the compactification-comparison clauses, so it is not an existing match.
- Direct rg in dag/lean_names_upstream.json and both allowed Lean source trees for the
  new declaration names found no collision. DAG searches identified the owning theorem nodes of the reused constructions;
  the new definition record below records their existing interface without new Lean data.

Validation: compilation is exclusively through scompile.py with the unchanged 60-second
per-file limit. Explicit compactification and object binders repair expensive projection inference.
The final file uses the default heartbeat budget and the unchanged wall-clock limit.
Final compiler and dry-run results are recorded below.

## New nodes

`def-sf-comp-refinement-data` records the six exact existing declarations in
`Sheaf.Paper.CompactificationRefinementLocalizing` with `existing: true`:
`refinementDerivedLowerStarComp`, `refinementOpenUnit_isIso`, `refinementOpenRestriction`,
`refinementOpenRestriction_isIso`, `refinementTheta`, and `localizingRefinementMap`.
They are the canonical compositor, open restriction, invertibility facts, theta, and adjoint
refinement map used in the Brown comparison. The source is the refinement-coherence blueprint
unit and its proof. The saved search records locate these constructions in the existing theorem
module; no separate definition node owns their interface. This delivery reuses that module,
with no new refinement declaration and no change to its existing theorem or constructions.

The separately landed `def-sf-localizing-lower-shriek` node is reused as it stands. It records
`localizingLowerShriek` and `localizingLowerShriekCommShift` in
`Sheaf.Paper.LocalizingExceptionalAdjoint`; no copy of that node or module is delivered.

## Repair of return fe34663dbb1e

The return identified six duplicate declarations in CompactificationRefinementData. All six
are now imported from their existing owner, CompactificationRefinementLocalizing. The copied
data module and the proposed edit of the existing coherence module have both been removed.
No name is changed. Each comparison in BrownExceptionalAdjoint uses the exact published
construction, including the normalized derived compositor and the open-adjunction map.
The new definition node is now an existing-declaration record, with no Lean file of its own.

The first required saved-packet dry run compiled its files but failed preflight because another
group had landed def-sf-localizing-lower-shriek and the stale copy was classified as an
unreported dependency repair. That saved node copy has been removed; the item cites the landed
node directly. No dependency module is now delivered. The item retains its original natural
statement and proof; only lean and stmt_deps differ from current main.

The normal proof-import cycle rule applies: when the refinement-coherence proof later uses the
Brown theorem, its reverse proof-only import must be omitted. Importing its existing construction
interface here is authorized reuse, with no duplicated fact or hollow definition.

## Second reading by NO

This is the required self-check under the dispatcher's prohibition on starting other agents;
the maintainer performs the independent review. I reopened the item statement, the blueprint
statement and proof parts (1)--(3), the final Lean file, the new existing-declaration record, and
the published refinement and lower-shriek declarations.

The field, prime, characteristic, separated finite-type geometry, six admissible coefficients,
source local smallness, triangulation, coproducts, and Dctf compact generating family have the
same binders as the earlier reading above. Clause (1) is G with adj, providing the natural Hom
bijections. Clause (2) installs rightAdjointCommShift before exactness and unit/counit shift
compatibility. Clause (3) states counit-compatible uniqueness for fixed compactification,
normalizes phi by every dense refinement using the published refinement map, and states the
transferred-counit equation, uniqueness, identity and cocycle for gamma. Both identity and
cocycle also occur for phi. The helper pushes the published open refinement map forward and
uses the inverse published derived compositor, then the proper-triangle transport.

No signature, hypothesis, conclusion, helper body, or proof is changed by this repair; only the
refinement import and its ownership record change. The file has exactly one sorry, the named
Brown theorem proof. It contains no copied refinement or lower-shriek declaration. Every
universe and variable is explicitly bound. Empty schemes, empty generating families, zero
coefficients, all integer shifts, and nondense compactifications remain covered.

Final validation (2026-10-18): scompile.py compiled the final Brown module cleanly in the
sandbox (16.1 s) and at its library path (7.6 s), with no diagnostics. The reduced packet
then passed deliver2.py --no-push: `OK (dry run): commit ec566f93dc passes the preflight
and compiles; nothing pushed`. The delivery contains only the Brown module, its node, the
new existing-declaration refinement-data record, and this report. No published module or
landed dependency node is modified.
