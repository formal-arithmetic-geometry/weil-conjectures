## Worker report

Repair of returned immutable head `dc74ed12fc53`, point H3 and points H2/H4.
The original primary theorem `AlgebraicGeometry.ProEtale.finite_level_projection_factors`
is retained with exactly its accepted signature. The module now additionally states the
Moreover clause for the same fixed-scalar category and the same `A : Type (u + 1)`.
Only the item's `lean` field changes; the statement, dependencies and proof plan are unchanged.

The new helpers belong to this node's coefficient-identification clause and are in
`AlgebraicGeometry.ProEtale.FiniteLevelComparison`. Their source/blueprint docstrings
identify this node and give the proof plan of every postponed property. They are not
independent replacement definitions of tensor, pullback, direct image or extension by zero.
Definitions have actual data; only named theorems are `sorry`.

Hypothesis-by-hypothesis reading of the primary signature:

| Node hypothesis | Lean |
| --- | --- |
| prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| field k, characteristic p > 0, p different from ell | `(k : Type u) [Field k] [CharP k p]`, `_hp : 0 < p`, `_hne : p ≠ ℓ` |
| finite commutative A killed by an ell-power | `A : Type (u + 1)`, `[CommRing A] [Finite A]`, `_hA : ∃ n : ℕ, 0 < n ∧ (ℓ ^ n : A) = 0` |
| X, X-bar, Y are k-schemes | `X Z Y : Over (Spec (.of k))` (Z denotes X-bar) |
| all three separated and finite type over k | `[LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]` for each T |
| j an open k-immersion | `j : X ⟶ Z`, `[IsOpenImmersion j.left]` |
| p_0 a proper k-morphism | `p₀ : Z ⟶ Y`, `[IsProper p₀.left]` |
| f = p_0 j | the composite is `j.left ≫ p₀.left`; f is an abbreviation in the prose, not an independently constrained datum, and neither displayed factor needs a separate f |
| ordinary unbounded derived C and B on the original small pro-etale sites | `DerivedCategory (Sheaf (Scheme.ProEt.topology T.left) (ModuleCat.{u + 1} A))` |
| bounded constructible cohomology for C and B | `_hCc`, `_hBc`: `TStructure.t.bounded` and the recorded `IsConstructibleProEtaleFixedModuleSheaf` on every homology sheaf |
| finite Tor amplitude for C and B | `_hCt`, `_hBt`: existential ordered bounds in the recorded `HasFixedCoefficientProEtaleTorAmplitude` |

Clause-by-clause reading:

1. The proper arrow is the component of `rightDerivedLowerStarProjectionMap` at
   `D(j_!) C, B`. This is the canonical counit transpose for
   `derivedUpperStarLowerStarAdjunction` and `leftDerivedUpperStarTensorComparison`.
   The first conjunct asserts invertibility of this particular morphism.
2. The open arrow is the component of `derivedOpenImmersionLowerShriekProjectionMap`
   at `C, Lp₀^*B`. It is the unit transpose under the exact open adjunction, with the
   canonical identification of total left-derived and exact pullback. The second
   conjunct asserts invertibility of this particular morphism.
3. The third conjunct identifies its inverse with
   `derivedTensorOpenImmersionLowerShriekIso.hom` at these same inputs.
4. The final two conjuncts give bounded intrinsic constructible cohomology and finite
   Tor amplitude for `D(j_!) C`, with exactly the input predicates now on Z.
5. Both canonical arrows are bifunctor natural transformations; their types supply
   naturality in both arguments. Substitution of `D(j_!) C` and `Lp₀^* B` preserves it.
6. `coefficient` is `(constantSheaf ... Ab).obj (AddCommGrpCat.of A)` on Profinite,
   the discrete constant condensed ring itself. It uses A in universe u+1 directly,
   without ULift or a different scalar ring. `Internal` uses the existing
   `condensedRingObj` pullback. `coefficient_comm` is its commutativity property.
7. `sectionRing` is the dependency's reconstructed section-ring sheaf.
   `scalarMap_existsUnique` characterizes the map from the ordinary constant ring
   sheaf on every constant section, using the existing monoidal `constantSchemeIso`.
   `scalarMap` selects this uniquely specified morphism. `encoding` is the existing
   `sectionModuleEquivalence.functor`, scalar restriction along `scalarMap`, the
   canonical constant-sheaf/forgetful comparison, and `constantRingModuleRestriction`.
   Thus its forward functor is the exact section-action construction, not an
   arbitrary equivalence. `encoding_properties` states additive equivalence, which
   implies exactness. `derivedEncoding` is its actual termwise derived equivalence.
8. `monoidal_existsUnique` specifies the tensorator on pure tensors of the original
   section groups. It uniquely determines the strong monoidal structure, including
   its unit via the monoidal unitor axioms. `monoidal` takes this unique value.
   `encoding_preservesFlat` supplies the named flatness property.
   `tensorIso` is the existing K-flat left-derived tensorator transported along the
   exact functor's canonical `LF ≅ D(F)`; it is an actual isomorphism, with no
   Nonempty assertion or arbitrary tensor identification.
9. `coefficient_models` states every ordered Tor interval equivalence against the
   dependency's `HasFixedCoefficientProEtaleTorAmplitude`, the equivalence between
   `HasFiniteConstantLocalModel` and local constants from finite A-modules on a
   pro-etale cover, and the equivalence of the bounded constructible finite-Tor
   predicates. It applies to all Noetherian schemes, hence to each standing
   separated finite-type k-scheme. Over finite A, finite and finitely presented
   modules coincide. No new constructibility or Tor predicate is defined.
10. `pushMap_existsUnique` fixes the underived direct-image comparison to the
    identity on the common section groups. `pushMap` takes this unique map;
    `pushMap_isIso` states invertibility. `pullIso` is its left-adjoint mate via
    uniqueness of left adjoints, and `openIso` is the open left-adjoint mate of
    this same pullback comparison. These constructions fix the adjunctions.
11. `derivedPushIso`, `derivedPullIso`, and `derivedOpenIso` are actual natural
    isomorphisms obtained by localization of those maps and the existing canonical
    exact-functor derived comparisons. `derivedRestrictionIso` gives the same open
    comparison in the exact `D(j^*)` form used by the fixed-scalar open adjunction.
12. `proper_adjunction_comparison` explicitly equates the transported internal
    derived unit and counit with the fixed-scalar unit and counit, with all
    comparison factors written out. `open_adjunction_comparison` states both
    corresponding equations for exact open extension/restriction. These are
    statements about this A and these fixed-scalar categories.
13. `proper_projection_comparison` explicitly identifies the internal canonical
    counit mate (written with `Adjunction.rightAdjointProjectionMap`) with
    `rightDerivedLowerStarProjectionMap (ModuleCat A)`. `open_projection_comparison`
    explicitly identifies `CondensedRing.openImmersionProjectionComparison'` with
    `derivedOpenImmersionLowerShriekProjectionMap (ModuleCat A)`.
    Both equations contain the tensor, pullback and direct-image/open-extension
    comparisons, and hold for arbitrary unbounded inputs over finite A. Applying
    them at the inverse images under `derivedEncoding` covers the item's C and B.
14. `compactificationIso` is the explicit composite of `derivedOpenIso` and
    `derivedPushIso`, with the displayed associators and whiskerings. It identifies
    the actual `Rp₀,* D(j_!)` functors in the two presentations, including the
    item's chosen factorization. It is a natural isomorphism, not Nonempty.
15. No algebraic closure or finiteness of k is assumed. The primary theorem's field
    hypotheses are unchanged; the comparison statements hold in greater generality.

Dependency declarations used (not claimed as declarations of this node):

- `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement` and its factorization setting.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`:
  `AlgebraicGeometry.ProEtale.derivedTensor` (the canonical monoidal derived tensor).
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence` and
  `sectionRingSheaf`, used directly in the new bridge.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` and
  `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`: recorded ordinary
  operations, alongside their existing upstream fixed-scalar realizations
  `upperStar`, `lowerStar`, `openImmersionLowerShriek` and their adjunctions.
- `Sheaf.Paper.ProEtaleFixedModuleConstructible`:
  `AlgebraicGeometry.Scheme.IsConstructibleProEtaleFixedModuleSheaf`.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`:
  `AlgebraicGeometry.Scheme.HasFixedCoefficientProEtaleTorAmplitude`.
- `Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence`:
  `FiniteDiscreteOrdinary.moduleObject_ordinary_coefficient_equivalence`, the
  recorded smaller-scalar theorem, remains a proof dependency. Its interface alone
  does not state the new comparison equations; no such claim is made in this repair.
- `Sheaf.Paper.FiniteConstantRingedLocalModel`, publicly importing
  `Sheaf.Paper.CondensedConstantConstructibility`: dependency declarations
  `HasFiniteConstantLocalModel`, `constantModelBoundedConstructible` and the
  constructible finite-Tor full subcategory, used without a private copy.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `CondensedRing.compactificationOverField`, with the field setting rendered by
  explicit Over and morphism-property binders in the primary theorem.
- Other canonical constructions: `FiniteDiscreteSchemeRing.constantSchemeIso`,
  `constantRingModuleRestriction`, the internal pure-tensor map
  `InternalAbelianSheafModule.comparison_internalTmul`, and the published
  exact/left/right-derived functor comparison and adjoint-uniqueness APIs.
- All recorded proof-dependency modules remain ordinary imports, including
  `ModuleRingedToposDerivedComparison` and `FiniteCoefficientModelComparison`.
  Their theorems are not in `lean.declarations`; that list contains only the 29
  declarations actually introduced in this module.

Edge cases checked:

- Zero ring A, zero C or B, and empty schemes are allowed. Neither construction nor
  statement adds nontriviality or nonemptiness. The constructibility dependency's
  positive-stratum convention permits an empty stratum. The scalar-map normalization
  uses sheafification and therefore also handles empty site objects correctly.
- Identity open/proper maps and a single-point scheme are admitted. The
  identity-on-sections direct-image normalization and adjoint-uniqueness constructions
  retain the canonical unit/counit normalization, including these cases.
- Arbitrary finite non-field coefficient rings such as Z/ell² are admitted; there
  is no global dimension or Z/ellⁿ-flatness hypothesis.
- Infinite and imperfect fields of the standing characteristic are admitted.
- Small pro-etale site objects stay in universe u+1, morphisms in u, coefficient
  A and sheaf values in u+1. The new constant coefficient and every operation
  comparison use exactly A, without an unjustified equality of universes.
- Tor bounds are separate from cohomology bounds. Zero-length ordered Tor intervals
  are retained, and local model and Tor tests quantify over all required modules.

Searches made for an existing complete statement:

- msearch LeanFinder: "Proper and open projection formulas for finite coefficient
  constructible sheaves on proetale schemes and internal module coefficient transport".
  Eight hits, including `SheafOfModules.Presentation.map_π_eq` and condensed-module
  constructions, none the complete assertion.
- msearch Loogle: `SheafOfModules, "projection"`: zero hits.
- msearch grep: `projectionFormula|projection_formula|derived.*[Pp]rojection|[Pp]rojection.*[Dd]erived`:
  two unrelated comments in `Mathlib/CategoryTheory/Monad/Algebra.lean`.
- msearch LeanSearch: "Proper projection formula and open extension by zero for bounded
  constructible complexes over finite torsion rings on small proetale sites": eight
  hits, proper restriction and unrelated homological declarations, no complete match.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for finite-level/projection factor names,
  projection maps/formulas, coefficient equivalences and the exact blueprint id.
  Upstream has the canonical proper/open maps and the open isomorphism, and a proper
  formula with explicit etale-origin input. `FiniteRingCompactSupportProjection`
  assumes the algebraic closure of a finite field and gives a composite, not this
  node's two factors over an arbitrary standing field. None is the full item.
  Reused all existing canonical maps and coefficient/comparison declarations.
- `dag/lean_names_upstream.json`: no declaration attached to this exact item id.


Repair searches:

- msearch LeanFinder, "Canonical section action equivalence from internal modules
  over the constant condensed ring to fixed scalar module sheaves compatible with
  derived projection maps": eight condensed-module hits, no operation/projection
  comparison for this setting.
- msearch Loogle, `Adjunction.rightAdjointProjectionMap, constantRingModuleRestriction`:
  zero hits; the service reported unknown identifier `Adjunction.rightAdjointProjectionMap`.
  This is a search limitation, not evidence of absence; repository source searches
  located and reused the upstream declaration.
- rg in Mathlib, WeilConjectures and Sheaf for finite-level factor names,
  section-action/constant module restriction, encoding push/pull/open comparisons,
  tensorators and derived monoidal APIs. Existing private comparisons in
  `FiniteDiscreteEncodingPullbackFixed` and `FiniteDiscreteEncodingCompactification`
  have ULift A with A : Type u and only publicly expose Nonempty object comparisons.
  They cannot express this item's A : Type(u+1) operation equations. The new bridge
  uses the same canonical constructions and normalization directly at the required
  universe. The generic section-module equivalence, constant-sheaf comparison and
  derived functor APIs are reused, not redefined.

Validation: `scompile.py Q118 lem-sp-finite-level-projection-factors` compiled the
complete module in sandbox and library modes with no error or warning. Initial
attempts exposed missing commutativity and declaration visibility, which were repaired
using a named property and explicit public imports. An unnecessary import of upstream
Localizing timed out; its only needed map is now written using its existing defining
adjunction expression, without importing the unrelated localizing results.

No STATEMENT-DISPUTED issue or statement correction. No new DAG node or dependency
replacement: the helpers are precisely the missing operation-comparison data in this
item's own Moreover clause, as authorized by the return and the same-node helper rule.

## Second reading by Q118

Reopened the node, primary signature, all comparison signatures and the current
blueprint paragraph (3). The primary theorem still has exactly the accepted
hypotheses, arrows and five conjuncts. The Moreover clause is now stated by the
local declarations in items 6--14 above, with literal A, no ULift, no Nonempty
operation choices, both units and counits, and both literal fixed-scalar projection
maps. The compactification comparison is a concrete composition of the normalized
operation isomorphisms. Each data selection is either a unique normalized map or
the existing adjunction/derived universal construction. Every postponed property
is a named theorem with a source and proof docstring.

H3 repaired: ringed-topos comparison theorems no longer stand in for fixed-scalar
comparison equations. H2/H4 repaired: `lean.declarations` lists only declarations
actually introduced in this node's module; imported proof-dependency theorems were
removed from the list. The report no longer claims their reexport states the
item's Moreover clause. Compared with current main, the node changes only `lean`.
This is a substantive addition to the returned head, not an unchanged rebase.
No additional agent was started; maintainer independent review follows delivery.
