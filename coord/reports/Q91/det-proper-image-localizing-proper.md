## Worker report

Item: `det-proper-image-localizing-proper`. Module:
`Sheaf.SixFunctors.ProperImageLocalizingProper`.

The delivery states both parts of the node, as
`AlgebraicGeometry.ProEtale.CondensedRing.proper_image_localizing_proper` and
`AlgebraicGeometry.ProEtale.CondensedRing.proper_image_localizing_proper_coefficients`.
Both theorem proofs are exactly `by sorry`. The two real-data Prop definitions
`ProperLocalizingHypotheses` and `ProperLocalizingRestriction` spell out this node's
hypotheses and conclusion; they introduce no alternative coefficient category,
constructibility definition, localizing closure, or pushforward. Every declaration
is listed in `lean.declarations`. There are no new nodes or dependency repairs.

Clause-by-clause correspondence:

- Prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`. The algebraic closure is the published
  `PadicAlgCl ℓ`. A finite extension inside it is
  `(E : PadicAlgCl.FiniteIntermediateField ℓ)`, i.e. an intermediate field with
  `FiniteDimensional ℚ_[ℓ] E.val`.
- A finite commutative ell-primary ring is `(A : Type) [CommRing A] [Finite A]`
  with `_hA : ∃ n : ℕ, (ℓ ^ n : A) = 0`. The discrete topology is explicitly
  `[TopologicalSpace A] [DiscreteTopology A]`. The topological ring instance is
  inferred, rather than imposed as another hypothesis. The published condensed
  construction takes ordinary small topological ring carriers, hence `A : Type`.
  Every finite ring admits such a carrier; no finiteness or regularity assumption
  is imposed on any other coefficient.
- The coefficient is a bundled `Mon` in condensed abelian sheaves, with
  `[IsCommMonObj Λ.X]`. `_hΛ` selects exactly six bundled objects, in the node's
  order A, Z_ell, O_E, Q_ell, E, Qbar. A is
  `Profinite.continuousMapRingObj A`; Z_ell and Q_ell use the same published
  continuous-map construction; O_E is `Profinite.padicIntegersRingObj ℓ E.val`;
  E is `Profinite.continuousMapRingObj E`; Qbar is
  `Profinite.padicAlgClRingObj ℓ`. In particular the last is the finite-subextension
  sheaf, not all continuous maps into Qbar. Bundled list membership identifies
  the multiplication as well as the underlying sheaf. A and E are fixed before
  selecting Λ, exactly as in the node's introductory coefficient convention.
- The scheme morphism and properness are `{X Y : Scheme.{u}} (p : X ⟶ Y)` and
  `[IsProper p]` in both theorems.
- The ambient category is the existing ordinary unbounded
  `DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  (condensedRingObj Λ.X X))`. No completeness condition is added.
- Dctf is the dependency's `ConstantModelConstructibleFiniteTor Λ.X X`.
  The first conjunct of `ProperLocalizingHypotheses` quantifies over its objects
  and asserts that the pushforward satisfies precisely the defining conjunction
  `constantModelBoundedConstructible Λ.X Y ⊓ DerivedCategory.finiteTorAmplitude`.
  Thus it is preservation of bounded constructible finite-Tor objects, not only
  bounded constructibility.
- Loc(Dctf) is `localizingClosureProEtale Λ.X X`, using the recorded declaration.
  The second conjunct quantifies over every diagram `F : Discrete I ⥤ Loc.FullSubcategory`
  and asserts `PreservesColimit (F ⋙ Loc.ι) (lowerStar Λ.X p).rightDerivedFunctor`.
  This is precisely the ambient coproduct comparison for families of Loc objects;
  it assumes nothing about families outside Loc. `PreservesColimit` applies to
  every colimit cocone, so it does not depend on a choice of sums.
- Rp_* is `(lowerStar Λ.X p).rightDerivedFunctor`, the total right derived functor
  of the entire module pushforward composite, as required by the dependency.
- `ProperLocalizingRestriction` includes the triangulated structures on both Loc
  predicates, then existentially supplies the image-membership proof `h` for all
  source objects. The restriction itself is exactly
  `ObjectProperty.lift LocY (LocX.ι ⋙ Rp_*) h`; it retains the actual ambient object
  and morphism maps. Exactness is its `Functor.IsTriangulated` with the canonical
  induced shift structure. Sum preservation is
  `∀ I, PreservesColimitsOfShape (Discrete I)` for this same restricted functor.
  Thus this is an actual restriction, not an arbitrary functor between the two
  subcategories. The universal instance binders let Lean build their standard
  induced pretriangulated structures after asserting they exist.
- The conditional theorem has no standing field, finite-type, qcqs or dimension
  hypotheses. Its only substantive functor assumptions are exactly the two in
  `ProperLocalizingHypotheses`.
- The coefficient theorem introduces `(k : Type u) [Field k]`,
  `[Fact (ringChar k).Prime]`, and `[Fact (ringChar k ≠ ℓ)]`. The first says positive
  characteristic (a field's positive characteristic is prime). Each scheme has
  an `Over (Spec (.of k))` instance; its structure map is separated, locally of
  finite type and quasi-compact, i.e. separated finite type. Finally
  `[p.IsOver (Spec (.of k))]` makes p a k-morphism. No further scheme hypothesis
  is imposed. Its conclusion is both hypotheses for every coefficient in the
  same six-element list. Q_ell and Z_ell appear explicitly and are also the
  E = Q_ell specializations described in the source.

Dependency declarations read and used:

- `Sheaf.Paper.LocalizingClosure`: `CategoryTheory.IsLocalizingSubcategory`,
  `CategoryTheory.localizingClosure`,
  `AlgebraicGeometry.ProEtale.localizingClosureProEtale`.
- `Sheaf.Paper.CondensedConstantConstructibility` (publicly imported by the
  preceding module): `IsConstantModelConstructible`,
  `constantModelBoundedConstructible`, `ConstantModelConstructibleFiniteTor`.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic` (imported through
  `...Condensed.FiniteSubextension`): `Profinite.padicAlgClCondensedRing`,
  `padicAlgClRingObj`, `padicIntegersRingObj`; `...Condensed.ContinuousMap`:
  `Profinite.continuousMapRingObj`. The closed upstream audit of
  `sk-def-sfb-qlbar-condensed` supplies its exact existing interface, without
  requiring a new lean record or duplicate construction.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`:
  `derivedUpperStarLowerStarAdjunction` and its total-derived interpretation;
  the actual pushforward is `Functor.rightDerivedFunctor` on the imported
  `CondensedRing.lowerStar` from `...UpperLowerStar.Defs`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, `.Triangulated`,
  `.Functor`, `.Subcategory`: `Pretriangulated`, `IsTriangulated`,
  `Functor.IsTriangulated`, `ObjectProperty.isTriangulated_lift`, respectively.
  These are transitively imported by the triangulated interfaces.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  the standing scheme conventions in its module documentation and
  `CondensedRing.compactificationOverField`. No new predicate for the standing
  setting is introduced. This dependency module is imported as a proof import;
  no chosen compactification is needed in the signature.
- Proof dependency `lem-pc-right-derived-functor-triangulated` uses the public
  import `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`,
  including its existing `CommShift` and `IsTriangulated` instances, needed to
  elaborate the canonical restricted functor's exactness.
- Recorded proof dependency `lem-fin-finite-type-fibre-dimension-bound` is imported
  as `Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`. Other mathematical
  proof inputs have no recorded Lean modules on the supplied base, so no modules
  were invented for them. The docstrings retain their complete natural-language
  proof routes for stage 3.

Edge cases checked: the empty index set is allowed, so preservation of zero is
included; singleton and arbitrary infinite families are included; empty schemes
and identity proper morphisms are not excluded. No ambient quasi-compactness is
required for the conditional assertion. Finite nonregular rings such as
Z/ell^2 are allowed; Dctf is never replaced by Dbc in the finite coefficient clause.
The zero finite ring is allowed (even n = 0 in the annihilation condition).
Qbar always uses finite-subextension-valued sections. The generic closure's
object universe is `u + 2` as confirmed by a temporary `#check` under scompile;
its own definition quantifies over `Type (u + 2)` indices, so both sum predicates
use exactly that universe. No universe equality is imposed on the pro-etale site.

Searches made (all msearch calls logged in `searches.jsonl`):

- LeanFinder: “Proper derived pushforward restricts to an exact coproduct preserving
  functor on the localizing closure of constructible finite Tor amplitude complexes”.
  Eight generic localization/derived-functor hits; no matching proper-image theorem.
- Loogle: `CategoryTheory.ObjectProperty.lift, CategoryTheory.Functor.IsTriangulated,
  CategoryTheory.Limits.PreservesColimitsOfShape`. Zero hits. Direct source inspection
  located the existing standard building blocks used above.
- Mathlib grep via msearch: `localizing|constructible` in
  `CategoryTheory/Triangulated`. Five hits, all Verdier left/right localizing
  notions, not the node's generated coproduct-closed category or proper-image claim.
- LeanSearch: “A proper direct image functor on the unbounded derived category of
  constructible sheaves restricts to a triangulated coproduct preserving functor
  on the localizing closure”. Eight generic exact/localization/finite-coproduct
  hits; no exact match.
- Direct rg in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and
  `lean/Sheaf`: `localizingClosure|localizing.*[Pp]roper|[Pp]roper.*[Ll]ocalizing`.
  Only the existing LocalizingClosure definitions and unrelated occurrences;
  no existing proper-image theorem. Searching the item ID in the source tree
  returned none. Searching all four proposed full-name stems in the source,
  `lean/Sheaf` and `dag/lean_names_upstream.json` returned none.

Validation: the final module passed `scompile.py Q91
 det-proper-image-localizing-proper <module file>` on 2026-10-18. Both the sandbox
compile (4.7 s) and library-path compile (7.1 s) returned clean with no errors or
warnings. Temporary diagnostic `#check` lines and pp options were removed.
No node fault or statement dispute was found. Only the item's `lean` field changes.

## Second reading by Q91

This is the author's explicit second pass, under the dispatcher instruction not
to start other agents; the independent review belongs to the maintainer. I reopened
the node and final file and checked the unrestricted conditional separately from
the standing-setting coefficient assertion. The former retains both hypotheses,
full image membership, actual ObjectProperty.lift, canonical triangulated exactness,
and all prescribed sums; the latter supplies both hypotheses for all six listed
coefficients with exactly the standing separated finite-type field assumptions.
I checked the bundled coefficient list, the finite-subextension definition of Qbar,
the finite-Tor conjunct, properness, positive characteristic and k-linearity.
I checked each direct statement dependency against its recorded declaration,
including the closed upstream qlbar audit. No mismatch required a node correction.
The two helpers are transparent expansions of this node's clauses and have real
Prop bodies. The two theorem docstrings contain the corresponding complete proof
plans, and every declaration carries this node's blueprint tag. No definition
uses sorry. No independent second reader is claimed in this report.
