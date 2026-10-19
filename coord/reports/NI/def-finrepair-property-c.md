## Worker report

Defines `AlgebraicGeometry.Etale.IsConstructibleHigherDirectImage` in
`Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImage`, without any theorem, proof,
new axiom, or sorry. The node and blueprint defining paragraph (order 1592) were read
verbatim, together with all four statement dependencies and their declaration sources.

Clause-by-clause correspondence:

- The fixed finite commutative coefficient ring is `Λ : Type (u + 1)` with
  `[CommRing Λ] [Finite Λ]`. The integer and allowable-coefficient hypotheses from
  `sbc-def-coefficient-conventions` are `N : ℕ`,
  `_hX : IsSmoothBaseChangeCoefficients N Λ X`, and
  `_hS : IsSmoothBaseChangeCoefficients N Λ S`. Expanding that recorded predicate
  gives positivity, finiteness, `(N : Λ) = 0` (annihilation), and invertibility on
  each coefficient-carrying scheme. Repeating the finiteness as a typeclass supplies
  the constructibility predicate's instance; it adds no mathematical restriction.
- The schemes are `X S : Scheme.{u}`. Their finite-type hypothesis is relative to
  an explicitly bound arbitrary base `B : Scheme.{u}`: `[X.Over B] [S.Over B]`,
  `[LocallyOfFiniteType (X ↘ B)] [QuasiCompact (X ↘ B)]`, and the same pair for `S`.
  This spells out the finite-type terminology of the recorded scheme conventions.
  The source does not name the base of “finite-type schemes”; `B` simply binds it,
  with no field, Noetherian, separation, or finite-dimension assumption. The
  predicate's formula is independent of the base and of these witnesses.
- The morphism is exactly `f : X ⟶ S`. No properness, separation, or compatibility
  with the chosen base is imposed on `f`.
- “Every q ≥ 0” is `∀ q : ℕ`, passed as `(q : ℤ)` to the existing higher-image API.
  This includes degree zero and every positive degree, with no upper bound.
- “Every constructible Λ-sheaf F” is universal quantification over
  `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, followed by the hypothesis
  `Scheme.IsConstructibleEtaleModuleSheaf F`.
- The conclusion is precisely
  `Scheme.IsConstructibleEtaleModuleSheaf (higherDirectImage Λ f (q : ℤ) F)`.
  No vanishing, boundedness, uniformity, or bounded-constructible-complex condition
  is conjoined. In particular this does not replace the clause by preservation of
  the bounded constructible derived category.

Dependency declarations read and reused:

- `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients`:
  `AlgebraicGeometry.Etale.IsSmoothBaseChangeCoefficients`, full definition read.
- `def-weil-pbc-scheme-conventions` has an intentional convention-only Lean record,
  with no declaration/module. Its specified `Scheme`, `LocallyOfFiniteType`, and
  `QuasiCompact` are used directly; the first two definitions were inspected in
  Mathlib's scheme and finite-type interfaces, and the finite-type composite is
  exactly the pair specified by this convention record.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`; its full generic-category signature and
  objectwise direct-image docstring were read. The recorded
  `rightDerivedLowerStarPlus` actually resides in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`; its signature
  and implementation are the bounded-below right derived functor of this lowerStar.
  `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs` publicly imports the
  direct-image framework and supplies `AlgebraicGeometry.Etale.higherDirectImage`.
  Its full signature/docstring/body were read: it is degree-q homology of the same
  module-valued bounded-below derived lowerStar applied to F in degree zero.
  Thus no dependency replacement module or second higher-image definition is needed.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible` and
  `BoundedConstructibleDerivedCategory`, both read. For this node only their
  publicly imported sheaf notion is needed:
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`,
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`. Its full definition
  was read: finite locally closed constructible stratification, etale trivializations,
  and finite constant module values. The upstream `IsConstructibleSheaf` uses a
  different recorded formulation and was not substituted.

Edge cases checked before writing: q=0 is included by the natural-number binder;
there is no dimension or degree bound. Empty X and empty S are not excluded;
constructibility retains the dependency's empty-stratification possibility.
The zero coefficient ring is allowed, and N=1 is allowed when the recorded
coefficient convention holds. N=0 is excluded precisely by that convention's
positivity. Nonseparated finite-type schemes are admitted: neither structure
morphism nor f has a separation hypothesis. The universe is the established
scheme/module-sheaf convention, `Scheme.{u}` and `ModuleCat.{u+1} Λ`, with no
independent small universe restricting the test sheaves.

Searches for an existing notion (all run via msearch.py with group NI and this item,
plus read-only source rg):

- LeanSearch: `Higher direct images preserve constructible etale sheaves`.
  UNAVAILABLE: service unavailable, Internal Server Error; no mathematical verdict.
- LeanFinder: `Every higher direct image of a constructible etale module sheaf is
  constructible`. Eight hits on LightCondMod/LightCondensed, finite-type and
  quasicoherent sheaves of modules, and locally constant condensed modules; no match.
- Loogle: `"Constructible"`. Twelve hits, all topological constructible/locally
  constructible subsets and their elementary closure properties; no match.
- Mathlib grep through msearch: `Constructible|constructible` in AlgebraicGeometry.
  Five hits, all in Morphisms/FinitePresentation (Chevalley statements); no match.
- Project and upstream rg: `propertyC|PropertyC|PreservesConstructible|preservesConstructible|
  def-finrepair-property-c`, plus the exact proposed declaration name. No exact
  definition exists. The upstream EtaleTopologicalInvariance.PropertyC candidate
  was opened: it asserts existence of an affine etale neighborhood through a point,
  not constructibility of higher direct images. Searches for the blueprint id
  found no existing upstream/project declaration.
- Broader source rg: `def .*([Cc]onstructib|[Ff]initeness)|abbrev
  .*([Cc]onstructib|[Ff]initeness)` in SixFunctors, ConstructibleSheaf and project
  AlgebraicGeometry. The results define constructibility of objects, bounded
  constructible categories and their restricted functors, not this unbounded-degree
  predicate using the project's constructible-module-sheaf definition.

No new nodes, dependency modules, statement correction, or STATEMENT-DISPUTED claim.
The only source wording requiring an explicit Lean parameter is the implicit base
of finite type, bound as the arbitrary scheme B as described above.

Validation: the delivered file compiled cleanly with scompile.py on the server,
nice 19, two threads, 60 seconds per file (2.5 seconds for the item). No local
compiler or lake command was used. The coefficient module was also compiled by
scompile.py's private overlay, without modifying the live library.

## Second reading by NI

I independently read the sandbox node and module, the entire cited blueprint paragraph
(order 1592), its enclosing unit and chapter, all four statement-dependency nodes and
their defining source paragraphs, and the Lean declarations described below. This item's
source is a blueprint definition, not a Stacks tag; it supplies no additional standing
hypothesis beyond the coefficient convention and the finite-type wording.

The node's objects, hypotheses and conclusion, matched individually:

1. A fixed finite commutative coefficient ring Lambda: `(Λ : Type (u + 1))
   [CommRing Λ] [Finite Λ]`. Verdict: exact. The repeated `Finite Λ` in the
   coefficient predicate supplies the same property, not an extra restriction.
2. The coefficient convention fixes a positive N killing Lambda and requires its
   invertibility on coefficient-carrying schemes: `(N : ℕ)`, `_hX` and `_hS`, both
   of type `IsSmoothBaseChangeCoefficients N Λ ...`. I opened its definition in
   `SmoothBaseChangeCoefficients.lean`: `0 < N ∧ Finite Λ ∧ (N : Λ) = 0 ∧
   IsUnit (N : Γ(T, ⊤))`. The same N is used on X and S. Verdict: exact, including
   positivity and invertibility; no characteristic assumption beyond these.
3. Finite-type schemes X and S: `{X S : Scheme.{u}}`, an arbitrary explicit
   `(B : Scheme.{u})`, `[X.Over B] [S.Over B]`, and the locally-finite-type and
   quasi-compact instances on their structure morphisms. I read the convention
   node's corrected finite-type clause, and Mathlib's `Scheme`, `LocallyOfFiniteType`
   and `QuasiCompact` definitions. Verdict: the pair is precisely the recorded
   finite-type convention. B binds the implicit base without imposing field,
   Noetherian, dimension, quasi-separatedness or separation requirements. The
   defining formula is independent of B and its structure maps.
4. A morphism f from X to S: `(f : X ⟶ S)`. Verdict: exact; there is no condition on
   f beyond being this morphism. In particular no base-compatibility equation is
   introduced, since neither the node nor its source specifies one.
5. Every q at least zero: `∀ (q : ℕ)`, mapped to `(q : ℤ)` in the higher-image API.
   Verdict: exactly all nonnegative integral degrees, in the specified order.
6. Every constructible Lambda-sheaf F on the small etale site of X:
   `(F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))` followed by
   `Scheme.IsConstructibleEtaleModuleSheaf F → ...`. Verdict: exact. I opened
   `BoundedConstructibleComplexes.lean` and its public dependency
   `IsConstructibleEtaleModuleSheaf.lean`. The latter uses a finite partition by
   locally closed constructible strata, with etale trivializations and finite
   constant module values, as required; no bounded complex is substituted for F.
7. The conclusion that R^q f_* F is constructible:
   `Scheme.IsConstructibleEtaleModuleSheaf (higherDirectImage Λ f (q : ℤ) F)`.
   Verdict: exact. I read `lowerStar` in `UpperLowerStar.Defs`, its objectwise
   base-change formula, `rightDerivedLowerStarPlus` in `Derived.UpperLowerStarCoherence`,
   and `higherDirectImage` in `SmoothBaseChange.Defs`. The latter is exactly homology
   in degree q of that bounded-below derived pushforward applied to F in degree zero.
   Its coefficient category is the same ModuleCat; no properness, etaleness or
   extra finiteness instance is required on f.
8. No uniform vanishing assertion: the definition ends with the constructibility
   conclusion alone. Verdict: exact; no upper bound, zero condition, or boundedness
   quantifier appears.

Edge cases: q = 0 is included, as are arbitrarily large q. Empty X or S are not
excluded by any nonemptiness binder; the constructibility dependency permits zero
strata on the empty scheme (I also opened `LocallyClosedStratification.lean`). Zero
sheaves and the zero coefficient ring are allowed. N = 0 is excluded by precisely
`0 < N` from the source convention; N = 1 remains allowed for a ring killed by 1.
No auxiliary index family is introduced. Universes u and u+1 are explicit and
polymorphic and agree with the established scheme/module-sheaf interfaces; no test
sheaves are quantified in a smaller independent universe. No variable is unbound.

Independent searches, with queries different from the first worker's:

- LeanFinder via msearch: `A morphism whose derived pushforward preserves constructible
  sheaves in every cohomological degree`. Eight hits on ordinary sheaf pushforward
  and its functoriality (including `sheafPushforwardContinuous` and
  `SheafOfModules.pushforward`), none defining this predicate.
- Loogle via msearch: `"higherDirectImage"`. Zero hits.
- LeanSearch via msearch: `All right derived pushforwards of constructible finite
  coefficient etale module sheaves are constructible`. Service unavailable with
  Internal Server Error; no mathematical verdict inferred from this failure.
- Independent rg in project Sheaf, upstream WeilConjectures and Mathlib
  AlgebraicGeometry for `preserv.*constructib|constructib.*preserv|propertyC` and
  the proposed full declaration name. No exact duplicate. I opened the apparent
  upstream `PropertyC`: it is an affine etale neighborhood lifting condition at a
  point, unrelated to higher direct images. I also opened the upstream
  `boundedConstructible_rightDerivedLowerStar_of_finite` and
  `DerivedCategoryBoundedConstructible.rightDerivedLowerStar`: these are respectively
  a preservation theorem over a field and a restricted functor on bounded derived
  categories, not the predicate C(f) without a vanishing bound. Broader rg for
  definition/abbreviation names involving constructibility and finiteness, and
  the declaration/blueprint id in `dag/lean_names_upstream.json` and upstream,
  found no existing declaration for this notion.

No mismatch was found. The Lean module and node record were retained unchanged;
only this independent review was appended. No new nodes, dependency modules,
statement correction, theorem, axiom or sorry is present. H5/H6 are satisfied by a
literal Prop-valued definition. Both docstrings cite the source and blueprint id;
there are no proof steps to copy for this definition node (`proof: []`). Imports,
namespace, exposed module header and 100-character line widths conform. A direct
text comparison confirmed that `lean.statement` equals the file signature verbatim.

Server validation: scompile.py compiled the delivered module cleanly in 2.5 seconds,
with nice 19, two threads and a 60-second per-file limit; it also compiled the
coefficient dependency in its private overlay (1.4 seconds). No local compiler,
Lake build or write to upstream/live source was used.
