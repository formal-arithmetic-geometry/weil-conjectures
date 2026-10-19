## Worker report

The module `Sheaf.Paper.ExceptionalInverseImageExistence` states
`AlgebraicGeometry.ProEtale.CondensedRing.exceptionalInverseImage_exists`, with the single
expected `sorry`. It states all four assertions of sk-thm-existence together, for the same
coefficient and the same chosen compactification, including the non-finite coefficient
identifications at the end. No definition or theorem is proved. No statement correction,
new node, dependency repair, or disputed statement is proposed.

The statement's local notation `S(T)` expands to
`constantModelBoundedConstructible Λ T ⊓ fun K ↦ DerivedCategory.finiteTorAmplitude _ K`,
exactly the property defining `ConstantModelConstructibleFiniteTor Λ T`. Its notation
`L(T)` is the recorded `localizingClosureProEtale Λ T`. They are local notation only,
not additional definitions. The localizing closure already uses finite constant scalar
models from the recorded constructibility dependency, without a completeness condition.

Hypotheses, individually:

- A coefficient prime: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- The standing field: `(k : Type u) [Field k]`.
- Positive characteristic, different from ℓ: `[Fact (ringChar k).Prime]` and
  `[Fact (ringChar k ≠ ℓ)]`. For a field these say precisely that its characteristic
  is a positive prime distinct from ℓ.
- The two standing k-schemes: `{X Y : Over (Spec (.of k))}`. Their actual schemes
  in every category are `X.left` and `Y.left`.
- Finite type over k: `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]`, and the
  corresponding two binders for Y.
- Separatedness over k: `[IsSeparated X.hom] [IsSeparated Y.hom]`.
- A k-morphism: `(f : X ⟶ Y)` in `Over (Spec (.of k))`, whose underlying map is
  `f.left`. No further hypothesis on f is added.
- A commutative condensed ring: the section variable
  `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`, with `[MonObj Λ]`
  and `[IsCommMonObj Λ]`.
- Exactly the admissible coefficient list: `_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ`.
  This is the recorded predicate from LocalizingAdmissibleCoefficients, including any
  finite discrete commutative ring killed by a power of ℓ, with no regularity or
  Gorenstein requirement. Its algebraic-closure case uses all continuous functions
  for the indicated topology, not finite-subextension-valued functions.

Conclusions, clause by clause:

1. `hSX : S(X.left) ≤ L(X.left)` provides the canonical full inclusion via
   `ObjectProperty.ιOfLE hSX`. The first conjunct asserts `IsCompactObject.{u + 1}`
   for the image of every `ConstantModelConstructibleFiniteTor Λ X.left` object.
   The next conjunct states `LocallySmall.{u + 1}` for Dctf and supplies
   `I : Type (u + 1)` and representatives `E` in Dctf. Local smallness ensures
   that the full skeletal category on these representatives also has small Hom sets;
   it is not merely a small set of objects with possibly larger morphism sets.
   `∀ K, ∃ i, Nonempty (E i ≅ K)` covers every isomorphism class;
   `∀ i j, Nonempty (E i ≅ E j) → i = j` makes the family skeletal.
   `IsTriangulatedGeneratingFamily` says that its images generate the closure.
   Since the preceding conjunct makes every Dctf object compact, this is a small
   skeleton of compact generators. The existential triangulation and coproduct
   witnesses precede these assertions, so the claims do not assume those structures
   or quantify over a possibly nonexistent coproduct structure.
2. `compactificationOverField f` is the recorded chosen compactification of the
   actual k-morphism. The existential membership proof `h` says its actual ambient
   `rightDerivedLowerShriekOfCompactification` preserves the closures.
   `localizingLowerShriek Λ (compactificationOverField f) h` is the existing literal
   restriction of that composite, on both objects and maps. Its `IsTriangulated`
   conjunct gives exactness with its inherited ambient shift comparison.
   `∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) ...` gives direct sums.
   The following implication `S(X.left) K.obj → S(Y.left) (F.obj K).obj` says it sends
   Dctf into Dctf. The comparison for every `c : Compactification f.left` identifies
   this chosen functor, after inclusion, with the corresponding ambient `Rp_* D(j_!)`
   restricted to the source closure. Thus the functor is tied to the actual
   compactifications rather than replaced by an unconstrained functor.
3. The existential `G : L(Y.left).FullSubcategory ⥤ L(X.left).FullSubcategory`,
   shift structure `s : G.CommShift ℤ`, `G.IsTriangulated`, and
   `Nonempty (F ⊣ G)` give an exact right adjoint to that same F. `Adjunction`
   includes the Hom equivalences, naturality, unit, counit, and triangle identities.
   Brown representability is the proof route, spelled out in the declaration's
   five-step proof docstring, rather than an additional assumption.
4. Inside the same existential for G, the implication
   `S(Y.left) N.obj → S(X.left) (G.obj N).obj` asserts preservation by this very
   right adjoint. Together with F-preservation and the witnesses `hSX`, `hSY`, this
   also expresses restriction of its adjunction: both subcategories are full,
   so the already asserted Hom equivalences on these objects are precisely the
   restricted Hom equivalences. No second or unrelated right adjoint is used.
5. The final implication explicitly lists ring-object isomorphism to each of
   `continuousMapRingObj ℤ_[ℓ]`, `continuousMapRingObj ℚ_[ℓ]`,
   `padicIntegersRingObj ℓ E`, `continuousMapRingObj E`, and
   `continuousMapRingObj (PadicAlgCl ℓ)`. In those cases it asserts equality
   `S(X.left) = constantModelBoundedConstructible Λ X.left` and the corresponding
   equality for Y. These are equalities of object properties in the same ambient
   categories, so the Dbc version follows by substitution, including equality of
   the associated localizing closures. The finite-ring case has no such equality.
   Z_l and Q_l are included explicitly; O_E and E quantify over finite intermediate
   fields in the fixed algebraic closure, exactly as the admissibility predicate.

Dependency declarations read and used:

- sk-def-sfb-dc-setting:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`.
  The current server source was fetched with `scompile.py --source`: its full
  signature uses `Over (Spec (.of k))` and accepts f without an explicit k argument.
  The older local framework source has a stale scheme-over presentation; the
  delivered statement follows the recorded and server-published Over interface.
- sk-def-sfb-constructible: `Sheaf.Paper.CondensedConstantConstructibility`,
  `AlgebraicGeometry.ProEtale.constantModelBoundedConstructible` and
  `AlgebraicGeometry.ProEtale.ConstantModelConstructibleFiniteTor`, with their
  underlying finite constant local models and constructibility definitions.
- sk-def-localizing-closure: `Sheaf.Paper.LocalizingAdmissibleCoefficients`,
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`, publicly importing
  `Sheaf.Paper.LocalizingClosure` and `localizingClosureProEtale` unchanged.
- sk-def-sfb-dc-lower-shriek: the recorded BoundedConstructible module and its
  `boundedConstructibleLowerShriekOfCompactification`,
  `boundedConstructibleLowerShriek`, and inclusion compatibility isomorphisms.
  This theorem uses their ambient compactification composite and the same chosen
  compactification; the Dctf restriction is the existing `localizingLowerShriek`.
  It does not impose the narrower `IsFinitenessCoefficient` hypothesis required
  by the upstream Dbc pushforward interface.
- def-sf-localizing-lower-shriek: existing declarations
  `AlgebraicGeometry.ProEtale.CondensedRing.localizingLowerShriek` and
  `localizingLowerShriekCommShift` in `Sheaf.Paper.LocalizingExceptionalAdjoint`.
  They are exactly the canonical full-subcategory lift and inherited CommShift required
  by clause 2, so the returned duplicate side module was removed and this dependency
  now reuses the live declarations.
- sk-prop-sf-existence: existing declaration
  `AlgebraicGeometry.ProEtale.CondensedRing.exists_localizingExceptionalAdjoint` in
  `Sheaf.Paper.LocalizingExceptionalAdjoint`; the item uses it only as a proof route.
  Reusing the live module avoids loading two copies of the helper declarations.
- def-pc-compact-object: `Sheaf.CategoryTheory.CompactObject`,
  `CategoryTheory.IsCompactObject`; def-pc-generators:
  `Sheaf.CategoryTheory.WeakTriangulatedGenerator`,
  `CategoryTheory.IsTriangulatedGeneratingFamily`. These already-landed definition
  nodes are added to stmt_deps because those predicates occur in clause 1.
- Mathlib's `ObjectProperty.ιOfLE` provides the full inclusion; its definitions
  of `Adjunction`, `CommShift`, `Functor.IsTriangulated`, `HasCoproducts`, and
  `PreservesColimitsOfShape` are used directly.
- The already stated proof dependencies are imported privately: BrownHypotheses,
  CompactificationLocalizing, FiniteLocalizingExceptionalPreservation,
  RationalExceptionalRestriction, and the recorded Nagata/Dense module.
  Proof dependencies without recorded modules are not invented or assumed as
  hypotheses. No import cycle was introduced.

Edge cases checked before writing and during the final statement reading:

- Finite nonregular A, e.g. Z/ℓ², is covered without identifying Dctf with Dbc.
  Finite Tor amplitude is imposed on the whole complex, not separately on its
  cohomology. No regularity, Gorenstein, or bounded-projective-dimension hypothesis
  has been added to the ring.
- The zero ring is allowed by the finite coefficient disjunct (finite A killed
  by ℓ⁰), and the resulting zero categories satisfy the asserted conclusions.
- Empty schemes give zero categories and zero adjoints. A skeletal generator
  family can contain its zero object; no hypothesis excludes these schemes.
- Empty coproducts are included since I has no Nonempty binder. They give zero
  objects and are preserved by the asserted functor.
- Identities and arbitrary standing k-morphisms are covered. No properness or
  smoothness is assumed for f, and no explicit redundant finite-type or separated
  hypotheses on f are required.
- Positive characteristic is expressed explicitly, including all primes distinct
  from ℓ. The stated coefficient and site universes are retained: schemes/profinite
  tests are in u, sheaf values and the small skeleton/coproduct index are in u+1,
  and the ordinary derived categories retain their existing larger universe.
- The O_E, E and algebraic-closure equality is asserted for both schemes, so both
  endpoints and the functors specialize to the Dbc formulation. Neither completeness
  nor a finite-subextension-valued replacement of the algebraic closure is introduced.

Searches for existing statements:

- LeanFinder, query `Exceptional inverse image exact right adjoint compact support
  localizing constructible finite Tor amplitude`: eight hits, including abstract
  Serre-quotient adjunctions, homological localization, and bounded derived objects;
  none is this theorem.
- Loogle, query `CategoryTheory.Adjunction, CategoryTheory.Functor.IsTriangulated`:
  seven hits in Mathlib.CategoryTheory.Triangulated.Adjunction. They describe
  exactness of an existing adjoint, not this geometric existence and preservation
  theorem.
- Mathlib grep via msearch, `Brown|[Ee]xceptional|Dctf` in CategoryTheory:
  three irrelevant author-name hits (Browning); no theorem match.
- LeanSearch, query `Exceptional inverse image exists as exact right adjoint to
  compactly supported pushforward on localizing constructible derived categories`:
  eight hits, generic derived/site adjunctions only.
- Direct rg in the upstream WeilConjectures tree for `sk-thm-existence`, localizing,
  Brown, and compact generation; no exact statement. The older exceptional-adjoint
  file concerns an optional unrestricted ambient hypothesis, not this localizing
  existence theorem.
- Direct rg in lean/Sheaf for localizing closures, compact objects, generation and
  exceptional adjoints found the canonical restriction helper and Brown hypotheses
  used here. `exists_localizingExceptionalAdjoint` alone lacks the present compact
  skeleton, Dctf-preservation, and non-finite-coefficient equality conclusions, so
  it is not an existing match for this node.

Validation: scompile.py successfully compiled the delivered module, both as the
sandbox check and at its actual library module path, with no errors or warnings.
The first check diagnosed only the stale compactification API; after reading the
current server source, the Over presentation compiled cleanly. The node's `lean.statement`
is extracted verbatim from the final file, from `theorem` through its signature.


## New nodes

No new definition node is added in this repair. The recorded definition dependency `def-sf-localizing-lower-shriek` is
already present in the live `Sheaf.Paper.LocalizingExceptionalAdjoint` module, and its
node copy now records that existing declaration directly.

## Dependency modules

No dependency module is added for `sk-prop-sf-existence`. The prior side files
`Sheaf.Paper.LocalizingLowerShriek` and `Sheaf.Paper.LocalizingExceptionalAdjoint`
were the source of the returned duplicate declaration: the current library already
contains `localizingLowerShriek`, `localizingLowerShriekCommShift`, and
`exists_localizingExceptionalAdjoint` in `Sheaf.Paper.LocalizingExceptionalAdjoint`.
The item imports and reuses that existing module, with no duplicate declarations.

## Second reading by NB

I reread the item and both repaired dependency records. The sole delivered Lean
module is `Sheaf.Paper.ExceptionalInverseImageExistence`. Every hypothesis and conclusion of `exceptionalInverseImage_exists` is
unchanged. Clause 2 resolves `localizingLowerShriek` and its CommShift instance from the
existing `Sheaf.Paper.LocalizingExceptionalAdjoint` module; clause 3's Brown route
resolves `exists_localizingExceptionalAdjoint` from that same module. No duplicate side
module remains, and the item compiles without errors or warnings.
