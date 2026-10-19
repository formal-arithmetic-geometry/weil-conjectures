## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.FiniteTorAmplitudePerfect` states
`DerivedCategory.finiteTorAmplitude_iff_perfect_iff_finiteFree`, with exactly one
`sorry` proof. No definitions are introduced and no statement correction is made.

The statement is the conjunction of the two equivalences in the DAG: finite Tor
amplitude iff perfect, and perfect iff a bounded finite-free representative.
In particular, it does not replace either equivalence by finite Tor amplitude
iff the conjunction of the other properties.

Hypotheses and clauses:

- `l : ℕ`, `[Fact l.Prime]`, `E : Type u`, `[Field E]`,
  `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]`, and `n : ℕ`
  with `hn : 1 ≤ n` give the finite coefficient extension and positive level.
  Every occurrence of the coefficient ring is the recorded construction
  `Padic.coefficientExtensionRing l E n`, whose actual definition is the
  quotient of the recorded integer ring by the nth power of the uniformizer
  ideal. The ambient finite-field scheme and geometric point do not enter this
  commutative-algebra statement: its objects are ordinary coefficient modules.
- `C : DerivedCategory (ModuleCat.{u} (Padic.coefficientExtensionRing l E n))`
  is the complex considered up to quasi-isomorphism. `hbounded` is
  `TStructure.t.bounded C`, boundedness in the derived category. This is the
  representative-independent rendering of the bounded complex in the node;
  good truncations give a bounded representative of every such derived object.
- `hfinite` says `Module.Finite A (H^i C)` for every integer degree, with
  `homologyFunctor` supplying precisely the derived cohomology modules.
  By `Padic.finite_coefficientExtensionRing l E n hn`, A is finite. Thus
  `Module.Finite A M` is equivalent to finiteness of the underlying set by
  Mathlib's `Module.finite_of_finite` and `Module.Finite.of_finite`.
  No termwise finiteness, flatness or projectivity is assumed for C.
- `[HasDerivedCategory.{w} (ModuleCat.{u} A)]` is the chosen localization
  interface of `def-weil-abstract-derived-category`, not an extra mathematical
  hypothesis. It is explicitly bound, and w is arbitrary. The coefficient,
  object and localization universes are not identified.
- The first equivalence starts with `∃ a b : ℤ, a ≤ b ∧ torAmplitudeIn
  (ModuleCat.{u} A) a b C`. The full upstream definition was read:
  `torAmplitudeIn ... a b C` quantifies over every ordinary module M and says
  the cohomology of `C ⊗ (singleFunctor ... 0).obj M` is concentrated in
  `[a,b]`. This is the ordinary-module condition spelled out in the node,
  with no constructibility, finiteness or flatness restriction on M.
- Its right side is the already landed `IsPerfectRingComplex C`. Its body is
  precisely existence of a bounded finite-projective complex P with
  `Nonempty (C ≅ Q.obj P)`. Thus it expresses membership in the *perfect*
  category of `def-trf-categorical-trace`, not the larger bounded
  finite-cohomology category. That node's trace/evaluation constructions and
  the coefficient-point functor are not needed to state this membership.
- The second equivalence starts with the very same `IsPerfectRingComplex C`.
  It concludes existence of a complex P and integer bounds a,b with
  `P.IsStrictlyGE a ∧ P.IsStrictlyLE b`, every term both `Module.Free A`
  and `Module.Finite A`, and `Nonempty (C ≅ Q.obj P)`. This is exactly a
  bounded complex of finitely generated free modules quasi-isomorphic to C.
  The isomorphism in the localization expresses quasi-isomorphism without
  requiring a single directed quasi-isomorphism between fixed representatives.

Dependency declarations inspected and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` (the abstract-derived-category node).
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, including its factorization through Q.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`:
  `DerivedCategory.TStructure.t.bounded` and its cohomology-bound interpretation.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite` (the node's recorded
  finitely-generated-module declaration); its cardinality equivalences are in
  `Mathlib.RingTheory.Finiteness.Cardinality`.
- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free`, the recorded
  free-module declaration, whose field supplies a basis with arbitrary index.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, importing the actual
  `Padic.coefficientExtensionRing` from `CoefficientExtension`.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`, the current recorded declaration of
  `def-pc-perfect-ring-complex`. It is the same finite-projective model notion
  as upstream `DerivedCategory.IsPerfect`, generalized to localization universe w.
- `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`:
  `DerivedCategory.torAmplitudeIn`. The upstream `finiteTorAmplitude` omits
  the syntactic ordered-bounds conjunct, so the statement writes ordered
  existential bounds explicitly around the shared interval predicate.
- The required stated proof-dependency modules are imported without `public`:
  `Mathlib.RingTheory.Noetherian.Defs` (`IsNoetherianRing`),
  `Mathlib.Algebra.Module.Projective` (`Module.Projective`),
  `Mathlib.RingTheory.Flat.Basic` (`Module.Flat.of_projective`),
  `Mathlib.RingTheory.LocalRing.Module` (`Module.free_of_flat_of_isLocalRing`),
  `Sheaf.RingTheory.RingPseudoCoherent` (`DerivedCategory.IsPseudoCoherent`),
  `Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion`
  (`DerivedCategory.isPseudoCoherent_iff_boundedAbove_finite_homology`),
  `Sheaf.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect`
  (`DerivedCategory.isPerfect_of_pseudoCoherent_finiteTorAmplitude`),
  `Sheaf.Algebra.Homology.BoundedFlatKFlat`
  (`CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat`),
  `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`
  (`CategoryTheory.MorphismProperty.kFlat`), and
  `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`
  (`DerivedCategory.QObjTensorQObjIsoOfKFlatLeft`).

The main node's statement dependencies gain only two already landed definition
nodes, `def-pc-perfect-ring-complex` and
`def-weil-l-adic-coefficient-extension`, to record the exact existing declarations
that supply these notions. The original statement dependencies are retained.
No dependency module or new notion is needed: the unstated large context nodes
supply no additional object used by this ordinary-module theorem. In particular,
we do not substitute the sheaf Tor condition or the categorical trace itself
for perfectness.

Sources read: the node and its recorded six-step proof; every statement
dependency's full node record; the recorded Mathlib and project declaration
signatures and docstrings; and the blueprint lemma and unit at
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-trace-perfectness/`
in the available read-only literature checkout. The module docstring records
all six steps of the repaired DAG proof, including the Noetherian
pseudo-coherence criterion, finite-projective to finite-free conversion, and
ordinary-module K-flat tensor calculation.

Edge cases checked mathematically before finalizing:

- The zero complex is included. It admits the zero free representative and
  ordered Tor interval `[0,0]`; no nonzero-object assumption is added.
- At n=1 the coefficient ring is a field, and bounded finite cohomology does
  give perfectness and finite Tor amplitude. At n>1 finite cohomology alone
  is insufficient, and the statement does not assert it suffices.
- Arbitrary modules M, including infinite and nonflat modules, are quantified
  over in `torAmplitudeIn`; zero testing modules cause no exception.
- Empty/free rank-zero terms and the zero terms outside a support interval
  are allowed by `Module.Free` and `Module.Finite`.
- No support ordering is imposed on the representative bounds; a zero complex
  can have empty strict support. The Tor existential explicitly requires a≤b.
- Universes u and w are explicitly bound; module types live in the coefficient
  universe u, and the localization universe is left independent. The statement
  covers each size convention by taking u sufficiently large.

Searches for an existing exact theorem or definition (msearch.py under NZ/item):

- LeanFinder: `finite Tor amplitude perfect bounded complex finitely generated
  free modules` returned eight hits: `DerivedCategory.isLE_iff`,
  `DerivedCategory.isGE_iff`, `CategoryTheory.HasProjectiveDimensionLT.mk`,
  `.mk'`, `CategoryTheory.hasProjectiveDimensionLT_iff`,
  `DerivedCategory.isGE_Q_obj_iff`, and the two projective Tor-vanishing lemmas.
  None states both equivalences over the coefficient ring.
- Loogle: `DerivedCategory.torAmplitudeIn, perfect, finite free` returned zero
  hits (the service does not index that upstream identifier).
- LeanSearch: `A bounded complex over a finite local ring has finite Tor
  amplitude if and only if it has a bounded finite free representative`
  was unavailable with `Internal Server Error`; no match is claimed from it.
- msearch grep: `finite.?tor|tor.?amplitude|categoricalTrace|finiteCoefficient`
  over the upstream source returned 25 hits concerning Fourier kernels and
  sheaf Tor conditions; none is this theorem.
- Direct rg over Mathlib's homology files for finite Tor, Tor amplitude and
  `IsPerfect` returned no hits. The broader initial Mathlib/project search
  located the upstream `IsPerfect` and the separate
  `isPerfect_of_finiteTorAmplitude`, which supply only the forward implication,
  and the already landed generalized perfect-ring predicate, which is reused.
- Direct rg over the upstream project and `lean/Sheaf` for the item id and
  `finiteTorAmplitude_iff_perfect_iff_finiteFree` returned no existing theorem.

Validation: compile every delivered module with the prescribed scompile.py
wrapper and run deliver2.py with `--no-push`. The second reader supplies its
independent reading and performs the delivery.


## Second reading by NZ

I read the node and the delivered Lean independently. I also opened the original
blueprint lemma and its enclosing unit `sk-prop-sf-trace-perfectness` in the
read-only literature checkout, and the Stacks TeX at Tags 0652
(`definition-tor-amplitude`), 066E (`lemma-Noetherian-pseudo-coherent`, part 2),
0658 (`lemma-perfect`, including the preceding perfect-complex definition), and
00NZ (`lemma-finite-flat-local`). These sources introduce an ordinary ring and
ordinary modules for this algebraic step. They impose no additional geometric,
Noetherian, flatness, or projectivity hypothesis on the terms of C. No statement
correction is needed; the DAG already repairs the original blueprint proof's
insufficient inference from 0-pseudo-coherence by using the Noetherian criterion.
The enclosing unit's statement is unchanged.

My object/hypothesis/conclusion checklist, matched against the actual signature:

1. The prime ell is `(l : ℕ) [Fact l.Prime]`. The coefficient extension is
   `(E : Type u) [Field E] [Algebra (Padic l) E]
   [FiniteDimensional (Padic l) E]`. The finite level is `(n : ℕ) (hn : 1 ≤ n)`.
   Every occurrence of A is `Padic.coefficientExtensionRing l E n`.
   Verdict: same finite p-adic coefficient ring as the node. I opened both
   `CoefficientExtensionFinite` and `CoefficientExtension`: the actual data are
   the spectral absolute value, its integer subring, and the quotient by
   `(Ideal.span {coefficientExtensionUniformizer l E}) ^ n`. The DVR theorem
   characterizes that integer subring by absolute value and the principal ideal
   as its unique maximal ideal, so the quotient does not depend on the selected
   generator. There is no arbitrary replacement ring or ring structure. Choosing
   an embedding of E in the fixed algebraic closure is immaterial to this
   ordinary-module assertion: neither the ring construction nor any conclusion
   uses such an embedding. Likewise the finite-field characteristic p, the
   inequality ell != p, and the scheme over the finite field introduce no object
   or operation in this lemma; they belong to its subsequent geometric uses.
2. C is a bounded complex of ordinary A-modules with finite cohomology. Lean
   uses `C : DerivedCategory (ModuleCat.{u} A)`,
   `hbounded : TStructure.t.bounded C`, and
   `hfinite : ∀ i : ℤ, Module.Finite A ((homologyFunctor (ModuleCat.{u} A) i).obj C)`.
   Verdict: exact up to the quasi-isomorphism identification already used in the
   node. The canonical t-structure's bounded predicate is boundedness on both
   sides; good truncations give a bounded complex representative. Its derived
   cohomology is the ordinary complex cohomology by `homologyFunctorFactors`,
   whose signature I opened. `Module.Finite` is finite generation, and over the
   finite ring A this is equivalent to a finite underlying set, as verified in
   Mathlib `Finiteness.Cardinality`. There is no termwise finiteness hypothesis.
3. The chosen derived category is
   `[HasDerivedCategory.{w} (ModuleCat.{u} A)]`. I opened Mathlib Basic: this
   abbreviates a localization of cochain complexes at quasi-isomorphisms, and Q
   is its localization functor. Verdict: the recorded abstract-derived-category
   dependency and a choice of localization universe, not a new algebraic
   condition. The signature introduces u and w explicitly and does not set them
   equal. All other structures needed by the Tor predicate are inferred for
   ordinary modules from the imported interfaces; none is an extra binder.
4. Finite Tor amplitude is
   `∃ a b : ℤ, a ≤ b ∧ torAmplitudeIn (ModuleCat.{u} A) a b C`.
   I opened the complete upstream definition and its homology-concentration
   dependency: it says `∀ F : ModuleCat.{u} A`, the canonical derived tensor of
   C with `(singleFunctor _ 0).obj F` has cohomology concentrated in [a,b].
   Verdict: exactly the node's ordinary-module condition, with the bounds chosen
   before all testing modules and degrees, and no finiteness or flatness
   restriction on F. The monoidal structure is the derived tensor supplied by
   `Qh.HasDerivedMonoidalCategory`, rather than an arbitrary monoidal structure.
   `ModuleCat.hasFunctorialFlatResolution` provides the required canonical
   construction; I opened its rank-one flat-separator implementation.
5. The first conclusion is the equivalence of the condition in item 4 with
   `IsPerfectRingComplex C`. I opened `PerfectRingComplexGeneral`: its body is
   existence of P, integer term bounds, finite-projective terms, and
   `Nonempty (C ≅ Q.obj P)`. I also opened upstream `DerivedCategory.IsPerfect`
   to compare: it has the same body but a specialized localization universe.
   Verdict: precisely the perfect-category membership explicitly specified in
   `def-trf-categorical-trace`. The trace node itself has no Lean record, but its
   statement defines this full subcategory via `def-pc-perfect-ring-complex`,
   which does have this usable recorded interface. No evaluation, coevaluation,
   trace map, or point-fibre functor is used here, so no missing contextual
   module is required to state this clause.
6. The second conclusion is
   `IsPerfectRingComplex C ↔ ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ)
   (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
   (∀ i : ℤ, Module.Free A (P.X i) ∧ Module.Finite A (P.X i)) ∧
   Nonempty (C ≅ Q.obj P)`.
   I opened `IsStrictlyGE`, `IsStrictlyLE`, and `IsStrictlySupported`: these
   require zero terms outside the bounds, not merely zero cohomology there.
   I opened the recorded `Module.Free` and `Module.Finite` class definitions:
   they assert a basis and finite generation. Verdict: exactly a bounded
   finite-free complex quasi-isomorphic to C. An isomorphism in the localization
   is the appropriate representative-independent condition. There is no demand
   for a specified single arrow between unchosen representatives.
7. Both equivalences occur as separate conjuncts of the conclusion. Verdict:
   every stated clause and implication is present, with the same C and the same
   perfectness predicate throughout. The signature does not merely assert that
   the Tor condition implies the conjunction of the other conditions.

I read every statement-dependency node and the signatures/bodies of the
interfaces actually used. The two added statement dependencies are already
landed definition nodes giving the coefficient construction and perfect-ring
predicate. The contextual `def-trf-coefficient-conventions`,
`def-weil-finite-coefficient-point`, and `def-trf-categorical-trace` introduce
larger geometric constructions; their unrecorded interfaces are not used as
private substitutes. The ordinary-module notions required here are precisely
the recorded declarations above. There are no new definition nodes and no
dependency modules in this delivery to audit under H12/H13.

I also checked the stated proof-dependency interfaces, including the
Noetherian pseudo-coherence criterion, the pseudo-coherent finite-Tor perfect
model theorem, and the K-flat tensor model. The module's six numbered proof
steps match the node's six steps: establish Noetherianness and finite
generation, deduce pseudo-coherence, obtain a finite-projective bounded model,
use locality to make it finite free, compute all ordinary-module derived
tensors on that K-flat model, and combine the implications. The imports for
these recorded dependencies are present. There is one named theorem with
whole proof `sorry`, no new definition, no local notation/instance or private
copy, and source/blueprint docstrings on module and theorem. I mechanically
checked the 100-column bound, the single sorry, and exact verbatim equality of
`lean.statement` with the file's theorem signature.

Edge cases checked:

- C = 0 and testing module M = 0 are included. The zero representative has
  finite free terms of rank zero and admits the ordered Tor interval [0,0].
- An empty basis and zero terms outside any support interval satisfy both
  module predicates. No nonzero rank or nonempty support assumption occurs.
- If the representative bounds are reversed, its terms are all zero; this
  still gives the zero-object case and can be widened to [0,0]. The conclusion
  need not require an ordered support interval to express boundedness.
- n = 1 is included, and n > 1 is included without silently assuming the
  coefficient ring is a field. n = 0 is excluded exactly as in the recorded
  coefficient convention n >= 1. Every prime l, including 2, is covered.
- No geometric scheme appears, so the empty scheme has no separate case in
  this algebraic lemma. There is no indexing-set hypothesis to exclude an
  empty family.
- u is the chosen universe for the coefficient field and its ordinary modules;
  the test-module universe is not an independent smaller universe. Arbitrarily
  large choices of u are available, and w is independent. In particular no
  equality of site universes or localization/coefficient universes is imposed.

Independent searches (different formulations from the first reading):

- msearch LeanFinder: `perfect complex over Artinian local ring equivalent
  bounded finite rank free resolution` returned projective/injective dimension
  predicates and an Artinian Krull-dimension lemma, not this equivalence.
- msearch Loogle: `Module.Free, Module.Finite` returned finite presentations,
  finite bases and rank lemmas. These confirm the available module notions,
  but none states this derived-category theorem.
- msearch LeanSearch: `A perfect complex over a local ring is quasi-isomorphic
  to a bounded complex of finitely generated free modules` was unavailable
  (`Internal Server Error`); no result is attributed to it.
- msearch grep: `tor.?amplitude|perfect|bounded.*free` in Mathlib
  `Algebra/Homology/DerivedCategory` returned no matches.
- Direct rg in the upstream source and project `lean/Sheaf` with
  `finiteTorAmplitude_iff_perfect`, `IsPerfectRingComplex.*↔`,
  `finite.free.*representative`, and both orders of `finite.?tor`/`perfect`
  located the upstream forward theorem `isPerfect_of_finiteTorAmplitude`,
  its dualizability results, the already recorded shared predicates, and
  geometric or pseudo-coherent results. I opened the forward theorem: it
  supplies only one implication and specializes the localization universe;
  it is not an existing exact statement of this node's two equivalences.
  The delivered declaration name is absent from `dag/lean_names_upstream.json`
  and from project/upstream Lean. No module should be dropped as existing.

Mismatches found: none in the Lean statement, node record, or docstrings.
Changes made by the second reader: appended this independent reading and
recorded the independent searches; left the correct Lean and node unchanged.
The prescribed scompile.py compile completed with exit 0, both sandbox and
library checks, with no warning or error. Delivery preflight and push follow.
