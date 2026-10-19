## Worker report

The module `Sheaf.RingTheory.CotangentResolutionCoherence` states
`Algebra.CotangentResolution.exists_coherence`, with its sole proof `sorry`.
Its result is `Nonempty Coherence`: the record spells out all constructions,
normalizations and compatibility equations of the node. This packages the
existence of the prescribed construction; it is not a hypothesis supplying an
arbitrary map, comparison, or complex. The accompanying definitions contain
real data, and none chooses data from this theorem.

The namespace is `Algebra.CotangentResolution`. All 25 top-level declarations
are recorded in `lean.declarations`. The primary signature is copied verbatim
from the source, with explicit universes and variables. No node statement,
statement dependency, proof, or proof dependency was changed.

Clause-by-clause correspondence:

1. A homomorphism of commutative rings is `f : Arrow CommRingCat.{u}`;
   `f.left`, `f.right`, and `f.hom` are A, B, and A → B. Quantification over
   all f includes all rings and all ring maps; no domain, nonzero, flatness,
   finite generation, or characteristic hypothesis is present. Taking a common
   universe for the rings is the usual small-universe formulation, not a bound
   on their cardinalities across instances of the universe-polymorphic theorem.
2. `standardTerm f 0` is literally `CommRingCat.of (MvPolynomial B A)`;
   the successor clause is literally `MvPolynomial (standardTerm f n) A`.
   These are `(F_A U)^(n+1) B`, not arbitrary polynomial algebras. `standardBase`
   is `MvPolynomial.C` and `standardAugmentation` is iterated evaluation.
3. `standardFace` evaluates the outer polynomial layer at face zero and
   otherwise applies the preceding face to the labels of its variables.
   Its degree-one last face applies B-evaluation to those labels.
   `standardDegeneracy` inserts `[x] ↦ [[x]]` at index zero and otherwise
   lifts the preceding degeneracy to variable labels. These are exactly the
   counit and unit formulas in Stacks 08PM, with face indices counted from the
   outer polynomial layer. `IsStandard` requires equality of the actual rings
   and heterogeneous equality of all these actual operators, coefficients,
   and augmentations. The heterogeneous equalities only account for the
   equalities of source and target rings.
4. `Augmentation f` includes the simplicial algebra, the base natural
   transformation and augmentation natural transformation. Its `triangle`
   requires their composite in every degree to be f. `AugmentedMap q P Q`
   includes a simplicial ring map commuting with both structure maps over
   the two sides of the square q. Naturality supplies compatibility with
   every simplicial operator.
5. `negativeComplex C` is Mathlib's `alternatingFaceMapComplex C` followed by
   extension along `ComplexShape.embeddingDownNat`, the embedding n ↦ -n.
   Consequently degree -n is M_n, the differential is the specified sum of
   signed faces, and every positive degree is zero. No normalized-complex
   substitute is used.
6. `differentialTerm P n` is the extension of scalars of
   `CommRingCat.KaehlerDifferential (P.base.app ...)` along the actual
   augmentation P_n → B. Thus it is B ⊗_{P_n} Ω¹_{P_n/A}, in the symmetric
   tensor-factor order of the node. `differentialGenerator P n b x` is the
   actual tensor b ⊗ dx, using Mathlib's universal derivation. These tensors
   generate this module as a B-module.
7. `DifferentialModel P` identifies every term of its simplicial B-module
   with this actual tensor module by `termIso`; its `operator` equation
   requires *every* simplicial operator to send b ⊗ dx to b ⊗ d(θx).
   This uniquely specifies the simplicial module up to its displayed
   coordinate isomorphisms. `differentialComplex` applies the alternating
   cochain construction; `derivedDifferentials` applies `DerivedCategory.Q`.
   `cotangentComplex C f` applies this construction specifically to
   `C.standard f`. It is the node's L_{B/A}.
8. `IsPolynomialResolution P` has exactly three conditions. First, in every
   degree there exists a set E and a ring isomorphism A[E] ≅ P_n carrying
   each coefficient a to its specified A-algebra image; this is precisely
   being a polynomial A-algebra. Second, the actual augmentation is
   surjective in every degree. Third, `QuasiIso (additiveAugmentation P)`
   is the required quasi-isomorphism of underlying additive complexes.
   `additiveAugmentation` uses Mathlib's alternating-complex augmentation
   to the degree-zero single complex, then extends both source and target
   along n ↦ -n. Its target is therefore the standard extension-by-zero
   model of B[0], not the alternating complex of constant B.
9. `Coherence.standard_spec` provides the prescribed standard construction;
   `standard_resolution` asserts that it is a polynomial resolution in
   exactly this sense. `differentials` supplies the fully normalized
   differential model for each augmentation. `comparison P hP` is an
   isomorphism from the represented differential complex of *each*
   polynomial resolution to L_{B/A}. It has no extra resolution hypothesis.
   `comparison_standard` fixes the standard comparison to the identity.
10. A commutative square is `q : f ⟶ g` in the arrow category. The recursive
    `standardSquareMap` maps coefficients using q.left and sends a variable
    labelled p to a variable labelled by the preceding map applied to p;
    degree zero uses q.right on labels in B. `standardMap_formula` requires
    these exact maps in every degree, and `standardMap` is an
    `AugmentedMap`, so they commute with the augmentation and all simplicial
    operators. `standardMap_id` and `standardMap_comp` are strict equalities
    of simplicial natural transformations, not merely derived equalities.
11. `DifferentialMap.generator` requires the induced cochain map in degree
    -n to send b ⊗ dx to q.right(b) ⊗ d(h_n x). Its target is the actual
    restriction of scalars along B → B', via `restrictComplex`. The
    positive terms are zero. `standardDifferentialMap_id` and
    `standardDifferentialMap_comp` assert identity and composition in all
    integer degrees; the displayed pointwise equalities identify the
    underlying linear maps through the canonical restriction identifications.
12. `compatibility` is the equation
    Res(c_Q) ∘ K(h) = K(standard(q)) ∘ c_P in D(B), with the localization
    comparison `mapDerivedCategoryFactors.inv` inserted on both targets.
    It holds for every square, every pair of polynomial resolutions, and
    every supplied semilinear augmented simplicial map between them.
    For an identity base square this is exactly naturality in morphisms
    of augmented polynomial resolutions (with the canonical identity
    restriction identification). For general squares it is precisely the
    final agreement clause of the node. `cotangentMap` defines the standard
    derived map. `transportedMap` defines the map for arbitrary choices of
    resolutions as c_P, then the standard map, then Res(c_Q inverse).
    Cancelling c_Q in `compatibility` identifies it with every supplied
    resolution map. Strict identity and composition of standard maps,
    together with cancellation of adjacent comparison isomorphisms,
    give identity, composition and transitivity for these transported maps.
    No semilinear algebra map between arbitrary resolutions is assumed
    to exist, and base change of a resolution is not asserted to be a
    resolution.

Dependency declarations read and used:

- `def-weil-abstract-derived-category`: recorded module
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`; `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q` (full signatures and source
  docstrings read). The chosen localization size is u+1 for
  `ModuleCat.{u} B`, whose object universe is u+1. The simultaneous
  `HasDerivedCategory` instance parameter supplies only this size choice;
  the family is available as `fun B ↦ HasDerivedCategory.standard _`.
- `def-weil-pbc-kahler-differentials`: recorded module
  `Mathlib.RingTheory.Kaehler.Basic`; `KaehlerDifferential`,
  `KaehlerDifferential.D`, `KaehlerDifferential.linearMapEquivDerivation`.
  The full docstrings/signatures were read, as were the bundled wrapper
  `CommRingCat.KaehlerDifferential`, its `D`/`d`, and its square map in
  `Mathlib.Algebra.Category.ModuleCat.Differentials.Basic`. The wrapper
  installs the ring-map algebra structure internally and uses precisely
  the recorded Kähler differential module and universal derivation.
- Additional Mathlib constructions used directly: `ModuleCat.extendScalars`,
  `ModuleCat.restrictScalars`, exactness of restriction in
  `Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact`, the exact-functor
  maps and localization comparisons in
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`,
  `AlgebraicTopology.alternatingFaceMapComplex`, its augmented epsilon,
  `HomologicalComplex.extendMap`, `extendXIso`, and
  `ComplexShape.embeddingDownNat`. Their relevant source signatures were read.
- Available proof-only dependencies are imported non-publicly:
  `Sheaf.CategoryTheory.AdjunctionStandardSimplicialHomotopy`
  (`CategoryTheory.Adjunction.exists_standardSimplicialHomotopy`, with
  its comonad interface and its docstring read), and
  `Sheaf.Paper.TrivialKanHomotopyEquivalence`
  (`SSet.exists_section_homotopy_equivalence`, signature and docstring read).
  The node proof is reproduced step by step in the theorem docstring.
- The three proof-only simplicial-abelian/derived-colimit nodes have no Lean
  record, so have no import yet. `def-weil-size-convention` is recorded as
  a metatheoretic convention with no module/declaration. Its containing
  universe is used in the proof docstring.
- Source availability fault, without a statement dependency defect:
  `def-weil-pbc-trivial-kan-fibration` records
  `Sheaf.AlgebraicTopology.TrivialKanFibration`, but the source is absent
  in the shared checkout and `scompile.py --source` reports
  `Module source unavailable: Sheaf.AlgebraicTopology.TrivialKanFibration`.
  A trial proof-only import failed both locally and on server confirmation,
  so that unavailable proof-only import is omitted. The item does not use
  its notion in its statement, and no replacement definition is needed.
  The proof docstring still cites its boundary-lifting input.

Edge cases checked before and during the second reading:

- Degree zero is A[B]; its evaluation includes a variable for every b,
  including when B is the zero ring. No nontriviality assumption occurs.
- Empty polynomial generator sets are allowed (`E : Type u`, without
  `Nonempty E`), and infinite generator sets are unrestricted.
- The resolution condition includes degree-zero surjectivity. There is no
  finite-generation or smoothness hypothesis hidden in polynomiality.
- In degree -1 the differential is d_0 - d_1. In all positive degrees
  extension by zero supplies the zero object; for constant B the odd
  negative differentials vanish and even negative differentials are identities.
- Ring-square identities and composites use the actual arrow-category maps.
  Differentials preserve the coefficient ring via explicit restriction,
  including identity ring maps. No base change flatness is assumed.
- The comparisons cover arbitrary supplied semilinear maps and arbitrary
  choices of polynomial resolutions; neither inverses of algebra maps nor
  contractibility of a base-changed intermediate resolution is required.

Searches for reuse (all performed on the authorized source directories):

- `msearch.py ... leansearch "cotangent complex from simplicial polynomial
  resolutions independent of resolution and functorial in commutative ring
  squares"`: eight hits on ideal cotangent modules, presentation H1,
  conormal exact sequences and generic commutative squares. None gives
  the full simplicial derived construction or resolution coherence.
- `msearch.py ... leanfinder "cotangent complex standard simplicial polynomial
  resolution canonical comparison functorial ring maps"`: eight hits,
  principally `Algebra.H1Cotangent.map`, `Extension.Cotangent.map`, and
  presentation conormal differentials. None is the full derived complex
  or the stated coherence assertion. Read the relevant declarations in
  `RingTheory/Extension/Cotangent/Basic.lean`: `cotangentComplex` there is
  the conormal differential, not L_{B/A}.
- `msearch.py ... loogle "AlgebraCat.adj, Comonad,
  KaehlerDifferential.map"`: no hits, unknown `AlgebraCat.adj`.
- Follow-up `msearch.py ... loogle '"KaehlerDifferential"'`: twelve hits,
  including the genuine differential module and universal derivation,
  which are reused here. No cotangent-resolution assertion was returned.
- `msearch.py ... grep "standardResolution|cotangentComplex|simplicial.*resolution"
  RingTheory`: 25 hits, all presentation-level conormal/smoothness results.
- `rg` in upstream `WeilConjectures` and shared `lean/Sheaf` for
  `standardResolution|cotangentComplex|CotangentComplex|polynomialResolution`
  found the conormal/symmetric-algebra comparison family, with no full
  standard simplicial cotangent construction. Grepping upstream for the
  exact blueprint id found no declaration.
- `rg` for `standardSimplicial|IsStandardSimplicialResolution|Comonad`
  found the existing generic adjunction and comonad modules; these were
  read and are imported through the proof-only adjunction module.
  The ring-specific helpers specialize the polynomial formulas that the
  item itself introduces, including changes of the base ring.
- `rg` for `negativeComplex`, simplicial/alternating definitions and
  `embeddingDownNat.extendFunctor` in the shared simplicial/category
  directories found no duplicate composite functor. Existing generic
  alternating-complex and extension functors are composed directly.
- `rg` for the proposed namespace and helper names in both project source
  trees found no conflicting declaration. Upstream name metadata was
  searched for the blueprint id, with no attachment.
- `python3 tools/blueprint_refs.py search 'cotangent resolution'`: no
  matching blueprint node. No additional independent notion/node is
  introduced: all helpers implement the constructions explicitly owned
  by this item's own statement.

Source checked: `literature/stacks-project/cotangent.tex`, definitions
`definition-standard-resolution`, `definition-cotangent-complex-ring-map`,
`remark-resolution`, and `section-functoriality`, including the explicit
A[B] → A'[B'] map and arbitrary-resolution comparison. The existing repair
note withdraws a superseded stage-1 route using dropped model machinery;
this delivery follows the current node's revised nine-step Stacks proof
and imports none of the dropped model/realization modules.

Validation: prescribed `scompile.py` compiled both sandbox and library-name
versions, each about four seconds, with no errors and no warnings. No
proofs are supplied beyond the one required `sorry`; all implementation
helpers are actual definitions/record specifications. There is no
STATEMENT-DISPUTED flag, statement correction, new node, or dependency module.

## Second reading by Q106

This is the dispatcher's requested author self-check; the maintainer's
independent reader performs the independent review. No sub-agent was started.
I reopened the current node, its source places, and the complete module and
checked the twelve correspondences above, including each coefficient and
augmentation equation, each degree convention, and every comparison target.

The check caught and repaired a missing explicit construction of the final
transported map: `cotangentComplex`, `cotangentMap`, and `transportedMap` now
expose the actual composites, instead of leaving that construction only in
the record's compatibility equation. It also caught the missing direct
CommRingCat → AddCommGrpCat functor; the additive augmentation now explicitly
composes CommRingCat → RingCat → AddCommGrpCat. The zero-degree single complex
is obtained from Mathlib's augmented alternating-complex construction, so no
replacement of the quasi-isomorphism hypothesis by an unexplained homotopy
condition occurs. A line-length warning was removed and compilation rerun clean.

In particular the record's existence is fully specified, rather than a bare
Nonempty collection of unrelated maps: standard terms and operators are
fixed by equality, differential tensors by their term isomorphisms and
all-operator generator formulas, and ring-square maps by coefficient and
generator recursion. The comparisons have identity normalization and
naturality for every resolution morphism and every ring square. Those are
exactly the source's canonical comparisons: common refinements force their
uniqueness once the standard comparison is fixed. The theorem contains no
assumption selecting an arbitrary standard object or canonical map.
