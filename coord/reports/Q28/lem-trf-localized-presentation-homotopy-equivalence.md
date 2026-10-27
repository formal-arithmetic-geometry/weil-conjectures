## Worker report

The module `Sheaf.RingTheory.LocalizedPresentationHomotopyEquivalence` states
`Algebra.Extension.localizedPresentation_homotopy_equivalence`, with `sorry` as its
only proof. It uses Mathlib's existing extension, conormal, differential, localization,
and polynomial definitions. No definitions, helper theorems, or new DAG nodes are added.
The existing node is changed only in `lean`.

Hypothesis and clause correspondence:

- The commutative rings and map A → B are `{A : Type u} {B : Type v}`,
  `[CommRing A] [CommRing B] [Algebra A B]`.
- The two surjective A-algebra presentations are `(R : Extension.{w} A B)` and
  `(P : Extension.{w'} A B)`. An `Extension` contains the A-algebra, its compatible
  algebra map to B, and a set section. Its `algebraMap_surjective` proves surjectivity.
  Conversely, any surjective A-algebra map yields exactly such an extension by
  `Extension.ofSurjective`; the section is available by choice and imposes no condition.
- The polynomial ring R = A[V] is specified by `(V : Type i)` and
  `(eR : R.Ring ≃ₐ[A] MvPolynomial V A)`. This merely names its identification as an
  A-algebra, with no finiteness or cardinality restriction. Taking R to be
  `ofSurjective` of the original polynomial augmentation makes this identification
  the identity. Keeping the identification explicit permits any representation of R.
- The other presentation P = W⁻¹A[E] is `(E : Type j)`,
  `[Algebra (MvPolynomial E A) P.Ring]`,
  `[IsScalarTower A (MvPolynomial E A) P.Ring]`,
  `(W : Submonoid (MvPolynomial E A))`, and `[IsLocalization W P.Ring]`.
  The tower says that this is the given A-algebra structure. `Submonoid` includes
  one and multiplicative closure, and `IsLocalization` is exactly localization at
  that submonoid, including the stated fraction equality relation. These encode
  the node's localization map, rather than any additional regularity hypothesis.
- I and J are `R.ker` and `P.ker`. The conormal modules are `R.Cotangent` and
  `P.Cotangent`; their `.val` identifies them with the existing `Ideal.Cotangent`.
- The degree-zero modules are `R.CotangentSpace` and `P.CotangentSpace`, namely
  B ⊗[R.Ring] Ω[R.Ring/A] and B ⊗[P.Ring] Ω[P.Ring/A]. Mathlib puts B first;
  this is the canonical tensor flip of the node's Ω ⊗ B, not a different module.
  The degree -1 to 0 differentials are `R.cotangentComplex` and `P.cotangentComplex`;
  `cotangentComplex_mk` gives δ([h]) = 1 ⊗ dh. Stating maps between these two terms
  and both degree equations is exactly the node's degreewise interpretation;
  all other terms and homotopy components are zero.
- Existence of an A-algebra map over B is `Nonempty (R.Hom P)`.
  The next clause, `∀ a : R.Hom P`, concerns every such map, not a selected lift.
  `Hom.toAlgHom` is the underlying A-algebra map, and the `Hom` fields impose the
  triangle over B.
- N(a) is the canonical pair `Cotangent.map a`, `CotangentSpace.map a`.
  `Cotangent.map_mk` gives [h] ↦ [a(h)]; `CotangentSpace.map_tmul` gives
  b ⊗ dr ↦ b ⊗ d(a(r)); `map_comp_cotangentComplex` supplies its chain identity.
  These are already defined, so the theorem does not add tautological conjuncts
  restating these unconditional facts.
- The more precise inverse lift is `ell : P.Hom R.infinitesimal`.
  `R.infinitesimal.Ring` is definitionally R.Ring / R.ker², and the extension Hom
  condition states exactly that ell reduces to the augmentation P → B.
- `dbar : R.infinitesimal.Ring →ₗ[A] R.CotangentSpace` and its formula for every
  `r : R.Ring` specify the descended universal derivation. Because the quotient
  map is surjective, this pins down the map completely; its derivation law for
  the action through B follows from Leibniz on representatives. Encoding it as
  an A-linear map with this universal representative formula avoids introducing
  a second quotient-module action solely to package the same map as `Derivation`.
- `gMinus` and `gZero` are explicitly B-linear and have exactly the two required
  source and target modules. For `h : P.ker`, the equation using
  `R.ker.cotangentToQuotientSquare (gMinus (Cotangent.mk h)).val = ell h`
  says that gMinus([h]) is ell(h) in I/I². The canonical map into R/I² is injective,
  so this specifies the class exactly, without a representative choice.
- The next clause gives `gZero (b ⊗ dp) = b • dbar (ell p)` for every p and b.
  The following equality `R.cotangentComplex ∘ₗ gMinus =
  gZero ∘ₗ P.cotangentComplex` makes the inverse pair a chain map.
- `HR` and `HP` have the exact B-linear types N(R)^0 → N(R)^(-1) and
  N(P)^0 → N(P)^(-1). The last four equations are, in order, the degree -1 and
  degree 0 components of gN(a) - 1 = δR HR + HR δR, and the degree -1 and
  degree 0 components of N(a)g - 1 = δP HP + HP δP. Thus they assert a chain
  homotopy inverse, with the node's signs. No map P → R is assumed or concluded.

Dependency declarations read and used:

- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, `MvPolynomial.algHom_ext`;
  evaluation `MvPolynomial.aeval` in `Mathlib.Algebra.MvPolynomial.Eval` was read
  for the variable-lifting proof plan. These give def-weil-pbc-mv-polynomial-ring.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`,
  `KaehlerDifferential.D`, `KaehlerDifferential.linearMapEquivDerivation` give
  def-weil-pbc-kahler-differentials, including its universal property.
- The mathlib leaf lem-trf-conormal-semilinear-difference-homotopy is used through
  `Mathlib.RingTheory.Extension.Basic` (`Extension.ofSurjective`, `Hom`,
  `Cotangent.map`, `Cotangent.map_mk`) and
  `Mathlib.RingTheory.Extension.Cotangent.Basic` (`CotangentSpace.map`,
  `CotangentSpace.map_tmul`, `CotangentSpace.map_comp_cotangentComplex`,
  `Hom.sub`, `Hom.sub_tmul`, `Cotangent.map_sub_map`, `CotangentSpace.map_sub_map`).
  The declaration signatures and docstrings were read, not merely their names.
- The mathlib leaf lem-weil-pbc-localization-square-zero-lifting is the proof-only
  import `Mathlib.RingTheory.Smooth.Basic`, particularly
  `Algebra.FormallySmooth.of_isLocalization` and `Algebra.FormallySmooth.comp_surjective`.
  Both full declarations were read. No missing recorded dependency requires repair.
- `Mathlib.RingTheory.Localization.Defs` supplies `IsLocalization`; its class,
  equivalent three-condition characterization, and fraction API were read.
  `Mathlib.RingTheory.Ideal.Cotangent` supplies `cotangentToQuotientSquare`
  and its injectivity. `Extension.infinitesimal` and `toInfinitesimal` are used
  directly rather than duplicated.

Sources read: local `literature/stacks-project/algebra.tex`, the complete statement
and proof of `lemma-NL-homotopy` (Tag 00S1, lines 35274 onward) and
`lemma-localization-formally-etale` (Tag 04EG, lines 41242 onward). The localized
extension here is the node's specified adaptation, using precisely the square-zero
lift instead of an unavailable reverse ring map.

Edge cases checked: V and E empty or infinite (independent universes i,j; no
`Finite`, `Fintype`, or `Nonempty` hypothesis); W = {1}; W containing zero
(which forces P and hence B to be zero); zero A, zero B, and zero kernel;
characteristic two (the equations retain subtraction, which specializes correctly).
Independent universes u,v,w,w',i,j impose no equality on base, quotient,
presentation rings or variable sets. None of the hypotheses is vacuous.

Searches for an existing statement:

- `msearch.py ... leanfinder "localized polynomial presentation naive cotangent
  complex homotopy equivalence square zero lift"`: eight hits, principally
  `Algebra.Generators.cotangentCompLocalizationAwayEquiv` and its formulas.
  These concern splitting the conormal of a principal localization, not this
  comparison for arbitrary W with a modulo-square inverse and four equations.
- `msearch.py ... loogle "Algebra.Extension.Cotangent.map_sub_map,
  Algebra.Extension.Hom.sub"`: one hit, `Cotangent.map_sub_map`, the already
  recorded difference-homotopy ingredient, not the full assertion.
- `msearch.py ... grep "homotop|homInfinitesimal|cotangentCompLocalization"
  RingTheory/Extension`: eleven hits, in Cotangent/LocalizationAway, Basis and
  Basic; no full statement.
- `msearch.py ... leansearch "Naive cotangent complexes of polynomial and
  localized polynomial presentations are chain homotopy equivalent"`: eight hits
  on the localization-away conormal splitting and H1 localization, no full match.
- `rg` in `lean/WeilConjectures/RingTheory` for `homotop|homInfinitesimal` and
  later for `localizedPresentation_homotopy_equivalence|homInfinitesimal|
  CotangentSpace.map`: related homotopies, principally the already proved
  principal-localization comparison, no exact statement. Search for the exact
  blueprint id in `lean/WeilConjectures` returned no matches.
- `rg` in `lean/Sheaf` for localized presentations and presentation homotopies,
  plus DAG searches for `nl-presentations-homotopy-equivalent`, located
  `PresentationsHomotopyEquivalent.lean` and `NaiveCotangentComparison.lean`.
  Read both: the former requires polynomial rings on both sides; the latter
  constructs a derived comparison with the standard cotangent resolution, not
  this explicit homotopy inverse theorem. Neither is an exact match. The existing
  Mathlib extension definitions already supply every notion needed here.

No statement correction, disputed statement, or node fault was found. Server compile
via the prescribed `scompile.py` succeeded for both sandbox and library module forms
(3.8 s and 1.7 s), with no errors or non-sorry warnings.

## Second reading by Q28

A fresh clause-by-clause self-review was performed with the node and final module
open; no additional agents were started, as the dispatcher brief requires. The
maintainer's independent review remains the external second reading.

Checked the two surjections encoded by `Extension`, the specified polynomial
identification `eR`, arbitrary E and V, the localization structure and its compatible
A-action, existence followed by universality in `a`, and the target R/I² of `ell`.
Checked that `ell` is over B by its Hom type, and that its conormal formula uses the
injective ideal map on `.val`, not an arbitrary map or an inverse P → R. Read the
universal representative formula for `dbar` and the generator formula for `gZero`;
together they give exactly the descended derivation used in the node. Checked the
chain identity and all four composite equations, including the signs and the
placement of each differential. In degree -1 the homotopy is Hδ; in degree 0
it is δH, on both R and P. No equation has been replaced by a quasi-isomorphism
or by an assertion about homology. Checked empty variable sets, zero localization,
zero quotient and characteristic two. No mismatch was found and no statement
change was made.
