## Worker report

The module Sheaf.Paper.CtfHomCoefficientComparison states
AlgebraicGeometry.Etale.ctf_hom_coefficient_comparison, with sorry, and defines the two
actual arrows ctfHomBidualMap and ctfHomCoefficientMap. Both definitions contain real
data: tensor--Hom transposition of evaluation; neither selects an arbitrary morphism.
The previous attempt's probe is retained under scratchpad/PreviousProbe.lean.txt.

Source read: ILO, Travaux de Gabber, Expose XVII, Theorem 7.6.1, printed pp. 310--311
(PDF pp. 316--317), and its proof and Definition 7.7.1 on printed p. 314 (PDF p. 320).
The source allows arbitrary coefficient extension. The node additionally specifies
Noetherian B to ensure that extended complexes remain bounded constructible of finite
Tor dimension. Its existing five-step proof is copied into the theorem's docstring.

Hypotheses and clauses, individually:

- Prime ell: `(l : ℕ) [Fact l.Prime]`. The prime-field category has coefficients
  `ULift.{u + 1} (ZMod l)`. ULift is the canonical size lift of the same prime field.
- Noetherian scheme X: `(X : Scheme.{u}) [IsNoetherian X]`. Mathlib's class is a locally
  Noetherian scheme with CompactSpace X, equivalently a finite affine cover by spectra
  of Noetherian rings. It does not impose finite type, separatedness, or nonemptiness.
- Commutative Noetherian prime-field algebra A: `(A : Type (u + 1)) [CommRing A]
  [IsNoetherianRing A] [Algebra (ZMod l) A]`. Giving the algebra over the unlifted prime
  field is equivalent to giving it over its canonical ULift; no characteristic or
  nontriviality assumption on A is silently added.
- Ordinary small-etale derived categories: all inputs are `DerivedCategoryModule R X`,
  the recorded `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))`.
  They are not the pro-etale, condensed, or intrinsically complete categories.
- Bounded constructible prime-field Q: the first conjunct of `hDual` is exactly
  `DerivedCategory.isBoundedConstructible (ULift (ZMod l)) X Q`, the recorded
  def-weil-pbc-constructible-complexes declaration.
- Preservation by Hom(-,Q): the universally quantified P in `hDual` satisfies that same
  bounded-constructible predicate, and the first conclusion says its derived Hom into
  Q does too. The second conclusion is `IsIso (ctfHomBidualMap ... P Q)`, not just
  existence of an unspecified isomorphism with the double dual.
- General D^b_ctf(X,R): uses the existing upstream
  `DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X`. Its definition is
  boundedConstructible AND finiteTorAmplitude. BoundedConstructible is standard bounded
  cohomology and constructibleHomology; `Scheme.IsConstructibleSheaf` uses a finite
  locally closed scheme stratification and `IsFiniteLocallyConstantSheaf` on strata.
  Importantly, `IsFiniteSheaf` means ConcreteCategory.IsFinitelyGenerated of geometric
  stalks: for ModuleCat R it means Module.Finite R, NOT a finite underlying set and NOT
  finite coefficients. Thus it applies to arbitrary Noetherian A and B in this item.
  Constructible strata add no condition on Noetherian X. Boundedness leaves only finitely
  many nonzero cohomology sheaves, so their finitely many stratifications have a common
  finite refinement, as required by the node's common-stratification wording.
- The finite-Tor part tests ALL sheaves F in degree zero:
  DerivedCategory.torAmplitudeIn is `∀ F, homologyConcentratedIn a b
  (K tensor (singleFunctor _ 0).obj F)`. It is not restricted to constant coefficients.
  The source predicate existentially quantifies a,b without a≤b; any witness can be
  enlarged to [min a b,max a b], including the zero object. This is the identical notion.
- First conclusion: the theorem's first top-level conjunct quantifies every P,L in
  D^b_ctf(X,A) and asserts the same predicate for `derivedHom ... P L`.
- Every coefficient homomorphism: the second top-level conjunct quantifies
  `(B : Type (u + 1)) [CommRing B] [IsNoetherianRing B] (φ : A →+* B)`.
  There is no Flat, Module.Finite, finite ring, invertibility of ell, or finite-type
  assumption on B over A. B obtains its prime-field structure by composition if needed.
- Extension preservation: its first conjunct says every ctf K has ctf
  `((scalarExtension φ X).obj K)` over B. The existing functor is the ordinary derived
  scalar extension, not underived tensor or a chosen arbitrary functor.
- The specified comparison: `ctfHomCoefficientMap X φ P L` is the existing comparison component
  `((etaleHomComparison_thickLocus X φ).choose L).app (op P)`.
  Its `IsEtaleHomTranspose` equation identifies it with the transpose of
  `(etaleHomTensorComparison X φ P Hom(P,L)).hom` followed by scalar extension of
  `(derivedTensorHomAdjunction ... P).counit.app L`.
  This is exactly TP tensor T(Hom(P,L)) -> T(P tensor Hom(P,L)) -> TL. The tensor
  comparison is fixed by ordinary scalar balancing on representatives. The signed symmetry is
  the existing derivedTensorSymmetry; the chosen P-first evaluation order is exactly
  the order specified in the statement, so no additional interchange is needed here.
- Isomorphism IN the ctf category: its second conjunct asserts IsIso of that map and
  ctf membership of its target. Its source is ctf by the first top-level clause and
  extension preservation, so both endpoints lie in the full ctf subcategory.
- Naturality: its final conjunct spells out, for arbitrary ctf P,P',L,L' and
  `f : P' ⟶ P`, `g : L ⟶ L'`, the equality
  `T(Hom(f,g)) ≫ alpha(P',L') = alpha(P,L) ≫ Hom(Tf,Tg)`.
  Hom acts contravariantly on f via `f.op` and covariantly on g. No naturality clause
  is replaced by nonempty objectwise isomorphisms.

Dependency declarations read and used (recorded interfaces, with their source docstrings):

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Mathlib.RingTheory.Noetherian.Defs: IsNoetherianRing.
- Mathlib.AlgebraicGeometry.Sites.Etale: Scheme.smallEtaleTopology, Scheme.Etale.
- WeilConjectures.AlgebraicGeometry.DerivedCategories and
  WeilConjectures.SixFunctors.Etale.Derived.Coefficients: DerivedCategoryModule and
  DerivedCategory.homologyFunctor; the live derived-categories record is used through
  the recorded public imports.
- Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules:
  SheafOfModules.IsLocallyConstantFiniteTypeModules (general-site constant-ring form).
  Its same small-etale ModuleCat specialization is supplied by upstream
  Scheme.IsLocallyConstantSheaf and Scheme.IsFiniteSheaf. No second definition is made.
- Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification:
  Scheme.FiniteLocallyClosedStratification. The upstream Stratification additionally
  records constructible strata; on Noetherian X this is automatic, as its
  Stratification.ofNoetherianSpace docstring and declaration explain.
- Mathlib.RingTheory.Finiteness.Defs: Module.Finite, underlying finite-type stalks.
- Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes:
  Etale.DerivedCategory.isBoundedConstructible, used in hDual.
- WeilConjectures.SixFunctors.Etale.Derived.Tensor: Etale.derivedTensor.
- Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses: reexports Etale.derivedHom and
  Etale.derivedTensorHomAdjunction, used directly; the generic ringed-site Hom is
  preserved and not duplicated.
- WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude:
  Etale.DerivedCategory.constructibleFiniteTor, torAmplitudeIn, finiteTorAmplitude.
- Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry: Etale.derivedTensorSymmetry.
- Sheaf.SixFunctors.EtaleHomThickLocus: Etale.etaleHomComparison_thickLocus,
  IsEtaleHomTranspose, etaleHomTensorComparison and its representative normalization
  IsEtaleHomTensorCanonical. Its public import Sheaf.Paper.EtaleDerivedScalarTensor
  supplies Etale.scalarExtension and scalarExtensionRepresentative, with no finiteness
  assumption on either ring. These are existing maps; no dependency repair is needed.
- Proof-only imports: Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
  (scalarInternalHomAdjunction_exists),
  Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
  (RingedHomUniverses.rightShift_existsUnique and its exact Hom interface), and
  Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses (rhom_global_sectionsOfUniverses).
  The three per-* proof dependencies have no recorded Lean declaration at this writing;
  their intended uses are retained by name in the proof docstring, with no invented import.

Only the item's lean record and additions of two already landed nodes to stmt_deps change:
lem-kun-tensor-sym and lem-coef-etale-hom-thick-locus. These expose the canonical
signed swap and canonical scalar tensor comparison used in the actual arrows. Traversal
of their statement/proof dependency graphs found no path back to this item. There are
no new nodes, dependency modules, statement corrections, or disputed statements.

Edge cases checked before writing:

- Empty X: no nonempty hypothesis, nonzero rank, or geometric point witness is demanded.
- Zero complexes and zero coefficient algebra: permitted; finite Tor intervals may be
  widened, and no nontriviality or nonzero ring class is imposed.
- A separably closed point: ctf becomes bounded perfect finite-module complexes, so the
  result reduces to perfect-complex Hom/tensor change of rings.
- Nonflat quotient A -> A/I: explicitly permitted. B need not be perfect as an A-module.
- A polynomial coefficient algebra, including B=A[t]: permitted although the ring can
  be infinite as a set and not finite as an A-module.
- Identity coefficient map: included by universal φ. Naturality covers identities and
  arbitrary coefficient-linear maps in each input, including zero maps.
- Noetherian schemes of arbitrary characteristic: no invertibility hypothesis on l
  has been introduced. The actual prime-field duality assumption is retained.
- Universes: X : Scheme.{u}, all coefficient carriers/module values : Type (u+1), the
  standard recorded ordinary small-etale encoding. No equality between site object and
  morphism universes is imposed, and all universes/variables are explicitly bound.

Searches (retained in searches.jsonl):

- LeanFinder, previous attempt: "finite Tor constructible internal Hom coefficient
  comparison": eight general condensed/internal-projectivity results, no exact match.
- LeanFinder, current run: "Derived internal Hom of constructible finite Tor etale
  complexes preserves finite Tor amplitude and commutes with coefficient extension":
  eight general Tor/derived/condensed results, no exact match.
- LeanSearch: "Etale derived internal Hom constructible finite Tor scalar extension":
  eight general change-of-scalars and etale-ring results, no matching theorem.
- Loogle, previous attempt: "boundedConstructible finiteTor derivedHom": unknown upstream
  identifiers in Mathlib's index; no match. Current query
  "ModuleCat.extendScalars, CategoryTheory.Sheaf.composeAndSheafify": zero hits.
- msearch grep: "constructibleFiniteTor|ctfHomCoefficientMap|ctfHomBidualMap": zero Mathlib
  hits. Prior grep "ctf": zero Mathlib matches.
- Direct rg over WeilConjectures and lean/Sheaf found the existing upstream
  constructibleFiniteTor/derivedHom and landed scalarExtension, tensorIso and canonical
  symmetry. Their complete signatures and normalization docstrings were read.
- Direct rg of the three proposed declaration names in both source trees: no collision.
  Direct rg of the item id in WeilConjectures and dag/lean_names_upstream.json: no match.

Validation of the returned version: scompile.py compiled the module in both sandbox and
library contexts cleanly (4.8 seconds each). Repair validation is recorded below. The only
postponed proof remains the main theorem.

## Second reading by Q03

The dispatcher explicitly requires one worker and prohibits starting another agent.
This section records this worker's separate rereading of the node and module; it does
not claim an independent second worker's review. The maintainer's independent review
is pending after delivery, as the task brief specifies.

I reread hDual against the exact finite-coefficient definition, checked its Hom closure
and actual bidual arrow, checked that A and B are arbitrary Noetherian rings of the
prescribed characteristic, expanded upstream constructibleFiniteTor and IsFiniteSheaf
(finitely generated, not finite sets), and checked the scalar tensor comparison's
normalization. The repaired coefficient arrow is now the exact thick-locus comparison
component used by the parent; its IsEtaleHomTranspose equation has the correct evaluation
order, and the naturality equation has the correct contravariance. The ctf target is explicitly asserted; the
ctf source follows from the other two clauses. The returned H4 mismatch is repaired as detailed below. The old
probe's nonexistent LeftDerivedFunctor.Basic import was not used in the final module.


## Repair of return L, H4

The returned immutable head e3d9a7c3fe32 used a transpose constructed with
ExceptionalCoefficients.tensorIso. Its choice was distinct from the tensor comparison
in the parent's existing homComparison, so no available equality identified the arrows.
The repair imports Sheaf.SixFunctors.EtaleHomThickLocus and replaces the dependency
lem-pur-exceptional-coefficient-comparison with lem-coef-etale-hom-thick-locus. The
coefficient arrow is now exactly
`((etaleHomComparison_thickLocus X φ).choose L).app (op P)`. Reading the current
Sheaf.Paper.CoefficientChangeDualizing source shows that this is definitionally
`(CoefficientChangeDualizing.homComparison X φ L).app (op P)`. The chosen family is
determined uniquely by IsEtaleHomTranspose and the tensor-Hom adjunction; no arbitrary
comparison is substituted. The parent's alpha and beta components therefore use the
very arrows asserted invertible by this item.

The saved node was compared with the current shared node: the only non-Lean difference
is the authorized addition of the two landed statement dependencies. No mathematical
statement, proof, or other node field changes. All previously accepted hypotheses and
clauses, including arbitrary nonflat coefficient extension and two-variable naturality,
are retained. The reviewer's suggestions about boundedConstructibleFiniteTor and the
lifted prime-field algebra are advisory; their already accepted equivalent encodings
are retained to keep this repair focused.

Repair validation: scompile.py compiled the repaired module in sandbox context
(4.6 s) and library context (4.8 s), without diagnostics. The scratch consumer
scratchpad/ComparisonConsumer.lean imports both this module and the current parent,
and checks the equality of ctfHomCoefficientMap with the parent's homComparison
component by rfl, with all universes and variables explicit. It is a validation
artifact only, not part of the delivered statement module.

The consumer compiled cleanly in sandbox (3.5 s) and library (3.6 s) contexts,
confirming that the corrected map serves the current parent by definitional equality.
Final self-check also confirmed the exact stored theorem signature, the single sorry,
the replacement statement dependency, and the 100-character Lean line limit.
