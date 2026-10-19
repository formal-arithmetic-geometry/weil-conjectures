## Worker report

The delivery realizes both predicates in def-kun-tor-amplitude. The bounded variant is
already exactly `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`, defined in
`WeilConjectures.SixFunctors.Etale.Derived.Coefficients`. The module adds only
`AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeGE` for the lower-bounded variant.
The node's mixed lean record lists both declarations; its primary signature is the new
predicate's signature verbatim. No theorem or proof is added, and there are no sorries.

Hypothesis and clause correspondence:

- Scheme T: `(T : Scheme.{u})`.
- Commutative coefficient ring Λ: `(Λ : Type (u + 1)) [CommRing Λ]`, following the
  landed derived-category encoding. This is the project's common universe convention
  for arbitrary etale module sheaves, with no finite-ring assumption.
- E in D(T_et,Λ): `E` is the argument of
  `ObjectProperty (DerivedCategoryModule Λ T)`. This abbreviation is precisely
  `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
- Integral endpoints: existing bounded predicate takes `(a b : ℤ)`; new predicate
  takes `(a : ℤ)`. Neither assumes `a ≤ b` or any boundedness of E.
- Every module sheaf M: `∀ (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))`;
  the existing predicate uses the identical quantifier named `F`.
- Placed in degree zero: `(_root_.DerivedCategory.singleFunctor _ 0).obj M`.
  This applies to arbitrary sheaves, not merely constant sheaves or flat sheaves.
- Derived tensor with E: `((derivedTensor (ModuleCat.{u + 1} Λ) T).obj E).obj ...`.
  This is the recorded K-flat derived tensor, not ordinary tensor or a Tor functor.
- Cohomology in degree i: `(_root_.DerivedCategory.homologyFunctor _ i).obj ...`.
- Vanishing: `CategoryTheory.Limits.IsZero` of that cohomology sheaf.
- Outside [a,b]: the existing predicate uses `q < a ∨ b < q`, exactly the complement
  of the closed integer interval, including empty intervals.
- Below a: the new predicate uses `(i : ℤ), i < a → IsZero ...` and imposes no
  upper bound.
- The final prose about bounded flat representatives is a reference to other properties,
  not an extra condition or theorem to be included here. The module documents it and
  does not equate boundedness with finite Tor amplitude.

Dependency declarations read and used:

- def-weil-pbc-etale-site: `AlgebraicGeometry.Scheme.smallEtaleTopology`, in
  `Mathlib.AlgebraicGeometry.Sites.Etale`, on `Scheme.Etale` from
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`. Read their full definitions and the
  jointly-surjective covering characterization `ofArrows_mem_smallEtaleTopology_iff`.
- def-kun-constant-sheaf: `CategoryTheory.Functor.mapHomologicalComplex`, in
  `Mathlib.Algebra.Homology.Additive`, imported publicly per the dependency record.
  Its full signature/docstring and object formula were read. No constant-sheaf
  restriction appears in the test quantifier: M is an arbitrary module sheaf.
- def-weil-pbc-derived-categories: import
  `Sheaf.AlgebraicGeometry.DerivedCategories`, whose record fixes the six-functor
  encoding. Read this full module and the abbreviation
  `AlgebraicGeometry.Etale.DerivedCategoryModule` in the upstream Coefficients module.
  The torsionCohomology predicate belonging to this dependency is not needed here.
- def-kun-derived-tensor: `AlgebraicGeometry.Etale.derivedTensor`, in
  `WeilConjectures.SixFunctors.Etale.Derived.Tensor`; read its full contextual signature,
  docstring and body `curriedTensor _`. Coefficients imports it transitively.
- def-weil-derived-cohomology-sheaves: mathlib_match
  `DerivedCategory.homologyFunctor`, in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`. Read its full contextual
  signature, docstring and `homologyFunctorFactors`; used on the same category of
  etale module sheaves as the landed derived-category dependency.
- Degree-zero embedding: read `DerivedCategory.singleFunctor` and
  `singleFunctorIsoCompQ` in `Mathlib.Algebra.Homology.DerivedCategory.Basic`.

Source and edge checks:

Read the blueprint source in the node and Stacks sites-cohomology.tex,
`definition-tor-amplitude` (08FZ) and `lemma-bounded-below-tor-amplitude` (0F1M).
The latter's proof explicitly says vanishing for every module and n < a.
The blueprint permits a > b, unlike Stacks' introductory a ≤ b convention;
this is consistent: every degree is then outside the interval. Testing with the
unit forces E to be zero. Both predicates accept E = 0; on the empty scheme
all sheaves are zero, so both are automatically satisfied. When a = b the only
allowed cohomology degree after tensoring is a. A flat sheaf in degree zero has
bounded amplitude [0,0] and lower amplitude [0,∞). The lower predicate does not
assert an upper bound: an unbounded-above complex of flat sheaves can qualify.
Over a ring such as k[ε]/(ε²), the bounded complex k[0] need not have finite
Tor amplitude (its derived self-tensor has nonzero Tor in arbitrarily negative
degrees), confirming why boundedness is not a definition clause. Zero coefficient
rings are allowed. These are mathematical edge checks; no stage-2 proofs were added.

Searches (all on 2026-10-15):

- msearch.py leanfinder: "For every sheaf of modules in degree zero derived tensor
  has cohomology vanishing outside an interval". Eight hits, including
  DerivedCategory.isZero_of_isLE, isZero_of_isGE and isGE_iff, and projective Tor
  vanishing; no Tor-amplitude predicate in Mathlib.
- msearch.py loogle: "torAmplitudeIn, torAmplitudeGE". Zero hits; unknown identifier
  torAmplitudeIn.
- msearch.py grep: "torAmplitudeIn|torAmplitudeGE|HasTorAmplitude". Zero Mathlib hits.
- rg in upstream WeilConjectures for tor amplitude / torAmplitude / tor_amplitude,
  followed by definition-only search, found the general DerivedCategory.torAmplitudeIn,
  its etale/pro-etale specializations and the exact Coefficients.hasTorAmplitudeIn.
  Read the full generic and etale TorAmplitude modules and the Coefficients definition.
  Reuse the latter rather than restating the bounded predicate.
- rg in lean/Sheaf found the pro-etale amplitude definition and unrelated scheme
  Tor-amplitude lemmas; none define the lower-bounded etale predicate.
- rg in upstream and lean/Sheaf for
  torAmplitude(GE|Above|From|Lower), tor amplitude with infinity/∞/below, and
  lower-bounded Tor: only prose about lower bounds and consequences of bounded
  amplitude, no existing predicate for [a,∞).
- rg for def-kun-tor-amplitude in upstream: no hits.

No statement correction, new node, dependency repair or STATEMENT-DISPUTED issue.

## Second reading by NZ

I independently read the sandbox node, its original blueprint source, Stacks
sites-cohomology.tex at definition-tor-amplitude (08FZ) and
lemma-bounded-below-tor-amplitude (0F1M), all five statement-dependency nodes,
and the declaration sources. No mathematical or signature mismatch was found;
the Lean file and node record are retained unchanged.

Object/hypothesis/clause checklist, taken from the node before comparing the Lean:

- An arbitrary scheme T: `(T : Scheme.{u})`; PASS. No separatedness, Noetherian,
  nonemptiness or characteristic assumption.
- A commutative ring Λ: `(Λ : Type (u + 1)) [CommRing Λ]`; PASS in the shared
  six-functor size convention of def-weil-pbc-derived-categories. Neither a field,
  a finite ring, nor a nonzero ring is required. Smaller coefficient types are
  cumulative inhabitants of this universe. The module imposes no additional
  instance or universe equality on its dependency's derived category.
- E in D(T_et,Λ): the argument of `ObjectProperty (DerivedCategoryModule Λ T)`;
  PASS. I read Coefficients.lean: this abbreviation is the derived category of
  `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`. The dependency module
  DerivedCategories.lean publicly imports it. This uses the recorded encoding,
  rather than confusing it with the separate SheafOfModules encoding.
- Integers a,b and both notions: bounded intervals are exactly the existing
  `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn Λ T a b` in
  Coefficients.lean; lower intervals use the new `hasTorAmplitudeGE Λ T a`;
  PASS. Both declarations are in lean.declarations; the primary signature in
  lean.statement is verbatim the new declaration header without its body.
- Every sheaf M of Λ-modules, placed in degree zero: the bounded predicate's
  `∀ (F : Sheaf ...) (q : ℤ)` and the new `∀ (M : Sheaf ...) (i : ℤ)`, with
  `(_root_.DerivedCategory.singleFunctor _ 0).obj M`; PASS. Basic.lean defines
  singleFunctor as the embedding of a single cochain complex in that degree.
  In particular, testing only constant, finite or flat sheaves would be wrong;
  neither predicate does that.
- Tensor E with that sheaf over Λ in the derived category:
  `((derivedTensor (ModuleCat.{u + 1} Λ) T).obj E).obj (...)`; PASS. I read
  Tensor.lean's contextual instances and its `curriedTensor _` definition:
  this is the existing unbounded K-flat derived monoidal tensor. Specializing
  to ModuleCat uses existing instances and introduces no extra hypotheses.
- Cohomology H^i and vanishing: `IsZero ((_root_.DerivedCategory.homologyFunctor
  _ i).obj ...)`; PASS. HomologySequence.lean defines this functor using
  ComplexShape.up ℤ and identifies its composite with Q with cochain homology.
  Thus it is cohomology of sheaves, not sections or a degreewise Tor group.
- Bounded condition for all i outside [a,b]: the existing predicate uses
  `q < a ∨ b < q → IsZero ...`; PASS, exactly the closed interval complement.
- Lower condition for all i<a, with no upper constraint: the new predicate uses
  `(i : ℤ), i < a → IsZero ...`; PASS. Quantifiers are universal in M and i,
  with E and a fixed, as in the source.
- The sentence on bounded flat representatives points to other properties and
  warns against boundedness alone. It introduces no third predicate or theorem;
  PASS. The module documents this and adds no proof.

Dependency/interface cross-check: smallEtaleTopology in Sites/Etale.lean is
precisely the small etale topology, on Scheme.Etale (Morphisms/Etale.lean), with
the jointly-surjective family criterion. For def-kun-constant-sheaf I opened
Additive.lean's Functor.mapHomologicalComplex and its degreewise object/map
formula, and read the node's specialization note; this definition is not used
to restrict the test sheaf. Its recorded module is imported. The tensor,
derived-category and cohomology dependencies are used as recorded, with no
private replacement. There are no new nodes or dependency modules to audit.
There is no statement_change and hence no citer-change audit is applicable.

Source hypotheses: Stacks 08FZ works on any ringed site and assumes a≤b in its
introductory definition. The node's own blueprint explicitly has unrestricted
integer endpoints; using the same displayed formula for an empty interval is
consistent and is also allowed by the existing bounded predicate. Stacks 0F1M
has no finiteness hypothesis; its proof explicitly interprets the lower bound
as vanishing for every module and n<a. No hidden geometric hypothesis is lost
in specializing these definitions to the constant coefficient small etale site.

Edge cases checked: a>b requires every tensor cohomology group to vanish
(the coefficient sheaf test forces E=0); a=b permits only that degree; a=0
keeps precisely nonnegative tensor cohomology in the lower version. The zero
object satisfies both predicates, including on the empty scheme; the zero
ring and every characteristic are allowed. There is no index family to which
an empty-index exclusion could apply. Unbounded E is permitted and the lower
predicate adds no upper bound. The single universe u is explicitly bound and
matches the already recorded category and tensor interfaces.

Independent searches on 2026-10-15:

- msearch leanfinder: `Derived tensor with all modules has no cohomology below
  an integer bound` returned eight hits (projective Tor vanishing and
  DerivedCategory.isGE_iff/isLE_iff/isZero_of_isGE/isZero_of_isLE), none a
  lower-Tor-amplitude predicate.
- msearch loogle: `"TorAmplitude"` returned zero hits.
- msearch leansearch: `Tor amplitude bounded below of a complex of sheaves of
  modules` was unavailable (Internal Server Error), recorded as unavailable.
- msearch grep: `torAmplitudeGE|torAmplitudeAbove|torAmplitudeFrom|torAmplitudeLower`
  returned zero Mathlib hits.
- Independently searched Mathlib, upstream WeilConjectures and project lean/Sheaf
  for Tor-amplitude spellings and definition/abbreviation headers. I opened
  the generic CategoryTheory/DerivedCategory/TorAmplitude.lean and the etale
  TorAmplitude.lean: these supply bounded and finite amplitude, not the lower
  variant. Coefficients.hasTorAmplitudeIn is exactly the bounded variant and
  is reused. ProEtaleTorAmplitude in the project is for a different site.

H5/H6/H8/H9: the new definition has real predicate data, no sorry, axiom or
proof; its module/declaration docstrings cite the blueprint and Stacks; the
node has no proof steps requiring a theorem docstring. All lines fit 100
columns. Imports serve the recorded dependencies. No file-local notation,
instance or unbound variable is introduced. Second reading changed only this
report and added search evidence; no correction to right Lean was needed.

Validation: scompile.py NZ def-kun-tor-amplitude
lean/Sheaf/AlgebraicGeometry/EtaleTorAmplitude.lean passed for both sandbox
and library contexts without errors or warnings (1.8 s and 1.7 s).
