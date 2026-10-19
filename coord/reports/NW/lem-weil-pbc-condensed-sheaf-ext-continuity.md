## Worker report

The module `Sheaf.Paper.CondensedSheafExtContinuity` states
`AlgebraicGeometry.ProEtale.isIso_constructible_condensed_sheaf_hom_colimit`.
Its proof is `sorry`; it introduces no definition or auxiliary theorem.
The natural comparison is expressed directly using Mathlib's additive coyoneda,
localization, shift, and colimit cocone. The node's statement is unchanged.

Hypotheses and clauses:

- A prime ℓ: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- The fixed algebraic closure is `PadicAlgCl ℓ`, the upstream normed algebraic
  closure of `ℚ_[ℓ]`. Choosing the upstream fixed closure makes its coefficient
  definitions applicable; the assertion does not depend on a different closure choice.
- A scheme with noetherian underlying space:
  `(T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]`. No scheme-theoretic
  noetherian, finite type, characteristic, or separatedness hypothesis is added.
- A finite intermediate coefficient field:
  `(E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))`. This uses the dependency's
  declaration and is definitionally the upstream `PadicAlgCl.FiniteIntermediateField ℓ`.
- The coefficient ring is `condensedRingObj (Profinite.continuousMapRingObj E.val) T`, definitionally
  the upstream `padicSubfieldRingObj T ℓ E`, exactly `p_T^* C(-,E)`.
  The contextual Ω coefficient ring is the upstream `padicAlgClRingObj T ℓ`;
  it does not occur in this single-E comparison and needs no extra parameter.
- An internal module sheaf is
  `M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
  (condensedRingObj (Profinite.continuousMapRingObj E.val) T)`.
- Constructibility is
  `hM : IsConstructibleModuleObject (condensedRingObj (Profinite.continuousMapRingObj E.val) T) M`.
  Its definition gives a finite scheme stratification and pro-etale-local finite
  presentations on the strata. On a noetherian underlying space every locally
  closed subset is constructible, so the upstream stratification's constructible
  subset condition adds no restriction here.
- A small filtered strict diagram of complexes is `N`, with
  `{I : Type (u + 1)} [SmallCategory I] [IsFiltered I]`.
  These sizes agree with the U/V convention and with the module category's
  Grothendieck universe. No independent lower index universe is used.
- The common termwise lower bound is
  `hN : ∃ a : ℤ, ∀ (i : I) (r : ℤ), r < a → IsZero ((N.obj i).X r)`.
  `IsZero` means the zero module object, independently of a chosen representative.
- The termwise sheaf colimit is `colimit N`. The imported
  `HomologicalComplexLimits` instances construct complex colimits degreewise.
  The module-object and sheaf colimits are the existing categorical colimits,
  with sheafification as required; presheaf colimits are not substituted.
- Localization is `DerivedCategory.Q`; `M[0]` is
  `(DerivedCategory.singleFunctor _ 0).obj M`; every shift is `(n : ℤ)` and
  `shiftFunctor _ n`.
- The abelian-group functor is
  `preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor _ 0).obj M))`.
  It sends a target to its additive Hom group out of `M[0]` and a morphism
  to postcomposition.
- The conclusion is `IsIso (colimit.desc _ (F.mapCocone (colimit.cocone N)))`,
  where this sentence's `F` denotes the explicit composite written in the file
  (there is no local abbreviation in the Lean). The domain is the colimit of
  the shifted derived Hom groups, and the codomain is the shifted derived Hom
  group into `colimit N`. Thus this is the specified canonical map, not an
  arbitrary isomorphism or just an abstract equality of objects.
- Its representative rule is forced by `colimit.ι_desc`: each Hom group maps
  by postcomposition with the localization and shift of the colimit leg.
  Naturality in M is built into `preadditiveCoyoneda.map` (precomposition);
  naturality in maps of strict diagrams is built into `colimit.map` and the
  functor's `mapCocone`; compatibility with shifts is the `shiftFunctor`
  construction and its standard composition isomorphisms. These naturalities
  are properties of the actual explicitly specified comparison, independently
  of the isomorphism assertion, rather than extra choices of isomorphisms.

Dependency declarations read and used:

- `Mathlib.NumberTheory.Padics.PadicNumbers`: `Padic`.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` and `.Basic`:
  `AlgebraicClosure`, `IsAlgClosure`; the fixed normed model is upstream `PadicAlgCl`.
- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`: `Padic.FiniteCoefficientFields`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `pointUpperStar`, `upperStarFromPoint`, `condensedRingObj`.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap`:
  `Profinite.continuousMapRingObj` (via `.FiniteSubextension`).
  The coefficient term unfolds the upstream `padicSubfieldRingObj` abbreviation
  directly to its recorded dependency declarations, avoiding unrelated scalar-change imports.
- `WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def`:
  `IsLocallyFinitelyPresented`, `IsConstructibleModuleObject`.
  These are supporting declarations of the existing condensed-category node;
  its primary base-change declaration is not the notion needed here.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.singleFunctor`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- The size convention has no declaration; explicit universe `u` and `u + 1`
  implement it. The framework supplies the existing derived-category instance.

Imports also retain all available recorded proof inputs:
`RingedSiteGrothendieckAbelian`, `RingedSiteKInjectiveResolutions`,
`LocallyClosedStratification`, `Triangulated.Pretriangulated`, `Grp.AB`, and
`Abelian.DiagramLemmas.Four`. The locally-free derived-Hom, qcqs continuity,
recollement, and local-triviality proof nodes have no Lean record yet, so their
imports are omitted pending their later statement deliveries. The declaration
of the item does not require them. The docstring includes all seven proof steps.

Edge cases checked: the empty scheme and zero M are allowed; zero diagrams
and arbitrary ranks including rank zero are allowed. Negative shifts, zero
shift, and negative lower bounds are all included because both are integers.
The bound is uniform over the whole diagram, not a separate bound for each
object. There is no constructibility or bounded-above assumption on N.
A filtered category is nonempty by definition, as in the mathematical statement.
Nothing replaces the noetherian underlying-space hypothesis by a stronger one.

Searches (2026-10-15):

- `msearch.py leanfinder`: “Derived Hom from a constructible pro-etale condensed
  module commutes with filtered colimits of uniformly bounded below complexes”.
  Eight results, including `localCohomology.diagram`, solid condensed objects,
  and the Grothendieck instance for light condensed modules; no exact match.
- `msearch.py loogle`: `CategoryTheory.preadditiveCoyoneda, CategoryTheory.Limits.IsColimit`.
  Zero hits. Direct source inspection supplies both constructions.
- `msearch.py leansearch`: “Derived Hom from a constructible sheaf commutes with
  filtered colimits of uniformly bounded below complexes”. Service unavailable
  (Internal Server Error); not counted as evidence of absence.
- `msearch.py grep`: `continuity|[Ee]xt.*[Cc]olimit|[Cc]olimit.*[Ee]xt`,
  `CategoryTheory`. Returned generic categorical colimit lemmas, no statement match.
- `rg` in the source project's `WeilConjectures` and this project's `lean/Sheaf`:
  `lem-weil-pbc-condensed-sheaf-ext-continuity`,
  `hom.*[Cc]olimit|[Cc]olimit.*[Hh]om|[Ee]xt.*[Cc]olimit`, and the narrower
  `condensed.*continuity|continuity.*condensed|constructible.*[Ii]sColimit|[Ii]sColimit.*constructible`.
  No exact continuity theorem. Existing constructible-colimit factorization
  concerns different objects; upstream `TwoColimit.lean` describes the desired
  continuity only as an informal input, not a standalone declaration.
- Read `coord/pefw-upstream-framework.md` and the actual side framework files.
  The document explicitly records continuity nodes as lacking complete matches.

No statement correction, new node, dependency replacement, or disputed statement.
Validation: `scompile.py NW lem-weil-pbc-condensed-sheaf-ext-continuity` passed
for the delivered module, with no errors or warnings (8.5 seconds for this file;
nice 19, two threads, 60-second limit). The tool also compiled its side-only
framework imports separately. Initial import/name/scope errors were repaired
without altering the mathematical statement. The required `deliver2.py --no-push`
is the final check; no delivery is pushed by this worker.

## Second reading by NW

I independently read the item's JSON, its seven statement-dependency nodes and
records, the delivered Lean module, and the actual framework declarations in the
newtargets group clone. The source place here is not a Stacks tag: it is
`ModuleObject/Colimit/TwoColimit.lean`, module docstring, Sorried input (Hom).
I read that paragraph and its surrounding assumptions: topologically noetherian
X, the continuous condensed finite-subfield coefficients, and a uniformly bounded
below second argument. Its single-sheaf input is exactly the node under review.
I also read `coord/pefw-upstream-framework.md`; its continuity input has no existing
complete declaration. There is no corrected statement, new node or dependency
replacement in this delivery, so the additional H12/H13 and citer checks do not arise.

Object/hypothesis/conclusion checklist, in the node's order:

1. Prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`. Exact; all primes are admitted.
2. Fixed algebraic closure Omega: `PadicAlgCl ℓ` is the source's chosen normed
   algebraic closure, rather than its completion. The source uses this fixed
   model; the node does not quantify over additional closure data to transport.
   Exact realization of the fixed closure convention.
3. Scheme T with noetherian underlying space: `(T : Scheme.{u})
   [TopologicalSpace.NoetherianSpace T]`. Exact; not the stronger condition that
   its rings are noetherian. No finite-type or characteristic restriction occurs.
4. Finite intermediate E: `E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)`.
   I opened `FiniteCoefficientFields.lean`: this is the subtype of intermediate
   fields with `FiniteDimensional ℚ_[ℓ] E`. It agrees with the upstream
   `PadicAlgCl.FiniteIntermediateField` subtype in `RingObjects/EllAdic.lean`.
   Exact, and the recorded dependency is used.
5. Coefficient ring E_T^c: `condensedRingObj
   (Profinite.continuousMapRingObj E.val) T`. I read the continuous-map presheaf
   (sections are ULift of continuous functions, restriction by precomposition),
   its sheaf construction, `pointUpperStar`, `upperStarFromPoint`, and
   `condensedRingObj`. This is the geometric inverse image from the profinite
   point, not a constant/discrete sheaf. The surrounding Omega_T^c definition
   is contextual and does not enter this comparison. Exact.
6. Module M: the explicit `CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T)
   Ab.{u + 1})` over that ring. This is the recorded internal-module category,
   without any completeness condition. Exact.
7. Constructibility: `hM : IsConstructibleModuleObject ... M`. I opened
   `ProEtaleModule/Def.lean`, `ConstructibleSheaf/Defs.lean`, and
   `ModuleObjects/Free.lean`: this means a finite scheme stratification, followed
   by pro-etale local presentations as cokernels of finite free maps on every
   stratum. The additional constructibility field of `Scheme.Stratification`
   follows from local closedness on a noetherian space, as confirmed by
   `Stratification.ofNoetherianSpace`. No extra hypothesis. Exact.
8. Small filtered strict diagram: `{I : Type (u + 1)} [SmallCategory I]
   [IsFiltered I]` and `N : I ⥤ CochainComplex (...) ℤ`. The coefficients and
   diagram use the chosen larger universe, as required by the size convention.
   This is an actual complex diagram, not just a diagram of derived objects.
   Exact.
9. Common termwise bound: `hN : ∃ a : ℤ, ∀ (i : I) (r : ℤ), r < a →
   IsZero ((N.obj i).X r)`. The existential is outside both universal
   quantifiers. IsZero is categorical zero of the module object, exactly the
   assertion that this term vanishes. Exact; no bound above is imposed.
10. Termwise sheaf colimit: `colimit.cocone N`. I read
    `HomologicalComplexLimits.lean`: the colimit is computed by degreewise
    colimits and evaluations preserve it. Its base category is module sheaves,
    so these are sheaf colimits. Exact.
11. Derived objects, M[0], and all shifts: `DerivedCategory.Q`,
    `(DerivedCategory.singleFunctor _ 0).obj M`, and `shiftFunctor _ (n : ℤ)`.
    I read their signatures in Mathlib's `DerivedCategory/Basic.lean`.
    They give precisely the specified localization, degree-zero object, and
    integer shift. Exact.
12. Abelian-group comparison and isomorphism: additive coyoneda at `op M[0]`
    sends Y to the Hom group M[0] -> Y. I read its actual definition in
    `Preadditive/Yoneda/Basic.lean`: its arrow map is postcomposition.
    Consequently the composite functor displayed in the theorem has values
    exactly Hom(M[0], Q(N_i)[n]). `colimit.desc` of its mapped colimit cocone
    is the canonical comparison into Hom(M[0], Q(colimit N)[n]); `IsIso`
    asserts its invertibility as an abelian-group homomorphism. Exact.
13. Cocone rule and naturalities: by the defining colimit-desc equations, its
    restriction at i sends f to f followed by the shifted localized cocone leg.
    Precomposition in M is the arrow map of additive coyoneda itself; maps of
    strict diagrams act through their colimit maps. Both commute with those
    legs and hence with the descended comparison by colimit uniqueness.
    The same formula for every integer n is compatible with the standard shift
    composition isomorphisms. Thus the statement specifies the canonical maps
    with the requested naturalities, rather than merely asserting existence of
    some isomorphism. Exact; no additional naturality hypothesis is needed.

Edge cases: T may be empty; M and N may be zero; presentations may have rank
zero; n and a may be negative, zero or positive. An empty indexing category is
excluded by filteredness in both the source and Lean. No extra nonemptiness of
T, nonzero rank, boundedness above, or constructibility of N is assumed. The
explicit universe u is arbitrary, the diagram lives in u+1, and every binder is
bound explicitly with no file-local notation, private definition or instance.

Independent searches: ran `msearch.py` LeanFinder with “Hom from constructible
module sheaves preserves filtered colimits of bounded below complexes”; it
returned generic condensed AB5/module-colimit facts, not this theorem. Ran
Loogle for `CategoryTheory.preadditiveCoyoneda`; its results confirm the existing
Hom functor and homological-sequence API, not continuity. Ran LeanSearch with
“Derived Hom of constructible sheaves commutes with filtered colimits of
uniformly bounded below complexes”; the service returned Internal Server Error,
recorded as unavailable, not negative evidence. Independently searched
`WeilConjectures`, `lean/Sheaf`, and Mathlib's homological algebra sources with
`ext.*filtered|filtered.*ext|constructible.*colimit|colimit.*constructible`.
The nearby constructible-colimit statements concern ordinary etale module
sheaves; they are not this pro-etale condensed derived continuity assertion.
The framework's TwoColimit paragraph is an informal input only. No duplicate
notion or exact existing theorem was found.

H5/H6/H8/H9: the module defines no new data and proves nothing; its only proof
is `sorry` on the named theorem. Both docstrings name the source and blueprint
node. I compared the seven numbered proof-plan steps with the node's seven
proof steps; all are present, including the canonical-map/naturality step.
The Lean record's statement agrees verbatim with the delivered signature.
No mathematical mismatch was found; I preserved the Lean file and node.
The only delivery change from this reading is this independent review section.

Second-reader validation: `scompile.py` compiled the delivered module cleanly
in 8.3 seconds, after individually compiling its side-framework imports.
The log confirms nice 19, two threads and a 60-second limit per file, with
no errors or warnings. A direct signature comparison returned exact equality;
no Lean line exceeds 100 characters. An initial invocation used a relative path
from the read-only checkout and failed before compilation; using the absolute
sandbox path corrected that invocation without changing any file.
