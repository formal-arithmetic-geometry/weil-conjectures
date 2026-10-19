## Worker report

The module states `AlgebraicGeometry.isConstructibleEtaleModuleSheaf_affineLine_shriek`.
Its sole theorem has proof `sorry`; no definition or proof is added.

Clause-by-clause correspondence:
- Finite commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
- Affine base `Y = Spec A`: `(Y : Scheme.{u}) [IsAffine Y]`. This is the equivalent
  intrinsic presentation of an arbitrary affine scheme, allowing every commutative ring A.
- Relative affine line: `AffineSpace (ULift.{u} (Fin 1)) Y`. The lifted singleton indexes
  exactly one coordinate, in the scheme's universe. Its structural projection is
  `AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y`.
- The sheaf F has values in `ModuleCat.{u + 1} Λ` on that affine line's small etale site.
  `hF : Scheme.IsConstructibleEtaleModuleSheaf F` is the recorded constructibility predicate.
- Every compactification: arbitrary `c : Compactification` of this projection. Its fields
  supply the open immersion, proper morphism and factorization equality. Quasi-compactness
  of the open immersion follows from quasi-compactness of the affine-line projection via
  `Compactification.quasiCompact_openImmersion_iff`; this does not enlarge the class of c.
  The affine base and affine line are quasi-compact and quasi-separated; the projection
  is separated of finite type. The introductory general h, T, B sets notation rather than
  adding a second assertion to this specialized theorem.
- F in degree zero: `DerivedCategory.Plus.singleFunctor _ 0` applied to F.
- `Ra_!^c`: `Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat Λ) c`,
  the upstream bounded-below exact extension by zero followed by right derived pushforward.
- Every integer degree: `(q : ℤ)` and `DerivedCategory.Plus.homologyFunctor _ q`.
- Conclusion: the resulting module sheaf satisfies the same recorded
  `Scheme.IsConstructibleEtaleModuleSheaf` predicate on Y.

Dependency declarations read and used:
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-weil-pbc-scheme-conventions`: `None`, `None`. Convention-only record: no declaration or import exists.
- `def-weil-pbc-projection-compactification`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`. Use its bounded-below companion `rightDerivedLowerShriekOfCompactificationPlus` in the same module.
- `def-weil-pbc-extension-by-zero`: `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`, `AlgebraicGeometry.Etale.openImmersionLowerShriek`.
- `def-weil-pbc-direct-image`: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, `AlgebraicGeometry.Etale.lowerStar`.
- `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories`, `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`. Use its documented existing `DerivedCategory.Plus` encoding and the Mathlib single and homology functors.
- `def-nagata-relative-affine-space`: `Mathlib.AlgebraicGeometry.AffineSpace`, `AlgebraicGeometry.AffineSpace`.
- `def-weil-pbc-etale-constructible-sheaf`: `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`, `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`.

Every proof dependency with a recorded module is imported without `public` unless its
module is already a statement import. Dependencies not yet stated contribute the natural
language proof plan in the docstring but have no module to import. The upstream lower
shriek declaration is available in the slopmaster2 source despite the older DAG record
labeling its branch master.

Edge cases checked: the empty affine scheme (including Spec of the zero ring), zero sheaf,
zero coefficient ring, negative q and q = 0 are all admitted. No nonempty, Noetherian-base,
positive-degree, characteristic or invertibility assumption is imposed. Finite coefficients
are Noetherian and torsion as required by Tag 0GKZ; no extra hypothesis is needed. The lifted
singleton is in Type u; the coefficients and module carriers use the established Type (u+1)
encoding without a finite or countable universe restriction.

Searches for reuse:
- msearch.py leanfinder: "Compact support etale cohomology of a constructible finite module
  sheaf on a relative affine line is constructible" returned eight hits on constructible
  images, local functions and limits. None concerns etale compact support.
- msearch.py loogle: `"shriek", "constructible"` returned zero hits.
- msearch.py grep: `shriek.*constructible|constructible.*shriek` returned zero hits.
- rg over upstream WeilConjectures and project lean/Sheaf:
  `affine.*[Cc]onstructible|[Cc]onstructible.*affine|` followed by the item id. Hits concern
  free etale sheaves, constructible stratifications, or pro-etale adic direct images;
  none states this compact-support assertion. No occurrence of this item's id was found.
- Read upstream `Etale.Derived.LowerShriek`, `Derived.Coefficients`, `UpperLowerStar.Defs`,
  `LowerShriek.OpenImmersion.Defs`, `Compactification.Defs`, and Mathlib AffineSpace and
  DerivedCategory.Plus, plus both recorded project definition modules.
- Read the complete source lemma and proof at literature/stacks-project/more-etale.tex,
  label lemma-constructible-shriek-rel-dim-1 (Tag 0GKZ).

No new nodes, dependency modules, statement correction or disputed statement.

## Second reading by NZ

Read the complete statement and all five proof steps of the item, its eight statement
dependency nodes and their recorded signatures, and Stacks more-etale.tex,
lemma-constructible-shriek-rel-dim-1 (Tag 0GKZ), including the complete proof.
The source assumes an affine base, a Noetherian coefficient ring, and a constructible
torsion module sheaf. The node explicitly takes its finite commutative ring specialization:
a finite ring is Noetherian and its positive additive exponent kills every module.
Thus no characteristic-invertibility or Noetherian-base assumption is missing.

Independent object/hypothesis/conclusion checklist (H3):

1. Coefficients: `Λ : Type (u + 1)` with `[CommRing Λ] [Finite Λ]` renders precisely
   the finite commutative ring. Verdict: exact, including the zero ring.
2. Base: `(Y : Scheme.{u}) [IsAffine Y]` renders `Y = Spec A` for arbitrary
   commutative A up to scheme isomorphism. It introduces no field, finiteness, or
   Noetherian restriction on A. Verdict: exact intrinsic affine presentation.
3. Relative affine line and projection: `AffineSpace (ULift.{u} (Fin 1)) Y` and
   `AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y`. Read Mathlib AffineSpace.lean:
   the construction is the base change of Spec of the polynomial ring over the integers,
   and `AffineSpace.over` selects its first projection. The index is a singleton in
   Type u. Verdict: the specified line, not a chosen alternative morphism.
4. Sheaf and constructibility: the explicit `Sheaf ...smallEtaleTopology
   (ModuleCat.{u + 1} Λ)` binder and `hF : Scheme.IsConstructibleEtaleModuleSheaf F`.
   Read IsConstructibleEtaleModuleSheaf.lean: it uses finite locally closed scheme
   stratifications with constructible parts, inverse image via `Etale.upperStar`,
   and etale trivializations by finite constant modules, exactly the dependency node.
   Verdict: correct module-sheaf notion; no underlying-set-only substitute.
5. Compactification: arbitrary `(c : Compactification (... ↘ Y))` supplies a scheme,
   open immersion, proper projection, and their factorization. Read upstream
   Compactification.Defs: it does not itself demand a quasi-compact open immersion,
   but `quasiCompact_openImmersion_iff` identifies that condition with quasi-compactness
   of the original morphism. The affine-line projection is affine, hence quasi-compact.
   Thus this quantifies over exactly the compactifications in the node. Verdict: exact.
6. Degree-zero input and bounded-below category: `DerivedCategory.Plus.singleFunctor
   ... 0` applied to F. Read Mathlib DerivedCategory/Plus.lean and the recorded
   DerivedCategories module: the single functor places F in cochain degree zero and
   Plus is the bounded-below derived category of this same sheaf category. Verdict: exact.
7. Compact support: `Etale.rightDerivedLowerShriekOfCompactificationPlus
   (ModuleCat.{u + 1} Λ) c`. Read its upstream definition, its unbounded companion,
   `Etale.lowerStar`, and `Etale.openImmersionLowerShriek`: it is the functor induced
   by exact extension by zero followed by bounded-below derived direct image,
   `D+(j_!) ⋙ R+(p_*)`. Verdict: precisely Rp_* j_!, with the prescribed coefficients.
8. Degrees and conclusion: arbitrary `(q : ℤ)`, `DerivedCategory.Plus.homologyFunctor
   ... q`, followed by `Scheme.IsConstructibleEtaleModuleSheaf`. Read the homology
   functor definition (inclusion followed by ordinary derived homology).
   Verdict: all and only the requested cohomology sheaves are asserted constructible.
   Quantifying c before q instead of q before c commutes two universal quantifiers.
9. The initial general h:T→B paragraph only defines notation for this specialized
   assertion; it does not request a second theorem for arbitrary h. All its required
   qcqs and separated finite-type conditions hold for the affine-line projection.

Edge cases: empty affine base (Spec of the zero ring), zero sheaf, and zero coefficient
ring remain allowed. All integer degrees, including negative q and q=0, are included.
No characteristic, invertibility, or nonemptiness assumption occurs. No family or n
is quantified: the dimension here is exactly one; empty index sets and n=0 are not
cases of this node. The finite coefficient ring can be lifted to Type (u+1) and any
finite stalk module fits that universe; the lifted coordinate singleton fits Type u.
The universe u is explicit and arbitrary, with no free variables or hidden instances.

Independent H4 searches:
- msearch leanfinder: "Higher direct images with proper support of finite constructible
  etale modules along polynomial affine line projection" returned eight hits on affine
  limits, scheme maps, and constructible subsets; their signatures do not state this result.
- msearch loogle: `"constructible", "cohomology"` returned zero hits.
- msearch grep: `properSupport|compactlySupported.*[Cc]onstructible|[Cc]onstructible.*[Ss]hriek`
  returned zero hits.
- Independently ran rg on Mathlib, upstream WeilConjectures, and project lean/Sheaf
  with `affineLine_shriek|properSupport|compactlySupported.*[Cc]onstructible|
  [Cc]onstructible.*[Ss]hriek|[Ss]hriek.*[Cc]onstructible`.
  Unlike the worker report's broad claim that matches were only unrelated constructions,
  this finds a close upstream result, `Etale.boundedConstructible_rightDerivedLowerShriek`
  in Derived/Finiteness/DirectImage.lean. Opened its actual signature and docstring:
  it requires a base field, locally finite-type structure maps, and
  `HasInvertibleExponent Λ X`, and concerns the chosen compactification and bounded
  constructible complexes. Those hypotheses exclude the arbitrary affine bases and
  arbitrary characteristic of this node. It is not an existing declaration of this
  statement. Other matches are pro-etale/adic or O-module proper-support results,
  ordinary extension by zero, or callers of that restricted finiteness theorem.

H5/H6/H8/H9: one public theorem with whole proof `sorry`, no new definition, instance,
private abbreviation, file-local notation, or proof. Its source/blueprint docstrings
are present, and its five numbered proof paragraphs carry all five node proof steps.
Statement imports use the recorded dependency modules; proof-only imports correspond
to the proof dependencies that already have modules. No new nodes, dependency modules,
statement correction, or disputed statement requires further review. Checked the node's
lean.statement verbatim against the complete signature and all lines against 100 characters.

Mismatches and changes: no Lean or node mismatch found; preserved both unchanged.
Corrected the reuse-search assessment above by explicitly inspecting and rejecting the
close but restricted upstream finiteness theorem. Added this independent second reading.
Validation: scompile.py compiled the delivered module cleanly on the server in 1.6 seconds,
nice 19, two threads, 60-second per-file limit, with no warnings or errors.
