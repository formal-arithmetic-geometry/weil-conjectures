## Worker report

The module `Sheaf.AlgebraicGeometry.KoszulAffineDetection` states
`AlgebraicGeometry.isZero_of_koszul_powers_orthogonal`. Its single theorem has proof
`sorry`; no theorem is proved and no definition is added.

Hypothesis and clause correspondence:

- A commutative ring A and X = Spec(A): `(A : Type u) [CommRing A]`, with X written
  explicitly as `Spec (.of A)` everywhere. No Noetherian or characteristic restriction.
- A finite sequence f_1,...,f_r: `(r : ℕ) (f : Fin r → A)`.
- U = X minus V(f_1,...,f_r): `(U : (Spec (.of A)).Opens)` and
  `hU : U = ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i)`. The union of principal opens
  is exactly the complement of the common zero locus, including when r = 0.
- E in D_QCoh(O_X): `(E : schemeDerivedQCohCategory (Spec (.of A)))`.
  `E.obj` is its underlying object in the shared D(O_X).
- For every positive exponent tuple: `∀ (e : Fin r → ℕ), (∀ i, 0 < e i) → ...`.
  Exponents can differ independently; the statement is not restricted to diagonal powers.
- K_e is the bounded Koszul complex on these powers: the exact existing construction
  `ExteriorAlgebra.koszulComplex A r (fun i ↦ f i ^ e i)`, extended by
  `ComplexShape.embeddingDownNat` (degree j goes to -j), then mapped termwise by
  `tilde.functor (.of A)` and localized by `DerivedCategory.Q.obj`.
  Its terms are the sheaves of exterior powers of A^r, and its differential is the
  existing contraction differential. Exterior powers above r vanish and each term
  is finite free, so these are precisely the perfect objects described by the node;
  no arbitrary family, perfection hypothesis, or additional finiteness assumption
  substitutes for the actual Koszul complexes. The Koszul differential sign is the
  standard chain differential placed in nonpositive cochain degrees.
- E restricts to zero on U: `hres : IsZero
  ((SheafOfModules.overFunctor ... U).mapDerivedCategory.obj E.obj)`.
- Hom(K_e[n], E) = 0 for every integer n: `∀ n : ℤ, Subsingleton
  ((DerivedCategory.Q.obj ...)⟦n⟧ ⟶ E.obj)`. The Hom type has a zero element;
  subsingleton therefore says every morphism is zero.
- Conclusion E = 0: `IsZero E.obj`, the categorical zero-object property rather
  than equality with an implementation-dependent chosen zero.
- The global and open `HasDerivedCategory.{w}` binders are the localization
  structures required by the dependency definitions, using the same morphism
  universe w. They add no mathematical condition on A or E.

Dependencies and existing declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `Spec` specializes the first recorded dependency to the affine scheme.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedQCohCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedCategory`; read the complete signatures
  and docstrings, including their shared sheaf-module carrier.
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `Scheme.IsStrictlyPerfect`,
  `Scheme.IsPerfect`, `Scheme.perfectSubcategory`; read their complete signatures and
  docstrings. Imported as the recorded dependency module (it also supplies D_QCoh).
  Perfection is a property of the concrete Koszul construction, not an added hypothesis.
- `Sheaf.Paper.KoszulComplex`: `ExteriorAlgebra.koszulComplex`, and its named
  contraction/differential-square-zero prerequisites; full signatures and docstrings
  read. Its existing node `def-weil-pbc-koszul-complex` is added to stmt_deps because
  the original dependencies did not explicitly name the Koszul construction.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: `tilde.functor`, `tilde.map_zero`.
  Zero-map preservation is supplied explicitly from that existing lemma so the
  termwise complex uses the shared `SheafOfModules` category instance, with no
  additional derived-category instance on `Scheme.Modules`.
- Mathlib's `ComplexShape.embeddingDownNat`, `HomologicalComplex.extend`,
  `Functor.mapHomologicalComplex`, `DerivedCategory.Q`, integer shifts,
  `PrimeSpectrum.basicOpen`, and `SheafOfModules.overFunctor` are reused.

Source read: https://stacks.math.columbia.edu/tag/09IR (the local Stacks checkout
is absent). The affine supported-object paragraph of its proof is exactly the
node's assertion; its Koszul powers and cohomology argument agree with the node.
The declaration docstring carries all three proof steps and their named inputs.

Edge cases checked: r = 0 gives U empty and the Koszul complex A in degree zero,
so Hom vanishing in every shift detects every affine quasi-coherent cohomology
module. The zero ring gives the empty spectrum, and is allowed. If a generator
is a unit, U is all of X and restriction vanishing already forces E zero. All
f_i = 0 gives U empty and a Koszul complex with zero differential whose degree-zero
summand detects E. No positivity condition is imposed on r; only on exponent
entries. Unbounded E is allowed; no boundedness hypothesis is introduced.

Searches for an existing statement (2026-10-11):

- msearch.py leanfinder: "Koszul powers detect zero objects in the derived category
  of an affine scheme"; eight generic derived/K-projective hits, no match.
- msearch.py loogle: "Koszul, DerivedCategory"; zero hits, unknown Koszul identifier.
- msearch.py grep: "koszul|Koszul"; three Mathlib hits (regular-sequence TODO,
  unrelated Koszul connections, local-cohomology roadmap), no Koszul detection.
- msearch.py leansearch: "Koszul powers detect zero objects in an affine derived
  category"; unavailable, Internal Server Error (not treated as a negative result).
- rg in WeilConjectures: "koszul|Koszul"; monoidal signs and the projective-line
  short exact sequence, no affine sequence detection theorem. Search for the item
  id there found no declaration. Search for the proposed full declaration name
  in Mathlib, WeilConjectures and dag/lean_names_upstream.json found no collision.
- rg in lean/Sheaf: "koszul|Koszul"; found the existing finite-sequence complex
  in Paper/KoszulComplex.lean, used here; no detection theorem.
- DAG filename/text search and tools/blueprint_refs.py search "Koszul complex":
  found the existing ring-level Koszul node; no missing new notion is required,
  because the sheafified complex is expressed directly with existing operations.

No statement correction, disputed statement, new node, or dependency repair.
Server single-file compilation passed cleanly. `deliver2.py K1
lem-pc-koszul-affine-detection --no-push` printed OK: compilation and preflight
passed except for the independent second reading, which the second reader supplies.
Nothing was pushed.

## Second reading by K1

I independently read the base and sandbox node, the entire delivered Lean module,
all four statement-dependency nodes and their recorded declaration signatures,
Mathlib's Scheme, tilde, restriction and complex-embedding implementations.
The local Stacks checkout is absent. I fetched the upstream `perfect.tex` into
`scratchpad/perfect.tex` and read `situation-complex` and
`lemma-orthogonal-koszul-complex`, also checking Tags 08CZ, 09IR and 08E3 online:
https://stacks.math.columbia.edu/tag/08CZ and
https://stacks.math.columbia.edu/tag/09IR. The surrounding situation assumes only
a ring, a finite sequence, its spectrum and the union of principal opens.
The node isolates the supported-object detection step of the proof, rather than
restating the entire equivalence of Tag 09IR; that is the correct source step.

The node's objects, hypotheses and conclusion, matched individually:

1. A commutative ring A and X = Spec(A): `(A : Type u) [CommRing A]` and
   `Spec (.of A)` throughout. Verdict: exact. The recorded `Scheme` is the
   locally affine locally ringed space definition; Spec uses this scheme category.
2. An arbitrary finite sequence: `(r : ℕ) (f : Fin r → A)`. Verdict: exact,
   including length zero; no regular-sequence or nonzero-generator hypothesis.
3. The specified open complement of the common vanishing locus:
   `(U : (Spec (.of A)).Opens)` with
   `hU : U = ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i)`. Verdict: exact;
   the union is precisely X minus V of the generated ideal, not the intersection.
4. A tuple of positive exponents: `∀ (e : Fin r → ℕ), (∀ i, 0 < e i) →`.
   Verdict: exact. Independent entries are allowed, with no diagonal restriction.
5. The actual bounded perfect Koszul object K_e: the term
   `ExteriorAlgebra.koszulComplex A r (fun i ↦ f i ^ e i)`, extended with
   `ComplexShape.embeddingDownNat`, sheafified by `tilde.functor (.of A)`, and
   sent through `DerivedCategory.Q.obj`. Verdict: exact. I read
   `koszulBoundary`, `koszulComplex` and the Koszul dependency node: contraction
   by `Finsupp.linearCombination` on the free module `Fin r →₀ A` gives the
   ordinary exterior-power complex. The embedding sends degree j to -j;
   exterior powers above r vanish. Termwise tilde gives finite free sheaves,
   hence a perfect complex with quasi-coherent cohomology. Not separately
   packaging this object into the perfect/QCoh full subcategories changes no
   Hom: those categories are full. There is no arbitrary complex hypothesis.
6. E belongs to D_QCoh: `(E : schemeDerivedQCohCategory (Spec (.of A)))`.
   Verdict: exact. I read `schemeDerivedQCohProperty`: every integer cohomology
   sheaf is quasi-coherent; the category imposes no boundedness restriction.
7. E restricts to zero on U: `hres : IsZero
   ((SheafOfModules.overFunctor ... U).mapDerivedCategory.obj E.obj)`.
   Verdict: exact. `overFunctor` restricts to the localized open site over U,
   with the restricted structure sheaf. This is the shared restriction used
   in the recorded perfect-complex definition, not scheme inverse image.
8. All shifted Hom groups vanish: `∀ n : ℤ, Subsingleton (K_e⟦n⟧ ⟶ E.obj)`.
   Verdict: exact. These Hom types have zero morphisms, so Subsingleton means
   every map is zero. Hom is in D(O_X), with the same full-subcategory Hom.
9. Conclusion E = 0: `IsZero E.obj`. Verdict: exact up to the usual categorical
   meaning of zero; a full-subcategory object is zero exactly when its underlying
   derived object is zero.
10. The two `HasDerivedCategory.{w}` binders choose the global and open
    localizations. Verdict: necessary shared infrastructure from the dependency
    signatures, not extra geometric hypotheses. Both use the same w; u and w
    are declared explicitly and every binder is bound. No independent small
    universe of test objects makes the hypothesis vacuous.

Edge cases: for r = 0, the union is empty, the exponent function is uniquely
empty, positivity is vacuous, and the Koszul object is O_X in degree zero;
all its shifted Homs still detect E. The zero ring and empty spectrum are
allowed. E = 0 satisfies the hypotheses and conclusion. A unit generator
makes U = X; all zero generators make U empty with zero Koszul differential.
No characteristic, field, Noetherian, boundedness or positivity-of-r restriction
is introduced. Any ring universe u is allowed; derived morphism universe w is
shared by the two localization structures.

Independent searches (2026-10-11), using different formulations:

- `msearch.py leanfinder`: "Vanishing of maps from all shifted finite free Koszul
  complexes detects an object supported on a closed affine subset" returned
  eight general derived-category/projective/T-structure results, no match.
- `msearch.py loogle`: "IsZero (DerivedCategory _)" returned zero hits with
  unknown identifier IsZero; this is inconclusive, not a negative semantic result.
- `msearch.py grep`: "Koszul.*orthogonal|koszul.*detect|supported.*object"
  returned zero Mathlib hits.
- Direct rg on Mathlib, WeilConjectures and lean/Sheaf for Koszul/koszul and on
  their algebraic-geometry trees for orthogonal/detect-zero/isZero_of found
  only unrelated braidings, stalk detection, and the landed Koszul construction;
  no duplicate affine detection statement. I read and reused that construction.
- `tools/blueprint_refs.py search 'Koszul complex'` found the intrinsic completion
  blueprint node, not a duplicate detection statement. The existing DAG Koszul
  definition supplies the added dependency; no new definition node or dependency
  module is in this delivery.

Mismatch verdict: none. I changed no Lean signature, definition, node statement
or proof. The docstring includes the source and blueprint marker and all three
node proof steps: compatible diagonal Koszul triangles, passage to cohomology
on U via the colimit, then affine derived equivalence. There is one named theorem
with `sorry`, no new definition, no hollow data or proved theorem. The node's
`lean.statement` is verbatim the file signature. The server single-file compile
passed in 5.4 seconds with exit code 0 and no warnings.
