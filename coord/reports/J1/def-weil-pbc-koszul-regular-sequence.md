## Worker report

The module `Sheaf.RingTheory.KoszulRegularSequence` defines all four predicates of
`def-weil-pbc-koszul-regular-sequence`, with full definitions and no proofs or sorries.
The source is Stacks Definition 15.31.1, Tag 062E, checked at
https://stacks.math.columbia.edu/tag/062E (the local literature source is absent).
The node agrees clause by clause with this source; no correction is needed.

Hypotheses and objects:
- A commutative ring is `{R : Type u} [CommRing R]`.
- A nonnegative length is `{r : ℕ}` and its ordered sequence is `(f : Fin r → R)`.
  Zero-based indexing represents the node's f₁,...,fᵣ without changing their order.
- An arbitrary module is `(M : Type v) [AddCommGroup M] [Module R M]`;
  `v` is independent of `u`, so modules of any universe are permitted.
- `ExteriorAlgebra.koszulComplex R r f` is precisely the dependency's complex.
- `ExteriorAlgebra.koszulComplexTensor R r f M` is the already-defined termwise
  tensor product of that complex, with `koszulBoundary.hom.rTensor M` differentials.
- `.homology i` is `HomologicalComplex.homology`, identified with the kernel
  modulo the image by `ShortComplex.moduleCatHomologyIso`.

Clause correspondence:
1. `RingTheory.Sequence.IsKoszulRegularOn M f` is
   `∀ i : ℕ, i ≠ 0 → IsZero ((ExteriorAlgebra.koszulComplexTensor R r f M).homology i)`.
2. `RingTheory.Sequence.IsH1RegularOn M f` is
   `IsZero ((ExteriorAlgebra.koszulComplexTensor R r f M).homology 1)`.
3. `RingTheory.Sequence.IsKoszulRegular f` is
   `∀ i : ℕ, i ≠ 0 → IsZero ((ExteriorAlgebra.koszulComplex R r f).homology i)`.
4. `RingTheory.Sequence.IsH1Regular f` is
   `IsZero ((ExteriorAlgebra.koszulComplex R r f).homology 1)`.
Here `IsZero` is applied to objects of `ModuleCat R`, so means the homology module
vanishes. It is not an `IsZero` predicate on a bare type. No proper-ideal or nonzero-module
condition is imposed: neither occurs in 062E.

Dependencies read and used:
- `Sheaf.Paper.KoszulComplex`, `ExteriorAlgebra.koszulComplex` and
  `ExteriorAlgebra.koszulComplexTensor` (both recorded on the Koszul-complex node).
- `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`,
  `HomologicalComplex.homology`, imported transitively by the Koszul module.
- `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`,
  `ShortComplex.moduleCatHomologyIso`: read its full signature and its explicit
  `moduleCatLeftHomologyData.H = ker g / range moduleCatToCycles` construction.
- The tensor dependency is the general `CategoryTheory.Functor.mapHomologicalComplex`
  (`Mathlib.Algebra.Homology.Additive`) specialized to `MonoidalCategory.tensorRight`.
  Its signature, terms and differentials and the ModuleCat monoidal implementation
  were read. The Koszul dependency already supplies this specialized construction as
  `koszulComplexTensor`, using `rTensor` directly, also supporting independent module
  universes. We reuse that declaration instead of defining a second tensor complex.
  No dependency record needs repair: the general tensor functor accurately describes
  the notion, and the existing Koszul tensor construction gives the required instance.

Edge cases checked before writing:
- `r = 0`: `Fin 0 → R` is allowed; the empty complex has only degree-zero homology,
  so all four predicates hold (also for a zero ring or zero module).
- `M = 0`: the tensor complex is zero, so both module predicates hold.
- `r = 1`: positive homology is concentrated in degree one, the kernel of scalar
  multiplication by `f 0`; the predicates do not demand nonvanishing of H₀.
- A unit in the sequence gives vanishing positive homology and is not excluded.
- Negative indices: the recorded Koszul complex is indexed by ℕ; the homology
  dependency explicitly permits extension by zero outside these degrees. Negative
  homology is automatically zero, so quantifying over nonzero ℕ says exactly the
  node's quantification over nonzero integers. No boundedness hypothesis is added.
- `i > r`: these zero terms remain covered by the universal quantifier.
- No Noetherian, local, nontriviality or characteristic assumption is introduced.

Searches for an existing notion (2026-10-11):
- msearch.py leanfinder: "Koszul regular sequence means Koszul homology vanishes
  in every nonzero degree; H1 regular sequence". Eight hits on ordinary/weakly regular
  sequences (`RingTheory.Sequence.IsRegular`, `IsWeaklyRegular` and associated lemmas),
  no definition of any of these four predicates.
- msearch.py loogle: "IsKoszulRegular, IsH1Regular". Zero hits; unknown identifier
  `IsKoszulRegular`.
- msearch.py grep: "koszul|Koszul|H1Regular" in RingTheory. One hit,
  Regular/RegularSequence.lean:21, explicitly listing Koszul/H₁ regularity as TODO.
- rg for `Koszul|koszul|IsH1Regular|IsKoszulRegular` in `lean/Sheaf` and upstream
  `WeilConjectures`: the existing Koszul construction, its differential and unrelated
  projective-line Koszul exact sequence and sign rules; none defines the predicates.
- rg for the item id in upstream `WeilConjectures`: no hits.
- rg for all four proposed names in `dag/lean_names_upstream.json`, Mathlib,
  `WeilConjectures` and `lean/Sheaf`: no hits, so no declaration name collision.

No new nodes, dependency modules, statement disputes or statement corrections.


## Second reading by J1

Independent reading of the node copy, its three dependency nodes and their actual
Lean declarations, and the complete sandbox module. The local Stacks .tex is absent;
I read the upstream `more-algebra.tex`, label
`definition-koszul-regular-sequence`, including the preceding section introduction,
and checked Tag 062E at https://stacks.math.columbia.edu/tag/062E.
It introduces only a ring, a nonnegative sequence length, its elements, and a module;
there is no local, Noetherian, finite-module, proper-ideal or characteristic assumption.
The commutative-ring convention is the node's explicit convention.

Object/hypothesis/clause checklist (all verdicts: exact):
- Ring R: `{R : Type u} [CommRing R]`, arbitrary commutative ring, including zero rings.
- Length r >= 0: `{r : ℕ}`; every permitted length, including zero.
- Ordered elements f_1,...,f_r: `(f : Fin r → R)`, translating i to i-1.
  This introduces no distinctness, nonzero, or proper-ideal requirement.
- Module M: `(M : Type v) [AddCommGroup M] [Module R M]` in the two On predicates;
  it is arbitrary, not finite or nonzero. The two ring predicates correctly omit M.
- Koszul complex K: `ExteriorAlgebra.koszulComplex R r f`, from the recorded
  `Sheaf.Paper.KoszulComplex`. I read its body: exterior powers of `Fin r →₀ R`,
  with boundary the codomain restriction of contraction by
  `Finsupp.linearCombination R f`. It is the dependency's complex, not a substitute.
- Tensor complex: `ExteriorAlgebra.koszulComplexTensor R r f M`. Its body has terms
  `⋀[R]^n (Fin r →₀ R) ⊗[R] M`, and boundaries `(koszulBoundary ...).rTensor M`.
  I also read `Functor.mapHomologicalComplex` in Mathlib/Additive.lean and
  ModuleCat's `tensorObj` and `whiskerRight` in Monoidal/Basic.lean: they describe
  exactly these terms and maps. Reusing the dependency's specialized construction
  avoids a private tensor-complex definition and allows different carrier universes.
- Homology H_i: `.homology i`. I read `HomologicalComplex.homology` and
  `ShortComplex.moduleCatHomologyIso`, including `moduleCatLeftHomologyData`:
  the latter is the kernel modulo the range of the incoming map to cycles.
  `IsZero` is on a ModuleCat object, so expresses precisely a zero homology module.
- Clause (1): `IsKoszulRegularOn M f` is `∀ i : ℕ, i ≠ 0 → IsZero
  ((ExteriorAlgebra.koszulComplexTensor R r f M).homology i)`.
- Clause (2): `IsH1RegularOn M f` is `IsZero
  ((ExteriorAlgebra.koszulComplexTensor R r f M).homology 1)`.
- Clause (3): `IsKoszulRegular f` is `∀ i : ℕ, i ≠ 0 → IsZero
  ((ExteriorAlgebra.koszulComplex R r f).homology i)`.
- Clause (4): `IsH1Regular f` is `IsZero
  ((ExteriorAlgebra.koszulComplex R r f).homology 1)`.
There are no reordered mathematical quantifiers or added hypotheses. The source's
negative degrees are zero; the Koszul dependency is indexed by ℕ with precisely
this extension convention. Thus all nonzero integer degrees reduce to positive
natural degrees, without weakening either universal clause.

Edge cases: `r = 0` admits the unique empty sequence, with all positive exterior
powers zero. Zero modules and zero rings are allowed and have zero positive
homology. For length one the positive homology condition is the kernel of
multiplication by the single element, and does not impose any condition on H_0.
Units are allowed. Degrees above r are still quantified over and have zero terms.
All characteristics are allowed. Both u and v are bound and independent; the tensor
complex lives in `ModuleCat.{max u v} R`. Empty schemes are not objects of this
ring/module definition. No universe or variable is left unbound.

Independent searches (2026-10-11), using alternative wording:
- msearch.py leanfinder: "vanishing of positive homology of the exterior contraction
  complex defines regularity"; eight ordinary regular/weakly regular sequence hits,
  no predicate on Koszul homology.
- msearch.py loogle: `"H1Regular"`; zero hits.
- msearch.py grep: `H.?1.?regular|Koszul.regular|IsH1Regular|IsKoszulRegular`;
  only Mathlib/RingTheory/Regular/RegularSequence.lean:21, which lists the notions
  as TODO.
- Direct rg of `h.?1.?regular|koszul.?regular|positive.*homology|homology.*vanish`
  in Mathlib's regular-sequence files, upstream WeilConjectures and project
  lean/Sheaf: ordinary regularity and unrelated vanishing results only; no definition
  of these four predicates. Direct rg of all four proposed declaration names in
  Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: no hits.

No mismatches found; no Lean or node changes. No new nodes, dependency modules,
statement correction or disputed statement is present. The definitions have full
bodies and no sorry, and this delivery proves nothing. Each declaration's docstring
names 062E and the correct blueprint id; no proof narrative is needed for this
pure definition node (its proof list is empty). The single import is used, the
namespace has no Sheaf prefix, and line lengths satisfy the convention. The node's
lean.statement is verbatim the primary declaration signature, stopping before :=.
The prescribed scompile.py run compiled the module cleanly, exit code 0, with no
warnings. Only this second-reading report was added.
