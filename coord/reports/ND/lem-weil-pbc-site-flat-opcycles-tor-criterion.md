## Worker report

The module `Sheaf.Algebra.Homology.SiteFlatOpcyclesTorCriterion` states
`SheafOfModules.isFlat_opcycles_of_universal_tensor_exactAt`. Its sole theorem
has proof `sorry`; no definition, axiom, or extra theorem is introduced.

Hypotheses and conclusion, clause by clause:

- Small site: `{C : Type u} [SmallCategory C] {J : GrothendieckTopology C}`.
  The coefficient and module universe is `u`; small-site sheafification and the
  locally bijective criterion are inferred, rather than additional hypotheses.
- Commutative structure sheaf: `O : Sheaf J CommRingCat.{u}`. The existing
  `sheafCompose J (forget₂ CommRingCat RingCat)` forgets commutativity only for
  the input type of the module category, retaining the given commutative sheaf
  for its canonical tensor product.
- Cochain complex of these module sheaves: `P : CochainComplex
  (ringedSiteModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ℤ`.
  This uses the recorded general-site category abbreviation, transparently equal
  to Mathlib's `SheafOfModules`, and Mathlib's integer cochain complex.
- Every term flat: `hflat : ∀ i : ℤ, IsFlat (R := O) (P.X i)` uses exactly the
  recorded exact-tensor-functor definition, including all integer degrees.
- Fixed arbitrary integer: `(n : ℤ)`.
- Every test sheaf: `∀ N : ringedSiteModules (...)`. It is concentrated in degree
  zero by `((CochainComplex.singleFunctor _ 0).obj N)`.
- Ordinary total tensor complex: `CochainComplex.mapBifunctor
  ((CochainComplex.singleFunctor _ 0).obj N) P
  (@curriedTensor _ _ (monoidalCategory O))`. This is the recorded direct-sum
  totalization of the tensor bicomplex, in the specified order `N ⊗ P`.
  The explicit monoidal argument avoids a file-local instance or a `let` in the
  theorem statement. KFlat supplies the already published zero-preservation
  instances needed by this existing totalization API; no K-flat hypothesis is used.
- Exactness in degree `n-1`: `.ExactAt (n - 1)` on that total complex. This is
  categorical exactness, equivalently zero cohomology sheaf, not exactness of
  global sections.
- Conclusion: `IsFlat (R := O) (P.opcycles n)`. Mathlib's `opcycles` is the
  cokernel of the incoming differential, as witnessed by `opcyclesIsCokernel`;
  for integer cochain complexes the incoming degree is `n - 1`. Thus this is
  precisely flatness of the node's quotient sheaf, with no truncation or bound.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`, recorded by
  `def-pc-cochain-complex-modules`, with chain maps as morphisms.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat`: `SheafOfModules.IsFlat`,
  recorded by `def-pc-flat-sheaf-modules`; exactness is finite limit and colimit
  preservation of the right tensor functor.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`,
  recorded by `def-pc-tensor-complex-sheaves`; its curried tensor is explicitly
  `SheafOfModules.monoidalCategory O`.
- `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`:
  `HomologicalComplex.Acyclic`, `ExactAt`, `opcycles`, and
  `opcyclesIsCokernel`; the exact-at-a-single-degree clause uses `ExactAt`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  recorded by `def-weil-sheaf-of-modules-category`; its full signature and the
  Mathlib `SheafOfModules` structure were read.

The stated proof dependencies are imported: TensorClosed supplies
`SheafOfModules.tensorClosed`; ModuleSheavesColimitsForgetful supplies
`CategoryTheory.moduleSheaves_colimits_forgetful`; EpiMono supplies
`CategoryTheory.Sheaf.isLocallySurjective_iff_epi'`; ExactSequence supplies the
recorded exact-sequence predicates. The abelian category infrastructure is
already publicly imported through RingedSiteModules and KFlat. The module
docstring includes all seven proof steps from the node, including the local
lifts, boundary correction, and passage from short exact sequences to exactness.

Edge cases checked before writing: all integers including `n = 0` and negative
`n` are admitted, without a lower or upper complex bound. The zero test sheaf
and zero complex are included. A complex concentrated in degree `n` satisfies
the hypothesis and has flat opcycles by the termwise flatness assumption. The
empty site and zero coefficient ring are included. No points, stalks, enough
points, global-section surjectivity, nonempty site, or boundedness is assumed.
Smallness is relative to the same chosen universe as the coefficient/module
category, the existing flat-sheaf interface's convention; `u` is arbitrary.

Searches for an existing exact statement:

- msearch leanfinder: “A complex of flat sheaves on a ringed site universally
  tensor exact in degree n minus one has flat opcycles in degree n”: eight hits,
  all ordinary-module tensor-exactness flatness criteria, no ringed-site statement.
- msearch loogle: `"opcycles", "flat"`: zero hits.
- msearch grep: `flat.*opcycles|opcycles.*flat`: zero Mathlib hits.
- msearch leansearch: “Flat opcycles from universal tensor exactness on a ringed
  site”: service unavailable (Internal Server Error); other searches completed.
- Source and project rg: `flat_opcycles_of_exactAt`, `flat.*opcycles`, and the
  item id. The item id has no existing declaration. The generic upstream
  `CategoryTheory.ObjectProperty.flat_opcycles_of_exactAt` was opened in
  `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`: it assumes a closed
  braided monoidal abelian category, uses categorical `ObjectProperty.flat` on
  just two terms and a termwise right tensor complex. It does not state this
  node's all-terms `SheafOfModules.IsFlat` criterion with the actual `N ⊗ P`
  totalization. Existing project uses are scheme or ordinary-ring specializations.
  No exact duplicate was found.

Source read: `literature/stacks-project/sites-cohomology.tex`,
`lemma-last-one-flat` (Tag 08G0), including its full proof. The node intentionally
extracts universal ordinary tensor exactness instead of the source's stronger
boundedness and Tor-amplitude premises; its complete seven-step local diagram
chase justifies this formulation. No statement correction or disputed clause.

Validation: only scompile.py on the server, nice 19, two threads, 60 seconds per
file. The explicit totalization coproduct search requires a documented
`synthInstance.maxHeartbeats` setting; the file still compiles well within the
unchanged 60 second limit. The first compile exhausted the default instance
search budget; increasing that search budget resolved it. No local compilation.


## Second reading by ND

I read the node, its source and the delivered Lean independently. No mismatch
was found; the module and node record are retained verbatim. This reading adds
only this report section.

Source checked: `sites-cohomology.tex`, Tag 08G0, `lemma-last-one-flat`,
including the preceding Tor-amplitude definition and the complete proof.
The source assumes bounded-above flat terms and Tor amplitude in an interval;
it uses these to obtain universal ordinary tensor exactness in degree a-1.
The present node explicitly extracts that criterion, with its own seven-step
local proof. It does not claim to restate the full source lemma. I checked the
extracted argument: tensor right exactness gives the cokernel sequence; the
cycle obstruction over N3 is removed by a lifted boundary; flatness of B and D
then makes Q tensor a monomorphism monic. Local lifts suffice at each step,
and separatedness descends the resulting zero section. No boundedness or
Tor-amplitude hypothesis is needed for this extracted argument.

Objects, hypotheses and conclusion, in the order written in the node:

- Small site: `{C : Type u} [SmallCategory C]` and
  `{J : GrothendieckTopology C}`. Verdict: the arbitrary small site, not an
  etale, scheme or point-bearing specialization. Smallness supplies the
  sheafification/abelian infrastructure rather than imposing an additional
  exactness or enough-points assumption.
- Commutative ring sheaf: `(O : Sheaf J CommRingCat.{u})`. Verdict: exact.
  `sheafCompose J (forget₂ CommRingCat RingCat)` passes precisely its underlying
  ring sheaf to the module category; it introduces no new coefficient object.
- Integer cochain complex of O-modules: `(P : CochainComplex
  (ringedSiteModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ℤ)`.
  Verdict: exact. I opened `RingedSiteModules.lean`: its abbreviation is exactly
  `SheafOfModules.{v} R`, with Mathlib's linear morphisms and abelian structure.
  Mathlib's `CochainComplex` is the complex shape `up`, so the differential
  goes from i to i+1.
- Flatness of every term: `hflat : ∀ i : ℤ, IsFlat (R := O) (P.X i)`.
  Verdict: exact, for all degrees. I opened the recorded `Flat.lean`:
  `IsFlat` is `exactFunctor _ _ (tensorRight F)` for the recorded monoidal
  structure, meaning preservation of finite limits and finite colimits.
- An arbitrary fixed integer: `(n : ℤ)`. Verdict: exact; no positivity or
  truncation condition.
- Every test O-module sheaf N: `hexact : ∀ N : ringedSiteModules (...)`.
  Verdict: every object in that same category, without a flatness hypothesis
  on N. `((CochainComplex.singleFunctor _ 0).obj N)` puts N in degree zero.
- Ordinary total tensor complex: `CochainComplex.mapBifunctor
  ((CochainComplex.singleFunctor _ 0).obj N) P
  (@curriedTensor _ _ (monoidalCategory O))`. Verdict: precisely Tot(N tensor P),
  not derived tensor. I opened Mathlib's Bifunctor and BifunctorShift sources:
  this is the direct-sum total of the bifunctor bicomplex. Only the p=0 row is
  nonzero, so the second differential has sign (-1)^0=1. The existing KFlat
  module supplies tensor zero-preservation instances, not an extra hypothesis.
- Exactness at degree n-1: `.ExactAt (n - 1)`. Verdict: exact. I opened
  `ShortComplex/HomologicalComplex.lean`: ExactAt is exactness of `K.sc i`,
  equivalent to zero homology by `exactAt_iff_isZero_homology`. This is
  exactness in the category of sheaves, not exactness on every section module.
- Conclusion: `IsFlat (R := O) (P.opcycles n)`. Verdict: exact. In the same
  Mathlib file `opcyclesIsCokernel` identifies this object with the cokernel
  of the incoming differential; `up` on integers has predecessor n-1.
  Thus the quotient is P^n/im(d^(n-1)), with flatness in the original category.

Dependency interfaces were opened, not inferred from their names: the five
statement-dependency records resolve respectively to `CochainComplex`,
`SheafOfModules.IsFlat`, `CochainComplex.mapBifunctor`,
`HomologicalComplex.Acyclic`/`ExactAt`, and `ringedSiteModules`.
For the proof imports I also read `tensorClosed` (tensor-Hom natural
bijections and symmetric monoidal closure), `moduleSheaves_colimits_forgetful`
(faithfulness and preservation of finite limits/colimits, with arbitrary site
and coefficient universes), and `Sheaf.isLocallySurjective_iff_epi'` (the
sheafification, concrete-forgetful and balanced assumptions hold here).
The exact-sequence and abelian notions are the recorded Mathlib notions.
There are no new nodes, dependency modules, or corrected statements in this
sandbox; the sole node difference against the supplied repository is `lean`.

Edge cases: n=0 and negative integers retain the same predecessor formula.
The zero test module and zero complex are included. An empty site is allowed;
no object, point, section, or nonzero ring is postulated. Zero rings and every
characteristic are allowed. A complex supported only at n has zero term in
n-1 and flat opcycles equal to its flat n-th term. There is no family index
binder needing nonemptiness. Universe u is arbitrary; site, coefficient and
module sizes use the existing flat-sheaf interface's common-universe
convention. A smaller site or coefficient can be regarded in a larger common
universe; there is no fixed universe ceiling or additional equality of two
independently introduced universe variables. Every variable and universe in
the signature is explicitly bound.

Independent searches, with different wording from the first reading:

- msearch leanfinder: "Universal tensor homology vanishing implies cokernel
  flatness for module sheaves" returned eight ordinary-module flatness and
  faithful-flatness criteria, no exact general-site statement.
- msearch loogle: `"cokernel", "flat"` returned zero hits.
- msearch grep: `cokernel.*[Ff]lat|[Ff]lat.*cokernel|[Ff]lat.*[Ee]xactAt`
  returned zero Mathlib hits.
- The same expression with rg on project `lean/Sheaf` and upstream
  `WeilConjectures` found specialized affine/scheme results and upstream
  `CategoryTheory.ObjectProperty.flat_opcycles_of_exactAt`. I opened its
  signature and proof in DerivedCategory/FlatModel. It uses categorical
  two-sided `ObjectProperty.flat`, flatness of two terms, and the termwise
  right tensor complex in a closed braided monoidal category. It is a useful
  proof tool, but does not have this node's hypothesis list, sheaf flatness
  predicate, or N[0] tensor-total hypothesis. Identifying these interfaces
  requires bridges, so it is not an exact existing-declaration replacement.

H5/H6/H8/H9: the delivered file contains one named theorem with whole proof
`sorry`, no new data definitions or axioms, no private or local notation or
instances, and source/blueprint docstrings. Its proof docstring follows all
seven node steps, including the two local lifts, the boundary correction,
and the factorization argument giving exactness of all exact pairs. Lines
respect the width limit. `lean.statement` was checked verbatim against the
file signature. No code repair or statement correction was necessary.

Validation: scompile.py compiled the delivered module successfully on the
server (5.3 seconds, nice 19, two threads, unchanged 60-second limit), with
no errors or warnings. Its required RingedSiteModules overlay also compiled.
