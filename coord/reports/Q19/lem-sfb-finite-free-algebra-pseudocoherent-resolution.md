## Worker report

The module Sheaf.RingTheory.FiniteFreeAlgebraPseudoCoherentResolution states
DerivedCategory.exists_finite_free_resolution_of_restrictScalars_pseudoCoherent,
with exactly one postponed proof and no new definitions. Source read in full:
literature/stacks-project/perfect.tex, Tag 0CSF,
lemma-pseudo-coherent-over-algebra, including its descending cone construction.
The accepted stage-1 split is preserved byte for byte outside the added lean record.
The preceding worker's stage-1 refusal is inapplicable: brief-stage2 section 0
explicitly permits this stage-2 attachment, and coord/queue.tsv assigns stage 2.

Hypotheses and conclusions, clause by clause:

- A commutative unital base ring: `(A : Type u) [CommRing A]`.
- A possibly noncommutative unital algebra, with central base image:
  `(B : Type v) [Ring B] [Algebra A B]`. Mathlib's Algebra includes
  commutes', the centrality condition; there is no CommRing B hypothesis.
- B finite free over A: `[Module.Free A B] [Module.Finite A B]`.
  Over a commutative ring these say exactly that B admits a finite basis,
  equivalently an isomorphism with a finite direct sum of copies of A.
- M in the unbounded derived category of right B-modules:
  `M : DerivedCategory (ModuleCat.{max u v t} Bᵐᵒᵖ)`.
  Left modules over the opposite ring are precisely right B-modules.
  The two HasDerivedCategory binders choose the localization sizes separately
  (wA and wB); they impose no ring-theoretic or boundedness hypothesis.
- The underlying A-object is pseudo-coherent: hM uses the dependency's exact
  `DerivedCategory.IsPseudoCoherent` on the image of M under the localization
  of `ModuleCat.restrictScalars (algebraMap A Bᵐᵒᵖ)`.
  `MulOpposite.instAlgebra` constructs the central map canonically, with
  `algebraMap A Bᵐᵒᵖ a = MulOpposite.op (algebraMap A B a)`.
  `mapHomologicalComplexUpToQuasiIso (ComplexShape.up ℤ)` is Mathlib's canonical
  induced functor on this localization, with its Factors isomorphism to
  termwise restriction. It is the implementation underlying mapDerivedCategory;
  using the general interface avoids that wrapper's finite-limit requirement
  for which Mathlib's automatic restriction instance assumes commutative rings.
- A cochain complex F of right B-modules: existential
  `F : CochainComplex (ModuleCat.{max u v t} Bᵐᵒᵖ) ℤ`.
- Bounded above: `∃ b : ℤ, F.IsStrictlyLE b`.
- Every term finite free as a right B-module:
  `∀ i : ℤ, Module.Free Bᵐᵒᵖ (F.X i) ∧ Module.Finite Bᵐᵒᵖ (F.X i)`.
- Its image is isomorphic to M in the derived category:
  `Nonempty (Q.obj F ≅ M)`. This does not require a chosen representative of M
  or a chain map to an arbitrary representative, and asserts exactly the node.

The module universe `max u v t` includes both rings and an arbitrary further
size. The base and algebra may occupy different universes; no site or ring
universes are equated. The derived category's morphism universes are independent.

Dependency declarations read and used:

- def-weil-abstract-derived-category: DerivedCategory, HasDerivedCategory and
  DerivedCategory.Q in Mathlib.Algebra.Homology.DerivedCategory.Basic.
- def-pc-ring-pseudo-coherent-complex: DerivedCategory.IsPseudoCoherent in
  WeilConjectures.RingTheory.RingPseudoCoherent (full defining body read).
- Proof imports: DerivedCategory.IsMPseudoCoherent in
  WeilConjectures.RingTheory.MPseudoCoherent;
  CategoryTheory.isMPseudoCoherent_cone in
  WeilConjectures.RingTheory.ConePseudoCoherent;
  DerivedCategory.finite_homology_of_isMPseudoCoherent in
  WeilConjectures.RingTheory.FiniteHomologyOfMPseudoCoherent; and
  DerivedCategory.HomologySequence in
  Mathlib.Algebra.Homology.DerivedCategory.HomologySequence.
- Canonical restriction: ModuleCat.restrictScalars from
  Mathlib.Algebra.Category.ModuleCat.ChangeOfRings, reexported by
  WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ModuleCat; the latter's
  ModuleCat.preservesHomology_restrictScalars works for arbitrary rings.
  CategoryTheory.Functor.mapHomologicalComplexUpToQuasiIso in
  Mathlib.Algebra.Homology.Localization requires exactly this homology preservation.
- Opposite central algebra: MulOpposite.instAlgebra and algebraMap_apply in
  Mathlib.Algebra.Algebra.Opposite.

Edge cases checked before writing: A is the zero ring; B has rank zero (then
B is the zero ring); M is zero or acyclic; empty generator families; B=A;
B a matrix algebra, hence genuinely noncommutative; complexes unbounded below.
Nothing assumes Nontrivial, positive rank, a nonzero cohomology group,
Noetherianity, boundedness below, or a finite projective dimension.
The source's erroneous 'smallest index' sentence is already corrected in the
accepted proof split by taking an upper cohomology bound. No statement correction
is needed and no STATEMENT-DISPUTED fault remains.

Searches made with the prescribed msearch.py wrapper (raw results retained in
searches.jsonl in the sandbox):

- leanfinder: 'Pseudo coherent underlying complex over a commutative ring has
  bounded above finite free resolution over a finite free noncommutative algebra'.
  Eight hits, including HasProjectiveDimensionLE, IsKProjective and generic
  projective/injective dimension notions; none gives this statement.
- loogle: '"PseudoCoherent"'. Zero hits.
- grep: 'pseudo.?coherent|finite.free.*resolution'. Zero Mathlib hits.
- leansearch: 'An object of the derived category of right modules over a finite
  free algebra whose restriction is pseudo-coherent admits a bounded above finite
  free resolution'. Eight hits on the derived localization, fractions, bounded
  representative lemmas, and generic projective resolutions; no exact match.
- rg of lean/WeilConjectures and lean/Sheaf for pseudo-coherence and finite-free
  resolutions found the existing commutative-base definitions and unrelated
  commutative or Noetherian resolution results. Targeted searches for
  `0CSF|lemma-pseudo-coherent-over-algebra|finite.free.algebra.*pseudo|pseudo.*finite.free.algebra`
  found no existing module; the item's id has no occurrence in WeilConjectures.
  The proposed full declaration name is absent in both project roots and Mathlib.

Validation: scompile.py compiled both the isolated sandbox module and the named
library module, each in 1.2 seconds, with no errors or unexpected warnings.
The docstring carries all six accepted proof steps, including cone signs,
finite obstruction generators, and degreewise stabilization.

## Second reading by Q19

A separate rereading in this worker turn compared the live node and final module
against Tag 0CSF. There is no claim of a second agent: the dispatcher prohibits
starting agents; the maintainer independently reviews this delivery.
All the hypotheses and conclusions were matched as listed above. In particular,
B retains Ring rather than CommRing, the module category uses Bᵐᵒᵖ in both the
input and witness, the restriction uses the canonical opposite algebra map,
and the conclusion quantifies all integer degrees with a single upper bound.
The only interface issue found in compilation was that mapDerivedCategory
requested a finite-limit instance unavailable for a noncommutative scalar ring.
It was replaced by the existing general localization functor using the existing
upstream homology-preservation instance. This changes no mathematical assumption,
adds no helper, and is definitionally the same localization construction.
No node fields outside lean changed and no dependency repair or new node is needed.
