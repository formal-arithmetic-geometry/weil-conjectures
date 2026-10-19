## Worker report

The module `Sheaf.RingTheory.WeakEtaleRefinement` constructs the refinement in
`def-weil-pbc-weak-etale-refinement`, using the published principal-partition strict cover
and retained localization. All declarations are actual data. There are no theorems,
no new sorries, no new nodes, no dependency repairs, and no statement correction.
The node copy changes only `lean`.

Hypotheses and clauses, in statement order:

- The commutative base ring is `(A : Type u) [CommRing A]`; the commutative
  algebra is `(B : Type v) [CommRing B] [Algebra A B]`. All section binders and
  universes are explicit. The main `algebra` additionally takes
  `(_hweak : Algebra.WeaklyEtale A B)`, retaining the node's weak-etaleness
  hypothesis. This hypothesis is unnecessary for the raw construction itself;
  the later refinement properties use it. There is no finite-presentation,
  nonzero-ring, or faithful-flatness assumption on B.
- `C = C_A` is exactly `PrincipalWLocalization.StrictWCover.algebra A`, with
  its recorded A-algebra instance. No strict cover is chosen independently.
- The w-locality assertion explaining closedness is supplied by
  `PrincipalWLocalization.StrictWCover.properties A`, imported from the
  recorded lemma module. Its third conjunct is `IsWLocalRing C`, which yields
  `WLocalSpace (PrimeSpectrum C)` and hence closedness of `closedPoints`.
  This contextual fact is not made an additional input to the construction.
- `J` is `closedIdeal A`, namely `PrimeSpectrum.vanishingIdeal (closedPoints
  (PrimeSpectrum C))`. The definition of `vanishingIdeal` is the intersection
  of the ideals of all points in this set. Mathlib identifies closed prime-spectrum
  points with maximal ideals. Thus this is precisely the intersection in the node,
  a radical ideal; the strict-cover lemma makes its zero locus the closed-point set.
- `D₀ = B ⊗[A] C` is `tensor A B`, bundled only to expose its commutative ring.
  The tensor product uses the existing A-algebra structures.
- `c ↦ 1 ⊗ c` is `coverToTensor A B`, the existing
  `Algebra.TensorProduct.includeRight` viewed as a ring homomorphism.
- `K = JD₀` is `extendedIdeal A B`, namely
  `(closedIdeal A).map (coverToTensor A B)`. `Ideal.map` is the ideal generated
  by the image, not the mere set image.
- `B' = (D₀)_[V(K)]` is `retainedAlgebra A B`, using the recorded
  `PrincipalWLocalization.Retained.algebra` on
  `PrimeSpectrum.zeroLocus (extendedIdeal A B : Set (tensor A B))`.
  `PrimeSpectrum.isClosed_zeroLocus _` supplies the required closedness.
  The underlying ring is the exact retained colimit, not an ordinary localization.
- The canonical `D₀ → B'` is `tensorToRefinement A B`: the composite
  `D₀ → D₀^w → B'`. The second arrow is the structural algebra map of the
  recorded retained localization (which is bundled over D₀^w).
- The B-algebra structure is the one in `algebra A B hweak`.
  Its ring map `structuralMap A B` composes the existing
  `Algebra.TensorProduct.includeLeftRingHom` (`b ↦ b ⊗ 1`) with the preceding
  canonical map. `RingHom.toAlgebra` equips this ring with precisely that map.
- The C-algebra structure on that same `algebra A B hweak` is the data
  `coverAlgebra A B hweak`. It is `RingHom.toAlgebra` of
  `coverStructuralMap A B`, the composite of `coverToTensor` with
  `tensorToRefinement`. Keeping this structure as a named abbreviation avoids
  a competing global algebra instance if the B and C scalar rings coincide.
  It is available for an explicit `letI` whenever C-scalars are needed.

Dependency declarations read and used:

- `Sheaf.RingTheory.IndPrincipalZariski` publicly exposes `Algebra.WeaklyEtale`,
  whose Mathlib signature gives flatness over A and flatness of tensor multiplication.
- `Sheaf.RingTheory.StrictWCover`: `PrincipalWLocalization.StrictWCover.algebra`.
- `Sheaf.RingTheory.StrictWCoverProperties`:
  `PrincipalWLocalization.StrictWCover.properties` (explanatory import).
- `Sheaf.RingTheory.RetainedLocalization`:
  `PrincipalWLocalization.Retained.algebra`, exposed by the strict-cover module.
- `WeilConjectures.RingTheory.ProEtale.WLocal`: `IsWLocalRing`, which supplies
  `WLocalSpace` on the prime spectrum; the existing `closedPoints` definition
  is the set of points with closed singleton.
- Existing Mathlib `PrimeSpectrum.vanishingIdeal`, `PrimeSpectrum.zeroLocus`,
  `PrimeSpectrum.isClosed_zeroLocus`, `Ideal.map`, tensor product inclusions,
  and `RingHom.toAlgebra` give the remaining constructions.

Edge cases checked before writing: zero A forces zero A-algebras; zero B is also
allowed over nonzero A. Empty spectra cause no failure: vanishingIdeal of the empty
set is the empty infimum, hence the unit ideal, and its zero locus is empty.
The retained localization already handles the empty closed set and empty parts.
B = A uses exactly the same tensor construction (canonically isomorphic to C);
B = C produces both tensor inclusions without identifying them.
No arbitrary choice of map or existence-only choice is used. Independent universes
u and v are supported: D₀ and the refinement lie in max u v, while C_A lies in u.

Searches for an existing declaration:

- `msearch.py leanfinder`, query "Affine refinement of a weakly etale algebra by
  retained localization of its tensor product with the strict w-local cover":
  eight hits, including RingHom.Etale.ofLocalizationSpanTarget and ordinary
  etale-localization lemmas; none defines this refinement.
- `msearch.py loogle`, query "PrimeSpectrum.vanishingIdeal,
  Algebra.TensorProduct.includeRight": zero hits.
- `msearch.py grep`, query "weak.*[Rr]efinement|[Rr]etained|[Ss]trictWCover"
  in Mathlib/RingTheory: zero hits.
- `msearch.py leansearch`, query "Affine refinement of a weakly etale algebra by
  retained localization of B tensor A C at the closed point ideal of a strict
  w-local cover": unavailable, Internal Server Error (recorded as unavailable).
- `rg` in project and upstream RingTheory for WeaklyEtale, weak-refinement
  names, and this blueprint id: no matching named definition. Upstream
  `Algebra.WeaklyEtale.exists_indEtale` has local `set C`, `set J`, `set D'`,
  `set K`, `set D` in its proof, with a different strict-cover implementation;
  its theorem is an existential statement, not this recorded construction.
- `rg` for this blueprint id / weakEtaleRefinement / WeakEtaleRefinement
  in `dag/lean_names_upstream.json`, all `lean/Sheaf`, and all upstream
  WeilConjectures: no matching declaration.

Source read: the full blueprint defining paragraph and formula, order 1231,
and all five statement dependencies with their declaration signatures/docstrings.
No statement is disputed.

## Second reading by NH

I independently read the node, its complete blueprint source paragraph (order 1231),
Stacks `proetale.tex` at Tags 097X and 097Z, all five dependency node records,
and the actual dependency declarations and their docstrings. The Stacks construction
uses arbitrary commutative rings; the algebraic-residue-field hypothesis in 097X
is supplied for weakly etale maps in 097Z. It is not an extra input here.

Object/hypothesis/clause checklist, in the order of the node:

- Commutative ring A: `(A : Type u) [CommRing A]`. Exact.
- Weakly etale A-algebra B: `(B : Type v) [CommRing B] [Algebra A B]`
  and main `algebra (_hweak : Algebra.WeaklyEtale A B)`. Exact. I opened
  Mathlib's class: its fields are flatness over A and flatness of tensor
  multiplication, with no finite-presentation assumption. Helpers give the raw
  construction more generally; the main declaration retains the hypothesis.
- C with its specified A-algebra structure: `StrictWCover.algebra A`, not an
  independently chosen cover. Its module constructs the composite A-algebra map
  through principal w-localization, etale contraction, and retained localization.
  Exact, and no replacement of a dependency notion.
- W-locality and closed closed-point set: the imported dependency theorem
  `StrictWCover.properties A` has `IsWLocalRing (StrictWCover.algebra A)` as
  its third conjunct. I opened `IsWLocalRing` and `WLocalSpace`: the latter
  includes `isClosed_closedPoints`. These facts explain the construction rather
  than introduce a new hypothesis or a theorem obligation in this definition. Exact.
- J is the intersection of maximal ideals: `closedIdeal A` is
  `PrimeSpectrum.vanishingIdeal (closedPoints (PrimeSpectrum C))`.
  I opened `vanishingIdeal`, whose body is the infimum of the prime ideals of
  the specified points, and `PrimeSpectrum.isClosed_singleton_iff_isMaximal`.
  Thus the ideal is precisely the required intersection; closedness makes its
  zero locus the closed-point set. No radicalization or quotient is substituted.
- D0 is B tensor_A C: `tensor A B` bundles exactly `B ⊗[A] C` as a commutative
  ring, using the specified A-algebra structures. Exact.
- The map c to 1 tensor c: `coverToTensor A B` is
  `Algebra.TensorProduct.includeRight` with its A-algebra structure forgotten.
  Exact; the tensor factors have not been exchanged silently.
- K is JD0: `extendedIdeal A B = (closedIdeal A).map (coverToTensor A B)`.
  Ideal extension means the generated ideal, as required, not just set image.
- B' is the retained localization at V(K): `retainedAlgebra A B` applies the
  dependency's `Retained.algebra` to `PrimeSpectrum.zeroLocus` of that ideal,
  with `PrimeSpectrum.isClosed_zeroLocus _`. I read the retained dependency:
  it is the colimit of selector localizations over reverse-inclusion constructible
  supersets. The delivered definition uses that exact construction. Exact.
- Canonical D0 to B': `tensorToRefinement A B` is the composite D0 to D0^w
  to the retained colimit, using its structural algebra map. Exact.
- B-algebra structure: `structuralMap A B` composes the left tensor inclusion
  with `tensorToRefinement`; `algebra A B hweak` uses precisely its `toAlgebra`
  to bundle B'. Exact.
- C-algebra structure on the same ring: `coverStructuralMap A B` composes
  the right tensor inclusion with the same canonical map, and
  `coverAlgebra A B hweak` supplies its `toAlgebra` on that very bundled B'.
  This is concrete data, with no arbitrary-map or mere-existence choice. Exact.

Edge cases: neither ring is required nonzero, nor is any spectrum nonempty.
The empty closed-point set gives the unit ideal (also recorded by Mathlib's
`vanishingIdeal_empty`); the empty zero locus is accepted by retained localization.
Its neighborhood diagram includes the whole spectrum, including the empty-spectrum
case, and the existing construction omits empty partition parts. There is no
index-set, degree, characteristic, field, Noetherian, or finite-type restriction.
For B = A the same tensor construction is used. For coinciding B and C, the two
inclusions remain distinct and the explicit `coverAlgebra` introduces no competing
global scalar instance. Universes u and v are independent: C is in u and the tensor
ring and B' are in max u v. All variables and universes are explicitly bound.

Independent searches used different terms from the first reader:

- `msearch.py leanfinder`: "Construct a weakly etale algebra refinement using the
  Jacobson ideal and a tensor product followed by retained w-localization".
  Eight hits concern ordinary etale localization or etale loci; no matching construction.
- `msearch.py loogle`: `"vanishingIdeal"`. Twelve hits identify the existing
  vanishing ideal and its basic identities, which are correctly reused here;
  none defines the refinement.
- `msearch.py grep`: `Jacobson.*[Tt]ensor|[Tt]ensor.*Jacobson|[Rr]etained`.
  Three unrelated documentation hits only.
- Direct `rg` over project Lean, upstream WeilConjectures, and the upstream name
  index for weak-refinement names and tensor/refinement combinations found no
  matching named construction. I also opened upstream
  `Algebra.WeaklyEtale.exists_indEtale`: its C/J/D'/K/D are local proof data,
  for the other strict-localization implementation, not an existing declaration
  of this node's construction. Mathlib's existing tensor and ideal operations
  are reused, not duplicated.

No mismatch was found and no Lean or node change was needed. There are no new nodes,
dependency modules, or statement corrections to audit. All ten declarations have
source/blueprint docstrings; all contain actual data and there are no theorems or
sorry terms in the delivered file. The node's `lean.statement` is verbatim its
main signature. Only this independent review section was added.
