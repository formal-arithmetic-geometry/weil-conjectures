## Worker report

The module `Sheaf.Algebra.Homology.MittagLefflerLimitHomology` states
`HomologicalComplex.isIso_limitPost_homology_of_mittagLeffler`, with its sole theorem
proof `sorry`. No new mathematical notion, dependency module, or statement correction
is needed. The module docstring and declaration docstring cite Stacks Tag 070E;
the declaration docstring gives all seven steps of the node's proof and its dependencies.

Source checked: https://stacks.math.columbia.edu/tag/070E (Lemma 12.31.7 and proof).
The local literature checkout contains the indexes but not homology.tex, so the actual
Stacks page was opened. Its four-term statement and three hypotheses agree with this node.

Clause-by-clause correspondence:

- Inverse systems indexed by positive integers are functors from `ℕᵒᵖ`, using the
  order-preserving reindexing `n ↦ n+1`. This is exactly the functor presentation in
  `def-weil-inverse-system`. It includes all composite transition maps, identities,
  and naturality. No extra restriction on transition homomorphisms is imposed.
- The four abelian groups in degrees -2,-1,0,1 are the objects of a
  `HomologicalComplex AddCommGrpCat.{u} c`, indexed by `Fin 4` in that order.
  The signature's local `let c` instantiates Mathlib's `ComplexShape`: its relation
  is `i.val + 1 = j.val`. Thus precisely the three consecutive differentials are
  allowed; no cyclic arrow 3→0 is present. Its two structure proofs use `Fin.ext`
  and cancellation in ℕ. This is just the shape of the four-term diagram, with
  no additional data or hypothesis and no new named notion. Every four-term
  complex gives such an object, and its consecutive differentials are unrestricted
  except for the required square-zero laws.
- `K : ℕᵒᵖ ⥤ HomologicalComplex AddCommGrpCat.{u} c` is the given inverse system
  of these complexes. Morphisms in this category contain exactly degreewise
  homomorphisms commuting with the differentials. Square-zero is part of each
  complex's structure.
- `limit K` is its limit complex. Mathlib's `coneOfHasLimitEval` and `HasLimit`
  construction compute this degreewise as `limit (K ⋙ eval AddCommGrpCat c j)`;
  its differentials are the induced limit maps (`limMap`). These are the given
  compatible-family limits and induced differentials up to their canonical limit
  identification, with no chosen alternative map.
- `(K ⋙ homologyFunctor AddCommGrpCat c 1)` is the induced system `H_i^{-1}`,
  and `(K ⋙ homologyFunctor AddCommGrpCat c 2)` is `H_i^0`. Mathlib homology in
  this abelian category is the kernel modulo the image of the preceding
  differential. The same homology functor applied to `limit K` gives `H^{-1}`
  and `H^0` respectively; the former is notation only, with no extra hypothesis.
- The first hypothesis
  `(K ⋙ eval AddCommGrpCat c 0 ⋙ CategoryTheory.forget AddCommGrpCat).IsMittagLeffler`
  says the terms `A_i^{-2}` are ML; the second uses index 1 and says `A_i^{-1}`
  are ML. These use the dependency's recorded Mathlib definition. The ranges of
  homomorphisms form decreasing subgroups, so its eventual-minimal-range
  formulation is precisely eventual stabilization of images.
- The third hypothesis
  `(K ⋙ homologyFunctor AddCommGrpCat c 1).IsEssentiallyConstant`
  uses the dependency's existing definition verbatim: it quantifies over X,
  compatible maps π, a splitting at i₀, and eventual factorization through X,
  exactly as the introductory definition in the node requires.
- The conclusion is
  `IsIso (limit.post K (homologyFunctor AddCommGrpCat c 2))`.
  Its source is H^0 of the limit and its target is the limit of H_i^0. The
  defining formula for `limit.post` is `limit.lift` of the homology image of the
  limit cone. `limit.post_π` identifies its projection at each index with
  `homologyMap (limit.π K i) 2`. Thus its action is exactly the specified
  `[(x_i)] ↦ ([x_i])`. The conclusion concerns this canonical map, not an
  arbitrary isomorphism between these objects.

Dependency declarations read and used:

- `def-weil-inverse-system`: `Mathlib.CategoryTheory.Functor.OfSequence`,
  `CategoryTheory.Functor.ofOpSequence` and `CategoryTheory.NatTrans.ofOpSequence`.
  Full signatures/docstrings were read. We use their functor/natural-transformation
  presentation directly, rather than reconstructing a tower from successor maps.
  This module is imported through `EssentiallyConstantSystem`.
- `def-weil-pbc-mittag-leffler-system`:
  `Mathlib.CategoryTheory.CofilteredSystem`, `CategoryTheory.Functor.IsMittagLeffler`.
- `def-weil-pbc-essentially-constant-system`:
  `Sheaf.CategoryTheory.EssentiallyConstantSystem`,
  `CategoryTheory.Functor.IsEssentiallyConstant` and its
  `IsEssentiallyConstantWithValue`. Both full definitions/docstrings were read.

Further existing Mathlib infrastructure read: `HomologicalComplex.eval`,
`HomologicalComplex.homologyFunctor`, `HomologicalComplex.coneOfHasLimitEval`,
`HomologicalComplex.isLimitConeOfHasLimitEval`, and `CategoryTheory.Limits.limit.post`
(with `limit.post_π`). Imports supply the abelian category, group limits, homology,
complex limits, ML condition and essentially constant condition.

Edge cases checked before writing: the zero system, constant systems, and systems
with noninjective/nonsurjective transitions are permitted; no finite generation,
boundedness beyond the stated four terms, or surjectivity has been imposed.
The indexing set is exactly the nonempty positive-integer tower (not a quantification
over arbitrary index sets). Arbitrary universe `u` permits abelian groups of any size.
At the boundary index 3 there is no outgoing differential, and at index 0 no incoming
differential; neither boundary imposes a condition absent from the four-term source.
The cohomology indices 1 and 2 are interior and use precisely the correct incoming
and outgoing arrows. ML is asserted only on the first two terms, and essential
constancy only on H^{-1}. Nothing requires H^0 or the last two terms to be ML.

Searches (2026-10-11):

- msearch LeanFinder: `inverse limit of complexes Mittag Leffler terms essentially
  constant homology comparison isomorphism`. Eight hits, on homology under shape
  restriction/extension; no matching inverse-limit theorem.
- msearch Loogle: `CategoryTheory.Functor.IsMittagLeffler,
  HomologicalComplex.homologyFunctor`. Zero hits.
- msearch grep: `Mittag|homology.*limit|limit.*homology`, subdirectory
  `Algebra/Homology`. Twenty-five hits, including eventually constant complexes,
  exact functors and filtered colimits; no ML homology-comparison theorem.
  Read `HomologicalComplexLimitsEventuallyConstant.lean`: its hypotheses require
  degreewise eventual constancy, unlike the present ML/essentially constant hypotheses.
- msearch LeanSearch: `inverse limit homology Mittag Leffler essentially constant`.
  Service unavailable (Internal Server Error); no search verdict inferred.
- rg over `WeilConjectures` and `lean/Sheaf`:
  `homology.*[Ll]imit|[Ll]imit.*homology|Mittag|EssentiallyConstant|essentiallyConstant`.
  Existing essentially constant and ML exact-sequence modules are dependencies or
  proof inputs. Other hits concern derived limits, filtered colimits or restrictions;
  none states this theorem. Searching the exact item id in `WeilConjectures` had
  no hits. `tools/lean_names_upstream.py show` for the item also had no declaration.

Validation: server single-file compile succeeded, no errors or warnings. An initial
name-resolution error (`HomologicalComplex.forget` shadowed the category forgetful
functor) was repaired by spelling `CategoryTheory.forget` explicitly.
No statement disputes or node faults were found.

## Second reading by K1

I reread the node statement against Stacks Tag 070E (Lemma 12.31.7 and its proof) and the Lean signature.
The correspondence is as follows.

- The inverse system of four term complexes is the universally quantified
  `K : ℕᵒᵖ ⥤ HomologicalComplex AddCommGrpCat.{u} c`; `ℕᵒᵖ` supplies the tower indexed by positive-stage natural indices, and morphisms are degreewise additive homomorphisms commuting with differentials.
- The four objects (A_i^{-2},A_i^{-1},A_i^0,A_i^1) are the `Fin 4` components of `HomologicalComplex ... c`; `Rel i j := i.val + 1 = j.val` gives exactly the three consecutive arrows and no cyclic boundary arrow. The `next_eq` and `prev_eq` fields only prove the `ComplexShape` laws.
- The limit complex is Mathlib's `limit K`; its degreewise limits and induced differentials are the canonical limit construction.
- The systems (H_i^{-1}) and (H_i^0) are `(K ⋙ homologyFunctor AddCommGrpCat c 1)` and `(K ⋙ homologyFunctor AddCommGrpCat c 2)`, while the homology of the limit is represented by `limit.post K ...`.
- The two ML assumptions are exactly the degree-0 and degree-1 evaluations followed by `CategoryTheory.forget AddCommGrpCat`, namely the systems (A_i^{-2}) and (A_i^{-1}). No ML condition is imposed on later terms.
- The essential-constancy assumption is exactly `(K ⋙ homologyFunctor AddCommGrpCat c 1).IsEssentiallyConstant`, i.e. (H_i^{-1}), using the dependency declaration.
- The conclusion `IsIso (limit.post K (homologyFunctor AddCommGrpCat c 2))` is the canonical map (H^0(lim A_i)\tolim H_i^0), whose component formula is the class map described in the node.

All quantifiers and implication order agree with the node, and the universe `u` is unrestricted. Edge cases checked include the zero and constant systems, noninjective and nonsurjective transition maps, the boundary indices of `Fin 4` (no incoming arrow at 0 and no outgoing arrow at 3), and the interior cohomology indices 1 and 2. The statement does not add finite generation, boundedness, surjectivity, characteristic, or nonempty-scheme assumptions; the tower index is fixed as in the source.

I searched Mathlib and the project with LeanFinder, Loogle, LeanSearch, `rg` over `Mathlib`, `WeilConjectures`, and `lean/Sheaf`, including queries for inverse-limit homology, Mittag-Leffler complexes, and `limit.post`; no existing theorem or competing definition was found. The cited dependency declarations (`Functor.IsMittagLeffler`, `IsEssentiallyConstant`, and the inverse-system presentation) were opened and match the notions used here.

No mismatch was found, so no statement or module change was necessary. The module compiles cleanly with `scompile.py`; its only proof placeholder is the permitted theorem `sorry`, and both module and theorem docstrings cite Tag 070E and the blueprint.
