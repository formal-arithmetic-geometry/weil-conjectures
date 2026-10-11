## Worker report

The module `Sheaf.Paper.HypercoverFreeResolution` states four theorems, all with
`sorry` proofs. The first and third state `QuasiIso` for the alternating-face
augmented complexes built from the free abelian sheaf and free
`R`-module sheaf on the representables of a split étale hypercover. The
augmentation is
`U.simplicial.augmentOfIsTerminal (terminalIsTerminal (C := X.Etale))`, so
the target is the terminal étale object and the quasi-isomorphism expresses
exactness of the augmented complex.

The second theorem has binders
`{X : Scheme.{w}}`, `[CompactSpace X]`, `[QuasiSeparatedSpace X]`,
`(U : SplitEtaleHypercover X)`, and an injective
`I : Sheaf X.smallEtaleTopology AddCommGrpCat.{w + 1}`. Its first conjunct
renders the augmentation identification (H^0=I(X)) in the required
chain-level form:
`Function.Injective (I.obj.map (terminal.from U_0).op)`, followed by
`∀ s : I(U_0), d 0 1 s = 0 ↔ s ∈ Set.range (I.obj.map (terminal.from U_0).op)`,
where U_0 is written explicitly as
`U.simplicial.obj (op (SimplexCategory.mk 0))` and d is the differential
of `AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{w + 1}`
on `U.simplicial.rightOp ⋙ I.obj`. This is exactness at the first two
terms of (0 → I(X) → I(U_0) → I(U_1)), through the augmentation. Its second
conjunct is
`∀ p : ℕ, 0 < p → IsZero (...homology p)`, rendering vanishing in every
positive degree.

The fourth theorem repeats those two cohomology clauses for
`I : Sheaf X.smallEtaleTopology (ModuleCat.{w + 1} R)` with
`R : Type (w + 1)` and `[CommRing R]`; the same inline alternating-coface
complex is formed in `ModuleCat.{w + 1} R`. Thus the degree-zero statement
again uses injectivity and the range of the restriction map induced by the
terminal augmentation, and the positive-degree clause is `IsZero`.

Dependency declarations used are
`AlgebraicGeometry.SplitEtaleHypercover` from
`Sheaf.Paper.FiniteSplitEtaleHypercover`, Mathlib's
`CategoryTheory.presheafToSheaf`, `Injective`,
`AlgebraicTopology.AlternatingFaceMapComplex.ε`, `QuasiIso`,
`AddCommGrpCat.free`, and `ModuleCat.free`. The dependency module supplies
the split hypercover structure (simplicial object, splitting, matching maps
and matching covers) and its finite extension.

Edge cases checked: degree zero is included separately from positive degrees;
the augmentation uses the terminal identity étale object; the injectivity and
range clauses express exactness even when sections or sheaves are zero; the
coefficient ring is arbitrary, including the zero ring; and no finiteness in
each degree is assumed.

Searches made: `msearch.py` LeanFinder for an exact augmented free sheaf
hypercover resolution (no match); Loogle for
`AlgebraicTopology.alternatingCofaceMapComplex` and injective hypercover
cohomology (no match); grep over Mathlib AlgebraicTopology/CategoryTheory
and `rg` over WeilConjectures and project Sheaf modules for
hypercover/free-resolution declarations (no exact theorem). The local Stacks
source was checked at Tags 01GC, 01GD, 01GE and 01GW.

## Dependency modules

The dependency node `def-weil-pbc-finite-split-hypercover` is delivered by
`lean/Sheaf/Paper/FiniteSplitEtaleHypercover.lean`. Its previous record provided only
`FiniteSplitEtaleHypercover`, although the node distinguishes split hypercovers
from the additional finite-in-each-degree condition. The item's hypothesis needs
that unrestricted split notion. The dependency module defines SplitEtaleHypercover without
finiteness and FiniteSplitEtaleHypercover as its finite-in-each-degree extension.
The item's four statements use SplitEtaleHypercover. All existing finite-structure
and independent truncation declarations are retained.

## Earlier second reading (a previous round; superseded)

I read the node statement, its Stacks source (Hypercoverings Tags 01GC,
01GD, 01GE and 01GW), and all four declarations in
`Sheaf.Paper.HypercoverFreeResolution`.

- The object U → X is rendered by (U : SplitEtaleHypercover X); the node imposes no
  finite-in-each-degree hypothesis. All four theorem binders use this unrestricted split structure.
- The first conclusion clause, exactness of the augmented free abelian
  alternating-face complex, is rendered by
  `freeAbelian_augmentation_quasiIso` and its explicit
  `AlternatingFaceMapComplex.ε` term. The free sheaf is built by
  `AddCommGrpCat.free` followed by `presheafToSheaf`.
- The second clause, injective abelian sections having degree-zero
  identification and no positive cohomology, is rendered by
  `injective_abelian_section_cohomology`: injectivity of the terminal
  restriction map, the explicit degree-zero cycle/range equivalence, and
  `∀ p, 0 < p → IsZero (homology p)`.
- The third clause, exactness with a constant commutative coefficient ring,
  is rendered by `freeModule_augmentation_quasiIso`, with
  `R : Type (w + 1)` and `[CommRing R]`, using `ModuleCat.free R`.
- The fourth clause is rendered by
  `injective_module_section_cohomology` with the same explicit degree-zero
  and positive-degree clauses in `ModuleCat R`.

The universe `w` is shared by the scheme, étale site, sheaf values, and
alternating complexes; the ring and module category use `Type (w + 1)` as
required by the sheaf encoding. No Noetherian, characteristic, or extra
flatness assumptions occur. Zero sheaves and the zero coefficient ring are
allowed by the stated typeclass hypotheses; `p = 0` is handled by the
separate degree-zero conjunct, and positive degrees by the quantified
vanishing. The terminal étale object is the identity of `X`, so the empty
and terminal-cover edge cases are included by the same terms.

I searched the local source and Mathlib with LeanFinder, Loogle, and `rg`
for hypercover resolutions, augmented free sheaf complexes, and matching
homology; no declaration states this result. The repaired dependency
`Sheaf.Paper.FiniteSplitEtaleHypercover` supplies
`AlgebraicGeometry.SplitEtaleHypercover` without finiteness and
`AlgebraicGeometry.FiniteSplitEtaleHypercover` as its finite-in-each-degree extension.
The item's four statements use `SplitEtaleHypercover`.


## Second reading by K1

Independent second reading, 2026-10-12. I opened the item node, all four
statement-dependency nodes and their recorded declarations, both delivered
modules, the base finite-hypercover module, and the Stacks source. The
repository's literature checkout lacks hypercovering.tex; I read the available
local Stacks source copy at c1-stacks-review/hypercovering.tex, specifically
example-hypercovering-in-C and the four labels lemma-compare-cosk0,
lemma-acyclicity, lemma-acyclic-hypercover-sheaves and
lemma-injective-trivial-cech (01GC, 01GD, 01GE, 01GW).

The node's objects, hypotheses and conclusions, matched individually:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Base scheme X, with the qcqs convention inherited from the cited definition | `{X : Scheme.{w}} [CompactSpace X] [QuasiSeparatedSpace X]` in all four declarations | Exact; qcqs is explicitly assumed by the dependency node, not added for this theorem. |
| Split étale hypercover U augmented to X, without finiteness | `(U : SplitEtaleHypercover X)`; `simplicial`, `splitting`, matching universal properties and `matching_cover` | Exact; the dependency repair removes finite-in-each-degree from the unrestricted notion. |
| Representable on an étale X-scheme V | `uliftYoneda.{w + 1}` on `X.Etale` | Exact; lifting Hom sets only aligns the universe. |
| Free abelian presheaf, then sheafification, denoted Z[V] | Whiskering by `AddCommGrpCat.free`, followed by `presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{w + 1}` | Exact; no free sheaf is replaced by a free group of global sections. |
| Alternating faces and the given augmentation to Z[X], with exactness including the last term | `freeAbelian_augmentation_quasiIso`, using `AlternatingFaceMapComplex.ε.app` on the whiskered `augmentOfIsTerminal` | Exact; ε maps the alternating-face chain complex to the single complex on the free sheaf of the terminal object. Its being a quasi-isomorphism means augmented exactness, including surjectivity to Z[X]. |
| Arbitrary injective abelian sheaf I | `(I : Sheaf X.smallEtaleTopology AddCommGrpCat.{w + 1}) [Injective I]` | Exact; `Injective.factors` is the extension property in the dependency node. |
| H^0 of the section complex identifies with I(X) through the augmentation | `injective_abelian_section_cohomology`: injectivity of `I.obj.map (terminal.from U_0).op`, and `d 0 1 s = 0 ↔ s ∈ Set.range (...)` | Exact; the cochain complex has no incoming degree-zero differential. The restriction map is therefore a bijection from I(X) onto the degree-zero cycles, and is additive. This specifies the canonical cohomology identification, rather than an unrelated abstract isomorphism. |
| H^p vanishes for every p > 0 | The same declaration's `∀ p : ℕ, 0 < p → IsZero (...homology p)` | Exact; homology is an object of AddCommGrpCat, so categorical IsZero expresses vanishing. |
| The same augmented resolution for a constant commutative ring R | `freeModule_augmentation_quasiIso`, `(R : Type (w + 1)) [CommRing R]`, whiskering by `ModuleCat.free R` and then sheafification | Exact; constant coefficients are the accepted module-valued-sheaf encoding of the recorded étale-sheaf dependency. |
| The same two section-cohomology assertions for injective R-module sheaves | `injective_module_section_cohomology`, `(I : Sheaf X.smallEtaleTopology (ModuleCat.{w + 1} R)) [Injective I]`, with the same injectivity, cycles/range and positive vanishing clauses | Exact; restriction maps are R-linear, giving the degree-zero identification as R-modules. |

Dependency-module reading (H13): `def-weil-pbc-finite-split-hypercover`
introduces both unrestricted split hypercovers and their finite subclass; its
previous declaration only supplied the finite subclass. The delivered repair
factors out exactly the existing fields through `matching_cover` into
`SplitEtaleHypercover`, and makes `FiniteSplitEtaleHypercover` extend it with
`finite_each_degree`. I compared the module with the base: these are the only
structural changes. All refinement, homotopy-quotient, truncation, section,
complex, cohomology and independent-truncation declarations are retained.
The finite condition still uses a finite coproduct of qcqs finitely presented
étale pieces. Matching projections and their compatibility are tested against
all `T : Over X`, not just étale tests. At degree zero the matching diagram is
empty and its universal property gives X; at degree one it gives U_0 ×_X U_0.
Morphisms in X.Etale are étale, so `Surjective (matchingMap n).left` gives
exactly the required matching cover. `splitting` is Mathlib's canonical
coproduct cofan over order-preserving epimorphisms, not arbitrary summand maps.
The retained independent truncation has these same data for n ≤ r, and its
base-change predicate compares the diagram and chosen nondegenerate summands.
No new DAG nodes are needed. The existing `IsEtaleHypercover` predicate was
also opened: it forgets the splitting and chosen matching data and is not a
duplicate of this dependency's split structure.

Edge cases: the empty scheme is allowed (there is no Nonempty hypothesis);
empty nondegenerate pieces and the zero sheaf are allowed. Empty matching
diagrams at n = 0 are handled by the universal property. The degree-zero
section assertion is separate from the quantified p > 0 assertion; the
alternating-face augmentation also covers degree zero. The zero ring and
all characteristics are allowed by CommRing, with no flatness, field,
Noetherian or torsion assumption. There is no bound on the number of
nondegenerate components. Scheme universes are arbitrary w; sheaf values and
R lie in w+1, the project's common small-étale encoding. Matching tests live
in the same universe as schemes, with no smaller independent test universe.

Independent searches: msearch LeanFinder query "augmented chain complex free
abelian sheaf hypercover resolution exact injective sections" returned generic
injective-resolution exactness and K-injective results, not this theorem.
Loogle query `"QuasiIso", "ε"` returned only the group-representation standard
resolution, whose category and simplicial object differ. LeanFinder query
"split simplicial scheme etale hypercover matching object nondegenerate
summands" returned Mathlib's Splitting data only, which this module uses.
LeanSearch query "hypercover free sheaf augmented complex exact" was
unavailable (Internal Server Error), so it supplies no verdict. I also ran rg
independently over Mathlib, WeilConjectures and project Sheaf for hypercover
acyclicity/resolutions, free hypercovers and hypercover quasi-isomorphisms.
The project's CechNerveFreeHomology and HypercoverCohomology are related
lemmas, not this assertion; no exact existing declaration was found.

H5/H6/H8/H9: no definition contains sorry; each of the four theorem proofs is
sorry only. Imports and dependency declarations were opened, including
Mathlib's ε, augmentOfIsTerminal, Injective, free functors, uliftYoneda,
presheafToSheaf and QuasiIso. The theorem docstrings retain the node's four
proof steps and source/blueprint citations, including the n = 1 coskeleton
boundary case. I found no statement mismatch and changed no signature or
node statement. I repaired one docstring: it redundantly repeated positive
vanishing and described the unrestricted section complex as the recorded
finite-hypercover complex; it now explicitly says that the same construction
is used without requiring finiteness. The node's lean.statement remains the
verbatim theorem signature. The two delivery modules compiled together with
lcompile, exit code 0, without warnings. The delivery dry run and server
compile are the final mechanical checks.
