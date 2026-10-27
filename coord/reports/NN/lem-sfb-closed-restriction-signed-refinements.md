## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedRestrictionSignedRefinements` states
`AlgebraicGeometry.closedRestriction_signed_refinements`, with one postponed proof.
`SignedClosedFamily`, `SignedClosedRow` and `SignedClosedRefinementSystem` are helper
structures expressing the data and every equation of this node. They do not choose
objects from an existence theorem. There are no new independent notions, dependency
repairs, changed natural-language statements, or other postponed theorems.

Sources read: the entire node, its eight proof steps, every statement-dependency
record and source signature; Stacks proetale.tex `lemma-ses-associated-to-open`
(Tag 09AH), cohomology.tex `section-alternating-cech` (Tag 01FG); and current blueprint
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3). The blueprint supplies
the application; as the node itself says, the signed identities are agent deductions,
not additional claims attributed to 09AH. The eight-step proof is in the theorem docstring.

Hypotheses and clauses, in node order:

- `X Z : Scheme.{u}` and `i : Z ⟶ X` are schemes and the support morphism;
  `[IsClosedImmersion i]` is the stated closed immersion. `_hqc` is existence of
  the complementary open `U : X.Opens`, equality of its image with the complement
  of the image of i, and `QuasiCompact U.ι` on the morphism, not on its source.
- `A : Sheaf (ProEt.topology X) CommRingCat.{u+1}` allows arbitrary commutative ring
  sheaves. Module categories are the dependency's
  `ringedSiteModules.{u+1} (proEtaleModuleCoefficients A)`. The small pro-etale site
  retains object universe u+1 and morphism universe u. There is no constant,
  finite, discrete, or constructible coefficient assumption.
- `SignedClosedFamily i` stores `length`, `positive`, `members : Fin length → Over X`,
  `closed`, `factor`, and `complement`. These are exactly the nonempty ordered family,
  closed immersions, factorizations through Z, and quasi-compact complementary open
  morphisms. `Fin m` is the usual zero-based reindexing of 1,...,m. No union or covering
  condition is present. Because i is mono, the chosen factorizations are unique;
  `Nonempty` here records their existence without replacing any canonical functor.
- `finiteClosedIntersection F.members s` is the existing finite product in `Over X`,
  hence the scheme-theoretic iterated fibre product. Its empty-set value is X; the
  augmentation from Z is only requested for nonempty s. In particular this encoding
  does not accidentally request an impossible E_Z → id restriction for the empty set.
- `finiteClosedRestriction` is precisely `proEtaleModuleInverseImage` followed by
  `proEtaleRingedDirectImage`. Coefficients on the closed scheme are the actual
  inverse-image ring. `finiteClosedUnit` is the unit of the dependency's
  `ProEtaleClosedProjection.adjunction`, not an independently selected adjunction.
- `restriction_unit`, `fromSupport_unit`, and `mixed_unit` pin the restriction maps
  to the actual pushed units with the composition identifications: composition of
  actual units satisfies these equations. They characterize the maps uniquely,
  since 09AH makes each source closed unit epic; intersections still have qc open
  complements, as finite unions of the given qc open immersions. Thus these fields
  do not allow arbitrary maps with merely coherent composition.
- `restriction_comp` and `fromSupport_comp` state both restriction transitivity
  equations. `fromSupport_unit` is r_{Z,J} eta_i = eta_{i_J}. The equality is of
  natural transformations, hence includes every M and every morphism of M.
- `rows`, `terms`, `differential` and `support` specify the cochain complex in degrees
  0,...,m-1, identified by actual natural isomorphisms with the existing finite
  products `finiteClosedTerms`. These are the finite direct sums in this abelian
  category. `finiteClosedDifferential` is the stated sum over deleted positions,
  with the integer coefficient (-1)^t. The HomologicalComplex type contains d²=0.
  `support_additive`, `intersection_additive`, and `additive` include the additivity
  of E_Z, E_J, and the row functor explicitly.
- `augment`, `augment_components`, `alpha`, and `alpha_f` specify the actual
  augmentation to column zero and its chain map E_Z[0] → rows. The single complex's
  canonical degree-zero identification is written explicitly. This is the equivalent
  encoding of the augmented cochain complex: put E_Z in column -1, the specified
  augment in d^{-1}, the given row above it, and zero below it. The chain-map condition
  is exactly d^0 d^{-1}=0. `fromSupport_unit` with `augment_components` gives the
  displayed alpha eta_i = (eta_{i_a})_a formula.
- The refinement system quantifies over EVERY pair F,G of such ordered families,
  EVERY function f, and every factorization witness `hf`. Its `refine` is a natural
  transformation into cochain complexes, so its components are chain maps.
  `refine_components` pins its entire matrix to `finiteClosedRefinementMap`.
  That existing formula sums sorting permutations: repetitions admit none and
  produce zero; otherwise exactly one permutation gives its sign and only the
  matching source summand is nonzero. `mixed_unit` pins the actual mixed restriction.
- `refine_augment`, `refine_id`, and `refine_comp` state augmentation compatibility,
  identity, and iterated-refinement composition. Under the augmented encoding the
  component in column -1 is identity on the common E_Z. The chain equation there
  is exactly the augmentation square; there is no isomorphism substituted for it.
- All objects are functors in M and all maps are natural transformations. Thus
  application to any small parameter diagram is ordinary whiskering. Diagrams of
  refinements use exactly the identity and composition equations, including arrows
  that permute or repeat indices. This is the node's objectwise diagram clause,
  and does not claim comparison of geometric pullbacks or parameter limits.
- `totalAugment`, `totalAugment_f`, `totalMap`, `totalMap_components`, and
  `totalMap_augment` give maps of the actual totals for EVERY `CochainComplex ... ℤ`,
  with no boundedness assumption. `finiteClosedDouble` applies the row termwise
  and flips so horizontal degree is first. Mathlib's total signs are epsilon_1=1
  and epsilon_2=p.negOnePow, exactly d_D+(-1)^p d_K. The row support makes each total
  degree a finite sum of potentially nonzero terms. `totalMap_components` pins the
  total map on every coprojection, so it is the termwise refinement map, rather than
  an unspecified natural map of totals. Naturality supplies commutation with d_K;
  identity and composition of total maps follow from their summand equations.
- Neither exactness, quasi-isomorphism, nor a derived isomorphism is asserted.

Dependency declarations used (read signatures and docstrings):

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Mathlib.AlgebraicGeometry.Sites.Proetale: `Scheme.ProEt`, `ProEt.topology`.
- Sheaf.CategoryTheory.RingedSiteModules: `CategoryTheory.ringedSiteModules`.
- Sheaf.AlgebraicGeometry.ProEtaleInverseImage: `Scheme.proEtaleModuleInverseImage`,
  `proEtaleSheafInverseImage`, its site base change and actual adjunction.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`;
  Mathlib.AlgebraicGeometry.OpenImmersion: `IsOpenImmersion` (implicit for U.ι);
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and Morphisms.QuasiCompact:
  `LocallyOfFiniteType` and `QuasiCompact` (only the latter is required).
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`, projections,
  universal lifts; the existing finite intersection uses products in Over X.
- Sheaf.AlgebraicGeometry.ProEtaleClosedUnderivedProjection:
  `ProEtaleClosedProjection.adjunction` and its unique sectionwise-unit characterization.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: the recorded cochain-complex framework;
  HomologicalComplex and CochainComplex are used, with no derived localization needed.
- Proof imports: Sheaf.CategoryTheory.SiteInverseImageTensor (`siteInverseImage_tensor`);
  Sheaf.AlgebraicGeometry.ProEtaleTensorCompositionUnit
  (`Scheme.proEtale_tensor_composition_unit`); WeilConjectures.Combinatorics.SignedFacePermutation
  (`Fin.signed_face_permutation`); Mathlib.CategoryTheory.Adjunction.Mates
  (`unit_conjugateEquiv_symm`); Adjunction.Basic (`Adjunction.comp`).

Reuse/import note: `Sheaf.AlgebraicGeometry.FiniteClosedCoverResolution` already owns
all `finiteClosed*` term, unit, signed-matrix and total helper constructions. They are
imported, never copied, and the old theorem is not invoked. That theorem itself has
this node as a new proof dependency in the DAG. Adding the automatic reverse proof
import to its module would create an import cycle, so that future automatic proof
import must be omitted under stages/2-statements.md §3(7). This delivery introduces
no DAG dependency on that theorem and no stronger covering assumption. The later
proof of the old theorem can import/use a lower helper module if the maintainer
subsequently relocates the existing helpers; this delivery does not edit live modules.

Edge cases checked mathematically before finalizing: m=1 (no positive differential),
noncovering families, empty Z, empty members and empty intersections, repeated members,
constant and non-order-preserving refinement functions, n>m (output degrees exceeding
source length), zero coefficient ring, characteristic two, zero M and zero K, and
unbounded K. The initial draft's support-to-empty-intersection field was removed:
only nonempty subsets have a Z-to-intersection restriction, exactly as the node says.
The empty s,t values of the internal intersection-to-intersection and mixed matrices
are harmless auxiliary X values, not additional augmented terms. No disputed statement
or source correction remains.

Searches (via msearch.py, NN and this item, plus direct rg):

- LeanFinder: "Signed alternating closed restriction complex ordered refinement sorting
  permutation repeated indices zero". Eight hits, including alternating-map
  repeated-input cancellation and ComplexShape sign lemmas; no matching theorem.
- LeanSearch: "Alternating closed restriction cochain complexes signed refinement maps
  preserving augmentation". Eight hits, including HomologicalComplex.restrictionMap,
  AlternatingFaceMapComplex.ε, shifts and alternating maps; no matching theorem.
- Loogle: "AlgebraicTopology.alternatingFaceMapComplex". Twelve hits about the full
  simplicial chain complex, its augmentation and functoriality; no finite increasing-
  tuple closed-restriction complex or signed arbitrary-function refinement result.
- msearch grep: "refin.*(alternat|[Cc]ech)|alternat.*refin|sorting.*sign". Twelve hits
  about alternating maps and unrelated topological refinements; no match.
- rg over lean/WeilConjectures and lean/Sheaf for closed-restriction/signed-refinement
  names and the item id. Found the finiteClosed* formulas in FiniteClosedCoverResolution,
  and unrelated derived restrictions; no existing theorem with this no-cover statement.
- dag/lean_names_upstream.json name search and the recorded declarations were read.
  All helpers are reused, and the four new names are absent from the live sources.

Validation: scompile.py compiles this file both as its sandbox module and under its
intended library name; both passed without warnings or errors. `autoImplicit false`
is set, every universe is bound, and lines are at most 100 characters. The theorem
alone has `sorry`; definitions and structure data contain none.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
