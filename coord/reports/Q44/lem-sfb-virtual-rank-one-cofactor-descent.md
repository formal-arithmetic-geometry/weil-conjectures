## Worker report

The module `Sheaf.AlgebraicGeometry.VirtualRankOneCofactorDescent` states
`AlgebraicGeometry.virtualRankOne_cofactor_descent`. It defines only predicates and
explicit comparison expressions for this theorem. Its sole postponed proof is the
main theorem; its docstring carries all five steps of the accepted DAG proof.

Clause-by-clause correspondence:

- `X : Scheme.{u}` is an arbitrary scheme. The only global instance is the choice of
  derived localizations for module sheaves, with independent morphism universe `w`.
- `L : schemeDerivedCategory X` uses the recorded shared category of module sheaves.
  `IsVirtualRankOne X L` says, point by point, that an open neighbourhood has an actual
  `TwoTermDeterminantModel`, an equality `nonnegRank = negRank + 1`, and a specified
  derived isomorphism to the pullback of L. The negative rank belongs to each model;
  no equality of ranks on different charts is imposed. `isTwoTermPerfect X L` is the
  determinant functor's membership proof, already implied by these local models; it
  adds no mathematical condition. The theorem quantifies over every such proof.
- `T : TwoTermPerfectDeterminantData` and `hT : T.IsCanonical` are the determinant
  functor and the normalized comparisons stipulated by the node, not arbitrary
  line identifications. `P.line` is the existing dual-first exterior tensor formula.
  `T.modelIso` and `twoTermDeterminantIso` supply the model and derived comparisons.
- `P.cofactorClass` is the actual projection of the degree-zero term to H0: double
  complex degree-zero identification, lift to cycles, homology projection, and the
  inverse of `DerivedCategory.homologyFunctorFactors`. Since the outgoing differential
  vanishes, this is the cokernel projection. It assumes no injectivity of u.
- `P.IsSheafCofactor hr f` quantifies over every open, negative basis, normalized dual
  wedge section, and lift `z`. The right side is `tmulSection rho` of the positive
  `exteriorSheafSection` with the differential images first and the lift last,
  using `Fin.snoc`. The normalized dual evaluates to one on the basis wedge.
- The local existence-and-uniqueness conjunct supplies exactly one such map for
  every model. Its type is H0 of the actual double complex, canonically coker(u).
- The two-model conjunct is the overlap identity: the composite from `P.line` to
  `Q.line` is `(T.modelIso P).inv`, det(a), `(T.modelIso Q).hom`. Its equality says
  `w_P ; D(a) = H0(a) ; w_Q`. Taking a to be lambda_j inverse lambda_i gives precisely
  the displayed t_ij equation; both models may have different negative ranks.
- `W` supplies the global O_X-linear morphism `H0(L) ⟶ det(L)`. The first conjunct
  says its expression in every further model has the wedge formula and characterizes
  it uniquely. `cofactorModelExpression` explicitly composes H0(lambda), the canonical
  H0 restriction comparison, the restricted global arrow, determinant pullback,
  det(lambda) inverse, and the exterior model comparison.
- The final cover conjunct quantifies over an arbitrary index type `I : Type v`,
  open family `U`, `iSup U = top`, specified models and lambdas. It states that the
  expressions of a global arrow on that very cover have the formula iff the arrow
  is W. Thus uniqueness is with respect to the specified cover, without requiring
  an additional all-model hypothesis on the competing arrow. No nonempty index
  hypothesis occurs.
- The naturality conjunct is exactly `w_L ; det(b) = H0(b) ; w_M` for every derived
  isomorphism b of rank-one objects.
- The restriction conjunct covers every open immersion, hence open subschemes,
  refinement maps and scheme isomorphisms. It supplies preservation of the local
  rank-one condition and the transport square, using the canonical determinant
  comparison. `CofactorRestrictionComparison` includes exactness of restriction and
  a comparison whose values on all K-flat representatives equal the fixed existing
  `CotangentPresentation.pullbackCounit` followed by the ordinary adjunction-induced
  restriction map. Hence the cohomology comparison cannot absorb an arbitrary scalar.
  Iterating this transport and the cover uniqueness clause gives refinements.
- There is no separatedness, affine-intersection, cotangent, smoothness, flatness,
  reducedness, regularity, or Noetherian binder.

Recorded statement dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory` (the shared SheafOfModules carrier).
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`, via the recorded model's two freeness fields.
- `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`:
  `Scheme.Modules.exteriorSheaf`, `exteriorSheafSection`.
- `Sheaf.TraceFormula.CanonicalTwoTermPerfectDeterminant`:
  `TwoTermPerfectDeterminantData.IsCanonical`,
  `exists_canonicalTwoTermPerfectDeterminantData`, and its imported
  `TwoTermDeterminantModel`, `.complex`, `.line`, `twoTermDeterminantIso`,
  `twoTermDeterminantValue`, `isTwoTermPerfect`.
- `Sheaf.LinearAlgebra.TwoTermCofactorNaturality`:
  `Module.twoTermCofactor_naturality`, with its actual derived isomorphism, good
  diagrams, independently varying ranks, and normalized determinant maps.

The stated proof dependencies are imported, including cofactor localization descent,
affine tilde, common principal affine intersections, sheaf-Hom gluing, exact open
restriction and the affine quasi-coherent derived equivalence. The proof dependency
`lem-trf-projective-exterior-scalar-comparisons` has no Lean record in the read clone;
no absent module is invented. Its mathematical role is recorded in the proof docstring.

Edge cases checked before writing: c=0 gives the empty negative wedge and the lift as
its sole positive wedge entry. Noninjective and zero differentials are admitted. The
empty scheme and empty cover are admitted and have a unique module-sheaf morphism.
Unequal negative ranks (including a contractible stabilization) are admitted in the
overlap clause. Arbitrary opens and nonseparated intersections are unrestricted.
Scheme isomorphisms and identity restriction are included among open immersions.
The global scheme/module universe u and derived morphism universe w are separate;
the cover index has independent universe v.

Searches (2026-10-24):

- msearch.py leanfinder: "The cofactor morphism from degree zero cohomology of a
  virtual rank one two term perfect complex to its determinant glues on a scheme and
  is natural under derived isomorphisms". Eight hits on general scheme gluing and
  injective-resolution classes; no determinant-valued cofactor statement.
- msearch.py loogle: `"cofactor", "determinant"`. Zero hits.
- msearch.py grep: `cofactor.*(sheaf|complex)|determinant.*cohomology|cohomology.*determinant`.
  Zero Mathlib hits.
- msearch.py leansearch: "Canonical sheaf cofactor map from H0 of virtual rank one
  perfect complex to determinant with descent and derived isomorphism naturality".
  Eight generic derived-functor/sheafification hits; no cofactor statement.
- rg on WeilConjectures and Sheaf for cofactor/Cofactor: the algebraic cofactor
  statement is recorded already; lci-curve formulas require a cotangent presentation
  and are not this general theorem. The upstream determinant wedge-morphism modules
  require a short exact sequence, including injectivity, and do not state derived
  naturality for noninjective two-term models. They cannot replace this statement.
- rg for the item id in WeilConjectures: no match. rg for the proposed declaration
  and rank-one predicates in both roots: no existing declaration.

The helper `cofactorRestriction` explicitly transports the existing restriction functor
to the shared category instances by retaining its object/map data; its additive law
is definitional. `cofactorRestrictionChainMap` has the actual ordinary comparison
as each component, with its commutativity inherited from naturality. No second
restriction construction or arbitrary comparison has been introduced.

Sources opened: duality.tex `lemma-determinant` (Tag 0E9Y), its actual basis-and-lift
formula; more-algebra.tex `lemma-determinant-two-term-complexes` (Tag 0FJM), its
perfect-complex functor and good-diagram construction. This node is the accepted
agent assembly of those inputs, not a unit's own statement. No node correction or
new DAG notion is needed; all auxiliary definitions express parts of this node.

## Second reading by Q44

The dispatcher explicitly prohibits starting another agent; no independent second
reader was started and this section does not claim one. I re-read the node beside
the signature and checked composition directions, the dual-first tensor order,
the appended lift, variable ranks, empty cover, naturality and canonical restriction
normalization. That pass added the explicit local uniqueness, two-model comparison,
and specified-cover iff clauses so the overlap and cover assertions are present in
the statement itself. Independent review remains with the maintainer as in the brief.

Validation: the server confirmation compiler accepted the delivered module in 47.5 s
at nice 19, two threads, and the prescribed 60-second limit, with no errors or
non-sorry warnings. All declarations use `autoImplicit false` and
`relaxedAutoImplicit false`; the longest source line is 97 characters or fewer.
The node copy differs from the original in `lean` alone.
