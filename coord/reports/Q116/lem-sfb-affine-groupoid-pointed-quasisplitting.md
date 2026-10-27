## Worker report

The module `Sheaf.AlgebraicGeometry.AffineGroupoidPointedQuasisplitting` states
`AlgebraicGeometry.affine_groupoid_pointed_quasisplitting`, with one `sorry` and no
new definitions. The natural-language proof in its docstring follows all six
steps of the accepted DAG proof. Source read: Stacks `spaces-more-groupoids.tex`,
`definition-split-at-point` (04RK), `situation-quasi-splitting`,
`lemma-strong-splitting-affine-scheme` (04RZ), and
`lemma-quasi-splitting-affine-scheme` (04S0).

Clause-by-clause correspondence:

- `S : Scheme.{u}` and `R U : Over S` supply the base and both schemes over it.
  `s t e i` are morphisms in `Over S`. The composition `c` is a scheme morphism
  on the chosen scheme pullback; the groupoid source law makes it over `S`.
- `hG : IsGroupoidScheme s.left t.left e.left i.left c` supplies exactly the
  dependency's groupoid laws on all test schemes.
- `[IsAffine U.left]` renders affineness of the object scheme.
- `[IsSeparated s.left]` and `[IsSeparated t.left]` render the two closed-diagonal
  hypotheses. `[Flat ...]` and `[LocallyOfFinitePresentation ...]` render both
  flatness and local finite-presentation hypotheses.
- `hs` and `ht` use `Scheme.Hom.IsLocallyQuasiFinite`, the dependency's Stacks
  definition including local finite type, rather than Mathlib's weaker predicate.
- `u₀ : U.left` is arbitrary. The existential `W : Over S`, `g : W ⟶ U`,
  `w : W.left` supplies an S-scheme neighborhood, an S-map, and the marked point.
  `IsAffine W.left`, `Etale g.left`, and `g.left w = u₀` are the first three clauses.
- `IsIso (g.left.residueFieldMap w)` means the actual induced field homomorphism
  is an isomorphism. Its source is the residue field at `g.left w`, identified
  with the field at `u₀` by the preceding equality; no arbitrary field isomorphism.
- `restrictedEtaleRelation s t g` is the existing iterated pullback in `Over S`:
  `(W ×_U R) ×_U W`. Its existing Source and Target are the first and last
  endpoint projections. The six conjunctions assert flatness, local finite
  presentation and local quasi-finiteness for each projection.
- The existential `eW iW cW`, together with `IsGroupoidScheme`, supplies the
  restricted groupoid. The next two equations fix the original unit and inverse
  after forgetting endpoints. For composition, the quantified `p,q` are related
  by both pullback projection equations; the resulting equality says the middle
  arrow is the original composition. For every `p` there is exactly one such
  `q`, by the pullback universal property and the endpoint equations. This clause
  is not vacuous. The middle map is written explicitly as projections, not a
  private copy of a construction or an arbitrary map.
- `P : (restrictedEtaleRelation s t g).left.Opens` is an actual open subscheme.
  `eP ≫ P.ι = eW` factors the ENTIRE unit section through it. `iP ≫ P.ι =
  P.ι ≫ iW` says inverse restricts. The two projection equations uniquely fix
  `k` as the induced map on composable pairs, and `cP ≫ P.ι = k ≫ cW` says
  composition restricts. Thus these are the inherited operations, not merely
  some unrelated groupoid structure on the same open subset.
- `IsGroupoidScheme` on these restricted maps is the asserted open subgroupoid.
  The last two clauses use `Scheme.Hom.IsFiniteLocallyFree` for both projections.
- Every scheme, open and fibre product has scheme universe `u`; test schemes
  have the same bound. No extra independent small test universe is used.

Dependencies used (full declarations read with docstrings):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec` and `Spec.map`; affine schemes are the existing `IsAffine` from
  `Mathlib.AlgebraicGeometry.AffineScheme`.
- `Sheaf.AlgebraicGeometry.GroupoidScheme`: `AlgebraicGeometry.IsGroupoidScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsSeparated` from its Separated
  import; the node asks only for separatedness, never properness.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `Scheme.Hom.IsLocallyQuasiFinite`, unfolding to `IsQuasiFiniteAtPoint` everywhere.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, with scheme pullbacks available from GroupoidScheme.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`; here an actual
  `Scheme.Opens` and its `toScheme` and `ι` give the open subscheme directly.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `Scheme.Hom.IsFiniteLocallyFree`, extending finite, flat, locally finitely presented.
- `def-weil-size-convention` is the existing metatheoretic convention: no Lean object.
- The already landed `def-sfb-restricted-groupoid-relation` is added to stmt_deps
  under the explicit rule allowing landed nodes. Its declarations are
  `AlgebraicGeometry.AlgebraicSpace.restrictedEtaleRelation`,
  `restrictedEtaleRelationSource`, `restrictedEtaleRelationTarget` in
  `Sheaf.AlgebraicGeometry.EtaleRelationRestrictionQuotient`. All three were read:
  none imposes etaleness, monicity, surjectivity or a cover assumption.

All recorded non-Mathlib proof modules are plain imports. The four proof nodes
`lem-sfb-section-marked-finite-parts-scheme`, `lem-sfb-universal-finite-parts-groupoid`,
`lem-sfb-separated-lqf-affine-finite-set`, and
`lem-sfb-locally-free-groupoid-invariant-affine` have no Lean declaration at this
checkout, so no speculative imports are added for them. No import cycle is added.

Edge cases checked before writing: if U is empty there is no u₀, so the assertion
is vacuous; no Nonempty hypothesis is imposed. For the unit groupoid, the identity
neighborhood and full open work. Nontrivial stabilizers and multiple arrows are
retained: no monicity/equivalence-relation hypothesis was inserted. A finite locally
free relation may have variable rank; no constant degree or positive fixed rank
was imposed. On a nonempty W the unit forces each source fibre to be nonempty,
as the source requires. No separatedness or surjectivity of g is added, and no
stabilizer-containment condition from strong splitting is added. Residue fields
need not be perfect or algebraically closed.

Searches made with the prescribed msearch.py (Q116, this item):

- leanfinder: "A separated flat locally quasi finite groupoid scheme admits a
  pointed affine etale neighborhood with a finite locally free open subgroupoid".
  Eight hits, including ordinary smooth/etale neighborhoods and Scheme.local_affine;
  none is the requested theorem.
- loogle: `"Scheme", "Groupoid"`: zero hits.
- grep of Mathlib/AlgebraicGeometry:
  `quasi.splitting|quasiSplitting|finite.*subgroupoid`: zero hits.
- rg of lean/WeilConjectures and lean/Sheaf with the same pattern: only unrelated
  finite quasi-splittings of nodal curves and consumers, no matching declaration.
- grep -rn of the exact item id in lean/WeilConjectures: no hits.
- rg of `affine_groupoid_pointed_quasisplitting` in Mathlib, WeilConjectures, Sheaf,
  and dag/lean_names_upstream.json: no existing declaration.
- Read the existing restricted-relation node and both EtaleRelationRestrictionQuotient
  and FppfGroupoidRestrictionQuotient modules; reused the former's definitions
  without introducing any new helper notion.

No node fault or disputed statement was found. The TeX statement, accepted proof,
and proof dependencies are unchanged. Only lean and the landed definition-node
addition to stmt_deps change. First scompile.py pass: sandbox and intended library
module both clean (6.9 s and 3.3 s), with no diagnostic beyond permitted sorry.

## Final author checks

A final author check reopened the node and the signature. No separate agent was
used, as this dispatch prohibits starting other agents. The delivery wrapper adds
the standing note that the maintainer performs the independent review.

Checked the base-S data and all hypothesis binders against the node, the
arbitrary marked point, the four neighborhood clauses, all six restricted
projection properties, and both finite locally free assertions. In particular,
checked that the composition middle-coordinate implication is nonvacuous:
composable restricted arrows satisfy equality of their middle s/t coordinates
because their endpoint coordinates agree. The original pullback then gives q.
The eW and iW endpoint coordinates are fixed by the groupoid source/target laws.
For the open subgroupoid k is fixed by its two projections. Thus both sets of
operations are the source's canonical restrictions. Open P contains all units,
not just the marked one. The entire statement stays in Scheme.{u}.

The only correction during this pass was a documentation tag: the strong affine
splitting proof is 04RZ, not 04RY (which is the quasi-splitting-scheme lemma).
No mathematical or Lean signature change was needed. Rechecked lines <= 100,
explicit universe and variable binding, sorry-only theorem body, and verbatim
lean.statement extraction. No new node or dependency module is delivered.

## Second reading by Q116

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
