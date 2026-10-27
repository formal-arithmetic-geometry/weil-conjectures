## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteEquivariantQuasiSplitNodalFibres` states
`AlgebraicGeometry.exists_finite_equivariant_quasiSplitNodalFibres` and
`AlgebraicGeometry.HasQuasiSplitNodalFibres.baseChange`, each with `sorry`.
There are no new definitions, no axioms and no hidden data constructions.
The main theorem states the finite equivariant quasi-splitting; the second theorem
states the last, independent arbitrary-base-change sentence of the same node.
Both carry source and blueprint docstrings, with the full ten-step proof and the
branch-cover proof of base-change preservation respectively.

The previous worker's blocker confused the stage-1 review with a stage-2 attachment:
the live node is `status: split`, reviewed PASS by L/NL on 2026-10-22, but has no
`lean` or `reviewed_lean` record. This delivery preserves its reviewed mathematical
statement and proof and supplies its missing Lean statement. It does not resplit it.
There is no repair note for this item.

Hypotheses, clause by clause:

* Field: `(k : Type u) [Field k]`.
* A k-scheme S: `(S : Scheme.{u}) (pS : S ⟶ Spec (.of k))`.
  Integrality is `[IsIntegral S]`; normality is `hnormal`, asserting domain and
  integral closure for every local stalk.
* Projectivity is `[IsHProjective pS]`, the recorded finite projective-space
  embedding convention. Its properness instance supplies finite type and
  quasi-compactness, so no redundant finite-type assumptions are needed.
* The family is `(Q : Scheme.{u}) (f : Q ⟶ S)` with `[IsHProjective f]`,
  `[Flat f]` and `[LocallyOfFinitePresentation f]`. H-projectivity supplies
  quasi-compactness and quasi-separatedness, so this is finite presentation.
  Q's k-structure is the composite `f ≫ pS`, rather than an arbitrary extra map.
* `hnodal : HasNodalGeometricFibres f` is the already landed definition:
  every algebraically closed geometric fibre is nonempty connected, has dimension
  one, and its nonsmooth points have completed local ring Ω[[u,v]]/(uv).
  `ConnectedSpace` includes nonemptiness. Its explicit formula uses
  `AdicCompletion (IsLocalRing.maximalIdeal ...) ...` and
  `MvPowerSeries (Fin 2) Ω ⧸ Ideal.span {X 0 * X 1}`.
* `hfibres` supplies reducedness and pure dimension one for each of these
  geometric fibres, using the landed `Scheme.IsPureDimension` definition.
  Thus neither reducedness nor equidimensionality is silently inferred from
  a weaker total-dimension condition.
* Smooth geometrically integral generic fibre is exactly
  `[Smooth (f.fiberToSpecResidueField (genericPoint S))]` and
  `[GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint S))]`.
* `(H : Type v) [Group H] [Finite H]` and the monoid homomorphisms `σk`, `σQ`,
  `σS` give genuine field/scheme automorphism actions, with no faithfulness.
  `hS` and `hQ` impose semilinearity of the k-structures and `heq` imposes
  equivariance of f. The inverse in `Spec.map (σk h⁻¹)` accounts for
  contravariance of Spec, exactly as in the landed one-curve theorem.

Conclusions, clause by clause:

* Existential `J : Type (max u v)` with `Group`, `Finite`, `ρ : J →* H` and
  `Function.Surjective ρ` is the finite extension of the prescribed group.
  This universe admits the finite extension for any scheme/group universes.
* Existential S' has `IsIntegral S'`; its structure over k is `b ≫ pS`.
  `IsHProjective (b ≫ pS)` gives projectivity and finite type; its stalkwise
  normality is written explicitly. No geometric integrality over k is added.
* `IsFinite b ∧ Surjective b` is finite surjective. The dense open U with
  `Etale (b ∣_ U)` is generic etaleness, over the original base S.
* `τS : J →* Aut S'` and `τQ : J →* Aut (pullback f b)` are the output
  actions. Their three equivariance clauses make b equivariant through ρ
  and both projections of Q'=Q×_S S' equivariant. Thus the action is the
  compatible pullback action, not an unrelated action on an abstract family.
  Semilinearity over `σk ∘ ρ` follows by composing these equations with pS.
* For `hb : b (genericPoint S') = genericPoint S`, the composite
  `S.presheaf.stalkSpecializes (specializes_of_eq hb) ≫ b.stalkMap ...`
  is the canonical inclusion k(S)→k(S'). The equivalence for every z says
  precisely that its image consists of the elements fixed by every `j : ρ.ker`
  under the actual induced `Scheme.functionFieldAut (τS j.val)`. This is
  k(S')^kerρ=k(S), without choosing an arbitrary field map or merely requiring
  a purely inseparable intermediate field.
* `HasQuasiSplitNodalFibres (pullback.snd f b)` uses the canonical family Q'.
  The shared definition states rationality of every nonsmooth fibre point,
  exactly two normalization points over it, and rationality of each branch.
  Rationality is surjectivity of a field homomorphism, hence an isomorphism.
* `HasQuasiSplitNodalFibres.baseChange` quantifies independently over every
  flat locally finitely presented nodal family with reduced pure-one geometric
  fibres and the quasi-split predicate, and every scheme S' and map b:S'→S.
  It imposes no projectivity, normality, generic-fibre, field, finite-type-base
  or Noetherian assumption. Its conclusion is the same predicate on the actual
  pullback projection. This states the node's general preservation clause.

Dependency declarations read and used (module, name):

* `def-weil-field`: Mathlib `['Field']`.
* `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
* `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`.
* `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`.
* `def-pc-geometrically-irreducible`: `Mathlib.AlgebraicGeometry.Geometrically.Integral`, `AlgebraicGeometry.GeometricallyIntegral`.
* `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, `AlgebraicGeometry.IsHProjective`.
* `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`.
* `def-weil-surjective-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, `AlgebraicGeometry.Surjective`.
* `def-sc-function-field`: `WeilConjectures.AlgebraicGeometry.FunctionField`, `AlgebraicGeometry.Scheme.functionFieldOfComponents`.
* `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra`.
* `def-pc-field-tower`: `Sheaf.FieldTheory.FieldTower`, `FieldExtension.degree`.
* `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `AlgebraicGeometry.Flat`.
* `def-sbc-locally-finite-presentation`: `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, `AlgebraicGeometry.LocallyOfFinitePresentation`.
* `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
* `def-weil-geometric-fibre`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `CategoryTheory.Limits.pullback`.
* `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`.
* `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `CategoryTheory.Limits.pullback`.
* `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`, `topologicalKrullDim`.
* `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`.
* `def-weil-pbc-reduced-normalization`: `Sheaf.AlgebraicGeometry.ReducedNormalization`, `AlgebraicGeometry.Scheme.reducedNormalization`.
* `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`, `AdicCompletion`.
* `def-weil-pbc-multivariate-power-series`: `Mathlib.RingTheory.MvPowerSeries.Basic`, `MvPowerSeries`.
* `def-trf-nodal-geometric-fibres`: `Sheaf.AlgebraicGeometry.NodalGeometricFibres`, `AlgebraicGeometry.HasNodalGeometricFibres`.
* `def-weil-pure-dimension`: `Sheaf.AlgebraicGeometry.PureDimension`, `AlgebraicGeometry.Scheme.IsPureDimension`.
* `def-sfb-quasi-split-nodal-fibres`: `Sheaf.AlgebraicGeometry.QuasiSplitNodalFibres`, `AlgebraicGeometry.HasQuasiSplitNodalFibres`.

The auxiliary canonical field automorphism is the upstream
`WeilConjectures.AlgebraicGeometry.StalkAut`, `Scheme.functionFieldAut`.
The integral function field itself is the generic stalk from Mathlib, imported
through the dependency's upstream `WeilConjectures.AlgebraicGeometry.FunctionField`.
The latter's component-product definition is not a replacement for this generic stalk.
The retained field-tower module supplies the dependency's extension conventions.

Proof imports follow every already-stated proof dependency, including the
Mathlib matches. `lem-sfb-nodal-branch-double-cover` and
`lem-sfb-equivariant-finite-residue-domination` have no Lean record or usable
Mathlib match on the current read clone, so there is no module to import for them.
They are proof prerequisites only; no statement notion or canonical map is
missing because of them, and they are not restated or assumed as new hypotheses.

Edge cases checked before writing:

* A smooth fibre has no nonsmooth points. The quasi-split predicate is vacuous
  there; no fake singular point or branch is required.
* Split self-nodes are admitted: reduced normalization may be connected and
  the definition asks for two points over the node, not two distinct components.
* A nonsplit node fails the rational-branch condition even when its singular
  point is rational; both clauses are retained. Nodes with a nontrivial
  separable residue field likewise require the extension to split that field.
* Characteristic two is admitted: there is no 2-invertibility assumption;
  uv and its two branches make sense in every characteristic.
* Empty S is excluded exactly by the integral-base hypothesis; empty Q over
  nonempty S is excluded by the nonempty geometric-fibre hypothesis.
  The base-change theorem permits the empty new base, when its conclusion is
  vacuous. Dimension-zero S is admitted without any extra condition.
* The trivial or nonfaithful group action is admitted. For an already
  quasi-split family the identity base cover and identity group map are
  consistent with every conclusion and the kernel fixed-field equation.
* The base-change theorem admits non-Noetherian, nonreduced and disconnected
  new bases; no normalization of a total space is claimed to commute with b.
* Geometric test fields live in the scheme universe, exactly as in the
  landed definition; no extra equality between independent universes is imposed.

Searches for an existing statement or notion:

* `msearch.py ... leanfinder "A semistable curve family becomes quasi split by a
  finite generically etale equivariant Galois base change"`: eight results,
  including etale base-change stability, smooth relative-dimension base-change
  stability and etale field-algebra product decomposition. None states the
  finite equivariant quasi-splitting assertion or its branch-rationality clause.
* `msearch.py ... loogle '"nodal"'`: twelve polynomial interpolation declarations
  (`Lagrange.nodal`, `Lagrange.nodalWeight`, etc.), no curve statement.
* `msearch.py ... grep 'quasi.?split|[Nn]odal|[Ss]emistable' AlgebraicGeometry`:
  zero Mathlib hits.
* `rg` of the exact item id in `lean/WeilConjectures` and `lean/Sheaf`:
  only the proof citations in `EquivariantSingleCurveNodalReduction`, no theorem.
* `rg 'quasi.?[Ss]plit|QuasiSplit|IsNodal|isNodal|Semistable|semistable'` in
  both project AlgebraicGeometry source trees found the shared predicates
  `HasNodalGeometricFibres`, `HasQuasiSplitNodalFibres` and the existing
  `Scheme.IsPureDimension`. Their full definitions and owning nodes were read.
  These three already-landed definition ids are added to stmt_deps; none is
  copied, generalized privately, or created again.

Primary source read: [de Jong (1997), publisher scan](https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf),
printed pp. 614--615 (PDF pp. 16--17), definition before Lemma 5.7 and its proof,
and the base-change use in Theorem 5.9 on printed p. 617. The reviewed node's
hypotheses and stronger explicit kernel fixed-field equation are retained.
No statement correction and no STATEMENT-DISPUTED fault.

Validation: the prescribed `scompile.py NB lem-sfb-nodal-finite-quasi-splitting`
compiled this complete module in sandbox and library form against the live
published build, with no errors or warnings reported (2.4 s and 2.3 s).
Independent mathematical review is performed by the maintainer on delivery;
no additional agent was started, as the dispatch brief requires.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
