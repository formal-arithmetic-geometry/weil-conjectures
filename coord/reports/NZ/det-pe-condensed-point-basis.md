## Worker report

The module `Sheaf.Paper.CondensedPointBasis` states the entire node as
`AlgebraicGeometry.ProEtale.condensed_point_basis`. This is the only postponed theorem;
its proof is `sorry`, and its docstring carries all nine steps of the DAG proof,
including the non-surjective inverse-system and empty-space cases. The natural statement,
statement dependencies, proof and proof dependencies are unchanged.

Two construction helpers belong to the same node and appear in `lean.declarations`:
`condensedPointAlgebraFunctor` has actual object data `CommAlgCat.of Ω (LocallyConstant S Ω)`
and sends a map to the opposite of `LocallyConstant.comapₐ Ω f.hom.hom`;
`condensedPointSchemeFunctor` composes it with the existing `AlgebraicGeometry.algSpec`.
Thus neither helper chooses data from a postponed existence statement. Both are the
specified functor in the node, with real ring and scheme data and the intended arrows.
The structure proofs in the algebra functor are discharged by the existing constructor
defaults, just as in the published integer-valued functor. No mathematical theorem is proved.

Clause-by-clause correspondence:

- The field hypothesis is `(Ω : Type u) [Field Ω]`, and separable closedness is
  `[IsSepClosed Ω]`, using the dependency's Mathlib definition. No characteristic,
  algebraic closedness or perfection assumption is added.
- A profinite set is `S : Profinite.{u}`. Its canonical Ω-algebra is
  `LocallyConstant S Ω`, using Mathlib's pointwise commutative ring and constant-scalar
  algebra structure. In particular no topology on Ω, and no stronger continuous-function
  notion, is imposed.
- The introductory `Ω[S] = Spec LC(S,Ω)` is the object of
  `condensedPointSchemeFunctor Ω`; `algSpec` supplies the structure morphism from the
  constant-scalar map. Its action on arrows is precisely the spectrum of precomposition.
- Clause (1) is the first conjunct. It quantifies over `(A : Type u) [CommRing A]
  [Algebra Ω A]` and assumes `Algebra.Etale Ω A` and `Algebra.FinitePresentation Ω A`.
  The conclusion `∃ n : ℕ, Nonempty (A ≃ₐ[Ω] (Fin n → Ω))` is an Ω-algebra isomorphism
  to Ω^n. The node's equality with locally constant functions on a finite discrete set
  is the ordinary identification of all functions on `Fin n` with locally constant ones.
  Finite presentation is explicitly retained as in the text, although it already follows
  from `Algebra.Etale`.
- The forward half of (2) is the second conjunct: every Ω-algebra whose scalar map
  satisfies `RingHom.IndEtaleAcrossUniverses` is Ω-algebra-isomorphic to
  `LocallyConstant S Ω` for some `S : Profinite.{u}`. The converse half is the third
  conjunct, asserting that exact ind-etale predicate for every such locally constant
  algebra. These use the recorded universe-transported interface of
  `def-weil-pbc-ind-etale-algebra`, without a private filtered-colimit predicate.
- Clause (3) is the fourth conjunct. Its function has domain `C(T,S)` and codomain
  `LocallyConstant S Ω →ₐ[Ω] LocallyConstant T Ω`, and sends `s` to
  `LocallyConstant.comapₐ Ω s`. Mathlib's definition sends `f` to `f ∘ s` literally.
  `Function.Bijective` expresses both existence and uniqueness for every algebra map.
- The equivalence in the penultimate paragraph is the fifth conjunct. It asserts an
  actual categorical equivalence `E` from `Profinite.{u}` to the full subcategory of
  `Over (Spec (.of Ω))` defined by `IsAffine Y.left ∧ proAffineEtale Y.hom`.
  Its forward functor, followed by `ObjectProperty.ι`, is naturally isomorphic to
  the specified `condensedPointSchemeFunctor Ω`. Thus this is the equivalence for the
  specified spectra and precomposition arrows, with all base-compatible scheme maps.
  `proAffineEtale` is the existing inverse-limit predicate in the recorded dependency's
  public imports; `proAffineEtale_Spec_iff` identifies it with ind-etale scalar maps.
  No arbitrary equivalence unconnected with the specified construction is substituted.
- The last sentence is the last conjunct, the natural isomorphism in the over-category
  between that exact spectrum functor and
  `profiniteToProEtOf (Spec (.of Ω)) ⋙ Scheme.ProEt.forget (Spec (.of Ω))`.
  This explicitly uses `def-sfb-profinite-test-objects` and retains naturality in S and
  compatibility with the structure morphisms. Forgetting the site's extra property
  gives the same over-schemes, not merely their underlying spaces.
- The size convention is expressed by the explicit common universe `u` on Ω, algebras,
  profinite spaces and schemes. The theorem is universe-polymorphic and can be used in
  any common universe containing the rings and spaces under consideration. It does not
  equate the small pro-etale site's object and morphism universes or add any size or
  essential-smallness hypothesis to that site.

Statement dependency declarations read and used:

- `def-sfb-profinite-test-objects`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.profiniteToProEtOf`. Read both the framework clone's module
  and the current published source through `scompile.py --source`; the latter contains
  the updated proofs while retaining this exact definition. Its result is a functor to
  `(Spec Ω).ProEt`, and `Scheme.ProEt.forget` lands in the over-category.
- `def-pc-separably-closed`: `Mathlib.FieldTheory.IsSepClosed`, `IsSepClosed`.
- `def-weil-pbc-ind-etale-algebra`: `Sheaf.RingTheory.IndEtaleUniverseTransport`,
  `RingHom.IndEtaleAcrossUniverses`. Read its full definition: it applies the original
  `RingHom.IndEtale` to `RingHom.ulift f`, canonically putting both rings in the common
  universe. The publicly imported original definition `Algebra.IndEtale` is a filtered
  colimit presentation by etale algebras. Its same-universe clause and
  `AlgebraicGeometry.proAffineEtale_Spec_iff` were also read in the upstream sources.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, `Spec.map`; the existing relative bundling is `algSpec` in
  `Mathlib.AlgebraicGeometry.Group.Affine`. The latter composes the algebra/under-category
  equivalence, opposite-over equivalence and `Over.post Scheme.Spec`.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`. Clause (1) uses the corresponding ring predicate
  `Algebra.Etale`, permitted by the standing convention; the affine comparison is the
  recorded `HasRingHomProperty.Spec_iff` with the Etale instance.
- `def-weil-pbc-finitely-presented-algebra`: `Mathlib.RingTheory.FinitePresentation`,
  `Algebra.FinitePresentation` (finite polynomial presentation with finitely generated kernel).
- `def-weil-size-convention`: a metatheoretic convention, no importable declaration;
  explicitly accounted for by universe polymorphism as above.

All stated proof-dependency modules are imported, including
`Mathlib.AlgebraicGeometry.GammaSpecAdjunction` (`Spec.reflective` and `Spec.homEquiv`),
`Mathlib.AlgebraicGeometry.Limits` (`sigmaSpec`, `ι_sigmaSpec`, finite IsIso instance),
`Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties` (`HasRingHomProperty.Spec_iff`),
`Mathlib.CategoryTheory.Limits.HasLimits` (colimit interfaces),
`Mathlib.RingTheory.Etale.Field` (`Algebra.Etale.iff_exists_algEquiv_prod`),
`Mathlib.RingTheory.Etale.Pi` (finite-product etaleness),
`WeilConjectures.Mathlib.RingTheory.Etale.Field`
(`Algebra.Etale.of_finite_of_isSeparable`), `Mathlib.FieldTheory.IsSepClosed`
(`IsSepClosed.algebraMap_bijective`), `Mathlib.Topology.Compactness.Compact`
(`IsClosed.isCompact`, `Pi.compactSpace`), `Mathlib.Topology.Homeomorph.Lemmas`
(`isHomeomorph_iff_continuous_bijective`), `Mathlib.Topology.Separation.Profinite`
(`isTopologicalBasis_isClopen`), and
`Mathlib.Topology.Category.Profinite.CofilteredLimit` (`Profinite.exists_locallyConstant`).
Their recorded source signatures and docstrings were inspected; none introduces a nonempty
space or surjective-transition requirement. The main theorem docstring cites the node ids
for these steps.

Edge cases checked before writing:

- `n = 0` is allowed: `Fin 0 → Ω` is the zero ring, with its usual Ω-algebra structure.
  No `Nontrivial A`, `FaithfulSMul Ω A` or injectivity of the scalar map is assumed.
- The empty profinite space is allowed in both directions of (2), gives the zero ring
  and empty spectrum, and is included in the full subcategory and the equivalence.
- In (3), when T is empty both sides are singletons; when S is empty and T nonempty
  both sides are empty because a unital map from the zero ring to the nonzero locally
  constant ring cannot exist. When both are empty both sides are singletons.
- A singleton S gives the field itself; finite discrete S gives the stated finite powers.
- Separably closed imperfect fields of positive characteristic are included. In particular
  the theorem never replaces separable closedness by algebraic closedness.
- Arbitrary cofiltered finite inverse systems, including non-surjective transitions and
  empty stages, are retained in the proof plan; no such restriction is added to the
  ind-etale definition or conclusions.

Searches for an existing statement or construction:

- `msearch.py leanfinder`, query `ind etale algebras over separably closed field locally
  constant functions profinite equivalence`: 8 hits, including
  `Algebra.Etale.iff_exists_algEquiv_prod` and
  `Algebra.FormallyEtale.iff_exists_algEquiv_prod`. These are finite-stage ingredients,
  not the ind-etale classification, categorical equivalence and relative-test comparison.
- `msearch.py loogle`, query `Algebra.Etale, LocallyConstant`: 0 hits.
- `msearch.py leansearch`, query `ind etale algebras over a separably closed field correspond
  to profinite sets`: 8 hits, headed by `Algebra.Etale`,
  `Algebra.FormallyEtale.of_isSeparable`, and the finite-product classification; no whole match.
- `msearch.py grep`, query `LocallyConstant.*(IndEtale|algHom)|[Ii]ndEtale.*LocallyConstant`:
  3 documentation hits in `Mathlib/Topology/LocallyConstant/Algebra.lean`, for comap/map/const
  algebra homomorphisms. Used the existing `LocallyConstant.comapₐ` for the required map.
- Direct `rg` of Mathlib, the slopmaster2 `WeilConjectures`, and the shared `lean/Sheaf`
  for `Profinite.*CommAlgCat|CommAlgCat.*Profinite|profinite.*[Aa]lg.*[Ff]unctor|
  [Ff]unctor.*profinite.*[Aa]lg` found no existing locally constant Ω-algebra functor.
  Searches for `LocallyConstant.*≌|≌.*LocallyConstant|[Ii]ndEtale.*[Ii]sSepClosed|
  [Ii]sSepClosed.*[Ii]ndEtale` found no matching statement (only unrelated locally constant
  sheaf category equivalences).
- Direct node-id search in upstream `WeilConjectures` found no declaration for this node.
  Direct searches in shared `lean/Sheaf` found `condensed_point_basis_evaluation`, which
  is a different sheaf-evaluation result. The relative profinite-test-object theorem is
  also different: its finite-limit, covering and relative-limit clauses do not give this
  field-specific algebra classification or equivalence.
- Read the nearby node `def-weil-pbc-profinite-locally-constant-hom-equiv` and the current
  upstream helper of that name. It concerns integer-valued functions and connected
  components of arbitrary spectra, rather than the Ω-algebra Hom map here; it cannot
  replace the whole item. The current integer-valued scheme functor is likewise reused
  through `profiniteToProEtOf`, not copied or replaced.

No new definition nodes, dependency repairs or statement corrections are needed.
No statement dispute was found.

Validation: `scompile.py NZ det-pe-condensed-point-basis` compiled the module cleanly,
with separate sandbox and final-module passes (8.7 s and 3.1 s in the initial pass).
The required delivery dry run and final delivery are run after completion of this report.

## Second reading by NZ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
