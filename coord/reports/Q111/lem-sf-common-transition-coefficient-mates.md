## Worker report

Stated `WeilConjectures.sfCommonTransitionCoefficientMates` in
`Sheaf.Paper.CommonTransitionCoefficientMates`. Its only proof is `sorry`.
The auxiliary `sfCommonTransitionScalarUnit` is real data: equality transport of
the dependency's canonical scalar unitor onto its published `stageTransition`.
It introduces no independent mathematical notion and postpones no new theorem.
No node statement, dependency list, proof plan, or source is changed.

Hypothesis and clause correspondence:

- The prime is `(l : ℕ) [Fact l.Prime]`; the algebraic closure is
  `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]`.
  `X Y : AlgebraicGeometry.Scheme.{u}` are unrestricted schemes. Scheme and
  closure universes are independent; there is no characteristic or finite-field
  hypothesis on the schemes.
- Finite subfields of Ω are `Padic.FiniteCoefficientFields l Ω`. For each such
  field `i`, `Stage l Ω X i` and `Stage l Ω Y i` are the recorded rational
  constructible categories, using their canonical small coefficient models.
- `stageTransition l Ω X i j h` (and its Y version) is exactly the specified
  scalar transition in `stageSystem`; `stageSystem_existsUnique` identifies it
  with `transition`, which unfolds to `sfRationalScalarExtension`. These are
  actual completed integral scalar extensions followed by raw rationalization.
- The literal pair categories are `Pair l Ω X` and `Pair l Ω Y`; inclusions are
  `inclusion i`, and canonical transitions are `(stageSystem l Ω X).transIso h`
  and its Y version. The imported construction supplies the filtered-colimit
  Hom groups. No substitute category, faithfulness assumption, or completion
  is used.
- `F`, `G`, and `adj : ∀ i, F i ⊣ G i` give all finite-stage adjunctions.
  `FΩ`, `GΩ`, and `adjΩ : FΩ ⊣ GΩ` give the common-stage adjunction.
  Their counits are `(adj i).counit` and `adjΩ.counit`.
- `q i j h` is the natural isomorphism from `F i ⋙ T^Y` to `T^X ⋙ F j`,
  namely the node's `q_{j/i}` in Lean's left-to-right functor notation.
  `b i j h` analogously is from `G i ⋙ T^X` to `T^Y ⋙ G j`.
  `qΩ i` and `bΩ i` are precisely the two common comparison isomorphisms.
- `finite_counit` states for every `i ≤ j` and `L` the composite
  `q_{j/i,G_i L} ≫ F_j(b_{j/i,L}) ≫ ε_j = T^Y(ε_i)`.
  `common_counit` states the same normalization along each inclusion,
  `q_i,G_i L ≫ FΩ(b_i,L) ≫ εΩ = I_i^Y(ε_i,L)`.
  These are exactly all comparison types requested in the node.
- `scalar_assoc` states the rational q associativity equation, including
  the actual `(stageSystem ...).assoc h k` on both X and Y. Its route through
  `q_{j/i}`, then `q_{m/j}`, then `F_m(assoc^X)` equals the route through
  `assoc^Y`, then `q_{m/i}`.
- `scalar_unit` is the rational identity equation
  `q_{i/i,K} ≫ F_i(u^X_i,K) = u^Y_i,F_i K`, with the actual unitors.
  `sfCommonTransitionScalarUnit` uses the functor equality in
  `stageSystem_existsUnique` and then `unitor`; no arbitrary isomorphism is
  chosen in this helper.
- The displayed definition of delta is expanded in `representative_action`:
  its source factors are `tau_im.inv ≫ I_m(q_{m/i}.hom)` and its target
  inverse factors are `I_m(q_{m/j}.inv) ≫ tau_jm.hom`.
  The full right side is `q_i.inv ≫ delta_i ≫ I_m(F_m(v)) ≫
  delta_j.inv ≫ q_j.hom`. Thus this is the exact displayed arrow formula,
  in Lean's order of composition.
- `representative_action` quantifies over every `i,j,m`, inclusions `hi,hj`,
  objects `K,L`, and actual common-stage map `v`. Its left side is
  `FΩ.map (ofHom ... m hi hj v)`, where `ofHom` is the dependency's existing
  quotient constructor. In particular this universal formula includes the
  canonical stage-j representative of the inverse transition; it is not
  restricted to a map inside one finite-stage pair object.
- The first conclusion conjunct quantifies over all `i,j,h,K` and is exactly
  `I_j(q_{j/i,K}) ≫ q_j,TK = tau^Y_ij,F_i K ≫ q_i,K ≫ FΩ(tau^X_ij,K.inv)`.
  This is the first displayed conclusion, with the order reversed only because
  Lean writes composition left to right.
- The second conclusion conjunct quantifies over all `i,j,h,L` and is exactly
  `I_j(b_{j/i,L}) ≫ b_j,TL = tau^X_ij,G_i L ≫ b_i,L ≫ GΩ(tau^Y_ij,L.inv)`.
  This is the second displayed conclusion. The pair-category endpoint
  identifications elaborate directly, so no heterogeneous equality is needed.

Dependencies read and reused:

1. `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
   `WeilConjectures.generalAlgebraicallyClosedConstructibleCategory` and the
   `GeneralAlgebraicallyClosedCoefficients` namespace's `Stage`, `transition`,
   `stageTransition`, `stageSystem`, `stageSystem_existsUnique`, `unitor`,
   `Pair`, `inclusion`, `StageHom`, `ofHom`, and the Hom-colimit specification.
   Its published record explicitly permits arbitrary schemes without a
   `FiniteFieldDatum`. Read the complete signatures and docstrings of the
   constructions used, including the actual scalar associator normalization.
2. `Sheaf.Paper.SfRationalizationKaroubi`:
   `WeilConjectures.sfRationalConstructibleCategory` and
   `WeilConjectures.sfRationalScalarExtension`; the former is the raw scalar
   localization and the latter is fixed on objects and pure tensor morphisms.
   `Stage` and `transition` specialize these recorded declarations.
3. The mathlib leaf `def-weil-pbc-adjunction-mate` has no Lean record; its
   `mathlib_match` is `CategoryTheory.mateEquiv` in
   `Mathlib.CategoryTheory.Adjunction.Mates`. Read its full signature,
   construction, and the counit characterization `mateEquiv_counit`.
   This imported bijection is the proof plan's uniqueness step.
4. Read upstream `CategoryTheory.StageSystem.ι`, `transIso`, `isoToStage`,
   and `PairCategory.mkHom` in `WeilConjectures.CategoryTheory.StageSystem.Basic`.
   These are the concrete constructions reused by the recorded dependency.

Edge cases checked before writing: `i = j` and repeated fields retain actual
unitors and associators; `m = j` is allowed in `representative_action`, as is
`hj = le_rfl`. Thus the inverse-transition identity/unitor representative is
covered. Both conclusions apply to zero objects and zero arrows without an
extra hypothesis. Empty schemes are allowed. There is no empty indexing-set
issue: finite subextensions contain the base coefficient field. No extension
functor or inclusion is assumed faithful. No finite-type or separatedness
hypothesis is needed for this abstract normalized-coefficient argument.

Searches for an existing statement:

- `msearch.py`, leanfinder: "A functor on the finite coefficient pair category
  normalized on common stage representatives commutes with transition
  isomorphisms and its counit normalized right adjoint comparisons commute too".
  Eight hits, all Dold-Kan compatibility results (`hη`, `τ₁`, `hε`,
  `compatibility_N₂_N₁_karoubi`, `N₂Γ₂_compatible_with_N₁Γ₀`,
  `τ₁_hom_app`, `τ₀_hom_app`, `comparisonN`); none states this result.
- `msearch.py`, loogle: `CategoryTheory.mateEquiv`. Twelve hits, including the
  existing mate bijection, its counit and unit equations and pasting laws.
  Reused this dependency; none states the representative-normalized theorem.
- `msearch.py`, grep:
  `commonStage.*[Cc]ocycle|[Cc]oefficient.*[Mm]ate.*[Tt]ransition|pairCategory.*[Tt]ransition`.
  No Mathlib hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id found no
  declaration. Searches for `commonStage`, `pairCategory`, coefficient mates,
  and transition/counit terminology found the recorded pair-category
  infrastructure and specialized exceptional-adjunction results, not this
  theorem with arbitrary supplied normalized adjunctions. A further name
  search for `commonTransitionCoefficientMates` and
  `commonTransition.*[Mm]ate` found no existing declaration.

Read the current blueprint's exceptional-inverse-image definition and
`sk-thm-sf-tensor-hom/_section.md`. The extracted node's proof supplies the
explicit inverse-transition and counit-transpose argument; the theorem
docstring records all five proof steps and the matched mate-bijection leaf.
There are no statement disputes, corrections, new nodes, or dependency repairs.

Validation: `scompile.py` compiled the module in both sandbox and library mode
in 3.5 seconds each, with no error or non-sorry warning. The prescribed `deliver2.py --no-push` dry run passed preflight and
compilation (dry-run commit `15698f95512`).

## Second reading by Q111

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
