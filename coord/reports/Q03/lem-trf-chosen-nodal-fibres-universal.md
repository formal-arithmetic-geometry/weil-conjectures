## Worker report

Item: `lem-trf-chosen-nodal-fibres-universal`. The module
`Sheaf.TraceFormula.ChosenNodalFibresUniversal` states
`AlgebraicGeometry.chosen_nodal_fibres_universal`, with its sole proof `sorry`.
It adds no definitions, dependency modules or nodes. The existing node changes only in `lean`.
The source is Stacks curves.tex, Tags 0C56 and 0C59, with morphisms.tex Tags 02NK and
02V4(1). I read those passages and the latest blueprint ancestor
`sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality` and its proof.
The imported DAG refinement has no separately matching statement in that current blueprint;
its mathematical statement is supplied by the recorded Stacks passages.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Schemes and a morphism `f : Y → S` | `{Y S : Scheme.{u}} (f : Y ⟶ S)` |
| Flat | `[Flat f]`, the recorded Mathlib predicate equivalent to flatness of all stalk maps |
| Locally finitely presented | `[LocallyOfFinitePresentation f]` |
| Every nonempty scheme-theoretic fibre is pure of dimension one | `hpure : ∀ s : S, Nonempty (f.fiber s) → (f.fiber s).IsPureDimension 1` |
| A chosen algebraic closure of each residue field | The arbitrary family `k : S → Type u`, its field and `Algebra (S.residueField s) (k s)` instances, and `[∀ s, IsAlgClosure (S.residueField s) (k s)]`. This does not fix the family to Mathlib's canonical closure. |
| The chosen geometric fibre | `pullback f (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) (k s))) ≫ S.fromSpecResidueField s)` |
| Every nonsmooth point of that fibre | `hnodal` quantifies over every `s` and every point `x` of that pullback, with premise that no open `V` containing `x` has `Smooth (V.ι ≫ pullback.snd ...)` |
| Its maximal-ideal-adic completed local ring is the node ring | `Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x)) (C.presheaf.stalk x) ≃+* (MvPowerSeries (Fin 2) (k s) ⧸ Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1}))`, with `C` expanded throughout the actual file |
| Every algebraically closed field and geometric point over `s` | `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : S) (φ : S.residueField s →+* Ω)`. By the recorded `Scheme.SpecToEquivOfField`, this parametrizes exactly all morphisms `Spec Ω ⟶ S`, not only chosen-closure points. Its inverse is exactly `Spec.map (CommRingCat.ofHom φ) ≫ S.fromSpecResidueField s`. |
| An embedding of the chosen closure extending the given residue-field map | `∃ ψ : k s →+* Ω, Function.Injective ψ ∧ ψ.comp (algebraMap (S.residueField s) (k s)) = φ ∧ ...` |
| Associating fibre products identifies `Y_Ω` with `Y_bar_s ×_(k_s) Ω` | An actual scheme isomorphism `e` from the direct pullback along the displayed geometric point to the iterated pullback of the chosen fibre's second projection along `Spec.map (CommRingCat.ofHom ψ)` |
| This is the fibre associativity identification | The two equations on `e.hom` say it preserves the projection to `Spec Ω` and the projection to `Y`. These characterize the canonical identification; an arbitrary unrelated scheme isomorphism is not substituted. |
| Every such geometric fibre is empty or pure of dimension one | `Nonempty (pullback f ...) → (pullback f ...).IsPureDimension 1`. Empty fibres are allowed, exactly as for `hpure`. |
| Every nonsmooth point has completed local ring `Ω[[u,v]]/(uv)` | The subsequent `∀ x`, the same no-smooth-neighbourhood premise, and `Nonempty` of the displayed ring equivalence with coefficients `Ω` |
| The relative smooth locus is open | The existing `f.smoothLocus : Y.Opens` is an open subscheme by its type and construction. The next conjunct identifies its points with exactly those admitting a smooth open neighbourhood. No second smooth-locus definition or tautological openness conjunct is introduced. |
| For every base change the smooth locus is `U ×_S S'` | `∀ (S' : Scheme.{u}) (g : S' ⟶ S), (pullback.snd f g).smoothLocus = pullback.fst f g ⁻¹ᵁ f.smoothLocus`. An inverse-image open subscheme is precisely that open fibre product; equality of opens identifies the full open subschemes, not merely their point counts. |
| A nonsmooth point upstairs has nonsmooth image | The last explicit conjunct `∀ x, x ∉ (pullback.snd f g).smoothLocus → pullback.fst f g x ∉ f.smoothLocus` |
| No quasi-compactness or Noetherian hypothesis on `S` | Neither hypothesis is present; no separatedness, properness, connectedness, surjectivity or flatness of `g` is assumed either. |

All scheme and field sizes follow the existing geometric-point convention: schemes are
`Scheme.{u}` and fields are `Type u`; the theorem is universe-polymorphic. There are no
unbound universes or auto-implicit variables (`set_option autoImplicit false`).
The ring equivalences are ring equivalences, as in the recorded nodal extension dependency;
no coefficient-compatible algebra equivalence is silently required.

Dependency declarations read and used:

| Node(s) | Module and declaration(s) |
| --- | --- |
| def-pc-fibre-product, def-weil-geometric-fibre | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`. Available through public `Mathlib.AlgebraicGeometry.Fiber`. The recorded geometric-fibre realization is expanded literally. |
| def-sbc-locally-finite-presentation | `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `AlgebraicGeometry.LocallyOfFinitePresentation` |
| def-sbc-smooth-morphisms | `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`, `Scheme.Hom.smoothLocus`. Read the smooth-locus construction and its open proof. |
| def-weil-flat-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat` |
| def-weil-algebraic-closure | `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, `IsAlgClosure`. This node's mathlib_match explicitly records these as well as `AlgebraicClosure`; arbitrary closure data require `IsAlgClosure`, not a duplicate notion. |
| def-weil-residue-field | `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.fromSpecResidueField`; available through public `Mathlib.AlgebraicGeometry.Fiber` |
| def-weil-pbc-adic-completion | `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, with its ring structure from public `Mathlib.RingTheory.AdicCompletion.Algebra` |
| def-weil-pbc-multivariate-power-series | `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, variables indexed by `Fin 2` |
| def-weil-pure-dimension | `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension` |
| def-weil-geometric-point | `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.SpecToEquivOfField`, justifying the equivalent `s, φ` parametrization; and public `IsAlgClosed` |
| lem-weil-pbc-algebraic-extension-embeds-algebraically-closed | `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed.lift` (already public for the closure hypotheses) |
| def-weil-finite-type-morphism, lem-weil-pbc-lft-base-change | Private proof import `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` and `locallyOfFiniteType_isStableUnderBaseChange` |
| lem-weil-pbc-smooth-local-on-source | Private proof import `Mathlib.AlgebraicGeometry.Morphisms.Basic`: `IsZariskiLocalAtSource.iff_of_iSup_eq_top` |
| lem-sfb-scheme-flat-smooth-point-base-change | Private proof import `Sheaf.AlgebraicGeometry.FlatSmoothPointBaseChange`: `smooth_at_point_pullback_snd_iff_of_flat` |
| lem-trf-node-algebraically-closed-extension | Private proof import `Sheaf.TraceFormula.NodeAlgebraicallyClosedExtension`: `node_algebraically_closed_extension` |
| lem-trf-relative-dimension-base-change | Private proof import `Sheaf.TraceFormula.RelativeDimensionBaseChange`: `pure_relative_dimension_base_change` |

The theorem docstring records the four accepted DAG proof steps, including the algebraic
embedding, local finite type and pure-dimension base change, nodal field extension, and the
smooth-locus argument. The imports contain every recorded proof-dependency module needed
for that plan. No proofs were supplied at stage 2.

Edge cases checked before writing:

- Empty `Y`, empty `S`, and empty individual fibres: the pointwise nodal conditions are
  vacuous; `hpure` and the geometric dimension conclusion explicitly permit empty fibres.
  If `S` is empty there are no pairs `s, φ`.
- A smooth family: there are no nonsmooth fibre points; its smooth locus is the full source.
- The ordinary node `k[u,v]/(uv)`, including characteristic two: the formal quotient is
  exactly by `X 0 * X 1`, with no division by two or characteristic restriction.
- A transcendental algebraically closed extension `Ω/k_s`, nonclosed `s`, and an arbitrary
  chosen closure: only algebraicity of `k_s/κ(s)` and closedness of `Ω` are used to extend
  the given residue map. `Ω/κ(s)` is not required algebraic.
- Non-quasi-compact source, non-Noetherian base, nonflat base-change map, identity base
  change and an empty base change: all are included; no finiteness assumption was added.
- The smooth-locus equality uses inverse image along `pullback.fst`; the base-changed
  family is `pullback.snd`. The isomorphism also preserves the second (field) projection.

Searches actually run with `batch2/msearch.py Q03 lem-trf-chosen-nodal-fibres-universal`:

- `leanfinder`, query: "Flat locally finitely presented curves nodal over chosen algebraic
  closures have nodal fibres over every algebraically closed field and smooth locus
  commutes with arbitrary base change". Eight hits: generic smoothness/base-change and
  Weierstrass nonsingularity results; no declaration states the node.
- `loogle`, query: `AlgebraicGeometry.Smooth, AlgebraicGeometry.Flat`. Three hits:
  `instFlatOfSmooth`, smooth descent, and `Smooth.of_smooth_fiberToSpecResidueField`.
  None supplies the chosen-closure comparison or the completed nodal local rings.
- `grep`, query: `nodal|ordinary.double|smoothLocus`, subdirectory `AlgebraicGeometry`.
  Ten hits: the scheme smooth-locus definition and uses, but no chosen-nodal-fibre theorem.
- `leansearch`, query: "Chosen algebraic closure nodal curve fibres imply nodal fibres
  at all geometric points and smooth locus commutes with base change". Eight hits:
  ring smooth locus, smooth-base-change results and Weierstrass base change; no full match.
- Local `rg` of `lean/WeilConjectures` and `lean/Sheaf` for smooth loci and nodal material
  found the dependency modules and `HasNodalGeometricFibres`. The latter additionally
  requires connected nonempty fibres and cannot be substituted for this statement.
  `SemistableMarkedBaseChange.smoothLocus_baseChange` specializes to semistable
  multipointed pairs and does not assert the chosen-closure embedding and comparison.
- Exact `rg` for `lem-trf-chosen-nodal-fibres-universal|chosen_nodal_fibres_universal|chosen.*closure.*nodal`
  in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`, plus the
  prescribed `grep -rn` for the node id in `lean/WeilConjectures`, gave no existing match.

Validation: the prescribed `scompile.py` compiled both the sandbox file and its library
module on the server (1.9 s each), with no errors or warnings. Exact signature extracted
from `theorem` to immediately before `:=` into `lean.statement`; every Lean line is at
most 100 characters. No statement correction or disputed mathematical assertion.

## Second reading by Q03

This is the worker's second pass; the dispatch brief assigns independent review to the
maintainer and prohibits starting another agent. I reopened the node and the completed
module and checked the correspondence table above against the binders and the complete
conclusion. In particular, I checked that the closure family is arbitrary, `φ` covers all
geometric points via `SpecToEquivOfField`, `ψ` extends precisely that map, and both
projection equations on the associativity isomorphism have the required directions.
The dimension clauses both retain nonemptiness as a premise, the singularity comparison
is a ring equivalence at every nonsmooth point, and the final universal quantifier allows
every base-change map without flatness. The existing open `f.smoothLocus` supplies the
openness assertion, while its neighbourhood characterization ensures it is the node's
relative smooth locus. The inverse-image open describes the whole open subscheme fibre
product. No missing hypothesis, omitted clause, new notion, or node correction was found;
no change was needed after this pass. Independent mathematical review remains the
maintainer's delivery review, not a claimed second agent review.
