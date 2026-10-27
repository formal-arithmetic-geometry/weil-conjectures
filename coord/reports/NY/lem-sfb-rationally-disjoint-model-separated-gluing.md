## Worker report

The module `Sheaf.AlgebraicGeometry.RationallyDisjointModelSeparatedGluing` states
`AlgebraicGeometry.exists_separated_gluing_of_rationally_disjoint_models`, with `sorry`
as its entire proof. There are no definitions, helper theorems, new nodes, dependency
repairs, or statement corrections. The copied node changes only `lean`.

Source read: Bosch–Lütkebohmert–Raynaud, *Néron Models*, 4.3 Proposition 4, first two
proof paragraphs, printed pp. 106–107, PDF pages 112–113 (zero-based):
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf .
The source shrinks special fibres using projections of schematic cross-diagonal
closures, and then glues along the generic fibres. The node isolates this geometric
argument with the explicit no-rational-identity hypothesis, without its surrounding
minimal-model/group-law applications. The docstring carries all eleven node proof
steps, including the local integral-neighbourhood argument rather than assuming an
integral global generic fibre.

Hypotheses and contextual conventions, clause by clause:

- `R : Type u`, `[CommRing R] [IsDomain R] [IsDiscreteValuationRing R]` give the DVR;
  `π` and `_hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}` give the uniformizer.
- `E`, `[Field E] [Algebra R E] [IsFractionRing R E]` give its fraction field.
  The trait is literally `Spec (.of R)`; its generic inclusion is
  `Spec.map (CommRingCat.ofHom (algebraMap R E))`.
- The residue field is taken canonically: `(m i).fiber (IsLocalRing.closedPoint R)`
  is the scheme-theoretic special fibre over the closed point. Thus no arbitrary
  field or unspecified residue map replaces k. `Scheme.Hom.fiber` is the existing
  pullback along `fromSpecResidueField`.
- The paragraph naming strict henselization, its fraction field, birational maps,
  and the maximal rational-map domain supplies background conventions. None occurs
  in the substantive hypothesis or conclusion of this lemma, so no extra choices
  of geometric point, strict henselization, or birational map are assumed. The
  recorded strict-henselization dependency is imported, rather than redefined.
- `X`, its structure map `x`, and `[Nonempty X] [Smooth x] [IsSeparated x]
  [LocallyOfFiniteType x] [QuasiCompact x]` give exactly the nonempty smooth
  separated finite-type E-scheme.
- `r`, `_hr : 0 < r`, `M : Fin r → Scheme.{u}`, and `m` give the nonempty finite
  indexed family. The four indexed classes on `m i` give the model properties.
- `g i : X ⟶ M i` together with `hg i : IsPullback (g i) x (m i) ...` specifies
  the generic-fibre identification as an E-scheme, including its structure map.
  This is the universal property of the scheme-theoretic base change; it neither
  assumes a mere pointwise bijection nor allows an arbitrary generic map.
- `h_irred` requires `IrreducibleSpace` of every special fibre. This Mathlib class
  includes `Nonempty` (Topology/Irreducible.lean:174–180), so both clauses are present.
- `h_disjoint` quantifies over every ordered distinct pair, giving both directions.
  For a representative `f : U.toScheme ⟶ M j`, the condition
  `∀ t, Dense ((m i).fiberι t ⁻¹' (U : Set (M i)))` says exactly that U is dense
  in every scheme-theoretic fibre, including the generic and special ones.
  `f ≫ m j = U.ι ≫ m i` says the representative is over the trait.
  A map `s : X ⟶ U.toScheme` with `s ≫ U.ι = g i` says its domain contains the
  entire generic fibre; `s ≫ f = g j` says its generic map is the specified identity.
  Negation of existence of these representatives is equivalent to the node's
  no-rational-identity condition: a rational identity on a base-dense open agrees
  with the identity on its generic restriction, and glues with the identity on
  all X. This enlarges its domain by X without losing fibrewise density. In the
  other direction the displayed data is already such a representative. If generic
  agreement is expressed on a smaller dense open, smoothness makes X reduced and
  separatedness gives equality on that entire generic restriction. Thus this
  normalization adds no hypothesis. No quotient of ordinary rational maps, whose
  density condition differs, is substituted for trait-relative rational maps.

Conclusions, clause by clause:

- `V : ∀ i, (M i).Opens` are actual opens of the original models.
  `a i : X ⟶ (V i).toScheme` and `a i ≫ (V i).ι = g i` retain the entire generic
  fibre. Since the generic inclusion is an open immersion by the DVR fraction
  inclusion, this also identifies the generic fibre of each V_i with X.
- The quantified `ξ` is a special-fibre point. `IsGenericPoint ((m i).fiberι _ ξ)
  (Set.range ((m i).fiberι ...))` says its image is the generic point of the closed
  special fibre in M_i; the conclusion places it in V_i. This uses exactly the
  recorded `IsGenericPoint` definition, rather than assuming a choice of point.
- For distinct indices the existential `d` maps X into the scheme-theoretic product
  `pullback ((V i).ι ≫ m i) ((V j).ι ≫ m j)`. Its two projection equations identify
  it with the cross diagonal, and `IsClosedImmersion d` gives scheme-theoretic
  closedness, not only closedness of its point image.
- `Y`, `y`, `Smooth y ∧ IsSeparated y ∧ LocallyOfFiniteType y ∧ QuasiCompact y`
  express the smooth separated finite-type scheme over the original trait.
- `c i` are open immersions; their equations with y make them trait morphisms,
  `a i ≫ c i = w` glues their generic identities, and the quantified points p,q
  express that the charts cover Y.
- `IsPullback w x y ...` identifies Y_E with the specified E-scheme X.
  For distinct charts, `IsPullback (a i) (a j) (c i) (c j)` states that their
  intersection is exactly the common generic X. Together with the open covering
  this characterizes the asserted gluing, without an arbitrary identification
  elsewhere on the special fibre.
- `z i` are the special-fibre chart morphisms; their equations after `y.fiberι`
  characterize them as the canonical base changes of `c i`. The final
  `Nonempty (IsColimit (Cofan.mk ... z))` states Y_k is their coproduct as schemes.
  These maps are over the residue field by their defining equations and the
  special-fibre pullback property, so this is also the claimed k-scheme coproduct.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Spec`, `Spec.map` (definitions at
  lines 42, 470, 479), for the objects, morphisms and affine base.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`
  (58–60), and `irreducible_iff_uniformizer` (93), for the DVR and its generator.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded
  `baseChange_morphism_projections`, `baseChange_fiber`, and their pullback
  convention; the underlying existing `Scheme.Hom.fiber` and `fiberι` are read
  in `Mathlib.AlgebraicGeometry.Fiber` (38,41).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth` (62–66).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` (43–47),
  together with `QuasiCompact` in Morphisms/QuasiCompact.lean (43–45).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`
  (45–46). `IsSeparated` from Morphisms/Separated.lean (44–46) is exactly
  closedness of the diagonal, as the node specifies.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion` (38–39).
- `Mathlib.Topology.Sober`: `IsGenericPoint` (39–40).
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`: the recorded
  `Scheme.strictHenselizationRing` (126–132), its docstring, scheme and properties
  read through line 192; not used as additional mathematical data here.
- The geometric-point inline convention was read in the dependency node and in
  `Scheme.SpecToEquivOfField`, Mathlib.AlgebraicGeometry.ResidueField (346ff),
  together with `IsAlgClosed`; no geometric-point datum occurs in this lemma.

All recorded statement dependency interfaces are usable. Stated proof dependencies
are imported non-publicly, including regularity, reduced images, fibre stalks and
gluing, as required for the node's stage-3 proof plan. There is no global build.

Edge cases: r=1 makes every mixed-pair condition vacuous, admits V_1=M_1, Y=M_1,
and leaves a singleton special-fibre coproduct; r=0 is explicitly excluded, exactly
as in the node. Empty X and empty special fibres are excluded by the stated hypotheses.
X is allowed to be disconnected: its component(s) not meeting the special fibre are
retained by the factorization of the whole X. No integrality or irreducibility of
X, M_i, or Y is assumed. No restriction on characteristic or on strict henselianity
of R is introduced. Fibrewise density, rather than density just in the total space,
prevents the generic open alone from supplying a forbidden rational map. All ring,
field, and scheme data share the explicit universe u; any concrete datum can be
placed in a common ambient universe, and all variables are bound explicitly with
`set_option autoImplicit false`.

Searches actually run (2026-10-24):

- `msearch.py ... leanfinder "Smooth models over a discrete valuation ring with no
  rational identity maps can be shrunk and glued to a separated scheme"`: 8 hits,
  including generic smooth charts, separatedness criteria and
  `Scheme.GlueData.gluedScheme`; none states the shrinking result.
- `msearch.py ... leansearch "Smooth models of a scheme over a DVR with pairwise no
  fibrewise rational identity can be shrunk to glue separatedly"`: 8 hits on
  smoothness and valuative separatedness; no exact match.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.Hom.fiber, IsPullback, Dense"`:
  service returned 0 hits and `unknown identifier 'IsPullback'`; this search
  supplies no negative mathematical evidence. Read its qualified Mathlib source
  `CategoryTheory/Limits/Shapes/Pullback/IsPullback/Defs.lean` instead.
- `msearch.py ... grep "baseDense|rationallyDisjoint|separated.*gluing|SmoothModel"
  AlgebraicGeometry`: 0 hits.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for `RationalMap`,
  `rationallyDisjoint`, `BaseDense`, `baseDense`, `SmoothModel`, `smoothModel`:
  existing ordinary rational maps and unrelated model constructions, no matching
  trait gluing or fibrewise-density declaration. Read Mathlib's `PartialMap`
  and `RationalMap` full opening definitions: they require density in the total
  space rather than fibrewise density, so are not interchangeable here.
- Item-id search in `lean/WeilConjectures`: no hit. Final full-name and concept
  search in those two Lean trees and `dag/lean_names_upstream.json`: no match.
  Read related DAG weak-Néron and model statements; no existing declaration of
  the present shrinking/gluing result was found.

Validation: scompile.py compiled the theorem independently under the sandbox and
actual module names against the live server library in approximately 1.8 seconds
per file. No errors or non-sorry warnings. The only postponed theorem is the item
itself. No STATEMENT-DISPUTED finding or node fault was found.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
