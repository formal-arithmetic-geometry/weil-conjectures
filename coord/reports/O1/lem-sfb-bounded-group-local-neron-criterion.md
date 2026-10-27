## Worker report

The module `Sheaf.AlgebraicGeometry.BoundedGroupLocalNeronCriterion` states
`AlgebraicGeometry.exists_localNeronModel_of_bounded_strictHenselization_points`.
Its only proof is `sorry`. No definition, additional axiom, new node, dependency
repair, or statement correction is introduced.

Source read: Bosch--Lütkebohmert--Raynaud, *Néron Models*, primary-source scan
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf,
1.1 Definition 2 and the following affine-coordinate characterization (printed
pp. 8–9), 1.2 Definition 1 (p. 12), and 1.3 Theorem 1 (p. 16, scan PDF page 23
when counted from one). The last theorem assumes a DVR, its strict henselization
and a smooth finite-type group; its sufficient boundedness condition is precisely
the item's. There is no extra completeness, excellence, residue characteristic,
residue-field perfection, or connectedness condition. All six proof steps of the
DAG node are reproduced in the declaration docstring. The item is not a unit
statement; neither its statement nor its proof plan was changed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- `R : Type u`, `[CommRing R] [IsDomain R] [IsDiscreteValuationRing R]` is the
  stated DVR: Mathlib's class is a local PID with nonzero maximal ideal.
  `[Field E] [Algebra R E] [IsFractionRing R E]` makes `E` any presentation of
  its fraction field. `Spec (.of R)` is exactly `T`.
- `Ω`, `[Field Ω] [IsAlgClosed Ω]`, and `s : Spec (.of Ω) ⟶ Spec (.of R)` give
  the geometric point. `hs` says that every point of its one-point spectrum
  maps to the maximal ideal of `R`, hence to the closed point.
- `Scheme.strictHenselizationRing s` is the recorded coordinate-ring colimit
  of affine pointed étale neighbourhoods, not a replacement henselian ring.
  `FractionRing (Scheme.strictHenselizationRing s)` is `E^sh`.
  The existential domain and DVR proof witnesses inside `hbounded` merely
  make explicit the DVR of which the node takes the valuation. They are not
  independent assumptions on `R` or on a chosen auxiliary extension.
  The node's boundedness condition already uses this DVR and its fraction
  field; these witnesses let that condition be stated without an unavailable
  global instance for the strict henselization.
- `j : E →+* FractionRing (Scheme.strictHenselizationRing s)` has the displayed
  restriction equation on `R`. Its right side is the canonical map obtained
  from `Spec.preimage (Scheme.strictHenselizationStructuralMap s)` and the
  fraction-ring inclusion. Because `E` is the fraction field of `R`, this
  equation uniquely determines `j`; two such maps agree on numerators and
  denominators. Thus the equation specifies the canonical extension, not an
  arbitrary action, extension field, or morphism. The usual injective map
  from a DVR into its strict henselization extends to precisely this `j`.
- `G : Over (Spec (.of E))`, `[GrpObj G]` is the group scheme from the recorded
  dependency. `[Smooth G.hom] [IsSeparated G.hom]` gives smoothness and
  separatedness. `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]` is finite
  type, following this dependency's recorded conjunction convention.
- Inside `hbounded`, `n : ℕ`, `B : Fin n → CommAlgCat.{u} E`, and the morphisms
  `ι i : Spec (B i) ⟶ G` in `Over (Spec E)` give finitely many affine charts
  with their actual structure maps. `IsOpenImmersion (ι i).left` and the
  pointwise cover condition say they are open subschemes covering `G`.
- `m : Fin n → ℕ`, `b i : Fin (m i) → B i`, and
  `Algebra.adjoin E (Set.range (b i)) = ⊤` say exactly that these are finite
  lists of generators as `E`-algebras.
- `C i` is a set of `E^sh`-points of the corresponding chart, encoded as
  morphisms in `Over (Spec E)` with the pinned scalar map `j`.
  `∀ x, ∃ i y, y ∈ C i ∧ y ≫ ι i = x` is precisely the union condition on
  **all** `G(E^sh)`, without requiring the `C i` to be disjoint or to contain
  every point of their chart.
- `c : Fin n → ℤ` and the final inequality in `hbounded` are the coordinate
  bounds for every `i`, every `x ∈ C i`, and every generator `k`.
  `(Spec.preimage x.left).hom (b i k)` evaluates that actual coordinate at
  that actual point. Mathlib's normalized multiplicative maximal-ideal
  valuation takes a uniformizer to `exp (-1)`; therefore its bound
  `≤ exp (-c i)` is exactly the additive bound `v ≥ c_i`. It takes zero to
  zero, so this includes `v(0) = +∞` without exception.
- The conclusion quantifies `M : Over (Spec R)` and an isomorphism `e` from
  `(Over.pullback (Spec.map (algebraMap R E))).obj M` to `G`. This is an
  isomorphism of `E`-schemes `M_E ≅ G`. No group structure on `M` or group
  compatibility of `e` is demanded, since the item's conclusion does not
  demand them.
- The four conjunctions on `M.hom` give smooth, separated, finite-type `M`.
  `IsSeparated` is exactly the closed-immersion condition on its diagonal,
  not merely a separatedness condition on the underlying topological space.
- For **every** `X : Over (Spec R)` with `Smooth X.hom`, the function whose
  bijectivity is asserted is `(Over.pullback ...).map f ≫ e.hom`.
  Its domain is `X ⟶ M` over `R`, its codomain is `X_E ⟶ G` over `E`.
  This is restriction/base change followed by the chosen generic-fibre
  identification. No finite-type, quasi-compactness, separatedness,
  nonemptiness, or connectedness condition is put on the test scheme.

Dependencies read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `IsSeparated`, whose
  only field is closed immersion of the diagonal.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
  `Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing`:
  `IsDiscreteValuationRing.maximalIdeal`; its associated normalized valuation
  is `IsDedekindDomain.HeightOneSpectrum.valuation` in
  `Mathlib.RingTheory.DedekindDomain.AdicValuation`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points
  use the dependency's recorded inline representation. Its equivalent
  residue-field description `Scheme.SpecToEquivOfField` was also read.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, applied to
  `Over (Spec E)` as required by `def-sc-group-scheme`.
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`:
  `Scheme.strictHenselizationRing`, full definition and docstring read;
  `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `Scheme.strictHenselizationStructuralMap`, the uniquely characterized
  canonical map. `Spec.preimage` is from
  `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded
  conventions identify scheme and morphism base change with
  `CategoryTheory.Over.pullback` (defined in
  `Mathlib.CategoryTheory.Comma.Over.Pullback`). The recorded
  `Scheme.Modules.moduleBaseChange` concerns modules and is not substituted
  for scheme base change.
- Proof imports: `Mathlib.AlgebraicGeometry.Morphisms.Proper` records
  `IsProper.isStableUnderBaseChange` from `lem-pc-proper-base-change`;
  `Smooth` supplies its smooth base-change clause, `smooth_comp` for
  `lem-trf-smooth-composition`, and the flatness/local-finite-presentation
  instances of `lem-pc-smooth-flat`. The other four proof dependencies have
  no Lean records, so no invented modules are imported for them.

Searches actually run:

- `msearch.py leanfinder`, query "Bounded unramified points of a smooth finite
  type group scheme over a discrete valuation field imply existence of a
  finite type Neron model": eight results, all Weierstrass minimal/good
  reduction statements, no exact match.
- `msearch.py leansearch`, query "Existence of a finite type Neron model from
  bounded points over the strict henselization fraction field": eight
  results concerning henselian rings and finite morphisms, no exact match.
- `msearch.py loogle`, query
  `IsDiscreteValuationRing.valuation, Over.pullback, Algebra.adjoin`: no hits;
  it reports unknown identifier `IsDiscreteValuationRing.valuation`.
  The actual valuation interface was subsequently located and read directly.
- `msearch.py grep`, query `Neron|neron|IsBounded` in `AlgebraicGeometry`:
  zero hits. Direct `rg` over both `lean/WeilConjectures` and `lean/Sheaf`
  for `Neron|Néron|neron` and the item id found no existing statement.
  Direct name search found no collision for the new theorem or module.
  `tools/lean_names_upstream.py show` was consulted as well.
- The strict-henselization DVR interface search found the withdrawn
  `Sheaf.AlgebraicGeometry.StrictHenselizationDVR`; `scompile.py --source`
  confirmed the current server also has it commented out. It is not used,
  reintroduced, or assumed as a theorem. The boundedness witness explicitly
  includes its specified DVR structures so that no unrecorded theorem or
  `sorry`-constructed datum is needed to elaborate this statement.

Edge cases checked: the zero ring and fields as `R` are excluded exactly by
DVR; the zero characteristic and mixed characteristic cases remain allowed.
Zero coordinate values satisfy the inequality since the multiplicative
valuation is zero there. Bounds of either sign are allowed. An empty
coordinate list is allowed whenever the algebra is generated by its scalars
(e.g. the identity group chart); empty `C i` are allowed. Empty charts cause
no problem. A completely empty cover would contradict the group identity
and the cover condition, as it should. The identity group is included without
positive dimension or connectedness assumptions. Empty smooth test schemes,
schemes with empty special fibre, and smooth schemes that are not of finite
type are all included by the final quantifier. The universe `u` is explicit
on every input, chart algebra, geometric field, and base scheme, using the
recorded same-universe scheme/strict-henselization interface; no independent
smaller test universe makes any hypothesis vacuous.

Validation: `scompile.py` compiled the module both as a sandbox file and at
its intended library module path, with no errors or non-sorry warnings.
The initial run found a parenthesis typo in a chart binder, which was fixed;
the clean run took 6.0 and 9.4 seconds respectively. The node copy changes
only `lean`, whose signature is extracted verbatim from the module.

## Second reading by O1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
