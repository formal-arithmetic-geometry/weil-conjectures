## Worker report

The module `Sheaf.AlgebraicGeometry.HenselianUnavoidableComponentValuationSection`
states `AlgebraicGeometry.henselian_unavoidable_component_valuation_section`, with
one sorry, and constructs the canonical `integralClosureGenericTest` using Spec
of the inclusion of the actual integral closure. There are no new nodes, no
dependency replacements and no statement correction. The helper has real data;
its over-category commutativity proof is the existing scalar-tower equality.

Hypothesis and clause correspondence:

- R is a henselian DVR: `[CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [HenselianLocalRing R]`.
- K is its fraction field: `[Field K] [Algebra R K] [IsFractionRing R K]`.
  S, eta and s use `Spec R`, the map induced by `algebraMap R K`, and
  `Spec.map (IsLocalRing.residue R)` respectively. No independent generic or
  closed point is substituted.
- The fixed algebraic closure is `[Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]`;
  the R-algebra structure is compatible through `[IsScalarTower R K Ω]`.
  B is always the existing `integralClosure R Ω`, never an arbitrary subring.
- X is the contravariant functor on `Over (Spec R)`, with values in
  `Type (max u v)`; `hX` is its sheaf condition for `Scheme.fpqcTopology.over`.
  The sheaf condition is the usual covering equalizer condition, not an etale
  or fppf replacement. Functor-value universes can be larger than scheme rings.
- `hchart` supplies a single fpqc-covering morphism t through membership in
  `Scheme.fpqcPrecoverage`, and a genuine `RepresentableBy Y` for the restriction
  `(Over.map t).op ⋙ X`. It requires `IsSeparated Y.hom`, `Flat Y.hom`,
  `LocallyOfFinitePresentation Y.hom`, `QuasiCompact Y.hom` and
  `QuasiSeparated Y.hom`. These are separatedness and finite presentation
  exactly: Mathlib's IsSeparated means the diagonal is a closed immersion;
  finite presentation includes the two quasi-compactness conditions.
- `Xη`, `eη` and `Xs`, `es` are schemes over the actual two fields with the
  representing natural bijections. `hη` and `hs` are precisely finite type,
  namely locally finite type and quasi-compact.
- C is an open of Xη whose underlying set equals `connectedComponent p` for
  some point p. This includes nonemptiness. Every connected component in a
  finite-type scheme over a field is clopen, as explained in proof step 5;
  thus specifying its open structure does not restrict the components.
- `hunavoidable` quantifies over every `Subfunctor X`. The first antecedent
  says for every scheme test H and section x there exists an open W such that,
  for every map f to H, restriction of x is in U exactly when f factors
  through W. The equivalent factorization criterion is `Set.range f.left ⊆ W`.
  This is the full representable-open inverse-image condition, without
  requiring X itself to be represented or be an algebraic space.
- The second antecedent says U is all of X on every test over the closed
  residue field (`U.obj ... = Set.univ`), i.e. `U_s = X_s`.
- The third antecedent presents its generic fibre by an open W stable under
  connected components (`∀ p ∈ W, connectedComponent p ⊆ W`), using eη on
  every generic test. This is exactly a union of connected components.
- The conclusion of `hunavoidable` says every generic test factoring through
  C belongs to U. By the same representable-open criterion this is precisely
  containment of C in the generic fibre of U.
- The result first supplies `IsLocalRing (integralClosure R Ω)` and
  `IsFractionRing (integralClosure R Ω) Ω`, then the displayed valuation-ring
  criterion `∀ a ≠ 0, a ∈ B ∨ a⁻¹ ∈ B`. B is already a domain as a subring
  of Ω, so this is the usual local valuation ring with that fraction field.
- The quantifier over D is over every connected component, with nonemptiness
  supplied by a point p, of the actual scheme pullback C ×_K Spec Ω.
- x belongs to `X.obj (op (Over.mk (Spec.map (algebraMap R B))))`, i.e. X(B).
  The morphism g is the generic Ω-valued point of Xη; z is its lift to C_Ω,
  explicitly commuting with the projection and C's inclusion. The equation
  `eη.homEquiv g = X.map (integralClosureGenericTest R K Ω).op x` identifies
  this point with the restriction of x, not some unrelated geometric point.
  Membership of `z.left (IsLocalRing.closedPoint Ω)` in D is precisely the
  prescribed component condition. Spec Ω has its single canonical point.
- The last equality says the closed point of Spec B maps to the closed point
  of Spec R. Consequently the closed restriction of x is in X_s: its base
  map R → κ(B) factors through κ(R), and X is a functor on S-schemes.
  This is the closed-value clause; it does not impose a chosen closed point
  of X_s or a residue-field identification.
- No group law, smoothness, excellence, finiteness of B/R or finite
  normalization module is assumed.

Existing dependency declarations were read in full, including docstrings:

- `def-sc-discrete-valuation-ring`: Mathlib.RingTheory.DiscreteValuationRing.Basic,
  `IsDiscreteValuationRing` (domain is a separate class binder).
- `def-weil-pbc-henselian-terminology`:
  WeilConjectures.Mathlib.RingTheory.Henselian and Mathlib.RingTheory.Henselian,
  `HenselianLocalRing`; the upstream strictly-henselian class was also inspected.
- `def-weil-affine-spectrum`: Mathlib.AlgebraicGeometry.Scheme, `Spec`, `Spec.map`.
- `def-weil-algebraic-closure`: Mathlib.FieldTheory.IsAlgClosed.Basic,
  `IsAlgClosure`, the class for an arbitrary chosen algebraic closure.
- `def-weil-pbc-integral-closure`:
  Mathlib.RingTheory.IntegralClosure.Algebra.Basic, `integralClosure`.
- `def-weil-pbc-fpqc-covering`: Mathlib.AlgebraicGeometry.Sites.Fpqc,
  `Scheme.fpqcPrecoverage` and `Scheme.fpqcTopology`.
- `def-pc-representable-functor`: Mathlib.CategoryTheory.Yoneda,
  `Functor.RepresentableBy` with its full natural hom-equivalence signature.
- `def-weil-flat-morphism`: Mathlib.AlgebraicGeometry.Morphisms.Flat, `Flat`.
- `def-sbc-locally-finite-presentation`:
  Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation,
  `LocallyOfFinitePresentation`.
- `def-weil-closed-immersion`: Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
  `IsClosedImmersion`, through `IsSeparated`'s diagonal definition.
- `def-weil-finite-type-morphism`: Mathlib.AlgebraicGeometry.Morphisms.FiniteType
  and QuasiCompact, `LocallyOfFiniteType` and `QuasiCompact`.
- `def-weil-connected-scheme`: Mathlib.Topology.Connected.Basic, `ConnectedSpace`
  and `connectedComponent` (the latter is the component-set operation used).
- `def-weil-open-immersion`: Mathlib.AlgebraicGeometry.OpenImmersion,
  `IsOpenImmersion`, via the existing scheme open objects and their inclusions.
- `def-pc-subfunctor`: Mathlib.CategoryTheory.Subfunctor.Basic, `Subfunctor`.
- `def-pc-fibre-product`:
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  `pullback`, `pullback.fst`, `pullback.snd`, with explicit scheme category.

All recorded proof modules are imported privately. The image flat-base-change
record has no module field; its declarations were located in
WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant,
which is imported privately. Three proof-only nodes have no current Lean
interface: lem-sfb-fpqc-finite-presentation-normalization-model,
lem-sfb-dense-generic-trait-selection, and
lem-sfb-geometric-connected-component-surjective. They are not needed to type
this statement and are not duplicated; all twelve proof steps are preserved in
the theorem docstring for their eventual proof imports.

Edge cases checked before writing: an empty generic fibre has no C and hence no
instance of hC; a connected component and every D are nonempty by their point
witnesses. An empty special fibre makes the empty open subfunctor a counterexample
to unavoidability, so no spurious section of a generic-only model is asserted.
For Spec R disjoint union Spec K, the generic-only component is avoidable. For
Spec R, the condition gives the canonical absolute valuation section. No
reducedness or separability condition is imposed: inseparable residue extensions
and nonreduced fibre schemes remain included. C's open structure is justified by
the finite-type hypothesis, not required on an arbitrary non-Noetherian chart.
No characteristic case is excluded. Universes for all scheme tests are the
scheme universe u, never an independently smaller test universe.

Searches (msearch.py, Q16/item; original machine search output retained in sandbox
searches.jsonl):

- LeanFinder: "henselian discrete valuation ring fpqc sheaf unavoidable generic
  connected component integral closure algebraic closure valuation section".
  Eight unrelated valuation/henselian results; no statement match.
- Loogle: "CategoryTheory.Subfunctor, CategoryTheory.Functor.RepresentableBy".
  Zero hits for the combined query; declarations located and read directly.
- Mathlib grep: "unavoidable|IsOpenSubfunctor|openSubfunctor|Representably.*Open".
  Two unrelated text matches, no statement or new notion needed.
- LeanSearch: "An fpqc sheaf over a henselian discrete valuation ring has a
  section over the integral closure in an algebraic closure through each
  unavoidable generic component". Eight hits about integral closure, generic
  points and scheme structure, none is this theorem.
- rg in WeilConjectures and Sheaf for the same unavoidable/open-subfunctor terms:
  no matching theorem. Open subspaces for algebraic spaces exist but require
  algebraic-space data absent from this node, so no such extra hypothesis is used.
- rg for the exact node id in WeilConjectures: no match. rg for both proposed
  declaration names in WeilConjectures, Sheaf and dag/lean_names_upstream.json:
  no match.
- Source read: Stacks more-morphisms.tex, label
  lemma-quasi-finite-quasi-section-meeting-nearby-open-X (05GU), and the latest
  blueprint unit sk-thm-sf-ctf-stability. The node is the reviewed auxiliary
  synthesis, not the unit's statement or a verbatim Stacks theorem.

Validation: scompile.py in module mode, with explicit universes and bound
variables. Final compile and delivery preflight results are recorded below.

## Second reading by Q16

The delivered section said "no second worker reading" (self-check under the direct-dispatch
policy). This section replaces it with an independent clause-by-clause reading, done by the
maintainer's reviewer against the node, Stacks 05GU (more-morphisms.tex) and the module at
delivery 55304ea3. The worker's original self-check had found and repaired: the generic
over-category structure-map mismatch, a missing public GrothendieckTopology.over import, and
scheme-category inference on pullbacks.

Node clauses → Lean (verdict):

- R henselian DVR → `[IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]` (exact;
  def-sc-discrete-valuation-ring, def-weil-pbc-henselian-terminology's HenselianLocalRing).
- K = Frac R → `[Field K] [Algebra R K] [IsFractionRing R K]` (exact). S = Spec R; η and s
  are given by Spec.map of `algebraMap R K` and `IsLocalRing.residue R` (canonical).
- Ω/K algebraic closure → `[IsAlgClosure K Ω]`. `[Algebra R Ω] [IsScalarTower R K Ω]` is the
  compatible structure and no restriction. B = `integralClosure R Ω` (exact).
- X is an fpqc sheaf of sets on S-schemes → `X : (Over Spec R)ᵒᵖ ⥤ Type (max u v)` with
  `Presheaf.IsSheaf (fpqcTopology.over _)`. `RepresentableBy` lets F's universe differ from
  the hom universe (Yoneda.lean:284), so no universe is forced.
- There is an fpqc T → S with X_T separated, flat and of finite presentation →
  `hchart`: singleton t ∈ fpqcPrecoverage, `RepresentableBy Y` of `(Over.map t).op ⋙ X`,
  IsSeparated (diagonal closed immersion), Flat, LocallyOfFinitePresentation, QuasiCompact,
  QuasiSeparated (exact; nothing stronger).
- X_η and X_s are represented and of finite type → `Xη, eη, Xs, es`, plus
  `LocallyOfFiniteType ∧ QuasiCompact` (exact).
- C is a connected component of X_η → `C : Xη.left.Opens` with `C = connectedComponent p`.
  This is no restriction: X_η is Noetherian (finite type over a field), so every component is
  clopen. It is nonempty by p.
- Unavoidability → `hunavoidable`, quantified over every `Subfunctor X`.
  - Openness: for each H and x ∈ X(H) there is an open W ⊆ H with X.map f x ∈ U ⟺ range f ⊆ W
    for all f. This is the representable-open criterion (def-weil-open-immersion,
    def-pc-subfunctor).
  - U_s = X_s: U is univ on every κ(R)-test.
  - U_η is a union of components: some open W of X_η is saturated under connectedComponent
    and represents U on every K-test through eη.
  - The conclusion "C ⊆ U_η" reads: every K-test factoring through C lies in U.
  - All four parts are exact. The parenthesization of the → chain and the ↔ was read: each ↔
    is inside its own ∀ and the antecedents are parenthesized.
- B is a local valuation ring with fraction field Ω, and a or a⁻¹ ∈ B → `∃ _ : IsLocalRing B,
  IsFractionRing B Ω ∧ ∀ a ≠ 0, a ∈ B ∨ a⁻¹ ∈ B` (exact; B is a domain as a subring of Ω).
- For each component D of C ×_K Ω there is x ∈ X(Spec B) whose Ω-restriction lies in D →
  ∀ D = connectedComponent p of `pullback (C.ι ≫ Xη.hom) (Spec Ω → Spec K)`; ∃ x, g, z with
  z a section of pullback.snd and z ≫ fst ≫ C.ι = g.left. The equation
  eη.homEquiv g = X.map (integralClosureGenericTest).op x pins g as the restriction of x.
  z(pt) ∈ D. By the pullback property z is determined by g, so this is exactly "the
  restriction lies in D" (exact).
- The closed value lies in X_s → the closed point of Spec B maps to the closed point of
  Spec R. Hence Spec κ(B) → S factors through s, and the restriction of x is an X_s-point
  (equivalent).
- No group law or smoothness: none is assumed (checked).

Helper: `integralClosureGenericTest` is Over.homMk of Spec(B ↪ Ω), with the scalar-tower
commutativity. It is real canonical data, listed in lean.declarations and docstringed with its
source and blueprint.

Edge cases:
- C_Ω is nonempty because Spec Ω → Spec K is surjective, so the closed-point clause under
  ∀ D is never vacuous.
- If the special fibre is empty, the empty subfunctor witnesses avoidability, so the
  hypothesis is unsatisfiable rather than wrong.
- Spec R ⊔ Spec K: the generic-only component is avoidable.
- Non-reduced and inseparable cases are covered; no characteristic is excluded.
- Every universe is bound (u for schemes and rings, v for the values of the sheaf).

Searches: rg in side-live lean/Sheaf and WeilConjectures for open-subfunctor notions
(`IsOpenSubfunctor`, `Subfunctor.IsOpen`, `openSubfunctor`, `^def Is*Open*`) and for
"unavoidable".
- The only hits are AlgebraicSpace.OpenSubspace, which needs algebraic-space data the node does
  not give, and the parent TraitComponentMinimalEnvelope's group-valued theorem-module helpers
  (HasFibre, IsComponentUnion). Neither fits a set-valued X, so the inline formulation is right.

Records:
- lean.statement equals the file signature verbatim (checked by script).
- The node differs from side-live only in `lean`; there is no statement_change and no new node.
- Every stmt_dep declaration matches its recorded `lean`.
- The module has one sorry (the theorem), source and blueprint docstrings, and all twelve
  proof steps in the theorem docstring.

Mismatches found: none in the Lean or the records; the only change is this report section.
