## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.FppfSourceFiniteAffineCharts` states
`AlgebraicGeometry.exists_fppf_source_finite_affine_charts`, with proof `sorry`.
No definition, helper, dependency module, new node or statement correction is needed.
The node copy changes only `lean`. There is no statement dispute.

I read the assigned node, every statement dependency and its Lean record, and the
recorded Mathlib definitions and docstrings. I also read every proof dependency and
its recorded Mathlib match. The source is Stacks descent.tex, Tag 02KL,
`lemma-flat-finitely-presented-permanence`, specifically the local-on-S-and-Y reduction,
openness and finite selection of affine source opens by their images. Its locally finite
type alternative gives precisely the hypotheses here. The blueprint ancestry is the
auxiliary affine reduction below lem-a1-affine-hc0, rather than the unit's statement.

Hypothesis and clause correspondence:

- Arbitrary schemes X,Y,S: `{X Y S : Scheme.{u}}`, with explicit `universe u`.
  Scheme morphisms q and h: `(q : X ⟶ Y) (h : Y ⟶ S)`.
- Flat q: `[Flat q]`; locally of finite presentation q:
  `[LocallyOfFinitePresentation q]`; surjectivity on points: `[Surjective q]`,
  whose field is `Function.Surjective q`.
- The composite h after q is locally of finite type:
  `[LocallyOfFiniteType (q ≫ h)]`. There is no assumption on h alone.
- Every y: `(y : Y)` before the existential conclusion.
- Affine V in S and W in Y: `∃ (V : S.Opens) (W : Y.Opens),
  IsAffineOpen V ∧ IsAffineOpen W`. These are actual open subschemes with the
  restricted structure sheaf, not just unrelated affine schemes or open embeddings.
  Here R is canonically Γ(S,V) and A is canonically Γ(Y,W). Mathlib's
  `IsAffineOpen.isoSpec` gives V.toScheme ≅ Spec Γ(S,V) and its counterpart for W;
  the node explicitly allows these canonical presentations up to isomorphism.
- The point containments are `h y ∈ V ∧ y ∈ W`.
- W contained in h inverse V is the witness `eWV : W ≤ h ⁻¹ᵁ V`.
- n is a nonnegative integer: `(n : ℕ)`; `Fin n` indexes the n charts (0-based indexing
  changes none of the finite-family content of the informal 1,...,n).
- Actual affine source opens: `(U : Fin n → X.Opens)` and
  `∀ i : Fin n, IsAffineOpen (U i)`. The canonical B_i is Γ(X,U i), and
  `(U i).toScheme ≅ Spec Γ(X,U i)` is supplied by `IsAffineOpen.isoSpec`.
- Every U_i is contained in q inverse W: the family of containment witnesses
  `eUW : ∀ i : Fin n, U i ≤ q ⁻¹ᵁ W`.
- The finite images cover exactly W:
  `(W : Set Y) = ⋃ i : Fin n, q '' (U i : Set X)`.
  This is not a claim that the U_i cover q inverse W.
- The canonical coordinate tower is
  `h.appLE V W eWV : Γ(S,V) ⟶ Γ(Y,W)` followed by
  `q.appLE W (U i) (eUW i) : Γ(Y,W) ⟶ Γ(X,U i)`.
  `appLE` is the structure-sheaf pullback followed by restriction, so there is no
  arbitrary choice of coordinate map. These use exactly the section-ring presentations
  selected in proof step 3 of the node.
- Each A → B_i is flat:
  `(q.appLE W (U i) (eUW i)).hom.Flat`.
- Each A → B_i is finitely presented:
  `(q.appLE W (U i) (eUW i)).hom.FinitePresentation`.
  `RingHom.FinitePresentation` unfolds exactly to the dependency's recorded
  `Algebra.FinitePresentation` for the algebra structure given by this ring map.
  Thus this uses the recorded notion and does not require a duplicate dependency module.
- Each R → B_i composite is finite type:
  `(h.appLE V W eWV ≫ q.appLE W (U i) (eUW i)).hom.FiniteType`.
- Tower compatibility with the given composite scheme morphism is the final equality
  of that composite with `(q ≫ h).appLE V (U i) (eUV i)`.
  `eUV` records the containment U_i in (h after q) inverse V, implied by eUW and eWV;
  this existential witness adds no assumption or extra restriction on the charts.
- No quasi-compactness, quasi-separatedness, separation or Noetherian hypothesis occurs.
  All variables and universes are explicitly bound; `autoImplicit` is disabled.

Dependency declarations used (all are the recorded Mathlib notions):

- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme, `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`.
- def-weil-flat-morphism: Mathlib.AlgebraicGeometry.Morphisms.Flat,
  `AlgebraicGeometry.Flat` (the stalkwise equivalence is `Flat.iff_flat_stalkMap`).
- def-sbc-locally-finite-presentation:
  Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  `AlgebraicGeometry.LocallyOfFiniteType`; only its local finite type clause is assumed.
- def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Spec` and `Spec.map`; Mathlib.AlgebraicGeometry.AffineScheme,
  `AlgebraicGeometry.IsAffineOpen` and `IsAffineOpen.isoSpec` implement affine opens
  with their canonical section-ring coordinates.
- def-weil-pbc-flat-ring-map: Mathlib.RingTheory.RingHom.Flat, `RingHom.Flat`,
  defined as `Module.Flat` via the ring map's algebra structure.
- def-weil-pbc-finitely-presented-algebra: Mathlib.RingTheory.FinitePresentation,
  `Algebra.FinitePresentation`, used through its exact ring-map form
  `RingHom.FinitePresentation`.
- def-weil-pbc-finite-type-algebra: Mathlib.RingTheory.FiniteType, `RingHom.FiniteType`.

Proof-dependency imports are present: Mathlib.AlgebraicGeometry.AffineScheme contains
`Scheme.isBasis_affineOpens` and `Scheme.compactSpace_of_isAffine`;
Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen contains `UniversallyOpen.of_flat`;
Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated contains
`quasiSeparatedSpace_of_isAffine`; Mathlib.Topology.Defs.Filter contains `CompactSpace`.
The three coordinate criteria are `flat_iff`,
`LocallyOfFinitePresentation.finitePresentation_appLE` and `locallyOfFiniteType_iff`
in their respective already imported morphism-property modules. The canonical
composition equation is `Scheme.Hom.appLE_comp_appLE` in the Scheme module.
The theorem docstring preserves all four proof steps and their cited DAG inputs.

Edge cases checked before writing: empty Y gives no y and is vacuous; a chosen W
contains y and is nonempty, so the displayed finite image-cover condition correctly
rules out n=0 for actual witnesses while retaining n≥0 in the signature. Empty affine
source charts, hence zero rings among B_i, are allowed. The base/target affine
neighbourhoods cannot be empty because of their marked points. For the identity map,
one affine chart works. An infinite disjoint union of copies of an affine target can
satisfy the hypotheses without quasi-compact source or q; one component's image covers
the target, consistent with the conclusion. No affine intersections are used, so
nonseparated ambient schemes are included. All schemes are objects of Mathlib's
category Scheme.{u}, at arbitrary u; no extra universe equality is imposed.

Duplicate searches actually run in this session using the prescribed msearch.py:

- LeanFinder: "Flat surjective locally finitely presented scheme morphisms admit finite
  affine source charts covering affine target neighbourhoods with finite type coordinate
  maps over a base". Eight hits: locallyOfFinitePresentation_iff, locallyOfFiniteType_iff,
  UniversallyOpen.of_flat, LocallyOfFinitePresentation and individual appLE criteria.
  None selects the finite charts and states the tower conclusions together.
- Loogle: "AlgebraicGeometry.Flat, AlgebraicGeometry.LocallyOfFinitePresentation".
  Twelve hits, including UniversallyOpen.of_flat, flat descent, fppf covering membership
  and étale criteria. No complete statement match.
- Mathlib grep: "finite.*affine.*(chart|refin)|appLE_comp" in AlgebraicGeometry.
  Twenty-five hits, primarily appLE_comp_appLE and its applications; these provide
  coordinate functoriality but not the finite-chart construction.
- LeanSearch: "A flat surjective locally finitely presented scheme morphism admits finite
  affine source charts covering an affine target neighbourhood with compatible coordinate
  ring towers over an affine base". Eight hits, primarily flat_appLE, affine faithful
  flatness, Flat.stalkMap and finitePresentation_appLE. No complete match.
- rg of lean/WeilConjectures and lean/Sheaf for finite affine charts, source charts,
  finite fppf refinements and the item's id; also searched dag/lean_names_upstream.json
  for the item's id. No exact declaration for this item.
  Read WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc's
  `Scheme.exists_finite_fppf_affine_open_refinement`: it refines an existing covering
  of an affine base and omits our base-neighbourhood choices and all three coordinate
  tower properties. Read Sheaf.AlgebraicGeometry.LftFiniteRelativeAffineAtlas:
  its `exists_finite_relative_affine_atlas` assumes qcqs schemes and asserts covers of
  full inverse images, so it is a different statement. The parent's
  `locallyOfFiniteType_of_flat_lfp_source` concludes local finite type, not chart data.

Validation: scompile.py compiled the sandbox and final library module successfully
(1.3 seconds each), with no errors and no non-sorry warnings. No local/global build was run.

## Second reading by Q07

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
