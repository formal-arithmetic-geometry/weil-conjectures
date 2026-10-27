## Worker report

The delivery states `AlgebraicGeometry.regularMorphism_formalCompletion` in
`Sheaf.AlgebraicGeometry.RegularMorphismFormalCompletion`. Its only theorem has proof
`sorry`. It also supplies the missing canonical ringed-space completion and formal affine
chart definitions in `Sheaf.AlgebraicGeometry.AdicFormalGeometry`, owned by the new node
`def-per-adic-formal-geometry`. That module has real definitions, with no postponed theorem
and no `sorry`. The item's statement, proof and proof dependencies are unchanged. Its
statement dependencies gain only the new definition node.

Hypothesis and conclusion correspondence:

- The objects `X Y : Scheme.{u}` and `f : Y ⟶ X` are the schemes and morphism of the node.
- `[IsNoetherian X] [IsNoetherian Y]` express Noetherian schemes. Mathlib's class is locally
  Noetherian plus quasi-compact, and `isNoetherian_iff_of_finite_affine_openCover` identifies
  this with the finite Noetherian affine-cover convention explicitly required by the node.
- `_qX : X ⟶ Spec (CommRingCat.of (ULift.{u} ℚ))` is the structure over Q. The structure on
  Y is its composite with f; thus f is automatically a Q-morphism for these structures.
  ULift only places Q in the scheme universe and changes neither the field nor its spectrum.
- `_hX` and `_hY` quantify over all affine opens and assert `IsQuasiExcellent Γ(X,U)` and
  `IsQuasiExcellent Γ(Y,V)`, respectively. This is the stated affine-chart convention.
- `[Flat f]` is precisely flatness of the morphism. Mathlib's `Flat.iff_flat_stalkMap` gives
  the equivalent stalkwise formulation in the flat-morphism dependency.
- `_hf` binds each point `x : X`, each field K, each residue-field algebra structure and
  each `Module.Finite (X.residueField x) K`. Its conclusion is `IsRegularScheme` of the
  pullback of `f.fiberToSpecResidueField x` along Spec of the algebra map to K. This is
  exactly the finite-extension base change of the scheme-theoretic fibre, not an arbitrary
  ring or an assumed smooth morphism. In particular it includes the identity extension.
  K uses the same universe as the residue field; every finite extension has a model in
  that universe. There is no independent smaller test universe making the condition vacuous.
- `I : X.IdealSheafData` and `J : Y.IdealSheafData` use the existing quasi-coherent ideal
  sheaf representation. `_hI` and `_hJ` assert the genuine `RingedSpace.IsCoherent`
  predicate for their `toModules`, including the finite-type-kernel clause, rather than
  merely naming the weaker quasi-coherent finite-type conjunction.
- `hIJ : I.comap f ≤ J` is exactly the extended ideal containment I O_Y ⊆ J.
- `adicFormalCompletion I` is the colimit in ringed spaces of the canonical diagram of
  closed subschemes V(I^n); its underlying topological colimit is V(I), and the sheaf is
  the inverse limit of the quotient sheaves. On affine charts its ring is lim A/I^n,
  the dependency's `AdicCompletion`. Including n=0 merely adds the empty initial
  thickening V(1); the tail n≥1 is cofinal and the completion is unchanged.
- `adicThickeningMap f I J hIJ` uses the existing `subschemeMap` with ideal-power
  containment. `adicFormalCompletionMap` applies the actual colimit functor to this
  natural transformation. No arbitrary map, chosen lift or extra comparison assumption
  stands in for the induced completed morphism.
- `IsAdicFormalAffineOpen Z U` requires that A=O_Z(U) be Noetherian, complete and separated
  for a finitely generated ideal K, and that Z restricted to U be isomorphic to Spf(A,K).
  `adicFormalSpec` itself is the same completion construction applied to Spec A and the
  ideal transported along `Scheme.ΓSpecIso`. This is the open-prime space with its
  inverse-limit structure sheaf. This definition allows all formal affine opens; it is
  not limited to completions of ordinary affine opens or to principal formal opens.
- `IsNoetherianAdicFormalScheme` spells out the explanatory finite-formal-affine-cover
  convention. `IsReducedAdicFormalScheme` and `IsQuasiExcellentAdicFormalScheme` spell out
  the node's explanatory chart-ring predicates. These are definitions, not additional
  hypotheses or conclusions imposed on the item.
- The conclusion `IsRegularOnAdicFormalAffines (adicFormalCompletionMap f I J hIJ)`
  quantifies over every target open U and source open V satisfying the formal affine
  predicate, and every containment V⊆fhat^(-1)(U). `adicFormalAppLE` is the structure
  sheaf map followed by restriction, so its ring homomorphism is exactly A→B with
  A=O(U) and B=O(V). The conclusion is the existing `RingHom.IsRegular`: flat with
  Noetherian geometrically regular fibres. Its purely-inseparable finite-extension
  test is the equivalent Stacks 0381 criterion, including arbitrary finite extensions
  as in the node. No finite-type hypothesis occurs anywhere on f.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian` and the
  finite affine-cover equivalence, for pqf-def-locnoeth and the explicit Noetherian convention.
- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent`, exposed by the new definition module,
  for def-exc-excellent-ring. Its complete signature and definition were read.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`, whose definition includes
  local Noetherianity and the upstream regular-stalk predicate, for def-weil-regular-scheme.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: exposes
  `AlgebraicGeometry.RingedSpace.IsCoherent` from `WeilConjectures.AlgebraicGeometry.Coherent`,
  for pqf-def-coherent. The current repaired record and source were read; no dependency
  interface repair is needed in this delivery.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`, `IsAdicComplete`,
  its compatible-sequence construction and ring structure, for def-weil-pbc-adic-completion.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`, for def-weil-flat-morphism.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberToSpecResidueField`, the
  canonical pullback fibre and its residue-field projection, for def-pc-scheme-fibre.
- `WeilConjectures.RingTheory.GRing`: `RingHom.IsRegular` and its definition via
  `Algebra.IsGeometricallyRegular`, for def-weil-pbc-g-ring.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`, `.Subscheme`, `.Functorial`, together with
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial` and `.Module`: existing
  ideal data, powers, inclusions, pullbacks, `subschemeMap`, `comap_pow`, and `toModules`.
- `Mathlib.Geometry.RingedSpace.SheafedSpace`: ringed-space colimits, explicitly built
  from topological colimits and limits of pushed-forward sheaves, and open restrictions.

Every already stated proof dependency is imported plainly: finite-type G-rings,
G-ring completion regularity, localization regularity, regular composition, the prime/maximal
local criterion, faithful-flat regular descent and regular-through-localization, together
with the Mathlib completion, pullback, localization-Noetherianity and quotient-Noetherianity
interfaces. Their source declarations were read. The proof-only nodes
lem-per-completed-base-regularity, lem-per-formal-affine-principal-refinement and
lem-per-quasi-excellent-formal-affines have no current Lean record or Mathlib match, so there
is no module to import yet. They are not statement prerequisites, and none of the new
constructions or predicates assumes their conclusions.

Edge cases checked before writing:

- Empty X or Y are allowed; finite formal covers permit n=0. Empty fibres and the zero
  coordinate ring are not excluded by a Nontrivial assumption.
- I=0 and J=0 give discrete formal schemes, recovering the ordinary scheme situation.
- The unit ideal gives an empty completion; the n=0 term of every thickening diagram is
  itself empty and is compatible with all the canonical transition maps.
- I and J need not agree, and hIJ need not be equality. No adic-morphism or finite-type
  assumption has been substituted for the node's containment.
- The finite-extension quantifier includes degree one and nontrivial finite extensions,
  with no separability restriction. The schemes are over Q as required by the item.
- Formal opens in the conclusion are arbitrary; the final maximal-local descent step
  of the node's proof is preserved in the theorem docstring, not replaced by a covering
  chart-only conclusion.

Searches performed before creating the module:

- msearch leanfinder, `Formal completion of a regular morphism of quasi excellent Noetherian
  schemes is regular on every formal affine chart`: 8 hits, ordinary formally unramified
  or smooth scheme morphisms; none states the theorem.
- msearch loogle, `"AdicCompletion", "IsRegular"`: 0 hits.
- msearch grep, `FormalScheme|FormalSpectrum|Spf|regular.*[Cc]ompletion`: hits were unrelated
  cusp-form names; the word-bounded formal-geometry follow-up had 0 hits.
- rg in both `lean/WeilConjectures` and `lean/Sheaf`, by declaration names and formal-geometry
  keywords: ordinary formal completion systems of modules and moduli-specific charts only;
  no formal spectrum or ringed-space completion construction and no copy of this theorem.
- The blueprint id has no upstream source match. `dag/lean_names_upstream.json` has no matching
  construction declaration. DAG and `tools/blueprint_refs.py` searches found no definition
  node for this formal geometry. The new node records the further LeanSearch, LeanFinder,
  Loogle and Mathlib grep outputs verbatim.

Source check: read Temkin Corollary 2.4.5 and Lemma 2.4.6 online, and the local Stacks
formal-spectrum construction in `formal-spaces.tex`, Tag 0AHY. The source confirms both
simultaneous completions with distinct ideals and the arbitrary-formal-affine conclusion.
No statement correction or STATEMENT-DISPUTED flag is needed.

Validation: scompile.py compiled each delivered module separately in dependency order,
including both sandbox and named-library passes. Both are clean; only the expected sorry
warning for the theorem is allowed. No live source or artifact was modified directly.

## New nodes

`def-per-adic-formal-geometry` owns `Sheaf.AlgebraicGeometry.AdicFormalGeometry` and its eleven
listed definitions. It supplies the missing adic formal completion, its functorial morphism,
formal spectrum and formal-affine terminology, including the exact all-affine regularity
conclusion. Source: Stacks Tag 0AHY (formal spectrum and completed structure sheaf), and
Temkin sections 2.4.1, 2.4.3, 2.4.12 and Lemma 2.4.6. Searches found generic colimits,
ordinary spectra and closed subschemes, which the construction reuses, but no definition
of the combined formal-geometric objects. Existing coherent formal modules are systems of
module sheaves, not a formal scheme or its underlying ringed space. All helper maps are
explicit; no existence theorem with a postponed proof is used to choose data.

## Second reading by Q47

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
